import CategoricalInfluenceDiagramsProofs.Obstruction

/-!
# Lenses and open-game equilibria (ADR 0020)

A reward kernel `f = (K, W) : X → Y` transports a context in two directions. Forward, a prior
`μ` on `X` becomes the boundary law `ν = μ K` on `Y` (`pushforward`); backward, a continuation
`c` on `Y` becomes the value function `x ↦ Σ_y (W x y + K x y · c y)` on `X` (`continuation`).
The pair is a lens, and serial composition of reward kernels is sent to composition of lenses
when the later kernel is normalised (`lens_comp`, `lens_id`). The expected utility pairs the
two directions: `EU_f(μ, c) = L_f(μ) + Σ_y ν y · c y` (`eu_eq_prefixReward_add`).

**Open games.** Following open games, a `Game X Y` has strategies, a play (a normalised reward
kernel for each strategy) and an equilibrium predicate over contexts `(μ, c)`. A *decision*
game is one component whose decisions are controlled together; its equilibria are the
strategies that maximise expected utility in the context. The serial composite `G.seq H` plays
the composite kernel, and `(s, t)` is an equilibrium in `(μ, c)` when `s` is one of `G` in the
context `(μ, c_t)` and `t` one of `H` in `(ν_s, c)`: each part sees the context the other
induces, transported by the lenses. The tensor is in `GameTensor.lean` (ADR 0020, amended).

**Results.**
- Serial composition is associative and unital on equilibria (`seq_assoc_eq`,
  `idGame_seq_eq`, `seq_idGame_eq`) and on plays (`seq_assoc_play`), because the induced
  contexts compose by the lens laws.
- For two decision games an equilibrium is exactly a pair from which neither component gains
  by changing its own strategy, measured by the composite's expected utility
  (`seq_decision_eq_iff`).
- A global optimum is an equilibrium, for every game built from decision games and identities
  by serial composition (`Sound`, `seq_sound`).
- The converse fails (`coordination_equilibrium_not_optimal`): two decisions that must agree,
  the later one not observing the earlier, have an equilibrium worth `1` where the optimum is
  `2`.
- In the obstruction witness of `Obstruction.lean` the equilibria are exactly the strategies
  that take the early action, which are the optimal ones (`obstruction_eq_iff`); the isolated
  choice is not an equilibrium.

Like `Obstruction.lean`, these are statements about the reward-kernel semantics; the play of a
component under a strategy is its `interpret` by the theorems of `Interpretation.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

namespace RewardKernel

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
/-- The forward map of the lens of a serial composite is the composite of the forward maps. -/
theorem pushforward_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (μ : X → ℝ) :
    (f.comp g).pushforward μ = g.pushforward (f.pushforward μ) := by
  funext z
  simp only [pushforward, comp_K, Kernel.comp_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The backward map of the lens of a serial composite with a normalised suffix is the
composite of the backward maps, in the opposite order. -/
theorem continuation_comp (f : RewardKernel X Y) (g : RewardKernel Y Z)
    (hg : Kernel.Normalised g.K) (c : Z → ℝ) :
    (f.comp g).continuation c = f.continuation (g.continuation c) := by
  classical
  funext x₀
  have h := eu_comp f g hg (fun x => if x = x₀ then 1 else 0) c
  simpa [eu_eq_continuation, ite_mul, Finset.sum_ite_eq'] using h

theorem pushforward_id [DecidableEq X] (μ : X → ℝ) : (id X).pushforward μ = μ := by
  funext y
  simp [pushforward, id, lift, Kernel.idK_apply, mul_ite, Finset.sum_ite_eq]

theorem continuation_id [DecidableEq X] (c : X → ℝ) : (id X).continuation c = c := by
  funext x
  simp [continuation, id, lift, Kernel.idK_apply, ite_mul]

/-- The expected utility pairs the two directions of the lens: the prefix reward plus the
continuation integrated against the boundary law. -/
theorem eu_eq_prefixReward_add (f : RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    f.eu μ c = f.prefixReward μ + ∑ y, f.pushforward μ y * c y := by
  simp only [eu, prefixReward, pushforward, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end RewardKernel

/-- A lens on real functions: forward on priors, backward on continuations. -/
structure Lens (X Y : Type) where
  /-- The forward map, a prior on `X` to a law on `Y`. -/
  fwd : (X → ℝ) → (Y → ℝ)
  /-- The backward map, a continuation on `Y` to a value function on `X`. -/
  bwd : (Y → ℝ) → (X → ℝ)

namespace Lens

variable {X Y Z : Type}

/-- Composition of lenses: forward maps in order, backward maps in reverse. -/
def comp (l : Lens X Y) (m : Lens Y Z) : Lens X Z := ⟨m.fwd ∘ l.fwd, l.bwd ∘ m.bwd⟩

/-- The identity lens. -/
def id (X : Type) : Lens X X := ⟨fun μ => μ, fun c => c⟩

end Lens

namespace RewardKernel

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The lens of a reward kernel: the boundary law forward, the value function backward. -/
def lens (f : RewardKernel X Y) : Lens X Y := ⟨f.pushforward, f.continuation⟩

/-- **Lens functoriality**: the lens of a serial composite with a normalised suffix is the
composite of the lenses. -/
theorem lens_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (hg : Kernel.Normalised g.K) :
    (f.comp g).lens = f.lens.comp g.lens := by
  simp only [lens, Lens.comp, Lens.mk.injEq]
  exact ⟨funext (pushforward_comp f g), funext (continuation_comp f g hg)⟩

/-- The lens of an identity is the identity lens. -/
theorem lens_id [DecidableEq X] : (id X).lens = Lens.id X := by
  simp only [lens, Lens.id, Lens.mk.injEq]
  exact ⟨funext pushforward_id, funext continuation_id⟩

end RewardKernel

/-- An open game `X → Y` over reward kernels: strategies, a normalised play for each, and an
equilibrium predicate over contexts `(μ, c)`. -/
structure Game (X Y : Type) [Fintype X] [Fintype Y] where
  /-- The strategies. -/
  Strat : Type
  /-- The reward kernel played by each strategy. -/
  play : Strat → RewardKernel X Y
  /-- Every play has a normalised probability component. -/
  normalised : ∀ s, Kernel.Normalised (play s).K
  /-- `Eq μ c s`: the strategy `s` is an equilibrium in the context `(μ, c)`. -/
  Eq : (X → ℝ) → (Y → ℝ) → Strat → Prop

namespace Game

open RewardKernel

variable {X Y Z V : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype V]

/-- A decision game: one component whose decisions are controlled together, in equilibrium
exactly when its strategy maximises expected utility in the context. -/
def decision {S : Type} (play : S → RewardKernel X Y)
    (h : ∀ s, Kernel.Normalised (play s).K) : Game X Y where
  Strat := S
  play := play
  normalised := h
  Eq μ c s := ∀ s', (play s').eu μ c ≤ (play s).eu μ c

/-- The identity game, with one strategy, always in equilibrium. -/
def idGame (X : Type) [Fintype X] [DecidableEq X] : Game X X where
  Strat := Unit
  play _ := RewardKernel.id X
  normalised _ := Kernel.Normalised.idK
  Eq _ _ _ := True

/-- Serial composition: each part is in equilibrium in the context the other induces, the
suffix's value function for the prefix and the prefix's boundary law for the suffix. -/
def seq (G : Game X Y) (H : Game Y Z) : Game X Z where
  Strat := G.Strat × H.Strat
  play p := (G.play p.1).comp (H.play p.2)
  normalised p := Kernel.Normalised.comp (G.normalised p.1) (H.normalised p.2)
  Eq μ c p := G.Eq μ ((H.play p.2).continuation c) p.1 ∧
    H.Eq ((G.play p.1).pushforward μ) c p.2

/-! ### Serial composition is a category on equilibria -/

theorem seq_assoc_play (G : Game X Y) (H : Game Y Z) (J : Game Z V) (s : G.Strat)
    (t : H.Strat) (u : J.Strat) :
    ((G.seq H).seq J).play ((s, t), u) = (G.seq (H.seq J)).play (s, (t, u)) :=
  RewardKernel.comp_assoc _ _ _

/-- **A chain of three games.** A strategy of `(G ; H) ; J` is an equilibrium exactly when
each game's strategy is an equilibrium in the context the lenses of the others transport to
it: `G` against the value functions of `H` and `J` in turn, `H` against the boundary law of
`G` and the value function of `J`, `J` against the boundary laws of `G` and `H` in turn. -/
theorem seq_seq_eq_iff (G : Game X Y) (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ)
    (s : G.Strat) (t : H.Strat) (u : J.Strat) :
    ((G.seq H).seq J).Eq μ c ((s, t), u) ↔
      G.Eq μ ((H.play t).continuation ((J.play u).continuation c)) s ∧
        H.Eq ((G.play s).pushforward μ) ((J.play u).continuation c) t ∧
        J.Eq ((H.play t).pushforward ((G.play s).pushforward μ)) c u := by
  change (G.Eq μ ((H.play t).continuation ((J.play u).continuation c)) s ∧
      H.Eq ((G.play s).pushforward μ) ((J.play u).continuation c) t) ∧
      J.Eq (((G.play s).comp (H.play t)).pushforward μ) c u ↔ _
  rw [pushforward_comp, and_assoc]

/-- **Associativity on equilibria.** Bracketing a chain of three games differently changes
neither its plays nor its equilibria, because the induced contexts compose by the lens laws. -/
theorem seq_assoc_eq (G : Game X Y) (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ)
    (s : G.Strat) (t : H.Strat) (u : J.Strat) :
    ((G.seq H).seq J).Eq μ c ((s, t), u) ↔ (G.seq (H.seq J)).Eq μ c (s, (t, u)) := by
  rw [seq_seq_eq_iff]
  change _ ↔ G.Eq μ (((H.play t).comp (J.play u)).continuation c) s ∧
      (H.Eq ((G.play s).pushforward μ) ((J.play u).continuation c) t ∧
        J.Eq ((H.play t).pushforward ((G.play s).pushforward μ)) c u)
  rw [continuation_comp _ _ (J.normalised u)]

theorem idGame_seq_eq [DecidableEq X] (G : Game X Y) (μ : X → ℝ) (c : Y → ℝ) (s : G.Strat) :
    ((idGame X).seq G).Eq μ c ((), s) ↔ G.Eq μ c s := by
  change True ∧ G.Eq ((RewardKernel.id X).pushforward μ) c s ↔ _
  rw [pushforward_id, true_and]

theorem seq_idGame_eq [DecidableEq Y] (G : Game X Y) (μ : X → ℝ) (c : Y → ℝ) (s : G.Strat) :
    (G.seq (idGame Y)).Eq μ c (s, ()) ↔ G.Eq μ c s := by
  change G.Eq μ ((RewardKernel.id Y).continuation c) s ∧ True ↔ _
  rw [continuation_id, and_true]

/-! ### Equilibria of two decisions are person-by-person optima -/

/-- **Equilibrium of two decision games.** `(s, t)` is an equilibrium of the serial composite
of two decision games exactly when neither component can raise the composite's expected
utility by changing its own strategy alone. -/
theorem seq_decision_eq_iff {S T : Type} (f : S → RewardKernel X Y) (g : T → RewardKernel Y Z)
    (hf : ∀ s, Kernel.Normalised (f s).K) (hg : ∀ t, Kernel.Normalised (g t).K)
    (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T) :
    ((decision f hf).seq (decision g hg)).Eq μ c (s, t) ↔
      (∀ s', ((f s').comp (g t)).eu μ c ≤ ((f s).comp (g t)).eu μ c) ∧
        (∀ t', ((f s).comp (g t')).eu μ c ≤ ((f s).comp (g t)).eu μ c) := by
  change (∀ s', (f s').eu μ ((g t).continuation c) ≤ (f s).eu μ ((g t).continuation c)) ∧
      (∀ t', (g t').eu ((f s).pushforward μ) c ≤ (g t).eu ((f s).pushforward μ) c) ↔ _
  simp only [eu_comp _ _ (hg _), eu_continuation, add_le_add_iff_left]

/-! ### Optima are equilibria -/

/-- A game is sound when every strategy that maximises expected utility in a context is an
equilibrium there. -/
def Sound (G : Game X Y) : Prop :=
  ∀ μ c s, (∀ s', (G.play s').eu μ c ≤ (G.play s).eu μ c) → G.Eq μ c s

theorem decision_sound {S : Type} (play : S → RewardKernel X Y)
    (h : ∀ s, Kernel.Normalised (play s).K) : (decision play h).Sound :=
  fun _ _ _ hs => hs

theorem idGame_sound [DecidableEq X] : (idGame X).Sound := fun _ _ _ _ => trivial

/-- **Optima are equilibria, compositionally.** Serial composition preserves soundness, so a
global optimum of any game built from decision games and identities by serial composition is
an equilibrium of it. -/
theorem seq_sound {G : Game X Y} {H : Game Y Z} (hG : G.Sound) (hH : H.Sound) :
    (G.seq H).Sound := by
  rintro μ c ⟨s, t⟩ hopt
  refine ⟨hG _ _ _ fun s' => ?_, hH _ _ _ fun t' => ?_⟩
  · have := hopt (s', t)
    change ((G.play s').comp (H.play t)).eu μ c ≤ ((G.play s).comp (H.play t)).eu μ c at this
    rwa [eu_comp _ _ (H.normalised t), eu_comp _ _ (H.normalised t)] at this
  · have := hopt (s, t')
    change ((G.play s).comp (H.play t')).eu μ c ≤ ((G.play s).comp (H.play t)).eu μ c at this
    rwa [eu_comp _ _ (H.normalised t'), eu_comp _ _ (H.normalised t), eu_continuation,
      eu_continuation, add_le_add_iff_left] at this

end Game

/-! ### The converse fails: a coordination witness -/

namespace Coordination

open RewardKernel Obstruction

/-- The early decision chooses `A = a` and earns nothing. -/
def first (a : Bool) : RewardKernel Unit Bool :=
  ⟨fun _ y => if y = a then 1 else 0, fun _ _ => 0⟩

/-- The payoff of the late decision `B = b` against the early `A`: 2 when both are taken,
1 when neither is, 0 otherwise. -/
def payoff (a b : Bool) : ℝ :=
  if a = true ∧ b = true then 2 else if a = false ∧ b = false then 1 else 0

/-- The late decision chooses `B = b` without observing `A`, and earns `payoff A b`. -/
def second (b : Bool) : RewardKernel Bool Unit := ⟨fun _ _ => 1, fun y _ => payoff y b⟩

theorem first_normalised (a : Bool) : Kernel.Normalised (first a).K := by
  intro u
  cases a <;> simp [first]

theorem second_normalised (b : Bool) : Kernel.Normalised (second b).K := by
  intro y
  simp [second]

/-- The two decisions in series, as a game. -/
def game : Game Unit Unit :=
  (Game.decision first first_normalised).seq (Game.decision second second_normalised)

theorem composite_eu (a b : Bool) :
    ((first a).comp (second b)).eu unitPrior zeroCont = payoff a b := by
  rw [eu_comp _ _ (second_normalised b), eu_continuation]
  cases a <;> cases b <;>
    simp [eu, prefixReward, pushforward, first, second, payoff, unitPrior, zeroCont]

theorem game_eq_iff (a b : Bool) :
    game.Eq unitPrior zeroCont (a, b) ↔
      (∀ a', payoff a' b ≤ payoff a b) ∧ (∀ b', payoff a b' ≤ payoff a b) := by
  refine (Game.seq_decision_eq_iff first second first_normalised second_normalised unitPrior
    zeroCont a b).trans ?_
  simp only [composite_eu]

/-- **An equilibrium need not be optimal.** Not taking either action is an equilibrium worth
`1`, taking both is an equilibrium worth `2`, and `2` is the optimum. -/
theorem coordination_equilibrium_not_optimal :
    game.Eq unitPrior zeroCont (false, false) ∧ game.Eq unitPrior zeroCont (true, true) ∧
      ((first false).comp (second false)).eu unitPrior zeroCont = 1 ∧
      ((first true).comp (second true)).eu unitPrior zeroCont = 2 ∧
      (∀ a b, ((first a).comp (second b)).eu unitPrior zeroCont ≤ 2) ∧ (1 : ℝ) < 2 := by
  refine ⟨(game_eq_iff _ _).mpr ⟨fun a => ?_, fun b => ?_⟩,
    (game_eq_iff _ _).mpr ⟨fun a => ?_, fun b => ?_⟩, by rw [composite_eu]; simp [payoff],
    by rw [composite_eu]; simp [payoff], fun a b => ?_, by norm_num⟩
  · cases a <;> norm_num [payoff]
  · cases b <;> norm_num [payoff]
  · cases a <;> norm_num [payoff]
  · cases b <;> norm_num [payoff]
  · rw [composite_eu]
    cases a <;> cases b <;> norm_num [payoff]

end Coordination

/-! ### Equilibria of the obstruction witness -/

namespace Obstruction

open RewardKernel

theorem early_normalised (a : Bool) : Kernel.Normalised (early a).K := by
  intro u
  cases a <;> simp [early, Fintype.sum_prod_type]

/-- The obstruction witness as a game: the early decision, then the late policy. -/
def game : Game Unit Unit :=
  (Game.decision early early_normalised).seq (Game.decision late fun _ => late_normalised _)

/-- **The equilibria of the obstruction witness** are exactly the strategies that take the
early action, which are its optima. The isolated choice `a = false` is not an equilibrium:
against the late component's value function, taking the action gains `3`. -/
theorem obstruction_eq_iff (a : Bool) (τ : Bool → Bool) :
    game.Eq unitPrior zeroCont (a, τ) ↔ a = true := by
  refine (Game.seq_decision_eq_iff early late early_normalised (fun _ => late_normalised _)
    unitPrior zeroCont a τ).trans ?_
  simp only [composite_eu]
  constructor
  · rintro ⟨h, -⟩
    have := h true
    cases a
    · norm_num at this
    · rfl
  · rintro rfl
    exact ⟨fun a' => by cases a' <;> norm_num, fun _ => le_rfl⟩

end Obstruction

end OpenInfluence
