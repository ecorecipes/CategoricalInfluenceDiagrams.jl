import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: optima are equilibria, compositionally

Claim `cid.game-optimum`, from `Game.decision_sound`, `Game.idGame_sound` and
`Game.seq_sound`. "Every game built from decision games and identities by serial
composition" is read as closure under the three constructors: the shadows state that
decision games and identity games are sound and that serial composition preserves soundness,
with "maximises expected utility in a context" written as the finite sum of ADR 0018.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.GameOptimum

open OpenInfluence FiniteKernelsProofs.Finite

/-- `EU(μ, c) = Σ_x μ x Σ_y (W x y + K x y c y)`. -/
abbrev EU {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ℝ := ∑ x, μ x * ∑ y, (W x y + K x y * c y)

/-- The strategy `s` maximises expected utility in the context `(μ, c)`. -/
abbrev Opt {X Y : Type} [Fintype X] [Fintype Y] (G : Game X Y) (μ : X → ℝ) (c : Y → ℝ)
    (s : G.Strat) : Prop :=
  ∀ s', EU (G.play s').K (G.play s').W μ c ≤ EU (G.play s).K (G.play s).W μ c

/-- Every maximiser is an equilibrium. -/
abbrev OptEq {X Y : Type} [Fintype X] [Fintype Y] (G : Game X Y) : Prop :=
  ∀ μ c s, Opt G μ c s → G.Eq μ c s

/-- The three cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y : Type) [Fintype X] [Fintype Y] (S : Type) (play : S → RewardKernel X Y)
      (h : ∀ s, Kernel.Normalised (play s).K), (Game.decision play h).Sound) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X], (Game.idGame X).Sound) ∧
    ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (G : Game X Y) (H : Game Y Z),
      G.Sound → H.Sound → (G.seq H).Sound

/-- "Every strategy that maximises expected utility in a context is an equilibrium there",
for a decision game ... -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (S : Type) (play : S → RewardKernel X Y)
    (h : ∀ s, Kernel.Normalised (play s).K), OptEq (Game.decision play h)

/-- ... for an identity game ... -/
abbrev Shadow2 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X], OptEq (Game.idGame X)

/-- ... and for a serial composite of games for which it holds. -/
abbrev Shadow3 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (G : Game X Y) (H : Game Y Z),
    OptEq G → OptEq H → OptEq (G.seq H)

theorem forward1 : Candidate → Shadow1 := fun h X Y _ _ S play hp => h.1 X Y S play hp

theorem forward2 : Candidate → Shadow2 := fun h X _ _ => h.2.1 X

theorem forward3 : Candidate → Shadow3 := fun h X Y Z _ _ _ G H => h.2.2 X Y Z G H

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun X Y _ _ S play hp => h1 X Y S play hp, fun X _ _ => h2 X,
    fun X Y Z _ _ _ G H => h3 X Y Z G H⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ play hp => Game.decision_sound play hp, fun _ _ _ => Game.idGame_sound,
    fun _ _ _ _ _ _ _ _ hG hH => Game.seq_sound hG hH⟩

end CategoricalInfluenceDiagramsProofs.Shadows.GameOptimum
