import CategoricalInfluenceDiagramsProofs.Lens
import Mathlib.Tactic.Linarith

/-!
# The tensor of open games (ADR 0020, amended)

ADR 0020 left the tensor of games undefined: the context a factor of `G ⊗ H` receives can
depend on the other factor's input state. This module makes that precise in both directions.

**The tensor.** `Game.tensor G H` plays `play s ⊗ play t`, and `(s, t)` is an equilibrium in
`(μ, c)` when `s` is one of `G` in the context of the first marginal of `μ` and the
continuation the second factor induces (`leftCont`: its reward, and the continuation `c`,
averaged over its input under the second marginal and over its output), and symmetrically
for `t`. When the prior is a product of probability vectors, this context is exact: the
composite's expected utility is the first factor's expected utility in it
(`tensor_eu_left`, `tensor_eu_right`). So for two decision games and a product prior, an
equilibrium of the tensor is exactly a pair from which neither factor gains alone, measured
by the composite's expected utility (`tensor_decision_eq_iff`).

**Correlated priors.** No such context exists in general. With two binary inputs that are
equal, a first factor that copies its input and a second that passes its input through, and
a payoff for matching outputs, the best responses of the first factor are exactly the policy
that copies (`correlated_best_responses`). But in no context of the first factor alone, a
probability vector on its input and a continuation on its output, are the decision game's
equilibria exactly that policy (`correlated_no_factor_context`): the continuation would have
to depend on the input, through the correlation. A tensor that is exact for correlated
priors needs contexts in which the continuation reads the input, which ADR 0020's `Game`
does not have.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

namespace Game

open RewardKernel

variable {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']

/-- The first marginal of a prior on a product. -/
def marg₁ (μ : X × X' → ℝ) : X → ℝ := fun x => ∑ x', μ (x, x')

/-- The second marginal of a prior on a product. -/
def marg₂ (μ : X × X' → ℝ) : X' → ℝ := fun x' => ∑ x, μ (x, x')

omit [Fintype Y] [Fintype X] in
/-- The continuation the second factor `g` induces for the first, with law `ν` on its input:
its reward and the continuation `c`, averaged over its input and its output. -/
def leftCont (g : RewardKernel X' Y') (ν : X' → ℝ) (c : Y × Y' → ℝ) : Y → ℝ :=
  fun y => ∑ x', ν x' * ∑ y', (g.W x' y' + g.K x' y' * c (y, y'))

omit [Fintype Y'] [Fintype X'] in
/-- The continuation the first factor `f` induces for the second, with law `ν` on its input. -/
def rightCont (f : RewardKernel X Y) (ν : X → ℝ) (c : Y × Y' → ℝ) : Y' → ℝ :=
  fun y' => ∑ x, ν x * ∑ y, (f.W x y + f.K x y * c (y, y'))

/-- The tensor of open games: each factor in equilibrium in the context of its marginal prior
and the continuation the other factor induces. Exact for product priors
(`tensor_decision_eq_iff`); no context of a factor alone is exact for correlated priors
(`correlated_no_factor_context`). -/
def tensor (G : Game X Y) (H : Game X' Y') : Game (X × X') (Y × Y') where
  Strat := G.Strat × H.Strat
  play p := (G.play p.1).tensor (H.play p.2)
  normalised p := Kernel.Normalised.tensor (G.normalised p.1) (H.normalised p.2)
  Eq μ c p := G.Eq (marg₁ μ) (leftCont (H.play p.2) (marg₂ μ) c) p.1 ∧
    H.Eq (marg₂ μ) (rightCont (G.play p.1) (marg₁ μ) c) p.2

/-- The product of two priors. -/
def prodPrior (μ₁ : X → ℝ) (μ₂ : X' → ℝ) : X × X' → ℝ := fun p => μ₁ p.1 * μ₂ p.2

omit [Fintype X] in
theorem marg₁_prod (μ₁ : X → ℝ) (μ₂ : X' → ℝ) (h₂ : ∑ x', μ₂ x' = 1) :
    marg₁ (prodPrior μ₁ μ₂) = μ₁ := by
  funext x
  simp [marg₁, prodPrior, ← Finset.mul_sum, h₂]

omit [Fintype X'] in
theorem marg₂_prod (μ₁ : X → ℝ) (μ₂ : X' → ℝ) (h₁ : ∑ x, μ₁ x = 1) :
    marg₂ (prodPrior μ₁ μ₂) = μ₂ := by
  funext x'
  simp [marg₂, prodPrior, ← Finset.sum_mul, h₁]

omit [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y'] in
/-- Reordering a fourfold sum. -/
theorem sum_comm4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ b, ∑ d, ∑ a, ∑ c, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ b, ∑ d, ∑ a, ∑ c, F a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The expected utility of a tensor with a product prior, as a fourfold sum. -/
theorem tensor_eu_sum (f : RewardKernel X Y) (g : RewardKernel X' Y') (μ₁ : X → ℝ)
    (μ₂ : X' → ℝ) (c : Y × Y' → ℝ) :
    (f.tensor g).eu (prodPrior μ₁ μ₂) c = ∑ x, ∑ x', ∑ y, ∑ y', μ₁ x * μ₂ x' *
      (f.W x y * g.K x' y' + f.K x y * g.W x' y' + f.K x y * g.K x' y' * c (y, y')) := by
  unfold eu prodPrior
  simp only [tensor_K, tensor_W, Kernel.tensor_apply, Pi.add_apply, Fintype.sum_prod_type,
    Finset.mul_sum]

/-- With a product prior whose second factor is a probability vector, the expected utility of a
tensor is the first factor's expected utility in the context the second induces. -/
theorem tensor_eu_left (f : RewardKernel X Y) (g : RewardKernel X' Y')
    (hg : Kernel.Normalised g.K) (μ₁ : X → ℝ) (μ₂ : X' → ℝ) (h₂ : ∑ x', μ₂ x' = 1)
    (c : Y × Y' → ℝ) :
    (f.tensor g).eu (prodPrior μ₁ μ₂) c = f.eu μ₁ (leftCont g μ₂ c) := by
  have hone : ∑ x', μ₂ x' * ∑ y', g.K x' y' = 1 := by simp [hg _, h₂]
  have rhs : f.eu μ₁ (leftCont g μ₂ c) = ∑ x, ∑ y, ∑ x', ∑ y', μ₁ x * μ₂ x' *
      (f.W x y * g.K x' y' + f.K x y * g.W x' y' + f.K x y * g.K x' y' * c (y, y')) := by
    unfold eu leftCont
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [← mul_one (f.W x y), ← hone]
    simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => by ring
  rw [rhs, tensor_eu_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- With a product prior whose first factor is a probability vector, the expected utility of a
tensor is the second factor's expected utility in the context the first induces. -/
theorem tensor_eu_right (f : RewardKernel X Y) (g : RewardKernel X' Y')
    (hf : Kernel.Normalised f.K) (μ₁ : X → ℝ) (μ₂ : X' → ℝ) (h₁ : ∑ x, μ₁ x = 1)
    (c : Y × Y' → ℝ) :
    (f.tensor g).eu (prodPrior μ₁ μ₂) c = g.eu μ₂ (rightCont f μ₁ c) := by
  have hone : ∑ x, μ₁ x * ∑ y, f.K x y = 1 := by simp [hf _, h₁]
  have rhs : g.eu μ₂ (rightCont f μ₁ c) = ∑ x', ∑ y', ∑ x, ∑ y, μ₁ x * μ₂ x' *
      (f.W x y * g.K x' y' + f.K x y * g.W x' y' + f.K x y * g.K x' y' * c (y, y')) := by
    unfold eu rightCont
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => ?_
    conv_lhs => rw [← mul_one (g.W x' y'), ← hone]
    simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [rhs, tensor_eu_sum, sum_comm4]

/-- **The tensor of two decision games, with a product prior**: an equilibrium is exactly a
pair from which neither factor can raise the composite's expected utility alone. -/
theorem tensor_decision_eq_iff {S T : Type} (pf : S → RewardKernel X Y)
    (hf : ∀ s, Kernel.Normalised (pf s).K) (pg : T → RewardKernel X' Y')
    (hg : ∀ t, Kernel.Normalised (pg t).K) (μ₁ : X → ℝ) (μ₂ : X' → ℝ) (h₁ : ∑ x, μ₁ x = 1)
    (h₂ : ∑ x', μ₂ x' = 1) (c : Y × Y' → ℝ) (s : S) (t : T) :
    ((decision pf hf).tensor (decision pg hg)).Eq (prodPrior μ₁ μ₂) c (s, t) ↔
      (∀ s', ((pf s').tensor (pg t)).eu (prodPrior μ₁ μ₂) c ≤
        ((pf s).tensor (pg t)).eu (prodPrior μ₁ μ₂) c) ∧
      ∀ t', ((pf s).tensor (pg t')).eu (prodPrior μ₁ μ₂) c ≤
        ((pf s).tensor (pg t)).eu (prodPrior μ₁ μ₂) c := by
  have L : ∀ s' t', ((pf s').tensor (pg t')).eu (prodPrior μ₁ μ₂) c =
      (pf s').eu μ₁ (leftCont (pg t') μ₂ c) := fun s' t' => tensor_eu_left _ _ (hg t') μ₁ μ₂ h₂ c
  have R : ∀ s' t', ((pf s').tensor (pg t')).eu (prodPrior μ₁ μ₂) c =
      (pg t').eu μ₂ (rightCont (pf s') μ₁ c) := fun s' t' => tensor_eu_right _ _ (hf s') μ₁ μ₂ h₁ c
  change (∀ s', (pf s').eu (marg₁ (prodPrior μ₁ μ₂)) (leftCont (pg t) (marg₂ (prodPrior μ₁ μ₂)) c) ≤
      (pf s).eu (marg₁ (prodPrior μ₁ μ₂)) (leftCont (pg t) (marg₂ (prodPrior μ₁ μ₂)) c)) ∧
    (∀ t', (pg t').eu (marg₂ (prodPrior μ₁ μ₂)) (rightCont (pf s) (marg₁ (prodPrior μ₁ μ₂)) c) ≤
      (pg t).eu (marg₂ (prodPrior μ₁ μ₂)) (rightCont (pf s) (marg₁ (prodPrior μ₁ μ₂)) c)) ↔ _
  rw [marg₁_prod μ₁ μ₂ h₂, marg₂_prod μ₁ μ₂ h₁]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun s' => by rw [L, L]; exact h1 s', fun t' => by rw [R, R]; exact h2 t'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun s' => ?_, fun t' => ?_⟩
    · have := h1 s'
      rwa [L, L] at this
    · have := h2 t'
      rwa [R, R] at this

end Game

/-! ### Correlated priors: no context of a factor alone -/

namespace CorrelatedTensor

open RewardKernel

/-- The first factor's play: output the state the policy `s` assigns to the input. -/
def copyPlay (s : Bool → Bool) : RewardKernel Bool Bool :=
  ⟨fun x y => if y = s x then 1 else 0, fun _ _ => 0⟩

theorem copyPlay_normalised (s : Bool → Bool) : Kernel.Normalised (copyPlay s).K := by
  intro x
  simp [copyPlay]

/-- The first factor as a decision game over all policies. -/
def first : Game Bool Bool := Game.decision copyPlay copyPlay_normalised

/-- The two inputs are equal, each value with probability one half. -/
def prior : Bool × Bool → ℝ := fun p => if p.1 = p.2 then 1 / 2 else 0

/-- One for matching outputs. -/
def payoff : Bool × Bool → ℝ := fun p => if p.1 = p.2 then 1 else 0

/-- The composite's value: one half for each input the policy copies. -/
theorem joint_eu (s : Bool → Bool) :
    ((copyPlay s).tensor (RewardKernel.id Bool)).eu prior payoff =
      (if s true = true then 1 / 2 else 0) + (if s false = false then 1 / 2 else 0) := by
  simp only [eu, copyPlay, prior, payoff, tensor_K, tensor_W, RewardKernel.id, lift,
    Kernel.tensor_apply, Pi.add_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    Kernel.idK_apply]
  rcases Bool.eq_false_or_eq_true (s true) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (s false) with h2 | h2 <;> simp [h1, h2]

/-- With the correlated prior, the first factor's best responses are exactly the policy that
copies its input. -/
theorem correlated_best_responses (s : Bool → Bool) :
    (∀ s', ((copyPlay s').tensor (RewardKernel.id Bool)).eu prior payoff ≤
        ((copyPlay s).tensor (RewardKernel.id Bool)).eu prior payoff) ↔ ∀ x, s x = x := by
  constructor
  · intro h
    have hid := h id
    rw [joint_eu, joint_eu] at hid
    intro x
    cases x <;> cases h1 : s true <;> cases h2 : s false <;> simp_all <;> norm_num at hid
  · intro hs s'
    rw [joint_eu, joint_eu, hs true, hs false]
    cases s' true <;> cases s' false <;> norm_num

/-- The first factor's expected utility in a context of its own. -/
theorem first_eu (s : Bool → Bool) (μ₁ c₁ : Bool → ℝ) :
    (copyPlay s).eu μ₁ c₁ = μ₁ true * c₁ (s true) + μ₁ false * c₁ (s false) := by
  simp only [eu, copyPlay, Fintype.sum_bool]
  cases s true <;> cases s false <;> simp

/-- **No context of a factor alone is exact for a correlated prior.** For every probability
context `(μ₁, c₁)` of the first factor, its equilibria as a decision game differ from its best
responses in the composite. -/
theorem correlated_no_factor_context :
    ¬ ∃ μ₁ c₁ : Bool → ℝ, (∀ x, 0 ≤ μ₁ x) ∧ ∀ s, (first.Eq μ₁ c₁ s ↔ ∀ x, s x = x) := by
  rintro ⟨μ₁, c₁, hμ, h⟩
  have eq_iff : ∀ s : Bool → Bool, first.Eq μ₁ c₁ s ↔
      ∀ s' : Bool → Bool, μ₁ true * c₁ (s' true) + μ₁ false * c₁ (s' false) ≤
        μ₁ true * c₁ (s true) + μ₁ false * c₁ (s false) := by
    intro s
    change (∀ s', (copyPlay s').eu μ₁ c₁ ≤ (copyPlay s).eu μ₁ c₁) ↔ _
    simp only [first_eu]
  have hid := (eq_iff _root_.id).mp ((h _root_.id).mpr fun _ => rfl)
  -- The copying policy beats both constant policies.
  have h_t := hid (fun _ => true)
  have h_f := hid (fun _ => false)
  simp only [_root_.id_eq] at h_t h_f
  have a0 := hμ true
  have b0 := hμ false
  -- If the constant `true` policy ties, it is an equilibrium that does not copy.
  by_cases hb : μ₁ false * (c₁ false - c₁ true) = 0
  · have heq : first.Eq μ₁ c₁ (fun _ => true) := by
      rw [eq_iff]
      intro s'
      have := hid s'
      simp only [_root_.id_eq] at this
      have hb' : μ₁ false * c₁ false = μ₁ false * c₁ true := by
        rw [mul_sub, sub_eq_zero] at hb
        exact hb
      linarith
    have := ((h _).mp heq) false
    simp at this
  · -- Otherwise the second input has positive weight and `c₁ false > c₁ true`, so the first
    -- input has weight zero and the constant `false` policy ties.
    have hpos : 0 < μ₁ false * (c₁ false - c₁ true) := lt_of_le_of_ne (by nlinarith) (Ne.symm hb)
    have hq : c₁ true < c₁ false := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have ha : μ₁ true = 0 := by nlinarith
    have heq : first.Eq μ₁ c₁ (fun _ => false) := by
      rw [eq_iff]
      intro s'
      have := hid s'
      simp only [_root_.id_eq] at this
      rw [ha] at this ⊢
      linarith
    have := ((h _).mp heq) true
    simp at this

end CorrelatedTensor

end OpenInfluence
