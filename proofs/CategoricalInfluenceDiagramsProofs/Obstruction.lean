import CategoricalInfluenceDiagramsProofs.Context
import Mathlib.Tactic.NormNum

/-!
# Optimisation does not compose component by component

The contextual identity says each component's value depends on its context: the prefix
sees the suffix only through the value function `c_g`, the suffix sees the prefix only
through the induced boundary law `ν_f`. This module proves that the context cannot be
dropped, with the finite witness of the sealed bundle's Lean track
(`INF-ISOLATED-OBSTRUCTION`, `INF-HIDDEN-OBSTRUCTION`), restated in the reward-kernel
semantics and not imported from the bundle.

**The witness.** A fair hidden Boolean `H` and an early action `A` that observes nothing
form the prefix `early a : Unit → H × A`, which chooses `A = a` and pays utility `-[A]`.
The suffix `late τ : H × A → Unit` is an action `B = τ A` that observes only `A` (so `H`
is hidden at the boundary) and pays utilities `4[A]` and `2[B = H]`. The closed composite
from the unit prior with zero continuation has expected utility `1 + 3[a]`.

**Isolated optimisation** (`isolated_optimisation_fails`). Optimised on its own (unit
prior, zero continuation), the prefix chooses `a = false`, since its only utility is
`-[A]`. Optimised on its own against the boundary law that this prefix actually induces,
every suffix policy has value `1`. So **every** pair of separately optimal components has
composite value `1`, while the composite with `a = true` attains `4`, the joint optimum:
`1 < 4`.

**Pointwise maximisation at a hidden boundary state** (`hidden_input_obstruction`). Against
the same boundary law, every legal suffix policy (a function of `A` only) has value `1`.
Choosing `B` to maximise reward separately at each boundary state `(H, A)` gives the
selector `B = H`, whose value is `2`; it reads the hidden `H` and is not a legal policy.

Both are statements about the fixed-strategy semantics; they are not instances of the
typed syntax of `Syntax.lean`, whose interpretation they would be (the theorems there
reduce such a diagram to these reward kernels by `interpret_comp`).
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

namespace Obstruction

open FiniteKernelsProofs.Finite RewardKernel

/-- The boundary between the components: the hidden `H` and the observed `A`. -/
abbrev Boundary : Type := Bool × Bool

/-- The prefix with early action `A = a`: a fair hidden `H`, and utility `-[A]`. -/
def early (a : Bool) : RewardKernel Unit Boundary :=
  ⟨fun _ s => if s.2 = a then 1 / 2 else 0,
    fun _ s => if s.2 = a then 1 / 2 * (if s.2 then -1 else 0) else 0⟩

/-- The suffix whose action `B` is chosen by a selector on the whole boundary state, with
utilities `4[A]` and `2[B = H]`. -/
def lateSel (sel : Boundary → Bool) : RewardKernel Boundary Unit :=
  ⟨fun _ _ => 1, fun s _ => (if s.2 then 4 else 0) + (if sel s = s.1 then 2 else 0)⟩

/-- A legal suffix policy reads only the observed `A`. -/
def late (τ : Bool → Bool) : RewardKernel Boundary Unit := lateSel fun s => τ s.2

/-- A selector is a legal policy when it reads only the observed coordinate. -/
def Legal (sel : Boundary → Bool) : Prop := ∃ τ : Bool → Bool, ∀ s, sel s = τ s.2

/-- The unit prior on the closed input. -/
def unitPrior : Unit → ℝ := fun _ => 1

/-- The zero terminal continuation. -/
def zeroCont {Y : Type} : Y → ℝ := fun _ => 0

/-- The boundary law induced by the prefix `early a`. -/
def boundaryLaw (a : Bool) : Boundary → ℝ := (early a).pushforward unitPrior

/-- `p` is optimal among the members of a family of reward kernels for the prior `μ` and
the continuation `c`, the component considered on its own. -/
def IsolatedOptimal {X Y P : Type} [Fintype X] [Fintype Y] (family : P → RewardKernel X Y)
    (μ : X → ℝ) (c : Y → ℝ) (p : P) : Prop :=
  ∀ q, (family q).eu μ c ≤ (family p).eu μ c

/-! ### Values -/

theorem early_eu (a : Bool) : (early a).eu unitPrior zeroCont = if a then -1 else 0 := by
  cases a <;>
    simp [eu, early, unitPrior, zeroCont, Fintype.sum_prod_type]

theorem early_prefixReward (a : Bool) :
    (early a).prefixReward unitPrior = if a then -1 else 0 := by
  cases a <;>
    simp [prefixReward, early, unitPrior, Fintype.sum_prod_type]

theorem late_normalised (sel : Boundary → Bool) : Kernel.Normalised (lateSel sel).K := by
  intro s
  simp [lateSel]

theorem lateSel_eu (sel : Boundary → Bool) (a : Bool) :
    (lateSel sel).eu (boundaryLaw a) zeroCont =
      (if a then 4 else 0) + ((if sel (true, a) = true then 1 else 0) +
        (if sel (false, a) = false then 1 else 0)) := by
  simp only [eu, lateSel, boundaryLaw, pushforward, early, unitPrior, zeroCont,
    Fintype.sum_prod_type, Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton]
  cases a <;> simp only [Bool.true_eq_false, Bool.false_eq_true, if_true, if_false] <;>
    split_ifs <;> norm_num

theorem late_eu (τ : Bool → Bool) (a : Bool) :
    (late τ).eu (boundaryLaw a) zeroCont = (if a then 4 else 0) + 1 := by
  rw [late, lateSel_eu]
  cases τ a <;> simp

theorem composite_eu (a : Bool) (τ : Bool → Bool) :
    ((early a).comp (late τ)).eu unitPrior zeroCont = 1 + (if a then 3 else 0) := by
  rw [eu_comp (early a) (late τ) (late_normalised _), eu_continuation, early_prefixReward]
  change _ + (late τ).eu (boundaryLaw a) zeroCont = _
  rw [late_eu]
  cases a <;> norm_num

/-! ### The isolated-optimisation obstruction -/

theorem early_isolatedOptimal_iff (a : Bool) :
    IsolatedOptimal early unitPrior zeroCont a ↔ a = false := by
  constructor
  · intro h
    have := h false
    rw [early_eu, early_eu] at this
    cases a
    · rfl
    · norm_num at this
  · rintro rfl b
    rw [early_eu, early_eu]
    cases b <;> norm_num

theorem late_isolatedOptimal (a : Bool) (τ : Bool → Bool) :
    IsolatedOptimal late (boundaryLaw a) zeroCont τ := by
  intro τ'
  rw [late_eu, late_eu]

/-- **Isolated optimisation is not globally sound** (`INF-ISOLATED-OBSTRUCTION`). Every
prefix policy that is optimal on its own, followed by every suffix policy that is optimal
on its own against the boundary law that prefix induces, has composite expected utility
`1`; such pairs exist; another pair attains `4`; and `4` is the joint optimum. -/
theorem isolated_optimisation_fails :
    (∀ (a : Bool) (τ : Bool → Bool), IsolatedOptimal early unitPrior zeroCont a →
        IsolatedOptimal late (boundaryLaw a) zeroCont τ →
          ((early a).comp (late τ)).eu unitPrior zeroCont = 1) ∧
      (IsolatedOptimal early unitPrior zeroCont false ∧
        IsolatedOptimal late (boundaryLaw false) zeroCont (fun _ => false)) ∧
      ((early true).comp (late fun _ => false)).eu unitPrior zeroCont = 4 ∧
      (∀ (a : Bool) (τ : Bool → Bool),
        ((early a).comp (late τ)).eu unitPrior zeroCont ≤ 4) ∧
      (1 : ℝ) < 4 := by
  refine ⟨?_, ⟨(early_isolatedOptimal_iff false).mpr rfl, late_isolatedOptimal _ _⟩, ?_, ?_,
    by norm_num⟩
  · intro a τ ha _
    rw [(early_isolatedOptimal_iff a).mp ha, composite_eu]
    norm_num
  · rw [composite_eu]
    norm_num
  · intro a τ
    rw [composite_eu]
    cases a <;> norm_num

/-! ### The hidden-input obstruction -/

/-- The selector that maximises the suffix's reward separately at each boundary state. -/
def peek : Boundary → Bool := Prod.fst

theorem peek_pointwise_max (sel : Boundary → Bool) (s : Boundary) :
    (lateSel sel).W s () ≤ (lateSel peek).W s () := by
  simp only [lateSel, peek]
  split_ifs <;> norm_num

theorem peek_not_legal : ¬ Legal peek := by
  rintro ⟨τ, h⟩
  have h1 := h (true, false)
  have h2 := h (false, false)
  simp only [peek] at h1 h2
  rw [← h1] at h2
  exact Bool.false_ne_true h2

/-- **Pointwise maximisation at a hidden boundary state is not a legal policy**
(`INF-HIDDEN-OBSTRUCTION`). Against the boundary law of the isolated-optimal prefix, every
legal suffix policy has value `1`, while the selector that maximises at each boundary state
(reading the hidden `H`) has value `2` and is not legal. -/
theorem hidden_input_obstruction :
    (∀ sel, Legal sel → (lateSel sel).eu (boundaryLaw false) zeroCont = 1) ∧
      (∀ sel s, (lateSel sel).W s () ≤ (lateSel peek).W s ()) ∧
      (lateSel peek).eu (boundaryLaw false) zeroCont = 2 ∧
      ¬ Legal peek ∧ (1 : ℝ) < 2 := by
  refine ⟨?_, peek_pointwise_max, ?_, peek_not_legal, by norm_num⟩
  · rintro sel ⟨τ, hτ⟩
    have : sel = fun s => τ s.2 := funext hτ
    subst this
    exact (late_eu τ false).trans (by norm_num)
  · rw [lateSel_eu]
    simp [peek]
    norm_num

end Obstruction

end OpenInfluence
