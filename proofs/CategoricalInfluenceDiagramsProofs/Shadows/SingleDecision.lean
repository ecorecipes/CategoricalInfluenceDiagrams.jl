import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# SA-Pass shadow module: one randomised decision never beats a deterministic rule

Claim `cid.single-decision`, from `RewardKernel.kernel_eq_mix_ofFun` and
`RewardKernel.single_decision_sufficiency`. The shadows spell the mixture as
`k x y = Σ_f (∏_x' k x' (f x')) [y = f x]` and the context as a prefix, the decision beside
the identity on the other wires, and a suffix.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SingleDecision

open OpenInfluence FiniteKernelsProofs.Finite RewardKernel

/-- The two theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y),
      Kernel.Normalised k → ∀ x y,
      k x y = ∑ f : X → Y, ruleWeight k f * Kernel.ofFun f x y) ∧
    ∀ (X Z P A V : Type) [Fintype X] [Fintype Z] [Fintype P] [DecidableEq P] [Fintype A]
      [DecidableEq A] [Nonempty A] [Fintype V] [DecidableEq V]
      (pre : RewardKernel X (P × V)) (k : Kernel P A), Kernel.Nonneg k → Kernel.Normalised k →
      ∀ (post : RewardKernel (A × V) Z) (μ : X → ℝ) (c : Z → ℝ),
      ∃ f : P → A, (pre.comp (((lift k).tensor (RewardKernel.id V)).comp post)).eu μ c ≤
        (pre.comp (((lift (Kernel.ofFun f)).tensor (RewardKernel.id V)).comp post)).eu μ c

/-- "Every stochastic kernel ... is the mixture of the deterministic kernels of its rules,
each weighted by the probability of drawing it". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (k : Kernel X Y),
    Kernel.Normalised k → ∀ x y,
    k x y = ∑ f : X → Y, (∏ x', k x' (f x')) * (if y = f x then 1 else 0)

/-- "one randomised decision placed anywhere in a serial context, beside other wires, has
expected utility at most that of some deterministic rule in its place". -/
abbrev Shadow2 : Prop :=
  ∀ (X Z P A V : Type) [Fintype X] [Fintype Z] [Fintype P] [DecidableEq P] [Fintype A]
    [DecidableEq A] [Nonempty A] [Fintype V] [DecidableEq V]
    (pre : RewardKernel X (P × V)) (k : Kernel P A), Kernel.Nonneg k → Kernel.Normalised k →
    ∀ (post : RewardKernel (A × V) Z) (μ : X → ℝ) (c : Z → ℝ),
    ∃ f : P → A, (pre.comp (((lift k).tensor (RewardKernel.id V)).comp post)).eu μ c ≤
      (pre.comp (((lift (Kernel.ofFun f)).tensor (RewardKernel.id V)).comp post)).eu μ c

theorem forward1 : Candidate → Shadow1 := fun h X Y _ _ _ _ k hk x y => by
  simpa [ruleWeight, Kernel.ofFun_apply] using h.1 X Y k hk x y

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun X Y _ _ _ _ k hk x y => by
    simpa [ruleWeight, Kernel.ofFun_apply] using h1 X Y k hk x y, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ k hk x y => kernel_eq_mix_ofFun k hk x y,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ pre k hk0 hk post μ c =>
      single_decision_sufficiency pre k hk0 hk post μ c⟩

end CategoricalInfluenceDiagramsProofs.Shadows.SingleDecision
