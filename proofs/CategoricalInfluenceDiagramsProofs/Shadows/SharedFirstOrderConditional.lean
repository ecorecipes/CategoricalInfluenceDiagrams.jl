import CategoricalInfluenceDiagramsProofs.SharedPolicy

/-!
# SA-Pass shadow module: the first-order condition for a shared policy given evidence

Claim `cid.shared-first-order-conditional`, from
`RewardKernel.shared_optimum_first_order_conditional`. The shadow spells the joint change as
the explicit tables `(1 - t) A₀ + t A₁` and `(1 - t) B₀ + t B₁`, and the conditional value as
the evidence-weighted value over the mass.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SharedFirstOrderConditional

open OpenInfluence OpenInfluence.RewardKernel

/-- `shared_optimum_first_order_conditional`, restated. -/
abbrev Candidate : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (A₀ A₁ : RewardKernel X Y)
    (B₀ B₁ : RewardKernel Y Z) (s : RewardKernel.State X) (e : RewardKernel.Effect Z),
    0 < mass s ((A₀.comp B₀).pull e) →
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      conditionalValue s (((RewardKernel.segment A₀ A₁ t).comp
        (RewardKernel.segment B₀ B₁ t)).pull e) ≤ conditionalValue s ((A₀.comp B₀).pull e)) →
    (value s ((A₁.comp B₀).pull e) -
        conditionalValue s ((A₀.comp B₀).pull e) * mass s ((A₁.comp B₀).pull e)) /
        mass s ((A₀.comp B₀).pull e) +
      (value s ((A₀.comp B₁).pull e) -
        conditionalValue s ((A₀.comp B₀).pull e) * mass s ((A₀.comp B₁).pull e)) /
        mass s ((A₀.comp B₀).pull e) ≤ 0

/-- The table `(1 - t) A + t B`. -/
abbrev between {X Y : Type} (A B : RewardKernel X Y) (t : ℝ) : RewardKernel X Y :=
  ⟨fun x y => (1 - t) * A.K x y + t * B.K x y, fun x y => (1 - t) * A.W x y + t * B.W x y⟩

/-- The conditional value as a ratio. -/
noncomputable abbrev ratio {X : Type} [Fintype X] (s : RewardKernel.State X)
    (e : RewardKernel.Effect X) : ℝ :=
  value s e / mass s e

/-- "Given evidence of positive mass, at an optimum of the conditional value of a policy
shared by two uses in series, the first-order changes in conditional value from changing each
use alone towards another policy sum to at most zero". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (A₀ A₁ : RewardKernel X Y)
    (B₀ B₁ : RewardKernel Y Z) (s : RewardKernel.State X) (e : RewardKernel.Effect Z),
    0 < mass s ((A₀.comp B₀).pull e) →
    (∀ t : ℝ, 0 < t → t < 1 →
      ratio s (((between A₀ A₁ t).comp (between B₀ B₁ t)).pull e) ≤
        ratio s ((A₀.comp B₀).pull e)) →
    (value s ((A₁.comp B₀).pull e) -
        ratio s ((A₀.comp B₀).pull e) * mass s ((A₁.comp B₀).pull e)) /
        mass s ((A₀.comp B₀).pull e) +
      (value s ((A₀.comp B₁).pull e) -
        ratio s ((A₀.comp B₀).pull e) * mass s ((A₀.comp B₁).pull e)) /
        mass s ((A₀.comp B₀).pull e) ≤ 0

theorem segment_eq {X Y : Type} (A B : RewardKernel X Y) (t : ℝ) :
    RewardKernel.segment A B t = between A B t := by
  ext x y <;> simp [RewardKernel.segment]

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ A₀ A₁ B₀ B₁ s e hpos hopt =>
  h X Y Z A₀ A₁ B₀ B₁ s e hpos fun t ht => by
    rw [segment_eq, segment_eq]
    exact hopt t ht.1 ht.2

theorem backward : Shadow1 → Candidate := fun h X Y Z _ _ _ A₀ A₁ B₀ B₁ s e hpos hopt =>
  h X Y Z A₀ A₁ B₀ B₁ s e hpos fun t h0 h1 => by
    have := hopt t ⟨h0, h1⟩
    rw [segment_eq, segment_eq] at this
    exact this

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ _ _ _ A₀ A₁ B₀ B₁ s e hpos hopt =>
  shared_optimum_first_order_conditional A₀ A₁ B₀ B₁ s e hpos hopt

end CategoricalInfluenceDiagramsProofs.Shadows.SharedFirstOrderConditional
