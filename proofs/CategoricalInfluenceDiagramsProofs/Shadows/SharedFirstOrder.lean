import CategoricalInfluenceDiagramsProofs.SharedPolicy

/-!
# SA-Pass shadow module: the first-order condition at a shared-policy optimum

Claim `cid.shared-first-order`, from `RewardKernel.shared_optimum_first_order`. The shadow
spells the two uses' joint change as the explicit tables `(1 - t) A₀ + t A₁` and
`(1 - t) B₀ + t B₁`.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SharedFirstOrder

open OpenInfluence OpenInfluence.RewardKernel

/-- `shared_optimum_first_order`, restated. -/
abbrev Candidate : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (A₀ A₁ : RewardKernel X Y)
    (B₀ B₁ : RewardKernel Y Z) (μ : X → ℝ) (c : Z → ℝ),
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ((RewardKernel.segment A₀ A₁ t).comp (RewardKernel.segment B₀ B₁ t)).eu μ c ≤
        (A₀.comp B₀).eu μ c) →
    ((A₁.comp B₀).eu μ c - (A₀.comp B₀).eu μ c) +
      ((A₀.comp B₁).eu μ c - (A₀.comp B₀).eu μ c) ≤ 0

/-- The table `(1 - t) A + t B`. -/
abbrev between {X Y : Type} (A B : RewardKernel X Y) (t : ℝ) : RewardKernel X Y :=
  ⟨fun x y => (1 - t) * A.K x y + t * B.K x y, fun x y => (1 - t) * A.W x y + t * B.W x y⟩

/-- "At an optimum of a policy shared by two uses in series, separated by any fixed kernels,
the gain from changing the first use alone towards another policy plus the gain from changing
the second use alone is at most zero". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (A₀ A₁ : RewardKernel X Y)
    (B₀ B₁ : RewardKernel Y Z) (μ : X → ℝ) (c : Z → ℝ),
    (∀ t : ℝ, 0 < t → t < 1 →
      ((between A₀ A₁ t).comp (between B₀ B₁ t)).eu μ c ≤ (A₀.comp B₀).eu μ c) →
    ((A₁.comp B₀).eu μ c - (A₀.comp B₀).eu μ c) +
      ((A₀.comp B₁).eu μ c - (A₀.comp B₀).eu μ c) ≤ 0

theorem segment_eq {X Y : Type} (A B : RewardKernel X Y) (t : ℝ) :
    RewardKernel.segment A B t = between A B t := by
  ext x y <;> simp [RewardKernel.segment]

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ A₀ A₁ B₀ B₁ μ c hopt =>
  h X Y Z A₀ A₁ B₀ B₁ μ c fun t ht => by
    rw [segment_eq, segment_eq]
    exact hopt t ht.1 ht.2

theorem backward : Shadow1 → Candidate := fun h X Y Z _ _ _ A₀ A₁ B₀ B₁ μ c hopt =>
  h X Y Z A₀ A₁ B₀ B₁ μ c fun t h0 h1 => by
    rw [← segment_eq, ← segment_eq]
    exact hopt t ⟨h0, h1⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ _ _ _ A₀ A₁ B₀ B₁ μ c hopt =>
  shared_optimum_first_order A₀ A₁ B₀ B₁ μ c hopt

end CategoricalInfluenceDiagramsProofs.Shadows.SharedFirstOrder
