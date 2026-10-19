import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# SA-Pass shadow module: the contextual identity with evidence

Claim `cid.evidence-contextual`, from `RewardKernel.eu_comp_pull` and
`RewardKernel.conditionalValue_comp`. The shadows spell everything on arbitrary real tables:
the expected utility `Σ_x μ x Σ_y (W x y + K x y c y)`, the suffix's effect
`(Σ_z K_g y z, Σ_z (W_g y z + K_g y z c z))`, and the conditional value as the ratio of the
evidence-weighted value to the evidence mass, so "normalised or not" is pinned by the
absence of any hypothesis.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.EvidenceContext

open OpenInfluence FiniteKernelsProofs.Finite
open RewardKernel (Effect pull push mass value conditionalValue)

/-- The expected utility of `(K, W)` against a prior and a continuation. -/
abbrev euF {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ℝ :=
  ∑ x, μ x * ∑ y, (W x y + K x y * c y)

/-- The conditional value of a state `(ν, ρ)` against an effect `(m, c)`. -/
noncomputable abbrev condF {X : Type} [Fintype X] (s e : (X → ℝ) × (X → ℝ)) : ℝ :=
  (∑ x, (s.2 x * e.1 x + s.1 x * e.2 x)) / ∑ x, s.1 x * e.1 x

/-- The backward action on a pair `(m, c)`. -/
abbrev pullF {Y Z : Type} [Fintype Z] (K W : Kernel Y Z) (p : (Z → ℝ) × (Z → ℝ)) :
    (Y → ℝ) × (Y → ℝ) :=
  (fun y => ∑ z, K y z * p.1 z, fun y => ∑ z, (W y z * p.1 z + K y z * p.2 z))

/-- The forward action on a pair `(ν, ρ)`. -/
abbrev pushF {X Y : Type} [Fintype X] (K W : Kernel X Y) (p : (X → ℝ) × (X → ℝ)) :
    (Y → ℝ) × (Y → ℝ) :=
  (fun y => ∑ x, p.1 x * K x y, fun y => ∑ x, (p.2 x * K x y + p.1 x * W x y))

/-- `eu_comp_pull` and `conditionalValue_comp`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z) (μ : X → ℝ) (c : Z → ℝ),
      (f.comp g).eu μ c =
        value (RewardKernel.State.ofPrior μ) (f.pull (g.pull (Effect.ofValue c)))) ∧
    ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z) (s : RewardKernel.State X) (e : Effect Z),
      conditionalValue s ((f.comp g).pull e) = conditionalValue (f.push s) (g.pull e)

/-- "For any two reward kernels, normalised or not, the composite's expected utility is the
prefix's value against the suffix's effect": the suffix contributes its mass `m_g` and its
value `c_g`, and the prefix's reward is weighted by `m_g`. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y)
    (Kg Wg : Kernel Y Z) (μ : X → ℝ) (c : Z → ℝ),
    euF (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) μ c =
      ∑ x, μ x * ∑ y, (Wf x y * ∑ z, Kg y z + Kf x y * ∑ z, (Wg y z + Kg y z * c z))

/-- "the composite's conditional value ... is the conditional value of the prefix's
pushed-forward state against the suffix's pulled-back effect". -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y)
    (Kg Wg : Kernel Y Z) (s : (X → ℝ) × (X → ℝ)) (e : (Z → ℝ) × (Z → ℝ)),
    condF s (pullF (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) e) =
      condF (pushF Kf Wf s) (pullF Kg Wg e)

-- The value of a plain prior against a pulled-back effect, unfolded.
theorem value_ofPrior_pull {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ)
    (e : Effect Y) :
    value (RewardKernel.State.ofPrior μ) ((⟨K, W⟩ : RewardKernel X Y).pull e) =
      ∑ x, μ x * ∑ y, (W x y * e.m y + K x y * e.c y) := by
  simp [value, RewardKernel.State.ofPrior, pull]

theorem forward1 : Candidate → Shadow1 := by
  intro h X Y Z _ _ _ Kf Wf Kg Wg μ c
  have e := h.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ μ c
  rw [value_ofPrior_pull] at e
  simpa [RewardKernel.eu, pull, Effect.ofValue] using e

theorem forward2 : Candidate → Shadow2 := fun h X Y Z _ _ _ Kf Wf Kg Wg s e =>
  h.2 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ ⟨s.1, s.2⟩ ⟨e.1, e.2⟩

theorem backward : Shadow1 → Shadow2 → Candidate := by
  intro h1 h2
  refine ⟨fun X Y Z _ _ _ f g μ c => ?_, fun X Y Z _ _ _ f g s e =>
    h2 X Y Z f.K f.W g.K g.W (s.ν, s.ρ) (e.m, e.c)⟩
  have e := h1 X Y Z f.K f.W g.K g.W μ c
  rw [value_ofPrior_pull]
  simpa [RewardKernel.eu, pull, Effect.ofValue] using e

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ f g μ c => RewardKernel.eu_comp_pull f g μ c,
    fun _ _ _ _ _ _ f g s e => RewardKernel.conditionalValue_comp f g s e⟩

end CategoricalInfluenceDiagramsProofs.Shadows.EvidenceContext
