import CategoricalInfluenceDiagramsProofs.Obstruction

/-!
# SA-Pass shadow module: isolated optimisation is not globally sound

Claim `cid.isolated-obstruction`, from `Obstruction.isolated_optimisation_fails`
(`INF-ISOLATED-OBSTRUCTION`). The claim is about one finite witness, so the candidate is a
closed proposition with nothing to quantify over: every shadow is decidable by computing the
witness, and the claim is registered as weak (`independently_provable = true`). The shadows
still pin what the prose means by "every pair of separately optimal components", "composes
to expected utility 1" and "the joint optimum is 4".
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.IsolatedObstruction

open OpenInfluence OpenInfluence.Obstruction RewardKernel

/-- `isolated_optimisation_fails`, restated. -/
abbrev Candidate : Prop :=
  (∀ (a : Bool) (τ : Bool → Bool), IsolatedOptimal early unitPrior zeroCont a →
      IsolatedOptimal late (boundaryLaw a) zeroCont τ →
        ((early a).comp (late τ)).eu unitPrior zeroCont = 1) ∧
    (IsolatedOptimal early unitPrior zeroCont false ∧
      IsolatedOptimal late (boundaryLaw false) zeroCont (fun _ => false)) ∧
    ((early true).comp (late fun _ => false)).eu unitPrior zeroCont = 4 ∧
    (∀ (a : Bool) (τ : Bool → Bool), ((early a).comp (late τ)).eu unitPrior zeroCont ≤ 4) ∧
    (1 : ℝ) < 4

/-- "every pair of separately optimal components composes to expected utility 1": the prefix
optimal on its own, then the suffix optimal on its own against the boundary law that prefix
induces. -/
abbrev Shadow1 : Prop :=
  ∀ (a : Bool) (τ : Bool → Bool),
    (∀ b, (early b).eu unitPrior zeroCont ≤ (early a).eu unitPrior zeroCont) →
    (∀ τ', (late τ').eu (boundaryLaw a) zeroCont ≤ (late τ).eu (boundaryLaw a) zeroCont) →
      ((early a).comp (late τ)).eu unitPrior zeroCont = 1

/-- There is such a pair, so the first shadow is not vacuous. -/
abbrev Shadow2 : Prop :=
  ∃ (a : Bool) (τ : Bool → Bool),
    (∀ b, (early b).eu unitPrior zeroCont ≤ (early a).eu unitPrior zeroCont) ∧
    (∀ τ', (late τ').eu (boundaryLaw a) zeroCont ≤ (late τ).eu (boundaryLaw a) zeroCont)

/-- "the joint optimum is 4": it is attained ... -/
abbrev Shadow3 : Prop :=
  ∃ (a : Bool) (τ : Bool → Bool), ((early a).comp (late τ)).eu unitPrior zeroCont = 4

/-- ... and not exceeded. -/
abbrev Shadow4 : Prop :=
  ∀ (a : Bool) (τ : Bool → Bool), ((early a).comp (late τ)).eu unitPrior zeroCont ≤ 4

theorem forward1 : Candidate → Shadow1 := fun h a τ ha hτ => h.1 a τ ha hτ

theorem forward2 : Candidate → Shadow2 := fun h => ⟨false, fun _ => false, h.2.1.1, h.2.1.2⟩

theorem forward3 : Candidate → Shadow3 := fun h => ⟨true, fun _ => false, h.2.2.1⟩

theorem forward4 : Candidate → Shadow4 := fun h => h.2.2.2.1

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := by
  intro h1 _ _ h4
  -- Shadows 2 and 3 say that such pairs exist; the candidate names them, so its middle
  -- conjuncts are checked on the witness.
  refine ⟨fun a τ ha hτ => h1 a τ ha hτ, ⟨fun b => ?_, fun τ' => ?_⟩, ?_, h4, by norm_num⟩
  · rw [early_eu, early_eu]; cases b <;> norm_num
  · rw [late_eu, late_eu]
  · rw [composite_eu]; norm_num

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := isolated_optimisation_fails

end CategoricalInfluenceDiagramsProofs.Shadows.IsolatedObstruction
