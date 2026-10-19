import CategoricalInfluenceDiagramsProofs.GameTensor

/-!
# SA-Pass shadow module: no context of a factor alone for a correlated prior

Claim `cid.tensor-correlated`, from `CorrelatedTensor.correlated_best_responses` and
`CorrelatedTensor.correlated_no_factor_context`. The claim is about one finite witness, so the
claim is registered as weak (`independently_provable = true`). The shadows pin the witness
(equal binary inputs, a payoff for matching outputs, a second factor that passes its input
through) and split the sentence into its two halves.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.TensorCorrelated

open OpenInfluence OpenInfluence.CorrelatedTensor

/-- The composite's value of the first factor's policy `s`. -/
noncomputable abbrev joint (s : Bool → Bool) : ℝ :=
  ((copyPlay s).tensor (RewardKernel.id Bool)).eu prior payoff

/-- The two theorems, restated. -/
abbrev Candidate : Prop :=
  (∀ s : Bool → Bool, (∀ s', joint s' ≤ joint s) ↔ ∀ x, s x = x) ∧
    ¬ ∃ μ₁ c₁ : Bool → ℝ, (∀ x, 0 ≤ μ₁ x) ∧ ∀ s, (first.Eq μ₁ c₁ s ↔ ∀ x, s x = x)

/-- "the first factor's best responses are exactly the policy that copies its input". -/
abbrev Shadow1 : Prop := ∀ s : Bool → Bool, (∀ s', joint s' ≤ joint s) ↔ ∀ x, s x = x

/-- "in no context of a probability vector on its input and a continuation on its output are
its equilibria exactly that policy". -/
abbrev Shadow2 : Prop :=
  ∀ μ₁ c₁ : Bool → ℝ, (∀ x, 0 ≤ μ₁ x) → ∃ s, ¬ (first.Eq μ₁ c₁ s ↔ ∀ x, s x = x)

/-- The witness: the inputs are equal, each value with probability one half. -/
abbrev Shadow3 : Prop :=
  prior (true, true) = 1 / 2 ∧ prior (false, false) = 1 / 2 ∧ prior (true, false) = 0 ∧
    prior (false, true) = 0

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := fun h μ₁ c₁ hμ => by
  by_contra hno
  push Not at hno
  exact h.2 ⟨μ₁, c₁, hμ, hno⟩

theorem forward3 : Candidate → Shadow3 := fun _ => by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [CorrelatedTensor.prior]

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 _ =>
  ⟨h1, fun ⟨μ₁, c₁, hμ, h⟩ => by
    obtain ⟨s, hs⟩ := h2 μ₁ c₁ hμ
    exact hs (h s)⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := ⟨correlated_best_responses, correlated_no_factor_context⟩

end CategoricalInfluenceDiagramsProofs.Shadows.TensorCorrelated
