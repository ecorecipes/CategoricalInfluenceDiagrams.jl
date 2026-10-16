import CategoricalInfluenceDiagramsProofs.Obstruction

/-!
# SA-Pass shadow module: pointwise maximisation at a hidden boundary state

Claim `cid.hidden-obstruction`, from `Obstruction.hidden_input_obstruction`
(`INF-HIDDEN-OBSTRUCTION`). As for `cid.isolated-obstruction`, the candidate is a closed
proposition about one finite witness, so the claim is registered as weak
(`independently_provable = true`); the shadows pin what "every legal suffix policy",
"maximising at each boundary state" and "not a legal policy" mean.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.HiddenObstruction

open OpenInfluence OpenInfluence.Obstruction RewardKernel

/-- `hidden_input_obstruction`, restated. -/
abbrev Candidate : Prop :=
  (∀ sel, Legal sel → (lateSel sel).eu (boundaryLaw false) zeroCont = 1) ∧
    (∀ sel s, (lateSel sel).W s () ≤ (lateSel peek).W s ()) ∧
    (lateSel peek).eu (boundaryLaw false) zeroCont = 2 ∧
    ¬ Legal peek ∧ (1 : ℝ) < 2

/-- "every legal suffix policy has value 1": a selector that reads only the observed
coordinate. -/
abbrev Shadow1 : Prop :=
  ∀ τ : Bool → Bool, (lateSel fun s => τ s.2).eu (boundaryLaw false) zeroCont = 1

/-- "maximising at each boundary state": `peek` attains the largest reward at every
boundary state ... -/
abbrev Shadow2 : Prop := ∀ sel s, (lateSel sel).W s () ≤ (lateSel peek).W s ()

/-- "... gives value 2". -/
abbrev Shadow3 : Prop := (lateSel peek).eu (boundaryLaw false) zeroCont = 2

/-- "a selector that reads the hidden variable and is not a legal policy": no function of
the observed coordinate agrees with it. -/
abbrev Shadow4 : Prop := ¬ ∃ τ : Bool → Bool, ∀ s, peek s = τ s.2

theorem forward1 : Candidate → Shadow1 := fun h τ => h.1 _ ⟨τ, fun _ => rfl⟩

theorem forward2 : Candidate → Shadow2 := fun h => h.2.1

theorem forward3 : Candidate → Shadow3 := fun h => h.2.2.1

theorem forward4 : Candidate → Shadow4 := fun h => h.2.2.2.1

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := by
  intro h1 h2 h3 h4
  refine ⟨?_, h2, h3, h4, by norm_num⟩
  rintro sel ⟨τ, hτ⟩
  have : sel = fun s => τ s.2 := funext hτ
  subst this
  exact h1 τ

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := hidden_input_obstruction

end CategoricalInfluenceDiagramsProofs.Shadows.HiddenObstruction
