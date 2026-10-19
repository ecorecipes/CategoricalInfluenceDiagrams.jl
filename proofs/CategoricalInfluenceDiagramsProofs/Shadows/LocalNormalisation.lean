import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# SA-Pass shadow module: normalising each component is not sound

Claim `cid.local-normalisation`, from `LocalNormalisation.local_normalisation_obstruction`.
The claim is about one finite witness, so every shadow is decidable by computing it, and the
claim is registered as weak (`independently_provable = true`). The shadows still pin what
the sentence means: the witness's tables are a uniform binary state worth `1` when true and
evidence nine times likelier when it is true; the composite conditioned on the evidence is
worth `9/10`; the components normalised one by one give `1/2`.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.LocalNormalisation

open OpenInfluence OpenInfluence.LocalNormalisation RewardKernel

/-- `local_normalisation_obstruction`, restated. -/
abbrev Candidate : Prop :=
  conditionalValue start ((prior.comp evidence).pull finish) = 9 / 10 ∧
    conditionalValue start (((normalise prior).comp (normalise evidence)).pull finish) =
      1 / 2

/-- "a uniform binary state worth 1 when true, and evidence nine times likelier when it is
true": the witness's tables. -/
abbrev Shadow1 : Prop :=
  (∀ b, prior.K () b = 1 / 2) ∧ prior.W () true = 1 / 2 ∧ prior.W () false = 0 ∧
    evidence.K true () = 9 * evidence.K false () ∧ ∀ b, evidence.W b () = 0

/-- "the conditional value is 9/10". -/
abbrev Shadow2 : Prop := conditionalValue start ((prior.comp evidence).pull finish) = 9 / 10

/-- "while the components normalised one by one give 1/2". -/
abbrev Shadow3 : Prop :=
  conditionalValue start (((normalise prior).comp (normalise evidence)).pull finish) = 1 / 2

theorem forward1 : Candidate → Shadow1 := fun _ =>
  ⟨fun _ => rfl, rfl, rfl, by norm_num [evidence], fun _ => rfl⟩

theorem forward2 : Candidate → Shadow2 := fun h => h.1

theorem forward3 : Candidate → Shadow3 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun _ h2 h3 => ⟨h2, h3⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := local_normalisation_obstruction

end CategoricalInfluenceDiagramsProofs.Shadows.LocalNormalisation
