import CategoricalInfluenceDiagramsProofs.Perfection

/-!
# SA-Pass shadow module: an equilibrium sustained by an untested threat

Claim `cid.threat-witness`, from `Threat.threat_equilibrium`, `Threat.threat_perfect_iff` and
`Threat.threat_optimum`. The claim is about one finite witness and is registered as weak
(`independently_provable = true`). The shadows pin the payoffs and split the sentence.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.ThreatWitness

open OpenInfluence OpenInfluence.Threat

/-- The composite's value. -/
noncomputable abbrev value (a : Bool) (b : Bool → Bool) : ℝ :=
  ((first a).comp (second b)).eu (fun _ => 1) (fun _ => 0)

/-- The three theorems, restated. -/
abbrev Candidate : Prop :=
  (((Game.decision first first_normalised).seq (Game.decision second second_normalised)).Eq
      (fun _ => 1) (fun _ => 0) (false, threat) ∧ value false threat = 1) ∧
    (∀ a b, ((Game.perfect first first_normalised).seq
        (Game.perfect second second_normalised)).Eq (fun _ => 1) (fun _ => 0) (a, b) ↔
      a = true ∧ b true = true) ∧
    ((∀ a b, value a b ≤ 4) ∧ value true (fun _ => true) = 4)

/-- The witness's payoffs: `1` without acting, `4` if both act, `0` if only the first does. -/
abbrev Shadow1 : Prop :=
  payoff false false = 1 ∧ payoff false true = 1 ∧ payoff true true = 4 ∧ payoff true false = 0

/-- "not acting, against a refusal that is never tested, is an equilibrium worth 1". -/
abbrev Shadow2 : Prop :=
  ((Game.decision first first_normalised).seq (Game.decision second second_normalised)).Eq
    (fun _ => 1) (fun _ => 0) (false, threat) ∧ value false threat = 1

/-- "its perfect equilibria are exactly the strategies in which the first acts and the second
cooperates when it does, worth the optimum 4". -/
abbrev Shadow3 : Prop :=
  (∀ a b, ((Game.perfect first first_normalised).seq
      (Game.perfect second second_normalised)).Eq (fun _ => 1) (fun _ => 0) (a, b) ↔
    a = true ∧ b true = true) ∧ (∀ a b, value a b ≤ 4) ∧ value true (fun _ => true) = 4

theorem forward1 : Candidate → Shadow1 := fun _ => by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Threat.payoff]

theorem forward2 : Candidate → Shadow2 := fun h => h.1

theorem forward3 : Candidate → Shadow3 := fun h => ⟨h.2.1, h.2.2⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun _ h2 h3 =>
  ⟨h2, h3.1, h3.2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := ⟨threat_equilibrium, threat_perfect_iff, threat_optimum⟩

end CategoricalInfluenceDiagramsProofs.Shadows.ThreatWitness
