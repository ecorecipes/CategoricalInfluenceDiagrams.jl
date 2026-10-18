import CategoricalInfluenceDiagramsProofs.Certificate.Json

/-!
# SA-Pass shadow module: faithfulness of the reward-certificate decoder

Claim `cid.certificate-decode`, from `RewardCertificate.Json.decodeCertificate_eq_ok`:
"`decodeCertificate_eq_ok` proves that the reward-certificate decoder succeeds on a parsed
JSON value with a certificate `c` exactly when the value is `c`'s layout key for key, with
exactly the nine top-level keys and with the network and the utility scope rows read by
CategoricalBayesianNetworks' record readers."

"`c`'s layout key for key" is `CertificateMatches`. The shadows split "exactly when" into its
directions, pin the nine top-level keys (an object of size nine holding each of them), and
state that the network is what `networkBody` (CategoricalBayesianNetworks' `variableData`,
`mechanism` and `boundary` readers) returns on the `network` value and that every utility's
scope rows are what CategoricalBayesianNetworks' `inputRow` reader returns.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.CertificateDecode

open Lean (Json)
open OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Json
open BayesianNetworksProofs.Raw (JsonObject)

/-- The cited theorem, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (j : Json) (c : Certificate), decodeCertificate j = .ok c ↔ CertificateMatches j c

/-- "succeeds … only when the value is `c`'s layout key for key". -/
abbrev Shadow1 : Prop :=
  ∀ (j : Json) (c : Certificate), decodeCertificate j = .ok c → CertificateMatches j c

/-- "exactly when": such a value decodes to `c`. -/
abbrev Shadow2 : Prop :=
  ∀ (j : Json) (c : Certificate), CertificateMatches j c → decodeCertificate j = .ok c

/-- "with exactly the nine top-level keys": an object of nine keys holding each of them. -/
abbrev Shadow3 : Prop :=
  ∀ (j : Json) (c : Certificate), decodeCertificate j = .ok c →
    ∃ o : JsonObject, j = .obj o ∧ o.size = 9 ∧ ∀ k ∈ certificateKeys, (o[k]?).isSome

/-- "the network and the utility scope rows read by CategoricalBayesianNetworks' record
readers". -/
abbrev Shadow4 : Prop :=
  ∀ (j : Json) (c : Certificate), decodeCertificate j = .ok c →
    (∃ (o : JsonObject) (v : Json), j = .obj o ∧ o["network"]? = some v ∧
      networkBody v = .ok c.network) ∧
    ∀ u ∈ c.utilities, ∃ v : Json,
      OpenNet.RawCertificate.JSON.list (OpenNet.RawCertificate.JSON.inputRow _) v =
        .ok u.scopeRows

theorem forward1 : Candidate → Shadow1 := fun h j c => (h j c).1

theorem forward2 : Candidate → Shadow2 := fun h j c => (h j c).2

theorem forward3 : Candidate → Shadow3 := fun h j c hd => by
  obtain ⟨o, rfl, hs, hf, hm, ⟨_, h3, -⟩, ⟨_, h4, -⟩, ⟨_, h5, -⟩, ⟨_, h6, -⟩, ⟨_, h7, -⟩,
    ⟨_, h8, -⟩, ⟨_, h9, -⟩⟩ := (h _ c).1 hd
  refine ⟨o, rfl, hs, ?_⟩
  intro k hk
  simp only [certificateKeys, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hf, hm, h3, h4, h5, h6, h7, h8, h9]

theorem forward4 : Candidate → Shadow4 := fun h j c hd => by
  obtain ⟨o, rfl, -, -, -, -, ⟨v, hv, hn⟩, -, -, ⟨w, hw, hu⟩, -⟩ := (h _ c).1 hd
  refine ⟨⟨o, v, rfl, hv, hn⟩, ?_⟩
  have := InfluenceDiagramsProofs.DVECertificate.ArrayMatches.forall hu
    (P := fun u => ∃ v : Json,
      OpenNet.RawCertificate.JSON.list (OpenNet.RawCertificate.JSON.inputRow _) v =
        .ok u.scopeRows)
    (fun _ _ u hm => by
      obtain ⟨_, -, -, -, ⟨s, -, hs⟩, -⟩ := hm
      exact ⟨s, hs⟩)
  exact this

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate :=
  fun s1 s2 _ _ j c => ⟨s1 j c, s2 j c⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ => decodeCertificate_eq_ok

end CategoricalInfluenceDiagramsProofs.Shadows.CertificateDecode
