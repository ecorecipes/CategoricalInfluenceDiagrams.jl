import CategoricalInfluenceDiagramsProofs.Certificate.Record

/-!
# Reward certificates: decoding the JSON

This module decodes a parsed `Lean.Json` tree into a `Certificate` (`decodeCertificate`) and
a certificate text into one (`read`). It reuses the readers of the two parent projects:

* the `network` object is decoded by CategoricalBayesianNetworks' record readers
  (`OpenNet.RawCertificate.JSON.variableData`, `mechanism`, `boundary`, with its `keys`,
  `field`, `list` and `natural`), exactly as `OpenNet.RawCertificate.JSON.network` decodes the
  body of `OpenNet.RawCertificate/v1`, except that there is no `format` key
  (`networkBody`). Utility scope rows have the shape of input rows and are decoded by its
  `inputRow`;
* number cells are decoded by InfluenceDiagrams' `decodeValue`, and the new records use its
  key and array helpers (`get`, `getArr`) and BayesianNetworks' exact-size `object`;
* the text is parsed by CategoricalBayesianNetworks' strict parser
  (`OpenNet.CertificateSyntax.parse`), which rejects duplicate keys, trailing input and
  non-integer number tokens.

Every object must have exactly its listed keys: a missing key fails, and since a JSON object
here has distinct keys, an extra key changes the size and fails too. Key order is ignored.

**Results.** For each new record, `decodeX_eq_ok` states that decoding succeeds with `x`
exactly when the JSON is `x`'s layout key for key (`XMatches`): flags
(`decodeFlag_eq_ok`), the numeric mode, metadata, observability, chance tables, utilities,
policies and the result. `decodeCertificate_eq_ok` states the same for the whole
certificate, with the `network` and the utility scope rows specified by the reused readers
(the network reader has no such characterisation in its own project;
`networkBody_fields` records what its success means). `read_eq_ok` adds the parser.

Trusted, not proved: the parser itself (shared with CategoricalBayesianNetworks) and the
Julia exporter.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate.Json

open Lean (Json)
open OpenNet.RawCertificate
open BayesianNetworksProofs.Raw (JsonObject object object_eq_ok bind_eq_ok pure_eq_ok
  throw_ne_ok natJson)
open InfluenceDiagramsProofs.DVECertificate (get get_eq_ok getArr getArr_eq_ok ArrayMatches
  strOf strOf_eq_ok natOf natOf_eq_ok decodeValue decodeValue_eq_ok ValueMatches)

/-! ## Constant strings -/

/-- A string that must equal `expected`. -/
def constant (expected : String) (j : Json) : Except String Unit := do
  let s ← strOf j
  if s = expected then pure () else throw s!"expected \"{expected}\", found \"{s}\""

theorem constant_eq_ok {expected : String} {j : Json} {u : Unit} :
    constant expected j = .ok u ↔ j = .str expected := by
  unfold constant
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split_ifs at h with he
    · rw [he]
  · rintro rfl
    exact ⟨expected, strOf_eq_ok.2 rfl, by rw [if_pos rfl]; rfl⟩

/-! ## Flags and numeric mode -/

/-- The JSON spelling of a flag. -/
def flagString : Observability → String
  | .observed => "observed"
  | .hidden => "hidden"

def decodeFlag (j : Json) : Except String Observability := do
  let s ← strOf j
  if s = "observed" then pure .observed
  else if s = "hidden" then pure .hidden
  else throw s!"unknown observability flag \"{s}\""

theorem decodeFlag_eq_ok {j : Json} {b : Observability} :
    decodeFlag j = .ok b ↔ j = .str (flagString b) := by
  unfold decodeFlag
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split_ifs at h with h1 h2
    · rw [pure_eq_ok] at h
      subst h h1
      rfl
    · rw [pure_eq_ok] at h
      subst h h2
      rfl
  · rintro rfl
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    cases b <;> simp [flagString] <;> rfl

def decodeMode (j : Json) : Except String NumericMode := do
  let s ← strOf j
  if s = "binary64_exact" then pure .binary64Exact
  else if s = "rational_exact" then pure .rationalExact
  else throw s!"unknown numeric mode \"{s}\""

theorem decodeMode_eq_ok {j : Json} {m : NumericMode} :
    decodeMode j = .ok m ↔ j = .str m.toString := by
  unfold decodeMode
  rw [bind_eq_ok]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [strOf_eq_ok] at hs
    subst hs
    split_ifs at h with h1 h2
    · rw [pure_eq_ok] at h
      subst h h1
      rfl
    · rw [pure_eq_ok] at h
      subst h h2
      rfl
  · rintro rfl
    refine ⟨_, strOf_eq_ok.2 rfl, ?_⟩
    cases m <;> simp [NumericMode.toString] <;> rfl

/-! ## Metadata and observability -/

def decodeMetadata (j : Json) : Except String Metadata := do
  let o ← object "metadata" 4 j
  let p ← get o "producer" strOf
  let pv ← get o "producer_version" strOf
  let jv ← get o "julia_version" strOf
  let d ← get o "description" strOf
  pure ⟨p, pv, jv, d⟩

def MetadataMatches (j : Json) (m : Metadata) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 4 ∧ o["producer"]? = some (.str m.producer) ∧
    o["producer_version"]? = some (.str m.producerVersion) ∧
    o["julia_version"]? = some (.str m.juliaVersion) ∧
    o["description"]? = some (.str m.description)

theorem decodeMetadata_eq_ok {j : Json} {m : Metadata} :
    decodeMetadata j = .ok m ↔ MetadataMatches j m := by
  unfold decodeMetadata MetadataMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, h1, rfl⟩, _, ⟨_, h2, rfl⟩, _, ⟨_, h3, rfl⟩, _, ⟨_, h4, rfl⟩,
      rfl⟩
    exact ⟨o, rfl, hs, h1, h2, h3, h4⟩
  · rintro ⟨o, rfl, hs, h1, h2, h3, h4⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, h1, rfl⟩, _, ⟨_, h2, rfl⟩, _, ⟨_, h3, rfl⟩, _, ⟨_, h4, rfl⟩,
      rfl⟩

/-- A flag array: element `k` is the spelling of flag `k`. -/
def FlagsMatch (j : Json) (l : List Observability) : Prop :=
  ArrayMatches (fun _ v b => v = .str (flagString b)) j l

def decodeObservability (j : Json) :
    Except String (List Observability × List Observability) := do
  let o ← object "observability" 2 j
  let i ← getArr o "inputs" (fun _ => decodeFlag)
  let out ← getArr o "outputs" (fun _ => decodeFlag)
  pure (i, out)

def ObservabilityMatches (j : Json) (ins outs : List Observability) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 2 ∧
    (∃ v, o["inputs"]? = some v ∧ FlagsMatch v ins) ∧
    (∃ v, o["outputs"]? = some v ∧ FlagsMatch v outs)

theorem decodeObservability_eq_ok {j : Json} {ins outs : List Observability} :
    decodeObservability j = .ok (ins, outs) ↔ ObservabilityMatches j ins outs := by
  unfold decodeObservability ObservabilityMatches FlagsMatch
  simp only [bind_eq_ok, object_eq_ok, getArr_eq_ok fun _ _ _ => decodeFlag_eq_ok, pure_eq_ok,
    Prod.mk.injEq]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, hi, _, ho, rfl, rfl⟩
    exact ⟨o, rfl, hs, hi, ho⟩
  · rintro ⟨o, rfl, hs, hi, ho⟩
    exact ⟨o, ⟨rfl, hs⟩, _, hi, _, ho, rfl, rfl⟩

/-! ## Tables, utilities, policies and the result -/

/-- A cell array: element `k` is the layout of cell `k`. -/
def CellsMatch (j : Json) (l : List Value) : Prop :=
  ArrayMatches (fun _ => ValueMatches) j l

def decodeChanceTable (j : Json) : Except String ChanceTable := do
  let o ← object "chance table" 2 j
  let g ← get o "mechanism" natOf
  let cells ← getArr o "cells" (fun _ => decodeValue)
  pure ⟨g, cells⟩

def ChanceTableMatches (j : Json) (t : ChanceTable) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 2 ∧ o["mechanism"]? = some (natJson t.mechanism) ∧
    ∃ v, o["cells"]? = some v ∧ CellsMatch v t.cells

theorem decodeChanceTable_eq_ok {j : Json} {t : ChanceTable} :
    decodeChanceTable j = .ok t ↔ ChanceTableMatches j t := by
  unfold decodeChanceTable ChanceTableMatches CellsMatch
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => natOf_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeValue_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, hg, rfl⟩, _, hc, rfl⟩
    exact ⟨o, rfl, hs, hg, hc⟩
  · rintro ⟨o, rfl, hs, hg, hc⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hg, rfl⟩, _, hc, rfl⟩

/-- The scope rows of a utility, read by CategoricalBayesianNetworks' input-row reader. -/
def decodeScopeRows (n : ℕ) (j : Json) : Except String (List (InputRow n)) :=
  JSON.list (JSON.inputRow n) j

def decodeUtility (n : ℕ) (j : Json) : Except String (Utility n) := do
  let o ← object "utility" 3 j
  let name ← get o "name" strOf
  let rows ← get o "scopeRows" (decodeScopeRows n)
  let cells ← getArr o "cells" (fun _ => decodeValue)
  pure ⟨name, rows, cells⟩

def UtilityMatches (n : ℕ) (j : Json) (u : Utility n) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 3 ∧ o["name"]? = some (.str u.name) ∧
    (∃ v, o["scopeRows"]? = some v ∧ decodeScopeRows n v = .ok u.scopeRows) ∧
    ∃ v, o["cells"]? = some v ∧ CellsMatch v u.cells

theorem decodeUtility_eq_ok {n : ℕ} {j : Json} {u : Utility n} :
    decodeUtility n j = .ok u ↔ UtilityMatches n j u := by
  unfold decodeUtility UtilityMatches CellsMatch
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    get_eq_ok (M := fun v x => decodeScopeRows n v = .ok x) fun _ _ => Iff.rfl,
    getArr_eq_ok fun _ _ _ => decodeValue_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, hn, rfl⟩, _, hr, _, hc, rfl⟩
    exact ⟨o, rfl, hs, hn, hr, hc⟩
  · rintro ⟨o, rfl, hs, hn, hr, hc⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hn, rfl⟩, _, hr, _, hc, rfl⟩

def decodePolicy (j : Json) : Except String Policy := do
  let o ← object "policy" 2 j
  let d ← get o "decision" strOf
  let a ← getArr o "actions" (fun _ => natOf)
  pure ⟨d, a⟩

def PolicyMatches (j : Json) (p : Policy) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 2 ∧ o["decision"]? = some (.str p.decision) ∧
    ∃ v, o["actions"]? = some v ∧ ArrayMatches (fun _ v a => v = natJson a) v p.actions

theorem decodePolicy_eq_ok {j : Json} {p : Policy} :
    decodePolicy j = .ok p ↔ PolicyMatches j p := by
  unfold decodePolicy PolicyMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => strOf_eq_ok,
    getArr_eq_ok fun _ _ _ => natOf_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, hd, rfl⟩, _, ha, rfl⟩
    exact ⟨o, rfl, hs, hd, ha⟩
  · rintro ⟨o, rfl, hs, hd, ha⟩
    exact ⟨o, ⟨rfl, hs⟩, _, ⟨_, hd, rfl⟩, _, ha, rfl⟩

def decodeResult (j : Json) : Except String Result := do
  let o ← object "result" 3 j
  get o "arithmetic" (constant "binary64")
  let k ← getArr o "K" (fun _ => decodeValue)
  let w ← getArr o "W" (fun _ => decodeValue)
  pure ⟨k, w⟩

def ResultMatches (j : Json) (r : Result) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 3 ∧ o["arithmetic"]? = some (.str "binary64") ∧
    (∃ v, o["K"]? = some v ∧ CellsMatch v r.K) ∧ ∃ v, o["W"]? = some v ∧ CellsMatch v r.W

theorem decodeResult_eq_ok {j : Json} {r : Result} :
    decodeResult j = .ok r ↔ ResultMatches j r := by
  unfold decodeResult ResultMatches CellsMatch
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => constant_eq_ok,
    getArr_eq_ok fun _ _ _ => decodeValue_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, ha, rfl⟩, _, hk, _, hw, rfl⟩
    exact ⟨o, rfl, hs, ha, hk, hw⟩
  · rintro ⟨o, rfl, hs, ha, hk, hw⟩
    exact ⟨o, ⟨rfl, hs⟩, (), ⟨_, ha, rfl⟩, _, hk, _, hw, rfl⟩

/-! ## The network -/

/-- The body of `OpenNet.RawCertificate/v1` without its `format` key, decoded by
CategoricalBayesianNetworks' readers exactly as its `network` does. -/
def networkBody (j : Json) : Except String Network := do
  JSON.keys j ["variableCount", "variableData", "mechanisms", "inputs", "outputs"]
  let n ← JSON.field j "variableCount" JSON.natural
  let vars ← JSON.field j "variableData" (JSON.list JSON.variableData)
  if h : vars.length = n then
    return {
      variableCount := n
      variableData := fun i => vars[i.val]'(h.symm ▸ i.isLt)
      mechanisms := ← JSON.field j "mechanisms" (JSON.list (JSON.mechanism n))
      inputs := ← JSON.field j "inputs" (JSON.list (JSON.boundary n))
      outputs := ← JSON.field j "outputs" (JSON.list (JSON.boundary n)) }
  else
    throw "variableCount does not match variableData length"

/-- What a successful network decoding means: exactly the five keys, and every field is what
the reused reader returns. -/
theorem networkBody_fields {j : Json} {N : Network} (h : networkBody j = .ok N) :
    JSON.keys j ["variableCount", "variableData", "mechanisms", "inputs", "outputs"] = .ok () ∧
    JSON.field j "variableCount" JSON.natural = .ok N.variableCount ∧
    (∃ vars : List VariableData, JSON.field j "variableData" (JSON.list JSON.variableData) =
      .ok vars ∧ ∃ hl : vars.length = N.variableCount,
        ∀ i : Fin N.variableCount, N.variableData i = vars[i.val]'(hl.symm ▸ i.isLt)) ∧
    JSON.field j "mechanisms" (JSON.list (JSON.mechanism N.variableCount)) = .ok N.mechanisms ∧
    JSON.field j "inputs" (JSON.list (JSON.boundary N.variableCount)) = .ok N.inputs ∧
    JSON.field j "outputs" (JSON.list (JSON.boundary N.variableCount)) = .ok N.outputs := by
  unfold networkBody at h
  simp only [bind_eq_ok] at h
  obtain ⟨u, hk, n, hn, vars, hv, h⟩ := h
  cases u
  split at h
  · rename_i hl
    simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨ms, hm, is, hi, os, ho, rfl⟩ := h
    exact ⟨hk, hn, ⟨vars, hv, hl, fun _ => rfl⟩, hm, hi, ho⟩
  · exact absurd h throw_ne_ok

/-! ## The certificate -/

/-- The top-level keys, in the format's order. -/
def certificateKeys : List String :=
  ["format", "numeric_mode", "metadata", "network", "observability", "chance_tables",
    "utilities", "strategy", "result"]

def decodeCertificate (j : Json) : Except String Certificate := do
  let o ← object "certificate" 9 j
  get o "format" (constant formatName)
  let mode ← get o "numeric_mode" decodeMode
  let md ← get o "metadata" decodeMetadata
  let N ← get o "network" networkBody
  let obs ← get o "observability" decodeObservability
  let tables ← getArr o "chance_tables" (fun _ => decodeChanceTable)
  let utils ← getArr o "utilities" (fun _ => decodeUtility N.variableCount)
  let strat ← getArr o "strategy" (fun _ => decodePolicy)
  let res ← get o "result" decodeResult
  pure ⟨mode, md, N, obs.1, obs.2, tables, utils, strat, res⟩

/-- The certificate `c` is the JSON `j`, key for key: the new records by their `Matches`
predicates, the network and the utility scope rows by the reused readers. -/
def CertificateMatches (j : Json) (c : Certificate) : Prop :=
  ∃ o : JsonObject, j = .obj o ∧ o.size = 9 ∧ o["format"]? = some (.str formatName) ∧
    o["numeric_mode"]? = some (.str c.numericMode.toString) ∧
    (∃ v, o["metadata"]? = some v ∧ MetadataMatches v c.metadata) ∧
    (∃ v, o["network"]? = some v ∧ networkBody v = .ok c.network) ∧
    (∃ v, o["observability"]? = some v ∧ ObservabilityMatches v c.inputFlags c.outputFlags) ∧
    (∃ v, o["chance_tables"]? = some v ∧
      ArrayMatches (fun _ => ChanceTableMatches) v c.chanceTables) ∧
    (∃ v, o["utilities"]? = some v ∧
      ArrayMatches (fun _ => UtilityMatches c.network.variableCount) v c.utilities) ∧
    (∃ v, o["strategy"]? = some v ∧ ArrayMatches (fun _ => PolicyMatches) v c.strategy) ∧
    ∃ v, o["result"]? = some v ∧ ResultMatches v c.result

theorem decodeObservability_eq_ok' {j : Json} {p : List Observability × List Observability} :
    decodeObservability j = .ok p ↔ ObservabilityMatches j p.1 p.2 := by
  obtain ⟨a, b⟩ := p
  exact decodeObservability_eq_ok

/-- **Faithfulness of the decoder**: decoding succeeds with `c` exactly when the JSON is
`c`'s layout. -/
theorem decodeCertificate_eq_ok {j : Json} {c : Certificate} :
    decodeCertificate j = .ok c ↔ CertificateMatches j c := by
  unfold decodeCertificate CertificateMatches
  simp only [bind_eq_ok, object_eq_ok, get_eq_ok fun _ _ => constant_eq_ok,
    get_eq_ok fun _ _ => decodeMode_eq_ok, get_eq_ok fun _ _ => decodeMetadata_eq_ok,
    get_eq_ok (M := fun v x => networkBody v = .ok x) fun _ _ => Iff.rfl,
    get_eq_ok fun _ _ => decodeObservability_eq_ok',
    getArr_eq_ok fun _ _ _ => decodeChanceTable_eq_ok,
    getArr_eq_ok fun _ _ _ => decodePolicy_eq_ok,
    get_eq_ok fun _ _ => decodeResult_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨o, ⟨rfl, hs⟩, _, ⟨_, hf, rfl⟩, mode, ⟨_, hm, rfl⟩, md, ⟨_, hmeta, hmeta'⟩, N,
      ⟨_, hn, hn'⟩, obs, ⟨_, hobs, hobs'⟩, tables, ht, utils, hu, strat, hst, res,
      ⟨_, hr, hr'⟩, rfl⟩
    rw [getArr_eq_ok fun _ _ _ => decodeUtility_eq_ok] at hu
    exact ⟨o, rfl, hs, hf, hm, ⟨_, hmeta, hmeta'⟩, ⟨_, hn, hn'⟩, ⟨_, hobs, hobs'⟩, ht, hu,
      hst, ⟨_, hr, hr'⟩⟩
  · obtain ⟨mode, md, N, ins, outs, tables, utils, strat, res⟩ := c
    rintro ⟨o, rfl, hs, hf, hm, ⟨_, hmeta, hmeta'⟩, ⟨_, hn, hn'⟩, ⟨_, hobs, hobs'⟩, ht, hu,
      hst, ⟨_, hr, hr'⟩⟩
    refine ⟨o, ⟨rfl, hs⟩, (), ⟨_, hf, rfl⟩, mode, ⟨_, hm, rfl⟩, md, ⟨_, hmeta, hmeta'⟩, N,
      ⟨_, hn, hn'⟩, (ins, outs), ⟨_, hobs, hobs'⟩, tables, ht, utils, ?_, strat, hst, res,
      ⟨_, hr, hr'⟩, rfl⟩
    rw [getArr_eq_ok fun _ _ _ => decodeUtility_eq_ok]
    exact hu

/-- Parse with CategoricalBayesianNetworks' strict parser, then decode. -/
def read (text : String) : Except String Certificate := do
  let j ← OpenNet.CertificateSyntax.parse text
  decodeCertificate j

theorem read_eq_ok {text : String} {c : Certificate} :
    read text = .ok c ↔ ∃ j, OpenNet.CertificateSyntax.parse text = .ok j ∧
      CertificateMatches j c := by
  unfold read
  rw [bind_eq_ok]
  simp only [decodeCertificate_eq_ok]

/-- A read certificate is the decoding of the parsed text, and its network is what the reused
network readers return on the `network` value. -/
theorem read_preserves_decoded {text : String} {c : Certificate} (h : read text = .ok c) :
    ∃ j, OpenNet.CertificateSyntax.parse text = .ok j ∧ decodeCertificate j = .ok c ∧
      ∃ o : JsonObject, j = .obj o ∧ ∃ v, o["network"]? = some v ∧
        networkBody v = .ok c.network := by
  obtain ⟨j, hj, hm⟩ := read_eq_ok.1 h
  have hd := decodeCertificate_eq_ok.2 hm
  obtain ⟨o, rfl, -, -, -, -, ⟨v, hv, hn⟩, -⟩ := hm
  exact ⟨_, hj, hd, o, rfl, v, hv, hn⟩

end OpenInfluence.RewardCertificate.Json
