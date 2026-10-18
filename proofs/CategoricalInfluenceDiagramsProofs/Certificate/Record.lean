import CategoricalInfluenceDiagramsProofs.Interpretation

/-!
# Reward certificates: the record

ADR 0019 adds a certificate format, `OpenInfluence.RewardCertificate/v1`, that records one open
influence diagram as `CategoricalInfluenceDiagrams.jl` holds it, together with its
observability flags, its numerical tables, one deterministic strategy and the reward kernel
`(K, W)` that Julia's `interpret` computed for that strategy. The format is specified in the
workspace plan `docs/REWARD-CERTIFICATES-PLAN-2026-10-17.md` ("The format"), which is the
contract between the Julia exporter and this checker.

This module defines the Lean record of a decoded certificate (`Certificate`). It reuses the
two parent projects instead of restating them:

* the structural part is CategoricalBayesianNetworks' raw network,
  `OpenNet.RawCertificate.Network`, unchanged: dense variable indices, ranks, positioned state
  rows, generators with tagged references and positioned input rows, and attributed boundary
  rows. A generator is a **decision** exactly when its `kernelRef` is a `policy` reference
  (`isPolicy`); every other generator is a **chance** generator;
* a number cell is InfluenceDiagrams' certificate value
  (`InfluenceDiagramsProofs.DVECertificate.Value`): a binary64 word, optionally with an exact
  rational companion, read exactly by `Value.toRat`.

What the format adds is recorded here as plain data: one observability flag per boundary row,
one chance table per chance generator, the utilities (a name, positioned scope rows that have
the shape of input rows, and a table), one policy per distinct decision name, and the
recorded `K` and `W`. Every table is a flat list of cells in lexicographic order of its axes,
the last axis fastest (`Exact.lean` defines that index). Decoding is `Json.lean`, the checker
`Check.lean`, the exact reward kernel `Exact.lean` and the soundness theorems `Sound.lean`.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate

/-- A number cell, as in InfluenceDiagrams' DVE certificate. -/
abbrev Value := InfluenceDiagramsProofs.DVECertificate.Value

/-- The numeric mode: binary64 words only, or exact rational companions on every chance and
utility cell. -/
inductive NumericMode where
  | binary64Exact
  | rationalExact
  deriving DecidableEq, Repr

/-- The JSON spelling of a numeric mode. -/
def NumericMode.toString : NumericMode → String
  | .binary64Exact => "binary64_exact"
  | .rationalExact => "rational_exact"

/-- Provenance strings; the checker does not read them. -/
structure Metadata where
  producer : String
  producerVersion : String
  juliaVersion : String
  description : String
  deriving DecidableEq, Repr

/-- The table of one chance generator: its 0-based generator index and its cells (axes: the
parents in input-position order, then the child). -/
structure ChanceTable where
  mechanism : ℕ
  cells : List Value

/-- One utility: its name, its scope rows (`varId` and 1-based `position`, the shape of an
input row) and its cells (axes: the scope rows in position order). -/
structure Utility (n : ℕ) where
  name : String
  scopeRows : List (InputRow n)
  cells : List Value

/-- The policy of one decision name: the 1-based action state position at every cell of the
information axes of the first decision generator with that name. -/
structure Policy where
  decision : String
  actions : List ℕ
  deriving DecidableEq, Repr

/-- Julia's reward kernel at the boundary coordinates (axes: the input rows, then the output
rows). `W` is signed. The arithmetic is always `"binary64"`. -/
structure Result where
  K : List Value
  W : List Value

/-- A decoded `OpenInfluence.RewardCertificate/v1`. -/
structure Certificate where
  numericMode : NumericMode
  metadata : Metadata
  network : Network
  inputFlags : List Observability
  outputFlags : List Observability
  chanceTables : List ChanceTable
  utilities : List (Utility network.variableCount)
  strategy : List Policy
  result : Result

/-- The format string of version 1. -/
def formatName : String := "OpenInfluence.RewardCertificate/v1"

/-- A reference marks a decision exactly when it is a `policy` reference. -/
def isPolicy : Reference → Bool
  | .policy _ => true
  | _ => false

/-- The decision name of a `policy` reference. -/
def policyName? : Reference → Option String
  | .policy d => some d
  | _ => none

theorem isPolicy_iff (r : Reference) : isPolicy r = true ↔ ∃ d, r = .policy d := by
  cases r <;> simp [isPolicy]

/-- A utility label of the decoded diagram: the utility's name and the attributes of its
scope variables in position order (`Sound.lean` uses these as the signature's utility
labels). -/
structure ULabel where
  name : String
  inputs : List VariableAttrs
  deriving DecidableEq, Repr

end OpenInfluence.RewardCertificate
