import CategoricalInfluenceDiagramsProofs.Certificate.Check
import CategoricalInfluenceDiagramsProofs.Certificate.Json
import CategoricalInfluenceDiagramsProofs.Certificate.Cli

/-!
# `lake exe check_certificate PATH [--tol τ]`

Reads an `OpenInfluence.RewardCertificate/v1` file, decodes it with the decoder of
`Certificate/Json.lean` and decides `check τ c` of `Certificate/Check.lean`, whose acceptance
`Certificate/Sound.lean` proves sound. The tolerance `τ` is a decimal (`1e-12`, `0.001`),
parsed exactly to a rational; the default is `1e-12`.

It prints the counts, the largest deviation of a chance row sum from one, the largest
errors of the recorded `K` and `W` against the exact reward kernel (computed only when the
network is valid and every table has its cell count), and then `accepted`, or `rejected:`
with the first failing stage. Exit status: `0` accepted, `1` rejected (including a file that
does not parse or decode), `2` usage or file error. The printed decimals are display
approximations; the decision is made over `ℚ`.
-/

open OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Cli

def usage : String :=
  "usage: check_certificate PATH [--tol TOLERANCE]   (TOLERANCE a decimal such as 1e-12)"

/-- Check one decoded certificate and print the report. -/
def report (c : Certificate) (τ : ℚ) : IO UInt32 := do
  let m := c.network.mechanisms.length
  let decisions := ((List.finRange m).filter fun g => c.isDecisionGen g).length
  IO.println s!"{formatName}: numeric mode {c.numericMode.toString}"
  IO.println s!"  variables {c.network.variableCount}, generators {m} ({m - decisions} chance, \
    {decisions} decision), utilities {c.utilities.length}, policies {c.strategy.length}"
  IO.println s!"  input rows {c.network.inputs.length}, output rows {c.network.outputs.length}, \
    result cells K {c.result.K.length}, W {c.result.W.length}"
  IO.println s!"  tolerance {showQ τ}"
  IO.println s!"  largest row deviation |row sum - 1|: {showQ c.rowDeviation}"
  if c.network.check && decide c.CellCounts then
    IO.println s!"  largest K error: {showQ c.kErrorFast}"
    IO.println s!"  largest W error: {showQ c.wErrorFast}"
  else
    IO.println "  largest K and W errors: not computed (invalid network or cell counts)"
  if c.check τ then
    IO.println "accepted"
    return (0 : UInt32)
  else
    IO.println s!"rejected: {(c.firstFailure τ).getD "unknown stage"}"
    return (1 : UInt32)

def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match parseArgs args with
  | none =>
    stderr.putStrLn usage
    return (2 : UInt32)
  | some (path, τ) =>
    try
      let text ← IO.FS.readFile path
      match Json.read text with
      | .error message =>
        IO.println s!"rejected: decode ({message})"
        return (1 : UInt32)
      | .ok c => report c τ
    catch error =>
      stderr.putStrLn s!"cannot read certificate: {error}"
      return (2 : UInt32)
