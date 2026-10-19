import CategoricalInfluenceDiagramsProofs.Certificate.Check
import CategoricalInfluenceDiagramsProofs.Certificate.Json

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

open OpenInfluence.RewardCertificate

/-- The digits of a string as a natural number, if it is a nonempty run of decimal digits. -/
def digitsNat? (s : List Char) : Option ℕ :=
  if s.isEmpty || !s.all Char.isDigit then none
  else some (s.foldl (fun acc ch => 10 * acc + (ch.toNat - '0'.toNat)) 0)

/-- An optionally signed exponent. -/
def exponent? : List Char → Option ℤ
  | '-' :: rest => (digitsNat? rest).map fun n => -(n : ℤ)
  | '+' :: rest => (digitsNat? rest).map fun n => (n : ℤ)
  | rest => (digitsNat? rest).map fun n => (n : ℤ)

/-- A nonnegative decimal `digits[.digits][(e|E)[sign]digits]`, exactly. -/
def parseDecimal? (s : String) : Option ℚ := do
  let cs := s.toList
  let (mant, ex) := cs.span fun ch => ch != 'e' && ch != 'E'
  let e ← match ex with
    | [] => some (0 : ℤ)
    | _ :: rest => exponent? rest
  let (whole, frac) := mant.span fun ch => ch != '.'
  let fracDigits := frac.drop 1
  if whole.isEmpty && fracDigits.isEmpty then none else
  let w ← if whole.isEmpty then some 0 else digitsNat? whole
  let f ← if fracDigits.isEmpty then some 0 else digitsNat? fracDigits
  if !frac.isEmpty && fracDigits.isEmpty && whole.isEmpty then none else
  let m : ℚ := (w : ℚ) + (f : ℚ) / (10 : ℚ) ^ fracDigits.length
  return m * (10 : ℚ) ^ e

/-- The largest `e` with `10 ^ e ≤ q`, for `q > 0`. -/
def decimalExponent (q : ℚ) : ℤ := Id.run do
  let mut e : ℤ := if 1 ≤ q then (Nat.log 10 q.floor.toNat : ℤ)
    else -((Nat.log 10 (1 / q).ceil.toNat : ℤ))
  for _ in [0:4] do
    if q < (10 : ℚ) ^ e then e := e - 1
    else if (10 : ℚ) ^ (e + 1) ≤ q then e := e + 1
  return e

/-- A display approximation of a rational with six significant digits. -/
def showQ (q : ℚ) : String :=
  if q = 0 then "0" else
  let sign := if q < 0 then "-" else ""
  let a := |q|
  let e := decimalExponent a
  let m := ((a / (10 : ℚ) ^ e) * 100000 + 1 / 2).floor.toNat
  let (m, e) := if m ≥ 1000000 then (m / 10, e + 1) else (m, e)
  let ds := toString m
  let es := if e < 0 then s!"-{(-e).toNat}" else s!"+{e.toNat}"
  s!"{sign}{ds.take 1}.{ds.drop 1}e{es}"

def defaultTolerance : ℚ := 1 / 10 ^ 12

def usage : String :=
  "usage: check_certificate PATH [--tol TOLERANCE]   (TOLERANCE a decimal such as 1e-12)"

/-- The path and tolerance of the command line. -/
def parseArgs : List String → Option (String × ℚ)
  | [path] => some (path, defaultTolerance)
  | [path, "--tol", t] => (parseDecimal? t).map fun τ => (path, τ)
  | ["--tol", t, path] => (parseDecimal? t).map fun τ => (path, τ)
  | _ => none

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
