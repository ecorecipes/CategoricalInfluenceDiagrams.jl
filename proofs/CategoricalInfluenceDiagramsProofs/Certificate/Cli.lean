import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-!
# Command-line helpers for the certificate checkers

Exact parsing of a decimal tolerance, a six-digit display of rationals and the argument
parser shared by `check_certificate` and `check_composition`. Nothing here is part of any
decision: the checkers decide over `ℚ`.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate.Cli

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

/-- The path and tolerance of the command line. -/
def parseArgs : List String → Option (String × ℚ)
  | [path] => some (path, defaultTolerance)
  | [path, "--tol", t] => (parseDecimal? t).map fun τ => (path, τ)
  | ["--tol", t, path] => (parseDecimal? t).map fun τ => (path, τ)
  | _ => none

end OpenInfluence.RewardCertificate.Cli
