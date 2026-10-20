import CategoricalInfluenceDiagramsProofs.Certificate.Check
import CategoricalInfluenceDiagramsProofs.Certificate.Json

/-!
# Composition certificates: the Julia composite against the Lean composite (ADR 0023)

A reward certificate (ADR 0019) checks Julia's numbers for one recorded diagram against the
exact semantics of that diagram. It says nothing about how the diagram was built: that the
diagram Julia composed from two parts behaves as the composite, in the category of reward
kernels, of those parts. A **composition certificate** records three reward certificates, the
`left` part, the `right` part and their `composite`, and the checker (`Composition.check`)
accepts when

1. each of the three is accepted at tolerance `τ` (`Certificate.check`);
2. the interfaces line up (`Aligned`): the left part's output rows have the attributes of the
   right part's input rows, the composite's input rows those of the left part's, and its
   output rows those of the right part's, in order;
3. every recorded cell of the composite is within `τ` of the composite of the parts' recorded
   cells: `K_C(x, z)` of `Σ_y K_L(x, y) K_R(y, z)`, and `W_C(x, z)` of
   `Σ_y (W_L(x, y) K_R(y, z) + K_L(x, y) W_R(y, z))` (`compKError`, `compWError`), with the
   coordinates carried across by the alignment (`recoord`).

**Soundness** (`composition_sound_K`, `composition_sound_W`). On acceptance, for all input
coordinates `x` of the left part and output coordinates `z` of the right part, the decoded
composite's exact probability `exactK` at `(x, z)` is within
`2τ + τ Σ_y (|K̂_L(x, y)| + |K̂_R(y, z)| + τ)` of `Σ_y exactK_L(x, y) exactK_R(y, z)`, and its
exact reward `exactW` within the corresponding bound of the expectation-semiring composite,
the hats being the recorded cells. By `interpret_K_eq` and `interpret_W_eq` (`Sound.lean`),
each certificate's `exactK` and `exactW` are `interpret σ f` of its decoded diagram and
strategy, so the decoded composite behaves, cell by cell and up to that bound, as the
composite of the decoded parts in the category of reward kernels.

**Not proved:** that the composite's syntax is `IDNet.comp` of the parts' (an isomorphism of
nets): the certificate ties the semantics, not the structure.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-- A decoded `OpenInfluence.CompositionCertificate/v1`: the two parts and their composite. -/
structure Composition where
  left : Certificate
  right : Certificate
  composite : Certificate

/-- The format string of version 1. -/
def compositionFormatName : String := "OpenInfluence.CompositionCertificate/v1"

/-! ## Carrying coordinates across aligned rows -/

/-- The attributes of a list of boundary rows. -/
def rowAttrs {n : ℕ} (rows : List (BoundaryRow n)) : List VariableAttrs := rows.map (·.attrs)

theorem length_of_rowAttrs {n m : ℕ} {A : List (BoundaryRow n)} {B : List (BoundaryRow m)}
    (h : rowAttrs A = rowAttrs B) : A.length = B.length := by
  have := congrArg List.length h
  simpa [rowAttrs] using this

theorem attrs_of_rowAttrs {n m : ℕ} {A : List (BoundaryRow n)} {B : List (BoundaryRow m)}
    (h : rowAttrs A = rowAttrs B) (j : ℕ) (hA : j < A.length) (hB : j < B.length) :
    A[j].attrs = B[j].attrs := by
  have := congrArg (fun l => l[j]?) h
  simp only [rowAttrs, List.getElem?_map, List.getElem?_eq_getElem hA,
    List.getElem?_eq_getElem hB, Option.map_some, Option.some.injEq] at this
  exact this

/-- Coordinates of rows `A` read as coordinates of rows `B` with the same attributes. -/
def recoord {n m : ℕ} (A : List (BoundaryRow n)) (B : List (BoundaryRow m))
    (h : rowAttrs A = rowAttrs B)
    (y : ∀ j : Fin A.length, Fin (dimension A[j].attrs)) :
    ∀ j : Fin B.length, Fin (dimension B[j].attrs) := fun j =>
  have hj : j.val < A.length := (length_of_rowAttrs h).symm ▸ j.isLt
  Fin.cast (congrArg dimension (attrs_of_rowAttrs h j.val hj j.isLt)) (y ⟨j.val, hj⟩)

namespace Composition

variable (cc : Composition)

/-- The interfaces line up: the left part's outputs are the right part's inputs, the
composite's inputs the left part's and its outputs the right part's (by attributes, in
order). -/
def Aligned : Prop :=
  rowAttrs cc.left.network.outputs = rowAttrs cc.right.network.inputs ∧
    rowAttrs cc.left.network.inputs = rowAttrs cc.composite.network.inputs ∧
    rowAttrs cc.right.network.outputs = rowAttrs cc.composite.network.outputs

instance : Decidable cc.Aligned := by unfold Aligned; infer_instance

variable {cc}

/-- A left input coordinate as a composite input coordinate. -/
def inC (h : cc.Aligned) (x : cc.left.InCoord) : cc.composite.InCoord :=
  recoord _ _ h.2.1 x

/-- A right output coordinate as a composite output coordinate. -/
def outC (h : cc.Aligned) (z : cc.right.OutCoord) : cc.composite.OutCoord :=
  recoord _ _ h.2.2 z

/-- A left output coordinate as a right input coordinate. -/
def mid (h : cc.Aligned) (y : cc.left.OutCoord) : cc.right.InCoord :=
  recoord _ _ h.1 y

/-- The recorded probability cell of a certificate. -/
def kHat (c : Certificate) (x : c.InCoord) (y : c.OutCoord) : ℚ :=
  cellQ c.result.K (c.resultIndex x y)

/-- The recorded reward cell of a certificate. -/
def wHat (c : Certificate) (x : c.InCoord) (y : c.OutCoord) : ℚ :=
  cellQ c.result.W (c.resultIndex x y)

/-- The largest gap between the composite's recorded `K` and the composite of the parts'. -/
def compKError (h : cc.Aligned) : ℚ :=
  (Finset.univ : Finset (cc.left.InCoord × cc.right.OutCoord)).fold max 0 fun p =>
    |kHat cc.composite (inC h p.1) (outC h p.2) -
      ∑ y, kHat cc.left p.1 y * kHat cc.right (mid h y) p.2|

/-- The largest gap between the composite's recorded `W` and the composite of the parts'. -/
def compWError (h : cc.Aligned) : ℚ :=
  (Finset.univ : Finset (cc.left.InCoord × cc.right.OutCoord)).fold max 0 fun p =>
    |wHat cc.composite (inC h p.1) (outC h p.2) -
      ∑ y, (wHat cc.left p.1 y * kHat cc.right (mid h y) p.2 +
        kHat cc.left p.1 y * wHat cc.right (mid h y) p.2)|

variable (cc)

/-- **The composition checker.** -/
def check (τ : ℚ) : Bool :=
  cc.left.check τ && cc.right.check τ && cc.composite.check τ &&
    if h : cc.Aligned then decide (compKError h ≤ τ) && decide (compWError h ≤ τ) else false

/-- The name of the first failing stage, if any. -/
def firstFailure (τ : ℚ) : Option String :=
  if !cc.left.check τ then some s!"left: {(cc.left.firstFailure τ).getD "unknown stage"}"
  else if !cc.right.check τ then some s!"right: {(cc.right.firstFailure τ).getD "unknown stage"}"
  else if !cc.composite.check τ then
    some s!"composite: {(cc.composite.firstFailure τ).getD "unknown stage"}"
  else if h : cc.Aligned then
    if !decide (compKError h ≤ τ) then
      some "composition K (a composite cell is not within the tolerance of the parts' composite)"
    else if !decide (compWError h ≤ τ) then
      some "composition W (a composite cell is not within the tolerance of the parts' composite)"
    else none
  else some "alignment (the interfaces of the parts and the composite do not line up)"

variable {cc}

/-! ## Soundness -/

/-- The error of a product of approximations. -/
theorem abs_mul_sub_le {b B c C τ : ℚ} (hb : |b - B| ≤ τ) (hc : |c - C| ≤ τ) :
    |b * c - B * C| ≤ τ * (|b| + |c| + τ) := by
  have hτ : 0 ≤ τ := (abs_nonneg _).trans hb
  have hC : |C| ≤ |c| + τ := by
    have := abs_sub_abs_le_abs_sub C c
    rw [abs_sub_comm] at hc
    linarith
  have e : b * c - B * C = b * (c - C) + (b - B) * C := by ring
  rw [e]
  calc |b * (c - C) + (b - B) * C| ≤ |b * (c - C)| + |(b - B) * C| := abs_add_le _ _
    _ = |b| * |c - C| + |b - B| * |C| := by rw [abs_mul, abs_mul]
    _ ≤ |b| * τ + τ * (|c| + τ) := by
        gcongr
    _ = τ * (|b| + |c| + τ) := by ring

theorem abs_sub_le_three {A a S T τ₁ τ₂ τ₃ : ℚ} (h₁ : |A - a| ≤ τ₁) (h₂ : |a - S| ≤ τ₂)
    (h₃ : |S - T| ≤ τ₃) : |A - T| ≤ τ₁ + τ₂ + τ₃ := by
  have e : A - T = (A - a) + (a - S) + (S - T) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)

theorem le_of_fold {α : Type} [Fintype α] {f : α → ℚ} {τ : ℚ}
    (h : (Finset.univ : Finset α).fold max 0 f ≤ τ) (a : α) : f a ≤ τ :=
  ((Finset.fold_max_le _).1 h).2 a (Finset.mem_univ _)

theorem accepted_of_check {τ : ℚ} (hc : cc.check τ = true) :
    cc.left.Accepted τ ∧ cc.right.Accepted τ ∧ cc.composite.Accepted τ ∧
      ∃ h : cc.Aligned, compKError h ≤ τ ∧ compWError h ≤ τ := by
  unfold check at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hl, hr⟩, hco⟩, ha⟩ := hc
  refine ⟨(Certificate.check_iff_accepted _ _).1 hl, (Certificate.check_iff_accepted _ _).1 hr,
    (Certificate.check_iff_accepted _ _).1 hco, ?_⟩
  by_cases h : cc.Aligned
  · rw [dif_pos h] at ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    exact ⟨h, ha⟩
  · rw [dif_neg h] at ha
    exact absurd ha (by simp)

/-- **Soundness for `K`**: on acceptance, the decoded composite's exact probability at
`(x, z)` is within `2τ + τ Σ_y (|K̂_L(x, y)| + |K̂_R(y, z)| + τ)` of the composite of the
decoded parts' exact probabilities. -/
theorem composition_sound_K {τ : ℚ} (hc : cc.check τ = true) :
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactK (inC h x) (outC h z) -
          ∑ y, cc.left.exactK x y * cc.right.exactK (mid h y) z| ≤
        2 * τ + τ * ∑ y, (|kHat cc.left x y| + |kHat cc.right (mid h y) z| + τ) := by
  obtain ⟨hl, hr, hco, h, hk, -⟩ := accepted_of_check hc
  refine ⟨h, fun x z => ?_⟩
  have hCA : |cc.composite.exactK (inC h x) (outC h z) - kHat cc.composite (inC h x) (outC h z)|
      ≤ τ := by
    rw [abs_sub_comm]
    exact Certificate.kError_le _ hco.kError (inC h x) (outC h z)
  have hcomp : |kHat cc.composite (inC h x) (outC h z) -
      ∑ y, kHat cc.left x y * kHat cc.right (mid h y) z| ≤ τ := le_of_fold hk (x, z)
  have hsum : |∑ y, kHat cc.left x y * kHat cc.right (mid h y) z -
      ∑ y, cc.left.exactK x y * cc.right.exactK (mid h y) z| ≤
      τ * ∑ y, (|kHat cc.left x y| + |kHat cc.right (mid h y) z| + τ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ =>
      abs_mul_sub_le (Certificate.kError_le _ hl.kError x y)
        (Certificate.kError_le _ hr.kError (mid h y) z))
  exact (abs_sub_le_three hCA hcomp hsum).trans (le_of_eq (by ring))

/-- **Soundness for `W`**: on acceptance, the decoded composite's exact reward at `(x, z)` is
within `2τ + τ Σ_y (|Ŵ_L| + |K̂_R| + |K̂_L| + |Ŵ_R| + 2τ)` of the expectation-semiring
composite of the decoded parts' exact tables. -/
theorem composition_sound_W {τ : ℚ} (hc : cc.check τ = true) :
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactW (inC h x) (outC h z) -
          ∑ y, (cc.left.exactW x y * cc.right.exactK (mid h y) z +
            cc.left.exactK x y * cc.right.exactW (mid h y) z)| ≤
        2 * τ + τ * ∑ y, (|wHat cc.left x y| + |kHat cc.right (mid h y) z| +
          |kHat cc.left x y| + |wHat cc.right (mid h y) z| + 2 * τ) := by
  obtain ⟨hl, hr, hco, h, -, hw⟩ := accepted_of_check hc
  refine ⟨h, fun x z => ?_⟩
  have hCA : |cc.composite.exactW (inC h x) (outC h z) - wHat cc.composite (inC h x) (outC h z)|
      ≤ τ := by
    rw [abs_sub_comm]
    exact Certificate.wError_le _ hco.wError (inC h x) (outC h z)
  have hcomp : |wHat cc.composite (inC h x) (outC h z) -
      ∑ y, (wHat cc.left x y * kHat cc.right (mid h y) z +
        kHat cc.left x y * wHat cc.right (mid h y) z)| ≤ τ := le_of_fold hw (x, z)
  have hterm : ∀ y, |(wHat cc.left x y * kHat cc.right (mid h y) z +
        kHat cc.left x y * wHat cc.right (mid h y) z) -
      (cc.left.exactW x y * cc.right.exactK (mid h y) z +
        cc.left.exactK x y * cc.right.exactW (mid h y) z)| ≤
      τ * (|wHat cc.left x y| + |kHat cc.right (mid h y) z| +
        |kHat cc.left x y| + |wHat cc.right (mid h y) z| + 2 * τ) := by
    intro y
    have h1 := abs_mul_sub_le (Certificate.wError_le _ hl.wError x y)
      (Certificate.kError_le _ hr.kError (mid h y) z)
    have h2 := abs_mul_sub_le (Certificate.kError_le _ hl.kError x y)
      (Certificate.wError_le _ hr.wError (mid h y) z)
    have e : (wHat cc.left x y * kHat cc.right (mid h y) z +
          kHat cc.left x y * wHat cc.right (mid h y) z) -
        (cc.left.exactW x y * cc.right.exactK (mid h y) z +
          cc.left.exactK x y * cc.right.exactW (mid h y) z) =
        (wHat cc.left x y * kHat cc.right (mid h y) z -
          cc.left.exactW x y * cc.right.exactK (mid h y) z) +
        (kHat cc.left x y * wHat cc.right (mid h y) z -
          cc.left.exactK x y * cc.right.exactW (mid h y) z) := by ring
    rw [e]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq (by simp only [kHat, wHat]; ring)))
  have hsum : |∑ y, (wHat cc.left x y * kHat cc.right (mid h y) z +
        kHat cc.left x y * wHat cc.right (mid h y) z) -
      ∑ y, (cc.left.exactW x y * cc.right.exactK (mid h y) z +
        cc.left.exactK x y * cc.right.exactW (mid h y) z)| ≤
      τ * ∑ y, (|wHat cc.left x y| + |kHat cc.right (mid h y) z| +
        |kHat cc.left x y| + |wHat cc.right (mid h y) z| + 2 * τ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hterm y)
  exact (abs_sub_le_three hCA hcomp hsum).trans (le_of_eq (by ring))

end Composition

/-! ## Decoding -/

namespace Json

open Lean (Json)
open BayesianNetworksProofs.Raw (object)
open InfluenceDiagramsProofs.DVECertificate (get)

/-- Decode a composition certificate: exactly the keys `format`, `left`, `right` and
`composite`, the last three reward certificates. -/
def decodeComposition (j : Json) : Except String Composition := do
  let o ← object "composition" 4 j
  get o "format" (constant compositionFormatName)
  let l ← get o "left" decodeCertificate
  let r ← get o "right" decodeCertificate
  let c ← get o "composite" decodeCertificate
  pure ⟨l, r, c⟩

/-- Read a composition certificate from its text. -/
def readComposition (text : String) : Except String Composition := do
  let j ← OpenNet.CertificateSyntax.parse text
  decodeComposition j

end Json

end OpenInfluence.RewardCertificate
