import CategoricalInfluenceDiagramsProofs.Certificate.Exact

/-!
# Reward certificates: a faster exact check

`exactK x y` and `exactW x y` (`Exact.lean`) each sum over every generator coordinate `z`, so
checking all recorded cells costs `|X| · |Y| · |Z|` weight evaluations, for the input, output
and generator coordinates. But the output coordinate is a function of `(x, z)`: at most one
`y` is read. This module accumulates, for each input coordinate `x`, the whole row of `K` and
`W` in one pass over `z` (`accRow`), into an array indexed by the flat index of the output
coordinate (`outIndex`), so all cells cost `|X| · |Z|` evaluations.

* `readOut? x z` is the output coordinate read at `(x, z)`, or `none` when some output row's
  value is out of range; `Reads x z y` holds exactly when it is `some y` (`reads_iff`).
* `accRow_getD`: the cell of `accRow x` at `outIndex y` is `(exactK x y, exactW x y)`. The
  accumulation is a `Multiset.foldl` over the generator coordinates, whose step commutes, so
  no enumeration order is assumed.
* `kErrorFast`, `wErrorFast` take the largest error row by row, and are within `τ` exactly
  when `kError`, `wError` are (`kErrorFast_le_iff`, `wErrorFast_le_iff`). The checker uses
  them (`Check.lean`), so acceptance, and every soundness theorem, is unchanged; they are
  in fact equal to `kError`, `wError` (`kErrorFast_eq`, `wErrorFast_eq`), and the command line
  reports them.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-! ## Accumulating into an array -/

/-- Add `w` to cell `k` of `a`, if there is one. -/
def addAt (a : Array (ℚ × ℚ)) (k : Option ℕ) (w : ℚ × ℚ) : Array (ℚ × ℚ) :=
  match k with
  | some i => a.modify i (· + w)
  | none => a

theorem size_addAt (a : Array (ℚ × ℚ)) (k : Option ℕ) (w : ℚ × ℚ) :
    (addAt a k w).size = a.size := by
  cases k <;> simp [addAt]

theorem getD_addAt (a : Array (ℚ × ℚ)) (k : Option ℕ) (w : ℚ × ℚ) (j : ℕ) (hj : j < a.size) :
    (addAt a k w).getD j 0 = a.getD j 0 + if k = some j then w else 0 := by
  cases k with
  | none => simp [addAt]
  | some i =>
    simp only [addAt, Array.getD_eq_getD_getElem?, Array.getElem?_modify, Option.some.injEq]
    by_cases h : i = j
    · subst h
      simp [Array.getElem?_eq_getElem hj]
    · simp [h]

theorem addAt_comm (a : Array (ℚ × ℚ)) (k k' : Option ℕ) (w w' : ℚ × ℚ) :
    addAt (addAt a k w) k' w' = addAt (addAt a k' w') k w := by
  apply Array.ext
  · simp [size_addAt]
  · intro j h1 h2
    have hj : j < a.size := by simpa [size_addAt] using h1
    have e1 := getD_addAt (addAt a k w) k' w' j (by simpa [size_addAt] using hj)
    have e2 := getD_addAt (addAt a k' w') k w j (by simpa [size_addAt] using hj)
    rw [getD_addAt a k w j hj] at e1
    rw [getD_addAt a k' w' j hj] at e2
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.getD_some] at e1 e2
    rw [e1, e2]
    abel

/-- One accumulation step: add `w z` into cell `key z`. -/
def accStep {α : Type} (key : α → Option ℕ) (w : α → ℚ × ℚ) (b : Array (ℚ × ℚ)) (z : α) :
    Array (ℚ × ℚ) :=
  addAt b (key z) (w z)

instance {α : Type} (key : α → Option ℕ) (w : α → ℚ × ℚ) : RightCommutative (accStep key w) :=
  ⟨fun b z z' => addAt_comm b (key z) (key z') (w z) (w z')⟩

/-- Accumulate `w z` into cell `key z` over a multiset of `z`; the steps commute, so no order
of the multiset is assumed. -/
def accumulate {α : Type} (key : α → Option ℕ) (w : α → ℚ × ℚ) (a : Array (ℚ × ℚ))
    (s : Multiset α) : Array (ℚ × ℚ) :=
  s.foldl (accStep key w) a

theorem size_accumulate {α : Type} (key : α → Option ℕ) (w : α → ℚ × ℚ) (s : Multiset α) :
    ∀ a : Array (ℚ × ℚ), (accumulate key w a s).size = a.size := by
  induction s using Multiset.induction_on with
  | empty => intro a; simp [accumulate]
  | cons z s ih =>
    intro a
    simp only [accumulate, Multiset.foldl_cons] at ih ⊢
    rw [ih, accStep, size_addAt]

theorem getD_accumulate {α : Type} (key : α → Option ℕ) (w : α → ℚ × ℚ) (s : Multiset α)
    (j : ℕ) : ∀ a : Array (ℚ × ℚ), j < a.size →
    (accumulate key w a s).getD j 0 =
      a.getD j 0 + (s.map fun z => if key z = some j then w z else 0).sum := by
  induction s using Multiset.induction_on with
  | empty => intro a _; simp [accumulate]
  | cons z s ih =>
    intro a hj
    simp only [accumulate, Multiset.foldl_cons, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [ih _ (by rwa [accStep, size_addAt]), accStep, getD_addAt a (key z) (w z) j hj]
    abel

namespace Certificate

variable (c : Certificate)

/-! ## The output coordinate read at `(x, z)` -/

/-- The output coordinate read at `(x, z)`, if every output row's value is in range. -/
def readOut? (x : c.InCoord) (z : c.GenCoord) : Option c.OutCoord :=
  if h : ∀ j : Fin c.network.outputs.length,
      c.value x z (c.network.output j) < dimension c.network.outputs[j].attrs then
    some fun j => ⟨c.value x z (c.network.output j), h j⟩
  else none

theorem reads_iff (x : c.InCoord) (z : c.GenCoord) (y : c.OutCoord) :
    c.Reads x z y ↔ c.readOut? x z = some y := by
  unfold Reads readOut?
  constructor
  · intro h
    have hr : ∀ j : Fin c.network.outputs.length,
        c.value x z (c.network.output j) < dimension c.network.outputs[j].attrs :=
      fun j => h j ▸ (y j).isLt
    rw [dif_pos hr]
    exact congrArg some (funext fun j => Fin.ext (h j).symm)
  · intro h j
    by_cases hr : ∀ j : Fin c.network.outputs.length,
        c.value x z (c.network.output j) < dimension c.network.outputs[j].attrs
    · rw [dif_pos hr] at h
      rw [← Option.some.inj h]
    · rw [dif_neg hr] at h
      exact absurd h (by simp)

/-- The flat index of an output coordinate (last row fastest). -/
def outIndex (y : c.OutCoord) : ℕ :=
  flatIndex (List.ofFn fun j => (dimension c.network.outputs[j].attrs, (y j).val))

/-- The number of output coordinates. -/
def outCount : ℕ := (c.network.outputs.map fun r => dimension r.attrs).prod

theorem outAxes_fst (y : c.OutCoord) :
    (List.ofFn fun j => (dimension c.network.outputs[j].attrs, (y j).val)).map Prod.fst =
      c.network.outputs.map fun r => dimension r.attrs :=
  List.ext_get (by simp) (fun k h1 h2 => by simp)

theorem outIndex_lt (y : c.OutCoord) : c.outIndex y < c.outCount := by
  unfold outIndex outCount
  rw [← c.outAxes_fst y]
  refine flatIndex_lt _ fun p hp => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
  exact Fin.isLt _

theorem outIndex_injective {y y' : c.OutCoord} (h : c.outIndex y = c.outIndex y') : y = y' := by
  have he := flatIndex_injective _ _ ((c.outAxes_fst y).trans (c.outAxes_fst y').symm)
    (fun p hp => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp; exact Fin.isLt _)
    (fun p hp => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp; exact Fin.isLt _) h
  funext j
  have := congrArg (fun l => l[j.val]?) he
  exact Fin.ext (by simpa using this)

/-! ## A row of `K` and `W` in one pass -/

/-- The row of `(K, W)` at the input coordinate `x`, accumulated in one pass over the
generator coordinates. -/
def accRow (x : c.InCoord) : Array (ℚ × ℚ) :=
  accumulate (fun z => (c.readOut? x z).map c.outIndex)
    (fun z => (c.joint x z, c.joint x z * c.reward x z)) (Array.replicate c.outCount 0)
    (Finset.univ : Finset c.GenCoord).val

theorem key_eq_iff (x : c.InCoord) (z : c.GenCoord) (y : c.OutCoord) :
    (c.readOut? x z).map c.outIndex = some (c.outIndex y) ↔ c.Reads x z y := by
  rw [c.reads_iff]
  constructor
  · intro h
    obtain ⟨y', hy', he⟩ := Option.map_eq_some_iff.1 h
    rw [hy', c.outIndex_injective he]
  · intro h
    rw [h]
    rfl

/-- **One pass gives the row**: the cell of `accRow x` at `outIndex y` is
`(exactK x y, exactW x y)`. -/
theorem accRow_getD (x : c.InCoord) (y : c.OutCoord) :
    (c.accRow x).getD (c.outIndex y) 0 = (c.exactK x y, c.exactW x y) := by
  unfold accRow
  rw [getD_accumulate _ _ _ _ _ (by simpa using c.outIndex_lt y)]
  have h0 : (Array.replicate c.outCount (0 : ℚ × ℚ)).getD (c.outIndex y) 0 = 0 := by
    simp [Array.getD_eq_getD_getElem?, c.outIndex_lt y]
  rw [h0, zero_add]
  change (Multiset.map _ Finset.univ.val).sum = _
  rw [← Finset.sum_eq_multiset_sum]
  simp only [c.key_eq_iff]
  ext
  · simp only [Prod.fst_sum, apply_ite Prod.fst, Prod.fst_zero, exactK]
  · simp only [Prod.snd_sum, apply_ite Prod.snd, Prod.snd_zero, exactW]

/-! ## The errors, row by row -/

/-- The largest error of the recorded `K`, computed row by row. -/
def kErrorFast : ℚ :=
  (Finset.univ : Finset c.InCoord).fold max 0 fun x =>
    let row := c.accRow x
    (Finset.univ : Finset c.OutCoord).fold max 0 fun y =>
      |cellQ c.result.K (c.resultIndex x y) - (row.getD (c.outIndex y) 0).1|

/-- The largest error of the recorded `W`, computed row by row. -/
def wErrorFast : ℚ :=
  (Finset.univ : Finset c.InCoord).fold max 0 fun x =>
    let row := c.accRow x
    (Finset.univ : Finset c.OutCoord).fold max 0 fun y =>
      |cellQ c.result.W (c.resultIndex x y) - (row.getD (c.outIndex y) 0).2|

theorem kErrorFast_le_iff (τ : ℚ) : c.kErrorFast ≤ τ ↔ c.kError ≤ τ := by
  unfold kErrorFast kError
  simp only [Finset.fold_max_le, Finset.mem_univ, true_implies, c.accRow_getD, Prod.forall]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun x y => (h x).2 y⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun x => ⟨h0, fun y => h x y⟩⟩

theorem wErrorFast_le_iff (τ : ℚ) : c.wErrorFast ≤ τ ↔ c.wError ≤ τ := by
  unfold wErrorFast wError
  simp only [Finset.fold_max_le, Finset.mem_univ, true_implies, c.accRow_getD, Prod.forall]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun x y => (h x).2 y⟩
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun x => ⟨h0, fun y => h x y⟩⟩

/-- The fast error of `K` is the error of `K`. -/
theorem kErrorFast_eq : c.kErrorFast = c.kError :=
  le_antisymm ((c.kErrorFast_le_iff _).2 le_rfl) ((c.kErrorFast_le_iff _).1 le_rfl)

/-- The fast error of `W` is the error of `W`. -/
theorem wErrorFast_eq : c.wErrorFast = c.wError :=
  le_antisymm ((c.wErrorFast_le_iff _).2 le_rfl) ((c.wErrorFast_le_iff _).1 le_rfl)

end Certificate

end OpenInfluence.RewardCertificate
