import CategoricalInfluenceDiagramsProofs.Certificate.Record

/-!
# Reward certificates: the exact reward kernel of the certificate's numbers

This module computes, over `ℚ` and by explicit enumeration, the reward kernel `(K, W)` that
the certificate's own numbers determine for its own strategy. Nothing here assumes that the
certificate has been checked; `Check.lean` compares the recorded result with these values
and `Sound.lean` proves that, on an accepted certificate, they are the values of
`interpret σ f` from `Interpretation.lean`.

**Cell layout.** A table with axes of lengths `d₁, …, dₖ` is a flat list of cells in
lexicographic order, the last axis fastest. `flatIndex` takes the list of pairs
`(dᵢ, aᵢ)` of axis lengths and 0-based coordinates and returns `a₁ (d₂ ⋯ dₖ) + ⋯ + aₖ`;
`flatIndex_lt` bounds it by the product of the lengths, `flatIndex_append` splits off the
last axis (so a chance table is a list of rows, one per parent coordinate) and
`flatIndex_injective` shows that distinct in-range coordinates have distinct cells. A
missing cell reads as `0` (`cellQ`); the checker requires every table to have exactly the
product of its axis lengths as its cell count. The axis length of a variable is
CategoricalBayesianNetworks' `dimension` of its attributes, which is its state count on a
checked network (`dimension_checked`).

**The enumeration.** Fix 0-based states `x` of the input rows and `z` of the generators (all
generators, chance and decision). The value of a variable (`value`) is `z g` if `g` is its
generator, otherwise `x i` if it is the variable of input row `i`. Then:

* a decision generator weighs `1` if its state is the action its policy (looked up by its
  decision name in the strategy) picks at the values of its information inputs, and `0`
  otherwise (`actionOf`; an action out of range reads as the first state, which the checker
  excludes);
* a chance generator weighs its own table's cell at its parents' values and its own state
  (`tableOf`, `chanceAt`);
* the reward is the sum over the utilities of each utility's cell at its scope's values;
* `exactK x y` sums the product of the weights over all `z` whose output rows read `y`, and
  `exactW x y` sums that product times the reward.

The result coordinate of `(x, y)` is `resultIndex x y`, the flat index of the input rows'
coordinates followed by the output rows'. The largest result errors (`kError`, `wError`) and
the largest deviation of a chance row sum from one (`rowDeviation`) are computed here too.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-! ## Flat indices -/

/-- The lexicographic (last axis fastest) index of the coordinates `aᵢ` on axes of lengths
`dᵢ`, given as the pairs `(dᵢ, aᵢ)`. -/
def flatIndex : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, a) :: rest => a * (rest.map Prod.fst).prod + flatIndex rest

theorem flatIndex_lt : ∀ l : List (ℕ × ℕ), (∀ p ∈ l, p.2 < p.1) →
    flatIndex l < (l.map Prod.fst).prod
  | [], _ => by simp [flatIndex]
  | (d, a) :: rest, h => by
    have ha : a < d := h (d, a) List.mem_cons_self
    have hr := flatIndex_lt rest (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [flatIndex, List.map_cons, List.prod_cons]
    calc a * (rest.map Prod.fst).prod + flatIndex rest
        < a * (rest.map Prod.fst).prod + (rest.map Prod.fst).prod := by omega
      _ = (a + 1) * (rest.map Prod.fst).prod := by ring
      _ ≤ d * (rest.map Prod.fst).prod := Nat.mul_le_mul_right _ ha

theorem flatIndex_append (l : List (ℕ × ℕ)) (d s : ℕ) :
    flatIndex (l ++ [(d, s)]) = flatIndex l * d + s := by
  induction l with
  | nil => simp [flatIndex]
  | cons p rest ih =>
    obtain ⟨d', a⟩ := p
    simp only [List.cons_append, flatIndex, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih]
    ring

theorem flatIndex_injective : ∀ l l' : List (ℕ × ℕ), l.map Prod.fst = l'.map Prod.fst →
    (∀ p ∈ l, p.2 < p.1) → (∀ p ∈ l', p.2 < p.1) → flatIndex l = flatIndex l' → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | (d, a) :: rest, (d', a') :: rest', hd, h, h', he => by
    simp only [List.map_cons, List.cons.injEq] at hd
    obtain ⟨rfl, hd⟩ := hd
    have hr := flatIndex_lt rest (fun p hp => h p (List.mem_cons_of_mem _ hp))
    have hr' := flatIndex_lt rest' (fun p hp => h' p (List.mem_cons_of_mem _ hp))
    rw [hd] at hr
    simp only [flatIndex, hd] at he
    set P := (rest'.map Prod.fst).prod
    have hP : 0 < P := by omega
    have hq : a = a' := by
      have e1 : (a * P + flatIndex rest) / P = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, zero_add]
      have e2 : (a' * P + flatIndex rest') / P = a' := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr', zero_add]
      rw [← e1, ← e2, he]
    subst hq
    have hrest : flatIndex rest = flatIndex rest' := by omega
    rw [flatIndex_injective rest rest' hd (fun p hp => h p (List.mem_cons_of_mem _ hp))
      (fun p hp => h' p (List.mem_cons_of_mem _ hp)) hrest]

/-- The exact value of cell `k`, or `0` when there is none. -/
def cellQ (cells : List Value) (k : ℕ) : ℚ := ((cells[k]?).map Value.toRat).getD 0

theorem cellQ_nonneg {cells : List Value} (h : ∀ v ∈ cells, 0 ≤ v.toRat) (k : ℕ) :
    0 ≤ cellQ cells k := by
  unfold cellQ
  cases hk : cells[k]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hk)

/-! ## Labels, tables and policies -/

/-- The axes of a table on the inputs of a label: their lengths paired with the values. -/
def inputAxes (l : LabelAttrs) (vals : List ℕ) : List (ℕ × ℕ) :=
  (l.inputs.map dimension).zip vals

/-- The number of parent rows of a chance table on `l`. -/
def rowCount (l : LabelAttrs) : ℕ := (l.inputs.map dimension).prod

/-- The cell of a chance table on `l` at the parent values `vals` and child state `s`. -/
def chanceAt (cells : List Value) (l : LabelAttrs) (vals : List ℕ) (s : ℕ) : ℚ :=
  cellQ cells (flatIndex (inputAxes l vals ++ [(dimension l.result, s)]))

theorem chanceAt_row (cells : List Value) (l : LabelAttrs) (vals : List ℕ) (s : ℕ) :
    chanceAt cells l vals s =
      cellQ cells (flatIndex (inputAxes l vals) * dimension l.result + s) := by
  unfold chanceAt
  rw [flatIndex_append]

/-- The cell of a utility table on `l` at the scope values `vals`. -/
def utilityAt (cells : List Value) (l : ULabel) (vals : List ℕ) : ℚ :=
  cellQ cells (flatIndex ((l.inputs.map dimension).zip vals))

namespace Certificate

variable (c : Certificate)

/-- A generator index. -/
abbrev Gen := Fin c.network.mechanisms.length

/-- A utility index. -/
abbrev UIdx := Fin c.utilities.length

/-- Whether generator `g` is a decision: its reference is a `policy` reference. -/
def isDecisionGen (g : c.Gen) : Bool := isPolicy (c.network.mechanism g).kernelRef

/-- The table of a generator: the cells of the first chance-table record that names it. -/
def tableOf (g : c.Gen) : List Value :=
  ((c.chanceTables.find? fun t => decide (t.mechanism = g.val)).map ChanceTable.cells).getD []

/-- The policy record of a decision name. -/
def policyOf (name : String) : Option Policy :=
  c.strategy.find? fun p => decide (p.decision = name)

/-- The raw (1-based) action that the policy of `l`'s decision name records at the
information values `vals`, or `0` when there is none. -/
def rawAction (l : LabelAttrs) (vals : List ℕ) : ℕ :=
  match policyName? l.kernelRef with
  | some name =>
    match c.policyOf name with
    | some p => p.actions.getD (flatIndex (inputAxes l vals)) 0
    | none => 0
  | none => 0

/-- The 0-based action state of a decision with label `l` at the information values `vals`;
an out-of-range action reads as `0` (the checker excludes it). -/
def actionOf (l : LabelAttrs) (vals : List ℕ) : ℕ :=
  if 1 ≤ c.rawAction l vals ∧ c.rawAction l vals ≤ dimension l.result then
    c.rawAction l vals - 1
  else 0

theorem actionOf_lt (l : LabelAttrs) (vals : List ℕ) : c.actionOf l vals < dimension l.result := by
  unfold actionOf
  have hpos : 0 < dimension l.result := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  split_ifs with h
  · omega
  · exact hpos

/-- The scope rows of utility `u`, in position order. -/
def scopeRows (u : c.UIdx) : List (InputRow c.network.variableCount) :=
  orderRows InputRow.position c.utilities[u].scopeRows

/-- The scope variables of utility `u`, in position order. -/
def scope (u : c.UIdx) : List (Fin c.network.variableCount) :=
  (c.scopeRows u).map InputRow.varId

/-- The label of utility `u`: its name and its scope's attributes. -/
def utilityLabel (u : c.UIdx) : ULabel :=
  ⟨c.utilities[u].name, (c.scope u).map c.network.attrs⟩

/-! ## Coordinates -/

/-- 0-based states of the input rows. -/
abbrev InCoord := ∀ i : Fin c.network.inputs.length, Fin (dimension c.network.inputs[i].attrs)

/-- 0-based states of the output rows. -/
abbrev OutCoord :=
  ∀ j : Fin c.network.outputs.length, Fin (dimension c.network.outputs[j].attrs)

/-- 0-based states of the generators (the generated variables). -/
abbrev GenCoord := ∀ g : c.Gen, Fin (dimension (c.network.label g).result)

/-- The generator of a variable, if any. -/
def genOf (v : Fin c.network.variableCount) : Option c.Gen :=
  (List.finRange _).find? fun g => decide (c.network.target g = v)

/-- The input row of a variable, if any. -/
def inputOf (v : Fin c.network.variableCount) : Option (Fin c.network.inputs.length) :=
  (List.finRange _).find? fun i => decide (c.network.input i = v)

/-- The 0-based state of variable `v`: its generator's state, else its input row's. -/
def value (x : c.InCoord) (z : c.GenCoord) (v : Fin c.network.variableCount) : ℕ :=
  match c.genOf v with
  | some g => (z g).val
  | none =>
    match c.inputOf v with
    | some i => (x i).val
    | none => 0

/-! ## The enumeration -/

/-- The weight of generator `g` at `(x, z)`. -/
def genWeight (x : c.InCoord) (z : c.GenCoord) (g : c.Gen) : ℚ :=
  if c.isDecisionGen g then
    (if (z g).val = c.actionOf (c.network.label g) ((c.network.parents g).map (c.value x z))
      then 1 else 0)
  else chanceAt (c.tableOf g) (c.network.label g) ((c.network.parents g).map (c.value x z))
    (z g).val

/-- The product of the generator weights. -/
def joint (x : c.InCoord) (z : c.GenCoord) : ℚ := ∏ g, c.genWeight x z g

/-- The total utility at `(x, z)`. -/
def reward (x : c.InCoord) (z : c.GenCoord) : ℚ :=
  ∑ u : c.UIdx, utilityAt c.utilities[u].cells (c.utilityLabel u) ((c.scope u).map (c.value x z))

/-- The output rows read `y` at `(x, z)`. -/
def Reads (x : c.InCoord) (z : c.GenCoord) (y : c.OutCoord) : Prop :=
  ∀ j, (y j).val = c.value x z (c.network.output j)

instance (x : c.InCoord) (z : c.GenCoord) (y : c.OutCoord) : Decidable (c.Reads x z y) := by
  unfold Reads
  infer_instance

/-- The exact probability component at `(x, y)`. -/
def exactK (x : c.InCoord) (y : c.OutCoord) : ℚ :=
  ∑ z : c.GenCoord, if c.Reads x z y then c.joint x z else 0

/-- The exact reward component at `(x, y)`. -/
def exactW (x : c.InCoord) (y : c.OutCoord) : ℚ :=
  ∑ z : c.GenCoord, if c.Reads x z y then c.joint x z * c.reward x z else 0

/-! ## Result coordinates -/

/-- The axis lengths of the input rows, then of the output rows. -/
def resultDims : List ℕ :=
  c.network.inputs.map (fun r => dimension r.attrs) ++
    c.network.outputs.map (fun r => dimension r.attrs)

/-- The result axes at `(x, y)`: the input rows' lengths and states, then the output rows'. -/
def resultAxes (x : c.InCoord) (y : c.OutCoord) : List (ℕ × ℕ) :=
  List.ofFn (fun i => (dimension c.network.inputs[i].attrs, (x i).val)) ++
    List.ofFn (fun j => (dimension c.network.outputs[j].attrs, (y j).val))

/-- The cell of `(x, y)` in the recorded `K` and `W`. -/
def resultIndex (x : c.InCoord) (y : c.OutCoord) : ℕ := flatIndex (c.resultAxes x y)

theorem resultAxes_fst (x : c.InCoord) (y : c.OutCoord) :
    (c.resultAxes x y).map Prod.fst = c.resultDims := by
  unfold resultAxes resultDims
  rw [List.map_append, List.map_ofFn, List.map_ofFn]
  congr 1
  · exact List.ext_get (by simp) (fun k h1 h2 => by simp)
  · exact List.ext_get (by simp) (fun k h1 h2 => by simp)

theorem resultAxes_lt (x : c.InCoord) (y : c.OutCoord) :
    ∀ p ∈ c.resultAxes x y, p.2 < p.1 := by
  intro p hp
  unfold resultAxes at hp
  rcases List.mem_append.1 hp with hp | hp <;>
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp <;> exact Fin.isLt _

theorem resultIndex_lt (x : c.InCoord) (y : c.OutCoord) :
    c.resultIndex x y < c.resultDims.prod := by
  rw [← c.resultAxes_fst x y]
  exact flatIndex_lt _ (c.resultAxes_lt x y)

/-- Distinct boundary coordinates have distinct result cells. -/
theorem resultIndex_injective {x x' : c.InCoord} {y y' : c.OutCoord}
    (h : c.resultIndex x y = c.resultIndex x' y') : x = x' ∧ y = y' := by
  have he := flatIndex_injective _ _ ((c.resultAxes_fst x y).trans (c.resultAxes_fst x' y').symm)
    (c.resultAxes_lt x y) (c.resultAxes_lt x' y') h
  unfold resultAxes at he
  have hl : (List.ofFn fun i => (dimension c.network.inputs[i].attrs, (x i).val)).length =
      (List.ofFn fun i => (dimension c.network.inputs[i].attrs, (x' i).val)).length := by simp
  obtain ⟨h1, h2⟩ := List.append_inj he hl
  refine ⟨funext fun i => Fin.ext ?_, funext fun j => Fin.ext ?_⟩
  · have := congrArg (fun l => l[i.val]?) h1
    simpa using this
  · have := congrArg (fun l => l[j.val]?) h2
    simpa using this

/-- The result cell of a pair of coordinates. -/
def resultCell (p : c.InCoord × c.OutCoord) : Fin c.resultDims.prod :=
  ⟨c.resultIndex p.1 p.2, c.resultIndex_lt p.1 p.2⟩

theorem card_coords : Fintype.card (c.InCoord × c.OutCoord) = c.resultDims.prod := by
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  simp only [Fintype.card_fin]
  unfold resultDims
  rw [List.prod_append, ← List.ofFn_getElem_eq_map, ← List.ofFn_getElem_eq_map, List.prod_ofFn,
    List.prod_ofFn]
  rfl

/-- **The cell layout is a bijection** between pairs of boundary coordinates and the cells
of a table with the result's axes. -/
theorem resultCell_bijective : Function.Bijective c.resultCell :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨fun p q e => by
      obtain ⟨h1, h2⟩ := c.resultIndex_injective (congrArg Fin.val e)
      exact Prod.ext h1 h2, by rw [card_coords, Fintype.card_fin]⟩

/-! ## Diagnostics -/

/-- The sum of row `r` of generator `g`'s chance table. -/
def rowSum (g : c.Gen) (r : ℕ) : ℚ :=
  ∑ s ∈ Finset.range (dimension (c.network.label g).result),
    cellQ (c.tableOf g) (r * dimension (c.network.label g).result + s)

/-- The largest `|row sum - 1|` over the chance generators' rows. -/
def rowDeviation : ℚ :=
  (Finset.univ.filter fun g => c.isDecisionGen g = false).fold max 0 fun g =>
    (Finset.range (rowCount (c.network.label g))).fold max 0 fun r => |c.rowSum g r - 1|

/-- The largest error of the recorded `K`. -/
def kError : ℚ :=
  (Finset.univ : Finset (c.InCoord × c.OutCoord)).fold max 0 fun p =>
    |cellQ c.result.K (c.resultIndex p.1 p.2) - c.exactK p.1 p.2|

/-- The largest error of the recorded `W`. -/
def wError : ℚ :=
  (Finset.univ : Finset (c.InCoord × c.OutCoord)).fold max 0 fun p =>
    |cellQ c.result.W (c.resultIndex p.1 p.2) - c.exactW p.1 p.2|

theorem kError_le {τ : ℚ} (h : c.kError ≤ τ) (x : c.InCoord) (y : c.OutCoord) :
    |cellQ c.result.K (c.resultIndex x y) - c.exactK x y| ≤ τ :=
  ((Finset.fold_max_le _).1 h).2 (x, y) (Finset.mem_univ _)

theorem wError_le {τ : ℚ} (h : c.wError ≤ τ) (x : c.InCoord) (y : c.OutCoord) :
    |cellQ c.result.W (c.resultIndex x y) - c.exactW x y| ≤ τ :=
  ((Finset.fold_max_le _).1 h).2 (x, y) (Finset.mem_univ _)

end Certificate

end OpenInfluence.RewardCertificate
