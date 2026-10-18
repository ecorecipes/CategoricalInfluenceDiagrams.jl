import CategoricalInfluenceDiagramsProofs.Certificate.Check

/-!
# Reward certificates: soundness

This module proves what acceptance by `check τ c` (`Check.lean`) means, in terms of the
definitions of `Syntax.lean` and `Interpretation.lean` that the functoriality and
contextual-identity theorems are stated for.

**The decoded diagram.**

* `sig` is one influence-diagram signature for every certificate: CategoricalBayesianNetworks'
  raw signature (types are variable attributes, labels are generator attributes), with a
  label a decision exactly when its reference is a `policy` reference, and with utility
  labels `ULabel` (a name and the scope's attributes).
* `diagram` is the `IDNet` of an accepted certificate: its net is
  `Network.normalize`, the checked net of CategoricalBayesianNetworks (what its `checkedNet`
  returns for a raw certificate), and its utility generators are the certificate's
  utilities, each reading its scope variables in position order.
* `model` is the `IDInterpretation`: the states of a type are `Fin (dimension t)`, as in
  CategoricalBayesianNetworks' `LocalTables` (on a valid network `dimension` is the state
  count, and state `k` is the state of position `k + 1`). The chance table of a label is the
  table of the first generator with that label, read at the parents' states and the child
  state (labels with no generator get the point mass at the first state); it is
  nonnegative because every chance cell is, and normalised because every chance row sums to
  exactly one (`chance_normalized` is where the exact row sums are needed). The utility of a
  label is the table of the first utility with that label.
* `strategyOf` is the `Strategy`: a decision label's policy is the policy record of its
  decision name, read at the information states (`actionOf`).

**The theorems.**

* `check_sound` (in `Check.lean`): acceptance gives a valid network and information
  locality; `diagram_informationLocal` restates information locality on the decoded
  `IDNet`: no decision generator reads an input port whose flag is not `observed`.
* `interpret_K_eq`, `interpret_W_eq`: on an accepted certificate (in fact under the four
  hypotheses nonnegativity, exact row sums, label consistency and network validity), for
  all 0-based states `x` of the input rows and `y` of the output rows, `interpret σ f`
  evaluated at the corresponding boundary assignments is exactly `exactK x y` and
  `exactW x y` (`Exact.lean`), the enumeration over the certificate's own tables.
* `reward_certificate_sound_K`, `reward_certificate_sound_W`: on an accepted certificate,
  for **every** pair of boundary assignments `x`, `y` of the decoded diagram, the recorded
  cell at `boundaryIndex x y` exists and is within `τ` of `(interpret σ f).K x y`
  (respectively `.W x y`). `boundaryIndex x y` is the flat index of the 0-based states
  `(x i).2` of the input rows followed by those `(y j).2` of the output rows
  (`boundaryIndex_eq`), and it is a bijection between pairs of boundary assignments and the
  recorded cells (`boundaryIndex_bijective`; `resultCell_bijective` in `Exact.lean` for the
  coordinates).

**Not proved.** That the certificate's diagram is the one Julia built, or that a Julia
composite is the Lean composite of its parts (ADR 0019, decision 5): the theorems are about
the decoded record. The reading of state `k` as the state of position `k + 1` is the
format's convention, not a theorem. Binary64 certificates whose chance rows do not sum to
exactly one are rejected, so nothing is claimed for them.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence.RewardCertificate

open OpenNet OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-- The influence-diagram signature of every reward certificate. -/
abbrev sig : IDSignature where
  toSignature := RawCertificate.signature
  isDecision l := isPolicy l.kernelRef
  ULabel := ULabel
  uinputs := ULabel.inputs

/-- A typed value: a type (variable attributes) and a 0-based state. -/
abbrev TypedValue := Σ t : VariableAttrs, Fin (dimension t)

/-- The states of a list of typed values. -/
def vals (p : List TypedValue) : List ℕ := p.map fun s => s.2.val

theorem sigma_eq_iff {a b : TypedValue} (h : a.1 = b.1) : a = b ↔ a.2.val = b.2.val := by
  obtain ⟨t, s⟩ := a
  obtain ⟨t', s'⟩ := b
  simp only at h
  subst h
  simp [Fin.ext_iff]

theorem sigma_mk_eq_iff {t : VariableAttrs} (s s' : Fin (dimension t)) :
    (⟨t, s⟩ : TypedValue) = ⟨t, s'⟩ ↔ s.val = s'.val := by
  simp [Fin.ext_iff]

theorem zip_typed (p : List TypedValue) :
    ((p.map Sigma.fst).map dimension).zip (vals p) = p.map fun s => (dimension s.1, s.2.val) := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [vals, List.map_cons, List.zip_cons_cons] at ih ⊢; rw [ih]

theorem dimension_pos (t : VariableAttrs) : 0 < dimension t :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem row_lt {l : LabelAttrs} {p : List TypedValue} (hp : p.map Sigma.fst = l.inputs) :
    flatIndex (inputAxes l (vals p)) < rowCount l := by
  unfold inputAxes rowCount
  rw [← hp, zip_typed]
  have h := flatIndex_lt (p.map fun s => (dimension s.1, s.2.val)) (by
    intro q hq
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hq
    exact s.2.isLt)
  simpa [List.map_map] using h

theorem find?_unique {α : Type} {l : List α} {p : α → Bool} {a : α} (ha : a ∈ l)
    (hp : p a = true) (hu : ∀ b ∈ l, p b = true → b = a) : l.find? p = some a := by
  cases h : l.find? p with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd hp (h a ha)
  | some b => rw [hu b (List.mem_of_find?_eq_some h) (List.find?_some h)]

namespace Certificate

variable (c : Certificate)

/-! ## Tables by label -/

/-- The chance table of a label: the table of the first generator with that label. -/
def labelTable (l : LabelAttrs) : Option (List Value) :=
  ((List.finRange _).find? fun g => decide (c.network.label g = l)).map c.tableOf

/-- The chance cell of a label at the parent states `vs` and the child state `s`; the point
mass at the first state when no generator has the label. -/
def chanceEntry (l : LabelAttrs) (vs : List ℕ) (s : ℕ) : ℚ :=
  match c.labelTable l with
  | some cells => chanceAt cells l vs s
  | none => if s = 0 then 1 else 0

/-- The table of a utility label: the table of the first utility with that label. -/
def ulabelCells (l : ULabel) : Option (List Value) :=
  ((List.finRange _).find? fun u => decide (c.utilityLabel u = l)).map
    fun u => c.utilities[u].cells

/-- The utility of a label at the scope states `vs`; `0` when no utility has the label. -/
def utilityEntry (l : ULabel) (vs : List ℕ) : ℚ :=
  match c.ulabelCells l with
  | some cells => utilityAt cells l vs
  | none => 0

theorem labelTable_spec {l : LabelAttrs} {cells : List Value}
    (h : c.labelTable l = some cells) : ∃ g, c.network.label g = l ∧ c.tableOf g = cells := by
  unfold labelTable at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp := List.find?_some hg
  exact ⟨g, by simpa using hp, rfl⟩

theorem labelTable_label (hcons : c.LabelsConsistent) (g : c.Gen)
    (hg : c.isDecisionGen g = false) : c.labelTable (c.network.label g) = some (c.tableOf g) := by
  cases h : c.labelTable (c.network.label g) with
  | none =>
    exfalso
    unfold labelTable at h
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    exact h g (List.mem_finRange g) (by simp)
  | some cells =>
    obtain ⟨g', hl, rfl⟩ := c.labelTable_spec h
    rw [hcons.1 g g' hg hl.symm]

theorem ulabelCells_label (hcons : c.LabelsConsistent) (u : c.UIdx) :
    c.ulabelCells (c.utilityLabel u) = some c.utilities[u].cells := by
  cases h : c.ulabelCells (c.utilityLabel u) with
  | none =>
    exfalso
    unfold ulabelCells at h
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    exact h u (List.mem_finRange u) (by simp)
  | some cells =>
    unfold ulabelCells at h
    obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.1 h
    have hp := List.find?_some hu'
    have hp' : c.utilityLabel u' = c.utilityLabel u := by simpa using hp
    rw [hcons.2 u u' hp'.symm]

theorem utilityEntry_label (hcons : c.LabelsConsistent) (u : c.UIdx) (vs : List ℕ) :
    c.utilityEntry (c.utilityLabel u) vs =
      utilityAt c.utilities[u].cells (c.utilityLabel u) vs := by
  unfold utilityEntry
  rw [c.ulabelCells_label hcons u]

theorem tableOf_nonneg (hnn : c.ChanceNonneg) (g : c.Gen) : ∀ v ∈ c.tableOf g, 0 ≤ v.toRat := by
  unfold tableOf
  cases h : c.chanceTables.find? fun t => decide (t.mechanism = g.val) with
  | none => simp
  | some t => exact hnn t (List.mem_of_find?_eq_some h)

theorem chanceEntry_nonneg (hnn : c.ChanceNonneg) (l : LabelAttrs) (vs : List ℕ) (s : ℕ) :
    0 ≤ c.chanceEntry l vs s := by
  unfold chanceEntry
  cases h : c.labelTable l with
  | none => dsimp only; split_ifs <;> norm_num
  | some cells =>
    obtain ⟨g, -, rfl⟩ := c.labelTable_spec h
    exact cellQ_nonneg (c.tableOf_nonneg hnn g) _

theorem chanceEntry_normalized (hrows : c.RowsExact) (l : LabelAttrs) (p : List TypedValue)
    (hl : isPolicy l.kernelRef = false) (hp : p.map Sigma.fst = l.inputs) :
    ∑ s : Fin (dimension l.result), c.chanceEntry l (vals p) s.val = 1 := by
  unfold chanceEntry
  cases h : c.labelTable l with
  | none =>
    dsimp only
    rw [Fin.sum_univ_eq_sum_range (fun s => if s = 0 then (1 : ℚ) else 0)]
    rw [Finset.sum_ite_eq' (Finset.range _) 0 (fun _ => (1 : ℚ))]
    simp [dimension_pos]
  | some cells =>
    obtain ⟨g, rfl, rfl⟩ := c.labelTable_spec h
    dsimp only
    simp only [chanceAt_row]
    rw [Fin.sum_univ_eq_sum_range (fun s => cellQ (c.tableOf g)
      (flatIndex (inputAxes (c.network.label g) (vals p)) *
        dimension (c.network.label g).result + s))]
    exact hrows g hl _ (row_lt hp)

/-! ## The interpretation, the strategy and the diagram -/

/-- The `IDInterpretation` of the certificate's tables. -/
def model (hnn : c.ChanceNonneg) (hrows : c.RowsExact) : IDInterpretation sig where
  states t := Fin (dimension t)
  finite _ := inferInstance
  chance := fun (l : LabelAttrs) (p : List TypedValue) (s : TypedValue) =>
    if s.1 = l.result then ((c.chanceEntry l (vals p) s.2.val : ℚ) : ℝ) else 0
  chance_nonneg := by
    intro l p s _
    change 0 ≤ (if s.1 = l.result then ((c.chanceEntry l (vals p) s.2.val : ℚ) : ℝ) else 0)
    split_ifs
    · exact_mod_cast c.chanceEntry_nonneg hnn l _ _
    · exact le_refl 0
  chance_normalized := by
    intro l p hl hp
    change ∑ s : Fin (dimension l.result), (if l.result = l.result then
      ((c.chanceEntry l (vals p) s.val : ℚ) : ℝ) else 0) = 1
    simp only [if_true]
    exact_mod_cast c.chanceEntry_normalized hrows l p hl hp
  utility := fun (l : ULabel) (p : List TypedValue) => ((c.utilityEntry l (vals p) : ℚ) : ℝ)

/-- The strategy of the certificate: each decision label reads the policy of its name. -/
def strategyOf (hnn : c.ChanceNonneg) (hrows : c.RowsExact) : (c.model hnn hrows).Strategy :=
  fun (l : LabelAttrs) _ (p : List TypedValue) =>
    (⟨c.actionOf l (vals p), c.actionOf_lt l (vals p)⟩ : Fin (dimension l.result))

/-- The decoded open influence diagram: CategoricalBayesianNetworks' checked net of the
certificate's network, with the certificate's utilities. -/
def diagram (hc : c.network.check = true) : IDNet (S := sig) c.network.dom c.network.cod where
  net := c.network.normalize hc
  UGen := c.UIdx
  ufinite := inferInstance
  ulabel := c.utilityLabel
  uparents u := (c.scope u).map (c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm
  uparents_typed u := by
    rw [List.map_map]
    exact congrArg (fun k => (c.scope u).map k)
      (funext (c.network.toLegged (c.network.check_sound hc)).decode_typed)

/-- The input boundary with the recorded flags (a missing flag reads as hidden). -/
def domFlag (i : Fin c.network.inputs.length) : Observability :=
  (c.inputFlags[i.val]?).getD .hidden

/-- The decoded input interface with its observability flags. -/
def observedDom : ObservedInterface sig.toSignature := ⟨c.network.dom, c.domFlag⟩

/-- **Information locality on the decoded diagram**: if the network is valid and the
certificate's information locality holds, no decision generator of the decoded `IDNet`
reads an input port whose flag is not `observed`. -/
theorem diagram_informationLocal_of (hc : c.network.check = true) (hl : c.InformationLocal) :
    ∀ a : (c.diagram hc).net.Gen, (c.diagram hc).IsDecision a →
      ∀ p : c.network.dom.Port, Sum.inl p ∈ (c.diagram hc).info a →
        c.observedDom.flag p = .observed := by
  intro a ha p hp
  change Sum.inl p ∈ (c.network.parents a).map
    (c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm at hp
  obtain ⟨v, hv, he⟩ := List.mem_map.1 hp
  have hvp : v = c.network.input p := by
    rw [Equiv.symm_apply_eq] at he
    exact he
  subst hvp
  change (c.inputFlags[p.val]?).getD .hidden = .observed
  rw [hl a ha _ hv p rfl]
  rfl

/-! ## The bridge: `interpret` is the exact enumeration -/

section Bridge

variable (hnn : c.ChanceNonneg) (hrows : c.RowsExact) (hc : c.network.check = true)

/-- The boundary assignment of 0-based input-row states. -/
def inAssign (x : c.InCoord) :
    ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).Boundary c.network.dom :=
  Interpretation.Assignment.ofPi _ x

/-- The boundary assignment of 0-based output-row states. -/
def outAssign (y : c.OutCoord) :
    ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).Boundary c.network.cod :=
  Interpretation.Assignment.ofPi _ y

/-- Generator states are the internal assignments of the decoded net. -/
def genEquiv : c.GenCoord ≃
    ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).Internal (c.diagram hc).net :=
  Interpretation.Assignment.piEquiv ((c.model hnn hrows).interp (c.strategyOf hnn hrows))
    (sig.result ∘ (c.diagram hc).net.label)

theorem valuation_value (x : c.InCoord) (z : c.GenCoord) (v : Fin c.network.variableCount) :
    (((c.model hnn hrows).interp (c.strategyOf hnn hrows)).valuation (c.diagram hc).net
      (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z)
      ((c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm v)).2.val =
      c.value x z v := by
  have hv := c.network.check_sound hc
  rcases hv.2.2.2.2.2.1 v with ⟨i, rfl⟩ | ⟨g, rfl⟩
  · have hs : (c.network.toLegged hv).varsEquiv.symm (c.network.input i) = Sum.inl i := by
      rw [Equiv.symm_apply_eq]
      rfl
    rw [hs]
    have hg : c.genOf (c.network.input i) = none := by
      unfold genOf
      rw [List.find?_eq_none]
      intro g _ hg
      exact hv.2.2.2.2.1 i g (of_decide_eq_true hg).symm
    have hi : c.inputOf (c.network.input i) = some i :=
      find?_unique (List.mem_finRange i) (by simp)
        (fun i' _ h' => hv.2.2.2.1 (of_decide_eq_true h'))
    simp only [value, hg, hi]
    rfl
  · have hs : (c.network.toLegged hv).varsEquiv.symm (c.network.target g) = Sum.inr g := by
      rw [Equiv.symm_apply_eq]
      rfl
    rw [hs]
    have hg : c.genOf (c.network.target g) = some g :=
      find?_unique (List.mem_finRange g) (by simp)
        (fun g' _ h' => hv.2.2.1 (of_decide_eq_true h'))
    simp only [value, hg]
    rfl

theorem vals_map (x : c.InCoord) (z : c.GenCoord) (vs : List (Fin c.network.variableCount)) :
    vals ((vs.map (c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm).map
      (((c.model hnn hrows).interp (c.strategyOf hnn hrows)).valuation (c.diagram hc).net
        (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z)).value) =
      vs.map (c.value x z) := by
  unfold vals
  refine List.map_map.trans (List.map_map.trans ?_)
  exact List.map_congr_left fun v _ => c.valuation_value hnn hrows hc x z v

theorem weight_eq (hcons : c.LabelsConsistent) (x : c.InCoord) (z : c.GenCoord) (g : c.Gen) :
    ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).weight ((c.diagram hc).net.label g)
      (((c.model hnn hrows).interp (c.strategyOf hnn hrows)).parents (c.diagram hc).net
        (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z) g)
      ((c.genEquiv hnn hrows hc z) g) = ((c.genWeight x z g : ℚ) : ℝ) := by
  have hp := c.vals_map hnn hrows hc x z (c.network.parents g)
  unfold genWeight
  by_cases hd : c.isDecisionGen g = true
  · have hd' : sig.isDecision ((c.diagram hc).net.label g) = true := hd
    rw [IDInterpretation.interp_weight_decision (c.model hnn hrows) (c.strategyOf hnn hrows) _
      hd', if_pos hd]
    have key : ((c.genEquiv hnn hrows hc z) g = ⟨sig.result ((c.diagram hc).net.label g),
        c.strategyOf hnn hrows _ hd' (((c.model hnn hrows).interp
          (c.strategyOf hnn hrows)).parents (c.diagram hc).net (c.inAssign hnn hrows x)
          (c.genEquiv hnn hrows hc z) g)⟩) ↔
        (z g).val = c.actionOf (c.network.label g)
          ((c.network.parents g).map (c.value x z)) := by
      change (⟨(c.network.label g).result, z g⟩ : TypedValue) =
        ⟨(c.network.label g).result, ⟨c.actionOf (c.network.label g) (vals _), _⟩⟩ ↔ _
      rw [sigma_mk_eq_iff]
      exact iff_of_eq (congrArg (fun vs => (z g).val = c.actionOf (c.network.label g) vs) hp)
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (key.1 h1) h2
    · exact absurd (key.2 h2) h1
    · simp
  · have hd2 : c.isDecisionGen g = false := by simpa using hd
    have hd' : sig.isDecision ((c.diagram hc).net.label g) = false := hd2
    rw [IDInterpretation.interp_weight_chance (c.model hnn hrows) (c.strategyOf hnn hrows) _
      hd', if_neg hd]
    change (if (c.network.label g).result = (c.network.label g).result then
      ((c.chanceEntry (c.network.label g) (vals (((c.network.parents g).map
        (c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm).map _))
        (z g).val : ℚ) : ℝ) else 0) = _
    rw [if_pos rfl]
    have e1 : c.chanceEntry (c.network.label g) ((c.network.parents g).map (c.value x z))
        (z g).val = chanceAt (c.tableOf g) (c.network.label g)
          ((c.network.parents g).map (c.value x z)) (z g).val := by
      unfold chanceEntry
      rw [c.labelTable_label hcons g hd2]
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((congrArg (fun vs => c.chanceEntry (c.network.label g) vs (z g).val) hp).trans e1)

theorem joint_eq (hcons : c.LabelsConsistent) (x : c.InCoord) (z : c.GenCoord) :
    ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).joint (c.diagram hc).net
      (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z) = ((c.joint x z : ℚ) : ℝ) := by
  unfold Interpretation.joint joint
  push_cast
  exact Finset.prod_congr rfl fun g _ => c.weight_eq hnn hrows hc hcons x z g

theorem reward_eq (hcons : c.LabelsConsistent) (x : c.InCoord) (z : c.GenCoord) :
    (c.model hnn hrows).reward (c.strategyOf hnn hrows) (c.diagram hc)
      (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z) = ((c.reward x z : ℚ) : ℝ) := by
  unfold IDInterpretation.reward reward
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  change ((c.utilityEntry (c.utilityLabel u) (vals (((c.scope u).map
    (c.network.toLegged (c.network.check_sound hc)).varsEquiv.symm).map _)) : ℚ) : ℝ) = _
  exact congrArg (fun q : ℚ => (q : ℝ))
    ((congrArg (fun vs => c.utilityEntry (c.utilityLabel u) vs)
      (c.vals_map hnn hrows hc x z (c.scope u))).trans (c.utilityEntry_label hcons u _))

theorem read_iff (x : c.InCoord) (z : c.GenCoord) (y : c.OutCoord) :
    c.outAssign hnn hrows y = ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).read
      (c.diagram hc).net (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z) ↔
      c.Reads x z y := by
  rw [Interpretation.Assignment.ext_iff, funext_iff]
  apply forall_congr'
  intro j
  rw [← c.valuation_value hnn hrows hc x z (c.network.output j)]
  exact sigma_eq_iff ((((c.model hnn hrows).interp (c.strategyOf hnn hrows)).read
    (c.diagram hc).net (c.inAssign hnn hrows x) (c.genEquiv hnn hrows hc z)).typed j).symm

/-- **`K` is the exact enumeration**: at the boundary assignments of 0-based states `x`,
`y`, the probability component of `interpret σ f` is `exactK x y`. -/
theorem interpret_K_eq (hcons : c.LabelsConsistent) (x : c.InCoord) (y : c.OutCoord) :
    ((c.model hnn hrows).interpret (c.strategyOf hnn hrows) (c.diagram hc)).K
      (c.inAssign hnn hrows x) (c.outAssign hnn hrows y) = ((c.exactK x y : ℚ) : ℝ) := by
  change ((c.model hnn hrows).interp (c.strategyOf hnn hrows)).kernel (c.diagram hc).net
    (c.inAssign hnn hrows x) (c.outAssign hnn hrows y) = _
  rw [IDInterpretation.kernel_eq_sum]
  unfold exactK
  push_cast
  symm
  refine Fintype.sum_equiv (c.genEquiv hnn hrows hc) _ _ fun z => ?_
  by_cases hr : c.Reads x z y
  · rw [if_pos hr, ite_cond_eq_true _ _ (eq_true ((c.read_iff hnn hrows hc x z y).2 hr)),
      c.joint_eq hnn hrows hc hcons]
  · rw [if_neg hr,
      ite_cond_eq_false _ _ (eq_false (fun e => hr ((c.read_iff hnn hrows hc x z y).1 e))),
      Rat.cast_zero]

/-- **`W` is the exact enumeration**: at the boundary assignments of 0-based states `x`,
`y`, the reward component of `interpret σ f` is `exactW x y`. -/
theorem interpret_W_eq (hcons : c.LabelsConsistent) (x : c.InCoord) (y : c.OutCoord) :
    ((c.model hnn hrows).interpret (c.strategyOf hnn hrows) (c.diagram hc)).W
      (c.inAssign hnn hrows x) (c.outAssign hnn hrows y) = ((c.exactW x y : ℚ) : ℝ) := by
  change (c.model hnn hrows).rewardTable (c.strategyOf hnn hrows) (c.diagram hc)
    (c.inAssign hnn hrows x) (c.outAssign hnn hrows y) = _
  unfold IDInterpretation.rewardTable exactW
  push_cast
  symm
  refine Fintype.sum_equiv (c.genEquiv hnn hrows hc) _ _ fun z => ?_
  by_cases hr : c.Reads x z y
  · rw [if_pos hr, ite_cond_eq_true _ _ (eq_true ((c.read_iff hnn hrows hc x z y).2 hr)),
      c.joint_eq hnn hrows hc hcons, c.reward_eq hnn hrows hc hcons, Rat.cast_mul]
  · rw [if_neg hr,
      ite_cond_eq_false _ _ (eq_false (fun e => hr ((c.read_iff hnn hrows hc x z y).1 e))),
      Rat.cast_zero]

end Bridge

/-! ## Acceptance -/

section Accepted

variable {c} {τ : ℚ}

theorem accepted_of_check (h : c.check τ = true) : c.Accepted τ := (c.check_iff_accepted τ).1 h

theorem network_check_of_check (h : c.check τ = true) : c.network.check = true :=
  (Network.check_iff _).2 (accepted_of_check h).valid

/-- The `IDInterpretation` of an accepted certificate. -/
def modelOf (h : c.check τ = true) : IDInterpretation sig :=
  c.model (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact

/-- The strategy of an accepted certificate. -/
def strategyOfCheck (h : c.check τ = true) : (modelOf h).Strategy :=
  c.strategyOf (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact

/-- The `IDNet` of an accepted certificate. -/
def diagramOf (h : c.check τ = true) : IDNet (S := sig) c.network.dom c.network.cod :=
  c.diagram (network_check_of_check h)

/-- The fixed-strategy semantics of the decoded diagram, `interpret σ f`. -/
def semantics (h : c.check τ = true) :
    RewardKernel (((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
      (((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :=
  (modelOf h).interpret (strategyOfCheck h) (diagramOf h)

/-- The result cell of a pair of boundary assignments: the flat index of the input rows'
0-based states, then the output rows'. -/
def boundaryIndex (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) : ℕ :=
  flatIndex (List.ofFn (fun i => (dimension c.network.inputs[i].attrs, (x i).2.val)) ++
    List.ofFn (fun j => (dimension c.network.outputs[j].attrs, (y j).2.val)))

theorem cast_val {t t' : VariableAttrs} (e : t = t') (s : Fin (dimension t)) :
    (cast (congrArg (fun u => Fin (dimension u)) e) s).val = s.val := by
  subst e
  rfl

theorem boundaryIndex_eq (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    boundaryIndex h x y = c.resultIndex (Interpretation.Assignment.toPi _ x)
      (Interpretation.Assignment.toPi _ y) := by
  unfold boundaryIndex resultIndex resultAxes
  congr 2
  · exact List.ofFn_inj.2 (funext fun i => Prod.ext rfl (cast_val (x.typed i) (x i).2).symm)
  · exact List.ofFn_inj.2 (funext fun j => Prod.ext rfl (cast_val (y.typed j) (y j).2).symm)

theorem inAssign_toPi (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom) :
    c.inAssign (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact
      (Interpretation.Assignment.toPi _ x) = x :=
  (Interpretation.Assignment.piEquiv _ _).apply_symm_apply x

theorem outAssign_toPi (h : c.check τ = true)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    c.outAssign (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact
      (Interpretation.Assignment.toPi _ y) = y :=
  (Interpretation.Assignment.piEquiv _ _).apply_symm_apply y

theorem boundaryIndex_lt_K (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    boundaryIndex h x y < c.result.K.length := by
  rw [boundaryIndex_eq, (accepted_of_check h).cellCounts.2.2.2.1]
  exact c.resultIndex_lt _ _

theorem boundaryIndex_lt_W (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    boundaryIndex h x y < c.result.W.length := by
  rw [boundaryIndex_eq, (accepted_of_check h).cellCounts.2.2.2.2]
  exact c.resultIndex_lt _ _

/-- Distinct pairs of boundary assignments have distinct result cells. -/
theorem boundaryIndex_injective (h : c.check τ = true)
    {x x' : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom}
    {y y' : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod}
    (he : boundaryIndex h x y = boundaryIndex h x' y') : x = x' ∧ y = y' := by
  rw [boundaryIndex_eq, boundaryIndex_eq] at he
  obtain ⟨hx, hy⟩ := c.resultIndex_injective he
  exact ⟨(Interpretation.Assignment.piEquiv _ _).symm.injective hx,
    (Interpretation.Assignment.piEquiv _ _).symm.injective hy⟩

/-- **The cell correspondence**: `boundaryIndex` is a bijection between pairs of boundary
assignments of the decoded diagram and the cells of the recorded `K` (and `W`, which has
the same length). -/
theorem boundaryIndex_bijective (h : c.check τ = true) :
    Function.Bijective (fun p : ((modelOf h).interp (strategyOfCheck h)).Boundary
        c.network.dom × ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod =>
      (⟨boundaryIndex h p.1 p.2, boundaryIndex_lt_K h p.1 p.2⟩ : Fin c.result.K.length)) := by
  constructor
  · intro p q e
    obtain ⟨h1, h2⟩ := boundaryIndex_injective h (congrArg Fin.val e)
    exact Prod.ext h1 h2
  · intro k
    have hk : k.val < c.resultDims.prod := (accepted_of_check h).cellCounts.2.2.2.1 ▸ k.isLt
    obtain ⟨⟨x, y⟩, hxy⟩ := c.resultCell_bijective.2 ⟨k.val, hk⟩
    refine ⟨(c.inAssign (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact x,
      c.outAssign (accepted_of_check h).chanceNonneg (accepted_of_check h).rowsExact y),
      Fin.ext ?_⟩
    change boundaryIndex h _ _ = k.val
    rw [boundaryIndex_eq]
    exact congrArg Fin.val hxy

theorem cellQ_getElem {cells : List Value} {k : ℕ} (hk : k < cells.length) :
    cellQ cells k = cells[k].toRat := by
  simp [cellQ, List.getElem?_eq_getElem hk]

/-- **Soundness for `K`.** If `check τ c` accepts, then for every pair of boundary
assignments `x`, `y` of the decoded diagram, the recorded `K` cell at `boundaryIndex x y`
exists and is within `τ` of `(interpret σ f).K x y`. -/
theorem reward_certificate_sound_K (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    ∃ v, c.result.K[boundaryIndex h x y]? = some v ∧
      |(v.toRat : ℝ) - (semantics h).K x y| ≤ τ := by
  have a := accepted_of_check h
  have hk := boundaryIndex_lt_K h x y
  refine ⟨c.result.K[boundaryIndex h x y], List.getElem?_eq_getElem hk, ?_⟩
  have he := c.interpret_K_eq a.chanceNonneg a.rowsExact (network_check_of_check h)
    a.labelsConsistent (Interpretation.Assignment.toPi _ x) (Interpretation.Assignment.toPi _ y)
  rw [inAssign_toPi, outAssign_toPi] at he
  change |(c.result.K[boundaryIndex h x y].toRat : ℝ) -
    ((modelOf h).interpret (strategyOfCheck h) (diagramOf h)).K x y| ≤ τ
  unfold modelOf strategyOfCheck diagramOf
  rw [he, ← cellQ_getElem hk, boundaryIndex_eq]
  exact_mod_cast c.kError_le a.kError _ _

/-- **Soundness for `W`.** If `check τ c` accepts, then for every pair of boundary
assignments `x`, `y` of the decoded diagram, the recorded `W` cell at `boundaryIndex x y`
exists and is within `τ` of `(interpret σ f).W x y`. -/
theorem reward_certificate_sound_W (h : c.check τ = true)
    (x : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom)
    (y : ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod) :
    ∃ v, c.result.W[boundaryIndex h x y]? = some v ∧
      |(v.toRat : ℝ) - (semantics h).W x y| ≤ τ := by
  have a := accepted_of_check h
  have hk := boundaryIndex_lt_W h x y
  refine ⟨c.result.W[boundaryIndex h x y], List.getElem?_eq_getElem hk, ?_⟩
  have he := c.interpret_W_eq a.chanceNonneg a.rowsExact (network_check_of_check h)
    a.labelsConsistent (Interpretation.Assignment.toPi _ x) (Interpretation.Assignment.toPi _ y)
  rw [inAssign_toPi, outAssign_toPi] at he
  change |(c.result.W[boundaryIndex h x y].toRat : ℝ) -
    ((modelOf h).interpret (strategyOfCheck h) (diagramOf h)).W x y| ≤ τ
  unfold modelOf strategyOfCheck diagramOf
  rw [he, ← cellQ_getElem hk, boundaryIndex_eq]
  exact_mod_cast c.wError_le a.wError _ _

/-- **Information locality on the decoded diagram of an accepted certificate.** -/
theorem diagram_informationLocal (h : c.check τ = true) :
    ∀ a : (diagramOf h).net.Gen, (diagramOf h).IsDecision a →
      ∀ p : c.network.dom.Port, Sum.inl p ∈ (diagramOf h).info a →
        c.observedDom.flag p = .observed :=
  c.diagram_informationLocal_of _ (accepted_of_check h).informationLocal

/-- The decoded diagram's `K` is stochastic, so the semantics is a morphism of `FinRew`. -/
theorem semantics_stochastic (h : c.check τ = true) : (semantics h).Stochastic :=
  (modelOf h).interpret_stochastic (strategyOfCheck h) (diagramOf h)

end Accepted

end Certificate

end OpenInfluence.RewardCertificate
