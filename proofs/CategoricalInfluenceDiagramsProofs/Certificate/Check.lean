import CategoricalInfluenceDiagramsProofs.Certificate.Exact

/-!
# Reward certificates: the checker

`check τ c` decides whether the decoded certificate `c` is accepted with tolerance `τ`. It
runs a fixed list of stages (`stages`) in order and accepts when every stage passes;
`firstFailure` names the first stage that fails (`check_iff_firstFailure`), and
`check_iff_accepted` states acceptance as the conjunction `Accepted` of the stage
properties:

1. **network**: CategoricalBayesianNetworks' `Network.check`, unchanged (positions, states,
   the input/target partition, attributed boundary rows, ranks);
2. **flag counts**: one flag per input row and per output row;
3. **decision names**: a decision generator's reference is `policy` of its own name;
4. **information locality** (rule 3 of ADR 0018): no decision generator has, among its
   information inputs, the variable of an input row whose flag is not `observed`;
5. **chance tables**: the records name exactly the chance generators, in generator order (so
   no decision generator has a chance table);
6. **utility scope positions**: each utility's scope positions are `1, …, k`;
7. **strategy names**: one policy record per distinct decision name, in order of first
   appearance among the decision generators;
8. **strategy shapes**: decision generators with equal names have equal information axis
   lengths and equal action counts;
9. **cell counts**: every chance table, utility table, policy and the recorded `K` and `W`
   have the product of their axis lengths as their number of cells;
10. **value shapes**: chance and utility cells are `{"f64"}` in `binary64_exact` mode and
    `{"q", "f64"}` in `rational_exact` mode, result cells are `{"f64"}`, and every value is
    finite, reduced, and its word the nearest-even rounding of its rational
    (InfluenceDiagrams' `ValueOk`);
11. **label consistency**: chance generators with equal labels have equal tables, and
    utilities with equal labels (name and scope attributes) equal tables; the decoded
    signature keys tables by label (`Sound.lean`), so this is what makes them well defined;
12. **chance nonnegativity**: every chance cell is `≥ 0`;
13. **actions in range**: every policy cell is a state position `1, …, n` of its decision's
    action variable;
14. **exact row sums**: every chance row sums to exactly `1` over `ℚ`. A binary64 model whose
    rows are not exactly normalised fails here: it is outside the exact semantics, and only
    the largest deviation (`rowDeviation`) is reported;
15. **result K**, 16. **result W**: every recorded cell is within `τ` of `exactK`, `exactW`
    (`kError ≤ τ`, `wError ≤ τ`).

Stages 3, 5 to 9 and 13 check the format's conventions; the soundness theorems use stages
1, 2, 4, 11, 12, 14, 15 and 16. Not checked: that the chance mechanisms precede the
decisions in `network.mechanisms` (the format's export order) and the metadata strings.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-- The first occurrence of each element, in order (Julia's `unique`). -/
def firstOccurrences (l : List String) : List String :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- A cell that is a binary64 word alone. -/
def Value.isF64 : Value → Bool
  | .f64 _ => true
  | _ => false

/-- A cell that is a rational with its binary64 word. -/
def Value.isQF64 : Value → Bool
  | .qf64 _ _ _ => true
  | _ => false

/-- The shape a chance or utility cell must have in a numeric mode. -/
def modeShape : NumericMode → Value → Bool
  | .binary64Exact, v => v.isF64
  | .rationalExact, v => v.isQF64

namespace Certificate

variable (c : Certificate) (τ : ℚ)

def FlagCounts : Prop :=
  c.inputFlags.length = c.network.inputs.length ∧ c.outputFlags.length = c.network.outputs.length

def DecisionNames : Prop :=
  ∀ g : c.Gen, c.isDecisionGen g = true →
    (c.network.mechanism g).kernelRef = .policy (c.network.mechanism g).name

/-- **Information locality** (rule 3 of ADR 0018, with the recorded flags): every
information input of a decision generator is either not the variable of an input row, or
the variable of an input row flagged `observed`. -/
def InformationLocal : Prop :=
  ∀ g : c.Gen, c.isDecisionGen g = true → ∀ v ∈ c.network.parents g,
    ∀ i : Fin c.network.inputs.length, c.network.input i = v →
      c.inputFlags[i.val]? = some .observed

/-- The chance generators, as 0-based indices in generator order. -/
def chanceGens : List ℕ :=
  ((List.finRange c.network.mechanisms.length).filter fun g => !c.isDecisionGen g).map Fin.val

def ChanceIndex : Prop := c.chanceTables.map ChanceTable.mechanism = c.chanceGens

def ScopePositions : Prop :=
  ∀ u : c.UIdx, (c.scopeRows u).map InputRow.position = List.range' 1 (c.scopeRows u).length

/-- The distinct decision names, in order of first appearance among the generators. -/
def decisionNameList : List String :=
  firstOccurrences ((List.finRange c.network.mechanisms.length).filterMap fun g =>
    policyName? (c.network.mechanism g).kernelRef)

def StrategyNames : Prop := c.strategy.map Policy.decision = c.decisionNameList

def StrategyShapes : Prop :=
  ∀ g g' : c.Gen, c.isDecisionGen g = true →
    policyName? (c.network.mechanism g).kernelRef = policyName? (c.network.mechanism g').kernelRef →
      (c.network.label g).inputs.map dimension = (c.network.label g').inputs.map dimension ∧
        dimension (c.network.label g).result = dimension (c.network.label g').result

/-- The first decision generator with a given name. -/
def firstDecision (name : String) : Option c.Gen :=
  (List.finRange _).find? fun g =>
    decide (policyName? (c.network.mechanism g).kernelRef = some name)

def CellCounts : Prop :=
  (∀ g : c.Gen, c.isDecisionGen g = false →
    (c.tableOf g).length = rowCount (c.network.label g) * dimension (c.network.label g).result) ∧
  (∀ u : c.UIdx, c.utilities[u].cells.length = ((c.utilityLabel u).inputs.map dimension).prod) ∧
  (∀ p ∈ c.strategy, ∃ g : c.Gen, c.firstDecision p.decision = some g ∧
    p.actions.length = rowCount (c.network.label g)) ∧
  c.result.K.length = c.resultDims.prod ∧ c.result.W.length = c.resultDims.prod

/-- Every chance and utility cell. -/
def tableValues : List Value :=
  c.chanceTables.flatMap ChanceTable.cells ++ c.utilities.flatMap Utility.cells

open InfluenceDiagramsProofs.DVECertificate.Spec (ValueOk) in
def ValuesOk : Prop :=
  (∀ v ∈ c.tableValues, modeShape c.numericMode v = true ∧ ValueOk v) ∧
  (∀ v ∈ c.result.K ++ c.result.W, v.isF64 = true ∧ ValueOk v)

def LabelsConsistent : Prop :=
  (∀ g g' : c.Gen, c.isDecisionGen g = false → c.network.label g = c.network.label g' →
    c.tableOf g = c.tableOf g') ∧
  (∀ u u' : c.UIdx, c.utilityLabel u = c.utilityLabel u' →
    c.utilities[u].cells = c.utilities[u'].cells)

def ChanceNonneg : Prop := ∀ t ∈ c.chanceTables, ∀ v ∈ t.cells, 0 ≤ v.toRat

def ActionsInRange : Prop :=
  ∀ p ∈ c.strategy, ∀ g : c.Gen, c.firstDecision p.decision = some g →
    ∀ a ∈ p.actions, 1 ≤ a ∧ a ≤ dimension (c.network.label g).result

def RowsExact : Prop :=
  ∀ g : c.Gen, c.isDecisionGen g = false → ∀ r < rowCount (c.network.label g), c.rowSum g r = 1

instance : Decidable c.FlagCounts := by unfold FlagCounts; infer_instance
instance : Decidable c.DecisionNames := by unfold DecisionNames; infer_instance
instance : Decidable c.InformationLocal := by unfold InformationLocal; infer_instance
instance : Decidable c.ChanceIndex := by unfold ChanceIndex; infer_instance
instance : Decidable c.ScopePositions := by unfold ScopePositions; infer_instance
instance : Decidable c.StrategyNames := by unfold StrategyNames; infer_instance
instance : Decidable c.StrategyShapes := by unfold StrategyShapes; infer_instance
instance : Decidable c.CellCounts := by unfold CellCounts; infer_instance
instance : Decidable c.ValuesOk := by unfold ValuesOk; infer_instance
instance : Decidable c.LabelsConsistent := by unfold LabelsConsistent; infer_instance
instance : Decidable c.ChanceNonneg := by unfold ChanceNonneg; infer_instance
instance : Decidable c.ActionsInRange := by unfold ActionsInRange; infer_instance
instance : Decidable c.RowsExact := by unfold RowsExact; infer_instance

/-- The stages of the checker, in order, each a name and a deferred decision. -/
def stages : List (String × (Unit → Bool)) :=
  [("network validity (Network.check: positions, states, partition, boundary rows, ranks)",
      fun _ => c.network.check),
    ("flag counts (one observability flag per boundary row)", fun _ => decide c.FlagCounts),
    ("decision names (a decision's reference is policy of its own name)",
      fun _ => decide c.DecisionNames),
    ("information locality (a decision reads a hidden input)",
      fun _ => decide c.InformationLocal),
    ("chance tables (one record per chance generator, in order)",
      fun _ => decide c.ChanceIndex),
    ("utility scope positions (1, ..., k)", fun _ => decide c.ScopePositions),
    ("strategy names (one policy per distinct decision name, in order)",
      fun _ => decide c.StrategyNames),
    ("strategy shapes (equally named decisions differ in shape)",
      fun _ => decide c.StrategyShapes),
    ("cell counts (a table's cells are not the product of its axis lengths)",
      fun _ => decide c.CellCounts),
    ("value shapes (numeric mode, finite words, companions)", fun _ => decide c.ValuesOk),
    ("label consistency (equal labels with different tables)",
      fun _ => decide c.LabelsConsistent),
    ("chance nonnegativity (a negative chance cell)", fun _ => decide c.ChanceNonneg),
    ("actions in range (a policy cell is not an action state position)",
      fun _ => decide c.ActionsInRange),
    ("exact row sums (a chance row does not sum to exactly 1: outside exact semantics)",
      fun _ => decide c.RowsExact),
    ("result K (a recorded K cell is not within the tolerance of the exact value)",
      fun _ => decide (c.kError ≤ τ)),
    ("result W (a recorded W cell is not within the tolerance of the exact value)",
      fun _ => decide (c.wError ≤ τ))]

/-- **The checker**: every stage passes. -/
def check : Bool := (c.stages τ).all fun s => s.2 ()

/-- The name of the first failing stage, if any. -/
def firstFailure : Option String := ((c.stages τ).find? fun s => !(s.2 ())).map Prod.fst

theorem check_iff_firstFailure : c.check τ = true ↔ c.firstFailure τ = none := by
  unfold check firstFailure
  rw [Option.map_eq_none_iff, List.find?_eq_none, List.all_eq_true]
  simp

/-- What acceptance means, stage by stage. -/
structure Accepted : Prop where
  valid : c.network.Valid
  flagCounts : c.FlagCounts
  decisionNames : c.DecisionNames
  informationLocal : c.InformationLocal
  chanceIndex : c.ChanceIndex
  scopePositions : c.ScopePositions
  strategyNames : c.StrategyNames
  strategyShapes : c.StrategyShapes
  cellCounts : c.CellCounts
  valuesOk : c.ValuesOk
  labelsConsistent : c.LabelsConsistent
  chanceNonneg : c.ChanceNonneg
  actionsInRange : c.ActionsInRange
  rowsExact : c.RowsExact
  kError : c.kError ≤ τ
  wError : c.wError ≤ τ

theorem check_iff_accepted : c.check τ = true ↔ c.Accepted τ := by
  unfold check stages
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
    exact ⟨c.network.check_sound h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
    exact ⟨(Network.check_iff _).2 h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16⟩

/-- **Acceptance gives a valid network with information locality.** -/
theorem check_sound {c : Certificate} {τ : ℚ} (h : c.check τ = true) :
    c.network.Valid ∧ c.InformationLocal :=
  let a := (c.check_iff_accepted τ).1 h
  ⟨a.valid, a.informationLocal⟩

end Certificate

end OpenInfluence.RewardCertificate
