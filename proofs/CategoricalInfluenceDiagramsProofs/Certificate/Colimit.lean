import CategoricalInfluenceDiagramsProofs.Certificate.Sound
import CategoricalInfluenceDiagramsProofs.Certificate.Json

/-!
# Colimit certificates: the composite's structure, and its exact semantics (ADR 0025)

A composition or tensor certificate (ADR 0023) checks a composite's *numbers* against its
parts', cell by cell, up to a tolerance; the structure, that Julia's composite is the colimit
of its parts, stays trusted. A **colimit certificate** records the parts, the composite and
Catlab's cocone maps (`legs`): for every part, where each of its variables, generators and
utilities went in the composite. The checker (`Colimit.check`) accepts when every reward
certificate is accepted and the legs are a colimit witness (`Wired`):

* the generator maps of the parts together are a bijection onto the composite's generators,
  and likewise for utilities (`genInj`, `genSurj`, `utilInj`, `utilSurj`);
* the variable maps preserve attributes, and each generator keeps its label, its target, its
  ordered parents, its chance table and (for a decision) its recorded policy; each utility its
  ordered scope and its table (`attrs`, `labels`, `targets`, `parents`, `tables`, `policies`,
  `scopes`, `ucells`);
* only boundary variables are identified: two distinct part variables with one image are both
  input or output rows of their parts (`joins`);
* every output row of the composite is an input row of it or the image of a boundary row of a
  part (`outputs`).

This is the structure of a colimit of the parts along their interfaces (a pushout for
`compose` and `glue`, a coproduct for `otimes`, the colimit of a wiring diagram for `oapply`),
checked on the records, with Catlab's cocone as the witness.

**The semantics** (`colimit_exactK`, `colimit_exactW`). Call a choice `t` of boundary
coordinates for every part *consistent* with composite coordinates `x`, `y` when any two rows,
of the parts or of the composite, whose variables have one image carry one state
(`Consistent`). Then, exactly, with no tolerance,

`K_C(x, y) = Σ_t [t consistent] Π_i K_i(t_i)` and
`W_C(x, y) = Σ_t [t consistent] Σ_i W_i(t_i) Π_{j ≠ i} K_j(t_j)`:

the composite's semantics is the junction sum of the parts' semantics in the expectation
semiring. For `compose` it is `(K_A K_B, W_A K_B + K_A W_B)`, for `otimes` the tensor; for
`glue` and `oapply` the sum over the shared variables. By `interpret_K_eq` and
`interpret_W_eq` (`Sound.lean`) every certificate's exact tables are `interpret σ f` of its
decoded diagram. The proof is a bijection: the composite's generator states split into the
parts' (`split`), every part variable takes the composite value of its image (`valueP`), the
joint weight and the reward factor over the parts (`joint_split`, `reward_split`), and the
only consistent choice of boundary coordinates compatible with the parts' outputs is the one
the composite's values give (`ports_unique`).

**Not claimed.** The decoded composite is not shown to be `IDNet.comp` of the decoded parts
as `IDNet`s: the isomorphism is checked on the records, and its consequence for the
semantics is proved here; `SyntaxCategory` proves separately that `interpret` respects
isomorphism of `IDNet`s.
-/

set_option autoImplicit false

namespace OpenInfluence.RewardCertificate

open OpenNet.RawCertificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-- One leg of a colimit certificate: for each variable, generator and utility of a part, its
0-based index in the composite. -/
structure Leg where
  vars : List ℕ
  gens : List ℕ
  utils : List ℕ
  deriving DecidableEq, Repr

/-- A decoded `OpenInfluence.ColimitCertificate/v1`. -/
structure Colimit where
  operation : String
  parts : List Certificate
  composite : Certificate
  legs : List Leg

/-- The format string of version 1. -/
def colimitFormatName : String := "OpenInfluence.ColimitCertificate/v1"

/-! ## Facts about one certificate -/

namespace Certificate

variable (c : Certificate)

/-- A variable is a boundary variable: the variable of an input or an output row. -/
def IsBoundary (v : Fin c.network.variableCount) : Prop :=
  (∃ k, c.network.input k = v) ∨ ∃ k, c.network.output k = v

instance (v : Fin c.network.variableCount) : Decidable (c.IsBoundary v) := by
  unfold IsBoundary
  infer_instance

/-- The recorded actions of the policy that a decision label reads, if any. -/
def policyActions (l : LabelAttrs) : Option (List ℕ) :=
  (policyName? l.kernelRef).bind fun nm => (c.policyOf nm).map Policy.actions

theorem rawAction_eq (l : LabelAttrs) (vals : List ℕ) :
    c.rawAction l vals =
      ((c.policyActions l).map fun a => a.getD (flatIndex (inputAxes l vals)) 0).getD 0 := by
  unfold rawAction policyActions
  rcases policyName? l.kernelRef with _ | nm
  · rfl
  · dsimp only [Option.bind_some]
    rcases c.policyOf nm with _ | p <;> rfl

theorem actionOf_congr {c d : Certificate} {l : LabelAttrs}
    (h : c.policyActions l = d.policyActions l) (vals : List ℕ) :
    c.actionOf l vals = d.actionOf l vals := by
  unfold actionOf
  rw [rawAction_eq, rawAction_eq, h]

theorem isDecisionGen_eq (g : c.Gen) : c.isDecisionGen g = isPolicy (c.network.label g).kernelRef :=
  rfl

variable {c}

theorem genOf_input (hv : c.network.Valid) (k : Fin c.network.inputs.length) :
    c.genOf (c.network.input k) = none := by
  unfold genOf
  rw [List.find?_eq_none]
  intro g _ hg
  exact hv.2.2.2.2.1 k g (of_decide_eq_true hg).symm

theorem inputOf_input (hv : c.network.Valid) (k : Fin c.network.inputs.length) :
    c.inputOf (c.network.input k) = some k :=
  find?_unique (List.mem_finRange k) (by simp) (fun _ _ h' => hv.2.2.2.1 (of_decide_eq_true h'))

theorem genOf_target (hv : c.network.Valid) (g : c.Gen) :
    c.genOf (c.network.target g) = some g :=
  find?_unique (List.mem_finRange g) (by simp) (fun _ _ h' => hv.2.2.1 (of_decide_eq_true h'))

theorem value_input (hv : c.network.Valid) (x : c.InCoord) (z : c.GenCoord)
    (k : Fin c.network.inputs.length) : c.value x z (c.network.input k) = (x k).val := by
  simp only [value, genOf_input hv, inputOf_input hv]

theorem value_target (hv : c.network.Valid) (x : c.InCoord) (z : c.GenCoord) (g : c.Gen) :
    c.value x z (c.network.target g) = (z g).val := by
  simp only [value, genOf_target hv]

theorem value_lt (hv : c.network.Valid) (x : c.InCoord) (z : c.GenCoord)
    (v : Fin c.network.variableCount) : c.value x z v < dimension (c.network.attrs v) := by
  rcases hv.2.2.2.2.2.1 v with ⟨k, rfl⟩ | ⟨g, rfl⟩
  · rw [value_input hv, hv.2.2.2.2.2.2.1 k]
    exact (x k).isLt
  · rw [value_target hv]
    exact (z g).isLt

theorem cellQ_congr {a b : List Value} (h : a.map Value.toRat = b.map Value.toRat) (k : ℕ) :
    cellQ a k = cellQ b k := by
  unfold cellQ
  rw [← List.getElem?_map, ← List.getElem?_map, h]

end Certificate

/-! ## The colimit witness -/

namespace Colimit

variable (cc : Colimit)

/-- A part index. -/
abbrev Part := Fin cc.parts.length

/-- The part `i`. -/
def part (i : cc.Part) : Certificate := cc.parts[i]

/-- The leg of part `i` (empty when missing). -/
def leg (i : cc.Part) : Leg := cc.legs.getD i ⟨[], [], []⟩

/-- The image of variable `v` of part `i`. -/
def vN (i : cc.Part) (v : ℕ) : ℕ := (cc.leg i).vars.getD v 0

/-- The image of generator `g` of part `i`. -/
def gN (i : cc.Part) (g : ℕ) : ℕ := (cc.leg i).gens.getD g 0

/-- The image of utility `u` of part `i`. -/
def uN (i : cc.Part) (u : ℕ) : ℕ := (cc.leg i).utils.getD u 0

/-- **The legs are a colimit witness**: bijective on generators and utilities, preserving
attributes, labels, targets, parents, tables, policies and scopes, identifying only boundary
variables, and covering the composite's outputs. -/
structure Wired : Prop where
  vars : ∀ i (v : Fin (cc.part i).network.variableCount),
    cc.vN i v < cc.composite.network.variableCount
  gens : ∀ i (g : (cc.part i).Gen), cc.gN i g < cc.composite.network.mechanisms.length
  utils : ∀ i (u : (cc.part i).UIdx), cc.uN i u < cc.composite.utilities.length
  genInj : ∀ i (g : (cc.part i).Gen) i' (g' : (cc.part i').Gen),
    cc.gN i g = cc.gN i' g' → i = i' ∧ g.val = g'.val
  genSurj : ∀ c : cc.composite.Gen, ∃ i, ∃ g : (cc.part i).Gen, cc.gN i g = c.val
  utilInj : ∀ i (u : (cc.part i).UIdx) i' (u' : (cc.part i').UIdx),
    cc.uN i u = cc.uN i' u' → i = i' ∧ u.val = u'.val
  utilSurj : ∀ c : cc.composite.UIdx, ∃ i, ∃ u : (cc.part i).UIdx, cc.uN i u = c.val
  attrs : ∀ i (v : Fin (cc.part i).network.variableCount)
    (h : cc.vN i v < cc.composite.network.variableCount),
    cc.composite.network.attrs ⟨_, h⟩ = (cc.part i).network.attrs v
  labels : ∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
    cc.composite.network.label ⟨_, h⟩ = (cc.part i).network.label g
  targets : ∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
    (cc.composite.network.target ⟨_, h⟩).val = cc.vN i ((cc.part i).network.target g)
  parents : ∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
    (cc.composite.network.parents ⟨_, h⟩).map Fin.val =
      ((cc.part i).network.parents g).map fun v : Fin _ => cc.vN i v.val
  tables : ∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
    (cc.composite.tableOf ⟨_, h⟩).map Value.toRat = ((cc.part i).tableOf g).map Value.toRat
  policies : ∀ i (g : (cc.part i).Gen),
    cc.composite.policyActions ((cc.part i).network.label g) =
      (cc.part i).policyActions ((cc.part i).network.label g)
  scopes : ∀ i (u : (cc.part i).UIdx) (h : cc.uN i u < cc.composite.utilities.length),
    (cc.composite.scope ⟨_, h⟩).map Fin.val = ((cc.part i).scope u).map fun v : Fin _ => cc.vN i v.val
  ucells : ∀ i (u : (cc.part i).UIdx) (h : cc.uN i u < cc.composite.utilities.length),
    (cc.composite.utilities[cc.uN i u].cells).map Value.toRat =
      ((cc.part i).utilities[u].cells).map Value.toRat
  joins : ∀ i (v : Fin (cc.part i).network.variableCount) i'
    (v' : Fin (cc.part i').network.variableCount), cc.vN i v = cc.vN i' v' →
      (i = i' ∧ v.val = v'.val) ∨ ((cc.part i).IsBoundary v ∧ (cc.part i').IsBoundary v')
  outputs : ∀ j : Fin cc.composite.network.outputs.length,
    (∃ k, cc.composite.network.input k = cc.composite.network.output j) ∨
      ∃ i, ∃ v : Fin (cc.part i).network.variableCount,
        (cc.part i).IsBoundary v ∧ cc.vN i v = (cc.composite.network.output j).val

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance : Decidable cc.Wired :=
  decidable_of_iff
    ((∀ i (v : Fin (cc.part i).network.variableCount),
        cc.vN i v < cc.composite.network.variableCount) ∧
      (∀ i (g : (cc.part i).Gen), cc.gN i g < cc.composite.network.mechanisms.length) ∧
      (∀ i (u : (cc.part i).UIdx), cc.uN i u < cc.composite.utilities.length) ∧
      (∀ i (g : (cc.part i).Gen) i' (g' : (cc.part i').Gen),
        cc.gN i g = cc.gN i' g' → i = i' ∧ g.val = g'.val) ∧
      (∀ c : cc.composite.Gen, ∃ i, ∃ g : (cc.part i).Gen, cc.gN i g = c.val) ∧
      (∀ i (u : (cc.part i).UIdx) i' (u' : (cc.part i').UIdx),
        cc.uN i u = cc.uN i' u' → i = i' ∧ u.val = u'.val) ∧
      (∀ c : cc.composite.UIdx, ∃ i, ∃ u : (cc.part i).UIdx, cc.uN i u = c.val) ∧
      (∀ i (v : Fin (cc.part i).network.variableCount)
        (h : cc.vN i v < cc.composite.network.variableCount),
        cc.composite.network.attrs ⟨_, h⟩ = (cc.part i).network.attrs v) ∧
      (∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
        cc.composite.network.label ⟨_, h⟩ = (cc.part i).network.label g) ∧
      (∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
        (cc.composite.network.target ⟨_, h⟩).val = cc.vN i ((cc.part i).network.target g)) ∧
      (∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
        (cc.composite.network.parents ⟨_, h⟩).map Fin.val =
          ((cc.part i).network.parents g).map fun v : Fin _ => cc.vN i v.val) ∧
      (∀ i (g : (cc.part i).Gen) (h : cc.gN i g < cc.composite.network.mechanisms.length),
        (cc.composite.tableOf ⟨_, h⟩).map Value.toRat =
          ((cc.part i).tableOf g).map Value.toRat) ∧
      (∀ i (g : (cc.part i).Gen),
        cc.composite.policyActions ((cc.part i).network.label g) =
          (cc.part i).policyActions ((cc.part i).network.label g)) ∧
      (∀ i (u : (cc.part i).UIdx) (h : cc.uN i u < cc.composite.utilities.length),
        (cc.composite.scope ⟨_, h⟩).map Fin.val =
          ((cc.part i).scope u).map fun v : Fin _ => cc.vN i v.val) ∧
      (∀ i (u : (cc.part i).UIdx) (h : cc.uN i u < cc.composite.utilities.length),
        (cc.composite.utilities[cc.uN i u].cells).map Value.toRat =
          ((cc.part i).utilities[u].cells).map Value.toRat) ∧
      (∀ i (v : Fin (cc.part i).network.variableCount) i'
        (v' : Fin (cc.part i').network.variableCount), cc.vN i v = cc.vN i' v' →
          (i = i' ∧ v.val = v'.val) ∨
            ((cc.part i).IsBoundary v ∧ (cc.part i').IsBoundary v')) ∧
      (∀ j : Fin cc.composite.network.outputs.length,
        (∃ k, cc.composite.network.input k = cc.composite.network.output j) ∨
          ∃ i, ∃ v : Fin (cc.part i).network.variableCount,
            (cc.part i).IsBoundary v ∧ cc.vN i v = (cc.composite.network.output j).val))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ =>
        ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩,
      fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ =>
        ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩⟩

/-! ## Consistent boundary coordinates -/

/-- A choice of input and output coordinates for every part. -/
abbrev Ports := ∀ i : cc.Part, (cc.part i).InCoord × (cc.part i).OutCoord

/-- The rows of the colimit: the composite's input and output rows, then every part's. -/
abbrev Row := (Fin cc.composite.network.inputs.length ⊕ Fin cc.composite.network.outputs.length) ⊕
  Σ i : cc.Part, Fin (cc.part i).network.inputs.length ⊕ Fin (cc.part i).network.outputs.length

/-- The composite variable of a row. -/
def rowVar : cc.Row → ℕ
  | .inl (.inl j) => (cc.composite.network.input j).val
  | .inl (.inr j) => (cc.composite.network.output j).val
  | .inr ⟨i, .inl k⟩ => cc.vN i ((cc.part i).network.input k)
  | .inr ⟨i, .inr k⟩ => cc.vN i ((cc.part i).network.output k)

/-- The 0-based state a row carries. -/
def rowVal (x : cc.composite.InCoord) (y : cc.composite.OutCoord) (t : cc.Ports) : cc.Row → ℕ
  | .inl (.inl j) => (x j).val
  | .inl (.inr j) => (y j).val
  | .inr ⟨i, .inl k⟩ => ((t i).1 k).val
  | .inr ⟨i, .inr k⟩ => ((t i).2 k).val

/-- The parts' boundary coordinates are consistent with the composite's: rows whose variables
have one image carry one state. -/
def Consistent (x : cc.composite.InCoord) (y : cc.composite.OutCoord) (t : cc.Ports) : Prop :=
  ∀ r r', cc.rowVar r = cc.rowVar r' → cc.rowVal x y t r = cc.rowVal x y t r'

instance (x : cc.composite.InCoord) (y : cc.composite.OutCoord) (t : cc.Ports) :
    Decidable (cc.Consistent x y t) := by
  unfold Consistent
  infer_instance

/-! ## The checker -/

/-- **The colimit checker**: every part and the composite accepted, and the legs a colimit
witness. -/
def check (τ : ℚ) : Bool :=
  cc.parts.all (fun c => c.check τ) && cc.composite.check τ && decide cc.Wired

/-- The first failing stage, if any. -/
def firstFailure (τ : ℚ) : Option String :=
  match (List.finRange cc.parts.length).find? (fun i => !(cc.part i).check τ) with
  | some i => some s!"part {i.val}: {((cc.part i).firstFailure τ).getD "unknown stage"}"
  | none =>
    if !cc.composite.check τ then
      some s!"composite: {(cc.composite.firstFailure τ).getD "unknown stage"}"
    else if !decide cc.Wired then
      some "structure (the legs are not a colimit witness of the parts in the composite)"
    else none

theorem part_check {τ : ℚ} (h : cc.check τ = true) (i : cc.Part) : (cc.part i).check τ = true := by
  unfold check at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1 _ (List.getElem_mem _)

theorem composite_check {τ : ℚ} (h : cc.check τ = true) : cc.composite.check τ = true := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem wired_of_check {τ : ℚ} (h : cc.check τ = true) : cc.Wired := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ## The bijection of generator states -/

section Split

variable {cc} (hw : cc.Wired)

/-- The image of a part variable. -/
def vm (i : cc.Part) (v : Fin (cc.part i).network.variableCount) :
    Fin cc.composite.network.variableCount := ⟨cc.vN i v, hw.vars i v⟩

/-- The image of a part generator. -/
def gm (i : cc.Part) (g : (cc.part i).Gen) : cc.composite.Gen := ⟨cc.gN i g, hw.gens i g⟩

/-- The image of a part utility. -/
def um (i : cc.Part) (u : (cc.part i).UIdx) : cc.composite.UIdx := ⟨cc.uN i u, hw.utils i u⟩

theorem gm_bijective : Function.Bijective (fun p : Σ i, (cc.part i).Gen => gm hw p.1 p.2) := by
  constructor
  · rintro ⟨i, g⟩ ⟨i', g'⟩ e
    obtain ⟨rfl, hg⟩ := hw.genInj i g i' g' (congrArg Fin.val e)
    rw [Fin.ext hg]
  · intro c
    obtain ⟨i, g, h⟩ := hw.genSurj c
    exact ⟨⟨i, g⟩, Fin.ext h⟩

theorem um_bijective : Function.Bijective (fun p : Σ i, (cc.part i).UIdx => um hw p.1 p.2) := by
  constructor
  · rintro ⟨i, u⟩ ⟨i', u'⟩ e
    obtain ⟨rfl, hu⟩ := hw.utilInj i u i' u' (congrArg Fin.val e)
    rw [Fin.ext hu]
  · intro c
    obtain ⟨i, u, h⟩ := hw.utilSurj c
    exact ⟨⟨i, u⟩, Fin.ext h⟩

/-- The generators of the composite are those of the parts. -/
noncomputable def gEquiv : (Σ i, (cc.part i).Gen) ≃ cc.composite.Gen :=
  Equiv.ofBijective _ (gm_bijective hw)

/-- The utilities of the composite are those of the parts. -/
noncomputable def uEquiv : (Σ i, (cc.part i).UIdx) ≃ cc.composite.UIdx :=
  Equiv.ofBijective _ (um_bijective hw)

theorem label_gm (i : cc.Part) (g : (cc.part i).Gen) :
    cc.composite.network.label (gm hw i g) = (cc.part i).network.label g :=
  hw.labels i g _

theorem dim_gm (i : cc.Part) (g : (cc.part i).Gen) :
    dimension (cc.composite.network.label (gm hw i g)).result =
      dimension ((cc.part i).network.label g).result := by
  rw [label_gm]

/-- A composite generator state read as the parts' generator states. -/
def split (z : cc.composite.GenCoord) : ∀ i, (cc.part i).GenCoord :=
  fun i g => Fin.cast (dim_gm hw i g) (z (gm hw i g))

theorem split_val (z : cc.composite.GenCoord) (i : cc.Part) (g : (cc.part i).Gen) :
    (split hw z i g).val = (z (gm hw i g)).val := rfl

theorem split_bijective : Function.Bijective (split hw) := by
  constructor
  · intro z z' e
    funext c
    obtain ⟨⟨i, g⟩, rfl⟩ := (gm_bijective hw).2 c
    have := congrArg (fun w => (w i g).val) e
    exact Fin.ext this
  · intro w
    let F : (Σ i, (cc.part i).Gen) → ℕ := fun p => (w p.1 p.2).val
    have hF : ∀ c : cc.composite.Gen,
        F ((gEquiv hw).symm c) < dimension (cc.composite.network.label c).result := by
      intro c
      have hc : gm hw ((gEquiv hw).symm c).1 ((gEquiv hw).symm c).2 = c :=
        (gEquiv hw).apply_symm_apply c
      exact lt_of_lt_of_eq (w ((gEquiv hw).symm c).1 ((gEquiv hw).symm c).2).isLt
        ((dim_gm hw _ _).symm.trans
          (congrArg (fun c' => dimension (cc.composite.network.label c').result) hc))
    refine ⟨fun c => ⟨F ((gEquiv hw).symm c), hF c⟩, ?_⟩
    funext i g
    apply Fin.ext
    rw [split_val]
    change F ((gEquiv hw).symm (gEquiv hw ⟨i, g⟩)) = F ⟨i, g⟩
    rw [Equiv.symm_apply_apply]

end Split

/-! ## Values, weights and rewards factor over the parts -/

section Factor

variable {cc} (hw : cc.Wired) (hC : cc.composite.network.Valid)
  (hP : ∀ i, (cc.part i).network.Valid)

theorem vm_target (i : cc.Part) (g : (cc.part i).Gen) :
    vm hw i ((cc.part i).network.target g) = cc.composite.network.target (gm hw i g) :=
  Fin.ext (hw.targets i g _).symm

theorem attrs_vm (i : cc.Part) (v : Fin (cc.part i).network.variableCount) :
    cc.composite.network.attrs (vm hw i v) = (cc.part i).network.attrs v :=
  hw.attrs i v _

/-- The input coordinates of part `i` that the composite's values give. -/
def xin (x : cc.composite.InCoord) (z : cc.composite.GenCoord) (i : cc.Part) :
    (cc.part i).InCoord := fun k =>
  ⟨cc.composite.value x z (vm hw i ((cc.part i).network.input k)), by
    have h := Certificate.value_lt hC x z (vm hw i ((cc.part i).network.input k))
    rwa [attrs_vm, (hP i).2.2.2.2.2.2.1 k] at h⟩

/-- The output coordinates of part `i` that the composite's values give. -/
def yout (x : cc.composite.InCoord) (z : cc.composite.GenCoord) (i : cc.Part) :
    (cc.part i).OutCoord := fun k =>
  ⟨cc.composite.value x z (vm hw i ((cc.part i).network.output k)), by
    have h := Certificate.value_lt hC x z (vm hw i ((cc.part i).network.output k))
    rwa [attrs_vm, (hP i).2.2.2.2.2.2.2.1 k] at h⟩

/-- **Every part variable takes the composite value of its image.** -/
theorem valueP (x : cc.composite.InCoord) (z : cc.composite.GenCoord) (i : cc.Part)
    (v : Fin (cc.part i).network.variableCount) :
    (cc.part i).value (xin hw hC hP x z i) (split hw z i) v =
      cc.composite.value x z (vm hw i v) := by
  rcases (hP i).2.2.2.2.2.1 v with ⟨k, rfl⟩ | ⟨g, rfl⟩
  · rw [Certificate.value_input (hP i)]
    rfl
  · rw [Certificate.value_target (hP i), split_val, vm_target, Certificate.value_target hC]

theorem parents_gm (i : cc.Part) (g : (cc.part i).Gen) :
    cc.composite.network.parents (gm hw i g) =
      ((cc.part i).network.parents g).map (vm hw i) := by
  apply List.map_injective_iff.2 Fin.val_injective
  rw [List.map_map]
  exact hw.parents i g (hw.gens i g)

theorem weight_gm (x : cc.composite.InCoord) (z : cc.composite.GenCoord) (i : cc.Part)
    (g : (cc.part i).Gen) :
    cc.composite.genWeight x z (gm hw i g) =
      (cc.part i).genWeight (xin hw hC hP x z i) (split hw z i) g := by
  have hvals : (cc.composite.network.parents (gm hw i g)).map (cc.composite.value x z) =
      ((cc.part i).network.parents g).map
        ((cc.part i).value (xin hw hC hP x z i) (split hw z i)) := by
    rw [parents_gm, List.map_map]
    exact List.map_congr_left fun v _ => (valueP hw hC hP x z i v).symm
  have hdec : cc.composite.isDecisionGen (gm hw i g) = (cc.part i).isDecisionGen g := by
    rw [Certificate.isDecisionGen_eq, Certificate.isDecisionGen_eq, label_gm]
  have hact : cc.composite.actionOf (cc.composite.network.label (gm hw i g))
      ((cc.composite.network.parents (gm hw i g)).map (cc.composite.value x z)) =
      (cc.part i).actionOf ((cc.part i).network.label g) (((cc.part i).network.parents g).map
        ((cc.part i).value (xin hw hC hP x z i) (split hw z i))) := by
    rw [label_gm, hvals]
    exact Certificate.actionOf_congr (hw.policies i g) _
  have hch : ∀ s, chanceAt (cc.composite.tableOf (gm hw i g))
      (cc.composite.network.label (gm hw i g))
      ((cc.composite.network.parents (gm hw i g)).map (cc.composite.value x z)) s =
      chanceAt ((cc.part i).tableOf g) ((cc.part i).network.label g)
        (((cc.part i).network.parents g).map
          ((cc.part i).value (xin hw hC hP x z i) (split hw z i))) s := by
    intro s
    rw [label_gm, hvals]
    unfold chanceAt
    exact Certificate.cellQ_congr (hw.tables i g (hw.gens i g)) _
  unfold Certificate.genWeight
  rw [hdec, hact, hch, split_val]

theorem joint_split (x : cc.composite.InCoord) (z : cc.composite.GenCoord) :
    cc.composite.joint x z =
      ∏ i, (cc.part i).joint (xin hw hC hP x z i) (split hw z i) := by
  unfold Certificate.joint
  rw [← Fintype.prod_equiv (gEquiv hw) (fun p => cc.composite.genWeight x z (gm hw p.1 p.2))
    _ (fun _ => rfl), Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun g _ => weight_gm hw hC hP x z i g

theorem scope_um (i : cc.Part) (u : (cc.part i).UIdx) :
    cc.composite.scope (um hw i u) = ((cc.part i).scope u).map (vm hw i) := by
  apply List.map_injective_iff.2 Fin.val_injective
  rw [List.map_map]
  exact hw.scopes i u (hw.utils i u)

theorem reward_split (x : cc.composite.InCoord) (z : cc.composite.GenCoord) :
    cc.composite.reward x z =
      ∑ i, (cc.part i).reward (xin hw hC hP x z i) (split hw z i) := by
  unfold Certificate.reward
  rw [← Fintype.sum_equiv (uEquiv hw) (fun p => utilityAt cc.composite.utilities[um hw p.1 p.2].cells
    (cc.composite.utilityLabel (um hw p.1 p.2))
    ((cc.composite.scope (um hw p.1 p.2)).map (cc.composite.value x z))) _ (fun _ => rfl),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
  have hlab : (cc.composite.utilityLabel (um hw i u)).inputs =
      ((cc.part i).utilityLabel u).inputs := by
    change (cc.composite.scope (um hw i u)).map cc.composite.network.attrs =
      ((cc.part i).scope u).map (cc.part i).network.attrs
    rw [scope_um, List.map_map]
    exact List.map_congr_left fun v _ => attrs_vm hw i v
  have hvals : (cc.composite.scope (um hw i u)).map (cc.composite.value x z) =
      ((cc.part i).scope u).map ((cc.part i).value (xin hw hC hP x z i) (split hw z i)) := by
    rw [scope_um, List.map_map]
    exact List.map_congr_left fun v _ => (valueP hw hC hP x z i v).symm
  unfold utilityAt
  rw [hlab, hvals]
  exact Certificate.cellQ_congr (hw.ucells i u _) _

/-- The parts' boundary coordinates that the composite's values give. -/
def tz (x : cc.composite.InCoord) (z : cc.composite.GenCoord) : cc.Ports :=
  fun i => (xin hw hC hP x z i, yout hw hC hP x z i)

theorem reads_tz (x : cc.composite.InCoord) (z : cc.composite.GenCoord) (i : cc.Part) :
    (cc.part i).Reads (xin hw hC hP x z i) (split hw z i) (yout hw hC hP x z i) := by
  intro k
  rw [valueP]
  rfl

/-- Every row of the choice `tz`, other than the composite's outputs, carries the composite
value of its variable. -/
theorem rowVal_tz (x : cc.composite.InCoord) (y : cc.composite.OutCoord)
    (z : cc.composite.GenCoord) (r : cc.Row) (hr : ∀ j, r ≠ .inl (.inr j))
    (hv : cc.rowVar r < cc.composite.network.variableCount) :
    cc.rowVal x y (tz hw hC hP x z) r = cc.composite.value x z ⟨cc.rowVar r, hv⟩ := by
  rcases r with (j | j) | ⟨i, k | k⟩
  · change (x j).val = _
    rw [← Certificate.value_input hC x z j]
    rfl
  · exact absurd rfl (hr j)
  · rfl
  · rfl

/-- **The choice `tz` is consistent exactly when the composite reads `y`.** -/
theorem consistent_tz_iff (x : cc.composite.InCoord) (y : cc.composite.OutCoord)
    (z : cc.composite.GenCoord) :
    cc.Consistent x y (tz hw hC hP x z) ↔ cc.composite.Reads x z y := by
  have hlt : ∀ r : cc.Row, cc.rowVar r < cc.composite.network.variableCount := by
    rintro ((j | j) | ⟨i, k | k⟩)
    · exact (cc.composite.network.input j).isLt
    · exact (cc.composite.network.output j).isLt
    · exact hw.vars i _
    · exact hw.vars i _
  constructor
  · intro hcons j
    rcases hw.outputs j with ⟨k, hk⟩ | ⟨i, v, hb, hv⟩
    · have := hcons (.inl (.inr j)) (.inl (.inl k)) (by simp [rowVar, hk])
      change (y j).val = (x k).val at this
      rw [this, ← hk, Certificate.value_input hC]
    · rcases hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have := hcons (.inl (.inr j)) (.inr ⟨i, .inl k⟩) (by simp only [rowVar]; exact hv.symm)
        change (y j).val = cc.composite.value x z (vm hw i ((cc.part i).network.input k)) at this
        rw [this]
        exact congrArg _ (Fin.ext hv)
      · have := hcons (.inl (.inr j)) (.inr ⟨i, .inr k⟩) (by simp only [rowVar]; exact hv.symm)
        change (y j).val = cc.composite.value x z (vm hw i ((cc.part i).network.output k)) at this
        rw [this]
        exact congrArg _ (Fin.ext hv)
  · intro hreads
    have hall : ∀ r, cc.rowVal x y (tz hw hC hP x z) r =
        cc.composite.value x z ⟨cc.rowVar r, hlt r⟩ := by
      intro r
      by_cases hr : ∃ j, r = .inl (.inr j)
      · obtain ⟨j, rfl⟩ := hr
        exact hreads j
      · push Not at hr
        exact rowVal_tz hw hC hP x y z r hr (hlt r)
    intro r r' e
    rw [hall r, hall r']
    exact congrArg _ (Fin.ext e)

/-- **The only consistent choice compatible with the parts' outputs is `tz`.** -/
theorem ports_unique (x : cc.composite.InCoord) (y : cc.composite.OutCoord)
    (z : cc.composite.GenCoord) (t : cc.Ports) (hcons : cc.Consistent x y t)
    (hreads : ∀ i, (cc.part i).Reads (t i).1 (split hw z i) (t i).2) :
    t = tz hw hC hP x z := by
  have hin : ∀ i, (t i).1 = xin hw hC hP x z i := by
    intro i
    funext k
    apply Fin.ext
    change ((t i).1 k).val = cc.composite.value x z (vm hw i ((cc.part i).network.input k))
    rcases hC.2.2.2.2.2.1 (vm hw i ((cc.part i).network.input k)) with ⟨j, hj⟩ | ⟨c, hc⟩
    · have := hcons (.inr ⟨i, .inl k⟩) (.inl (.inl j))
        (by simp only [rowVar]; exact (congrArg Fin.val hj).symm)
      change ((t i).1 k).val = (x j).val at this
      rw [this, ← hj, Certificate.value_input hC]
    · obtain ⟨⟨i', g'⟩, rfl⟩ := (gm_bijective hw).2 c
      have hvt : vm hw i ((cc.part i).network.input k) =
          vm hw i' ((cc.part i').network.target g') := by
        rw [vm_target]
        exact hc.symm
      rcases hw.joins i _ i' _ (congrArg Fin.val hvt) with ⟨rfl, he⟩ | ⟨-, hb⟩
      · exact absurd (Fin.ext he : (cc.part i).network.input k = (cc.part i).network.target g')
          ((hP i).2.2.2.2.1 k g')
      · rcases hb with ⟨k', hk'⟩ | ⟨k', hk'⟩
        · exact absurd hk' ((hP i').2.2.2.2.1 k' g')
        · have := hcons (.inr ⟨i, .inl k⟩) (.inr ⟨i', .inr k'⟩)
            (by simp only [rowVar]; rw [hk']; exact congrArg Fin.val hvt)
          change ((t i).1 k).val = ((t i').2 k').val at this
          rw [this, hreads i' k', hk', Certificate.value_target (hP i'), split_val, ← hc,
            Certificate.value_target hC]
  funext i
  refine Prod.ext (hin i) ?_
  funext k
  apply Fin.ext
  change ((t i).2 k).val = cc.composite.value x z (vm hw i ((cc.part i).network.output k))
  rw [hreads i k, hin i, valueP]

end Factor

/-! ## The exact semantics of the composite -/

theorem sum_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {κ : ι → Type}
    [∀ i, Fintype (κ i)] (A R : ∀ i, κ i → ℚ) :
    ∑ i, (∑ a, A i a * R i a) * ∏ j ∈ Finset.univ.erase i, ∑ a, A j a =
      ∑ w : (∀ i, κ i), (∏ i, A i (w i)) * ∑ i, R i (w i) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hB : ∀ w : (∀ i, κ i), (∏ j, A j (w j)) * R i (w i) =
      ∏ j, (A j (w j) * if j = i then R j (w j) else 1) := by
    intro w
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
  simp only [hB]
  rw [← Fintype.prod_sum (fun j a => A j a * if j = i then R j a else 1),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [if_pos]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [if_neg (Finset.ne_of_mem_erase hj), mul_one]

section Exact

variable {cc} (hw : cc.Wired) (hC : cc.composite.network.Valid)
  (hP : ∀ i, (cc.part i).network.Valid)

include hw hC hP

open Classical in
/-- **The composite's probability is the junction sum of the parts'**: exactly, the
composite's `exactK` at `(x, y)` is the sum, over the parts' boundary coordinates consistent
with `x` and `y`, of the product of the parts' `exactK`. -/
theorem colimit_exactK (x : cc.composite.InCoord) (y : cc.composite.OutCoord) :
    cc.composite.exactK x y = ∑ t : cc.Ports,
      if cc.Consistent x y t then ∏ i, (cc.part i).exactK (t i).1 (t i).2 else 0 := by
  have hrhs : ∀ t : cc.Ports, (if cc.Consistent x y t then
      ∏ i, (cc.part i).exactK (t i).1 (t i).2 else 0) =
      ∑ w : (∀ i, (cc.part i).GenCoord), if cc.Consistent x y t ∧
        (∀ i, (cc.part i).Reads (t i).1 (w i) (t i).2) then
          ∏ i, (cc.part i).joint (t i).1 (w i) else 0 := by
    intro t
    unfold Certificate.exactK
    rw [Fintype.prod_sum]
    by_cases hc : cc.Consistent x y t
    · rw [if_pos hc]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.prod_ite_zero]
      simp only [Finset.mem_univ, true_implies, hc, true_and]
    · rw [if_neg hc]
      simp [hc]
  simp only [hrhs]
  rw [Finset.sum_comm]
  unfold Certificate.exactK
  refine Fintype.sum_bijective (split hw) (split_bijective hw) _ _ fun z => ?_
  symm
  rw [Finset.sum_eq_single (tz hw hC hP x z)]
  · by_cases hr : cc.composite.Reads x z y
    · rw [if_pos hr, if_pos ⟨(consistent_tz_iff hw hC hP x y z).2 hr,
        reads_tz hw hC hP x z⟩, joint_split hw hC hP]
      rfl
    · rw [if_neg hr, if_neg fun h => hr ((consistent_tz_iff hw hC hP x y z).1 h.1)]
  · intro t _ ht
    rw [if_neg]
    exact fun h => ht (ports_unique hw hC hP x y z t h.1 h.2)
  · exact fun h => absurd (Finset.mem_univ _) h

open Classical in
/-- **The composite's reward is the junction sum of the parts'** in the expectation
semiring: exactly, the composite's `exactW` at `(x, y)` is the sum, over the consistent
boundary coordinates, of `Σ_i W_i Π_{j ≠ i} K_j`. -/
theorem colimit_exactW (x : cc.composite.InCoord) (y : cc.composite.OutCoord) :
    cc.composite.exactW x y = ∑ t : cc.Ports,
      if cc.Consistent x y t then ∑ i, (cc.part i).exactW (t i).1 (t i).2 *
        ∏ j ∈ Finset.univ.erase i, (cc.part j).exactK (t j).1 (t j).2 else 0 := by
  have hrhs : ∀ t : cc.Ports, (if cc.Consistent x y t then ∑ i, (cc.part i).exactW (t i).1 (t i).2 *
        ∏ j ∈ Finset.univ.erase i, (cc.part j).exactK (t j).1 (t j).2 else 0) =
      ∑ w : (∀ i, (cc.part i).GenCoord), if cc.Consistent x y t ∧
        (∀ i, (cc.part i).Reads (t i).1 (w i) (t i).2) then
          (∏ i, (cc.part i).joint (t i).1 (w i)) *
            ∑ i, (cc.part i).reward (t i).1 (w i) else 0 := by
    intro t
    by_cases hc : cc.Consistent x y t
    · rw [if_pos hc]
      have hW : ∀ i, (cc.part i).exactW (t i).1 (t i).2 = ∑ a, (if (cc.part i).Reads (t i).1 a
          (t i).2 then (cc.part i).joint (t i).1 a else 0) * (cc.part i).reward (t i).1 a := by
        intro i
        unfold Certificate.exactW
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
      have hK : ∀ i, (cc.part i).exactK (t i).1 (t i).2 = ∑ a, (if (cc.part i).Reads (t i).1 a
          (t i).2 then (cc.part i).joint (t i).1 a else 0) := fun i => rfl
      simp only [hW, hK]
      rw [sum_mul_prod_erase (fun i a => if (cc.part i).Reads (t i).1 a (t i).2 then
        (cc.part i).joint (t i).1 a else 0) (fun i a => (cc.part i).reward (t i).1 a)]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.prod_ite_zero]
      simp only [Finset.mem_univ, true_implies, hc, true_and]
      split_ifs <;> simp
    · rw [if_neg hc]
      simp [hc]
  simp only [hrhs]
  rw [Finset.sum_comm]
  unfold Certificate.exactW
  refine Fintype.sum_bijective (split hw) (split_bijective hw) _ _ fun z => ?_
  symm
  rw [Finset.sum_eq_single (tz hw hC hP x z)]
  · by_cases hr : cc.composite.Reads x z y
    · rw [if_pos hr, if_pos ⟨(consistent_tz_iff hw hC hP x y z).2 hr,
        reads_tz hw hC hP x z⟩, joint_split hw hC hP, reward_split hw hC hP]
      rfl
    · rw [if_neg hr, if_neg fun h => hr ((consistent_tz_iff hw hC hP x y z).1 h.1)]
  · intro t _ ht
    rw [if_neg]
    exact fun h => ht (ports_unique hw hC hP x y z t h.1 h.2)
  · exact fun h => absurd (Finset.mem_univ _) h

end Exact

/-! ## Soundness on acceptance -/

section Sound

variable {cc} {τ : ℚ}

theorem valid_composite (h : cc.check τ = true) : cc.composite.network.Valid :=
  (Network.check_iff _).1 (Certificate.network_check_of_check (cc.composite_check h))

theorem valid_part (h : cc.check τ = true) (i : cc.Part) : (cc.part i).network.Valid :=
  (Network.check_iff _).1 (Certificate.network_check_of_check (cc.part_check h i))

open Classical in
/-- **Exact semantics on acceptance**: if the colimit checker accepts, the composite's exact
probability is the junction sum of the parts'. -/
theorem colimit_sound_K (h : cc.check τ = true) (x : cc.composite.InCoord)
    (y : cc.composite.OutCoord) :
    cc.composite.exactK x y = ∑ t : cc.Ports,
      if cc.Consistent x y t then ∏ i, (cc.part i).exactK (t i).1 (t i).2 else 0 :=
  colimit_exactK (cc.wired_of_check h) (valid_composite h) (valid_part h) x y

open Classical in
/-- **Exact semantics on acceptance**, for the reward. -/
theorem colimit_sound_W (h : cc.check τ = true) (x : cc.composite.InCoord)
    (y : cc.composite.OutCoord) :
    cc.composite.exactW x y = ∑ t : cc.Ports,
      if cc.Consistent x y t then ∑ i, (cc.part i).exactW (t i).1 (t i).2 *
        ∏ j ∈ Finset.univ.erase i, (cc.part j).exactK (t j).1 (t j).2 else 0 :=
  colimit_exactW (cc.wired_of_check h) (valid_composite h) (valid_part h) x y

end Sound

end Colimit

/-! ## Decoding -/

namespace Json

open Lean (Json)
open BayesianNetworksProofs.Raw (object)
open InfluenceDiagramsProofs.DVECertificate (get getArr natOf strOf)

/-- Decode a leg: exactly the keys `variables`, `generators` and `utilities`, each an array
of natural numbers. -/
def decodeLeg (j : Json) : Except String Leg := do
  let o ← object "leg" 3 j
  let vs ← getArr o "variables" (fun _ => natOf)
  let gs ← getArr o "generators" (fun _ => natOf)
  let us ← getArr o "utilities" (fun _ => natOf)
  pure ⟨vs, gs, us⟩

/-- Decode a colimit certificate: exactly the keys `format`, `operation`, `parts`,
`composite` and `legs`. -/
def decodeColimit (j : Json) : Except String Colimit := do
  let o ← object "colimit" 5 j
  get o "format" (constant colimitFormatName)
  let op ← get o "operation" strOf
  let ps ← getArr o "parts" (fun _ => decodeCertificate)
  let c ← get o "composite" decodeCertificate
  let ls ← getArr o "legs" (fun _ => decodeLeg)
  pure ⟨op, ps, c, ls⟩

/-- Read a colimit certificate from its text. -/
def readColimit (text : String) : Except String Colimit := do
  let j ← OpenNet.CertificateSyntax.parse text
  decodeColimit j

end Json

end OpenInfluence.RewardCertificate
