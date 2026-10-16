import CategoricalInfluenceDiagramsProofs.Basic

/-!
# Decision and utility generators on the typed open-network syntax

ADR 0010's typed open-network syntax (`OpenNet.Net X Y`) has one kind of generator: a
mechanism with a label, an ordered list of typed parents and one typed output. This module
extends it in the two ways ADR 0018 (decision 5) asks for.

* **Decision generators.** An influence-diagram signature (`IDSignature`) marks each
  generator label as a chance mechanism or a decision (`isDecision`). A decision generator
  is an ordinary generator of the underlying net whose label is a decision label; its
  ordered parent list is its list of **information ports**, so a policy for it is a
  function of the values on those ports (`Interpretation.lean`).
* **Utility generators.** A signature also has utility labels, each with an ordered list
  of input types (`uinputs`). An open influence diagram (`IDNet X Y`) is a net together
  with a finite set of utility generators, each with a label and an ordered, typed list
  of the net's variables (its **scope**). A utility reads its scope and produces no
  variable, so utilities never cross a boundary; their reward crosses only through the
  semantics, as ADR 0018 requires.

Serial composition (`IDNet.comp`) and tensor (`IDNet.tensor`) are those of the underlying
nets, with the utility generators of the two components placed side by side and their
scopes substituted along the nets' variable maps (`Net.left`, `Net.right`, `Net.tinl`,
`Net.tinr`). Identities have no generators and no utilities. Every net embeds with no
utility (`IDNet.ofNet`), and the atomic generators are `IDNet.generator` (one chance or
decision generator on its own inputs) and `IDNet.utility` (one utility on a scope of an
interface, passing the interface through).

**Scope.** The syntax is the full generality of `OpenNet.Net`: arbitrary finite nets, not
only terms built from generators. It is **not** quotiented by structural isomorphism, so
the functoriality theorems of `Interpretation.lean` are equations on representatives
rather than a Mathlib `Functor` out of a syntax category. Observability flags
(`Basic.lean`) are not part of this syntax: the fixed-strategy semantics does not read
them, and information locality is a separate side condition on strategies.
-/

set_option autoImplicit false

namespace OpenInfluence

/-- A signature for open influence diagrams: an `OpenNet` signature whose labels are
chance mechanisms or decisions, together with utility labels and their input types. -/
structure IDSignature extends OpenNet.Signature where
  /-- Whether generators with this label are decisions (`true`) or chance mechanisms. -/
  isDecision : Label → Bool
  /-- Utility labels. -/
  ULabel : Type
  /-- The ordered input types of a utility label. -/
  uinputs : ULabel → List Ty

/-- The finite typed interfaces of a signature, those of the underlying `OpenNet`
signature. -/
abbrev IDSignature.Iface (S : IDSignature) := OpenNet.Interface S.toSignature

variable {S : IDSignature}

/-- An open influence diagram `X → Y`: a typed open net (whose generators are chance
mechanisms and decisions) with a finite set of utility generators, each reading an ordered,
typed list of the net's variables. -/
structure IDNet (X Y : S.Iface) where
  /-- The underlying open net of chance and decision generators. -/
  net : OpenNet.Net X Y
  /-- The utility generators. -/
  UGen : Type
  /-- There are finitely many utility generators. -/
  ufinite : Fintype UGen
  /-- The label of each utility generator. -/
  ulabel : UGen → S.ULabel
  /-- The ordered scope of each utility generator: input ports or internal generators. -/
  uparents : UGen → List net.Var
  /-- Each scope has the input types of its label. -/
  uparents_typed : ∀ u, (uparents u).map net.varType = S.uinputs (ulabel u)

attribute [instance] IDNet.ufinite

namespace IDNet

variable {X Y Z X' Y' : S.Iface}

/-- A generator of the underlying net is a decision when its label is a decision label. -/
def IsDecision (f : IDNet X Y) (a : f.net.Gen) : Prop := S.isDecision (f.net.label a) = true

/-- The information ports of a generator: its ordered parents. -/
def info (f : IDNet X Y) (a : f.net.Gen) : List f.net.Var := f.net.parents a

/-- An open net with no utility generators. -/
def ofNet (n : OpenNet.Net X Y) : IDNet X Y where
  net := n
  UGen := Empty
  ufinite := inferInstance
  ulabel := Empty.elim
  uparents := Empty.elim
  uparents_typed u := u.elim

/-- The identity: pure wiring, with no generators and no utilities. -/
def identity (X : S.Iface) : IDNet X X := ofNet (OpenNet.Net.identity X)

/-- Serial composition: compose the nets, and keep the utilities of both components with
their scopes substituted along the gluing. -/
def comp (f : IDNet X Y) (g : IDNet Y Z) : IDNet X Z where
  net := f.net.comp g.net
  UGen := f.UGen ⊕ g.UGen
  ufinite := inferInstance
  ulabel := Sum.elim f.ulabel g.ulabel
  uparents := Sum.elim
    (fun u => (f.uparents u).map (OpenNet.Net.left f.net g.net))
    (fun u => (g.uparents u).map (OpenNet.Net.right f.net g.net))
  uparents_typed := by
    intro u
    cases u with
    | inl u =>
      change ((f.uparents u).map (OpenNet.Net.left f.net g.net)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (f.uparents u).map k)
        (funext (OpenNet.Net.left_typed f.net g.net))).trans (f.uparents_typed u)
    | inr u =>
      change ((g.uparents u).map (OpenNet.Net.right f.net g.net)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (g.uparents u).map k)
        (funext (OpenNet.Net.right_typed f.net g.net))).trans (g.uparents_typed u)

/-- Tensor: place the nets side by side, and keep the utilities of both components with
their scopes reindexed into the disjoint union. -/
def tensor (f : IDNet X Y) (g : IDNet X' Y') : IDNet (X.sum X') (Y.sum Y') where
  net := f.net.tensor g.net
  UGen := f.UGen ⊕ g.UGen
  ufinite := inferInstance
  ulabel := Sum.elim f.ulabel g.ulabel
  uparents := Sum.elim
    (fun u => (f.uparents u).map (OpenNet.Net.tinl f.net g.net))
    (fun u => (g.uparents u).map (OpenNet.Net.tinr f.net g.net))
  uparents_typed := by
    intro u
    cases u with
    | inl u =>
      change ((f.uparents u).map (OpenNet.Net.tinl f.net g.net)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (f.uparents u).map k)
        (funext (OpenNet.Net.tinl_typed f.net g.net))).trans (f.uparents_typed u)
    | inr u =>
      change ((g.uparents u).map (OpenNet.Net.tinr f.net g.net)).map _ = _
      rw [List.map_map]
      exact (congrArg (fun k => (g.uparents u).map k)
        (funext (OpenNet.Net.tinr_typed f.net g.net))).trans (g.uparents_typed u)

@[simp] theorem comp_net (f : IDNet X Y) (g : IDNet Y Z) : (f.comp g).net = f.net.comp g.net :=
  rfl

@[simp] theorem tensor_net (f : IDNet X Y) (g : IDNet X' Y') :
    (f.tensor g).net = f.net.tensor g.net := rfl

/-! ### Atomic generators -/

/-- The interface of the ordered input types of a generator label. -/
def inputIface (l : S.Label) : S.Iface :=
  ⟨Fin (S.inputs l).length, inferInstance, fun i => (S.inputs l).get i⟩

/-- The one-port interface of the output type of a generator label. -/
def outputIface (l : S.Label) : S.Iface := ⟨Unit, inferInstance, fun _ => S.result l⟩

/-- A single chance or decision generator labelled `l`, reading its input ports in order
(for a decision, its information ports) and exposing its output. -/
def generator (l : S.Label) : IDNet (inputIface l) (outputIface l) :=
  ofNet {
    Gen := Unit
    finite := inferInstance
    label := fun _ => l
    parents := fun _ => List.ofFn (fun i => Sum.inl i)
    output := fun _ => Sum.inr ()
    parents_typed := fun _ => by
      rw [List.map_ofFn]
      exact List.ofFn_get (S.inputs l)
    output_typed := fun _ => rfl
    acyclic := ⟨fun _ => 0, fun _ _ h => by simp at h⟩ }

/-- A single utility generator labelled `u` reading the ports `scope` of `X`, which it
passes through unchanged. -/
def utility (X : S.Iface) (u : S.ULabel) (scope : List X.Port)
    (h : scope.map X.type = S.uinputs u) : IDNet X X where
  net := OpenNet.Net.identity X
  UGen := Unit
  ufinite := inferInstance
  ulabel _ := u
  uparents _ := scope.map Sum.inl
  uparents_typed _ := by
    rw [List.map_map]
    exact h

end IDNet

end OpenInfluence
