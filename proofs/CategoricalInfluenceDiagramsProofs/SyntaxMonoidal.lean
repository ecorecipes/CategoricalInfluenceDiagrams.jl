import CategoricalInfluenceDiagramsProofs.SyntaxCategory
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The symmetric monoidal category of open influence diagrams, and a monoidal semantics

`SyntaxCategory` quotients open influence diagrams by isomorphism for serial composition.
This module adds the tensor, following CategoricalBayesianNetworks' construction for nets
(`OpenNet.monoidal`, `OpenNet.symmetric`) and extending every generator bijection to the
utility generators.

**The tensor up to isomorphism.** Isomorphism is a congruence for the tensor
(`IDNet.Iso.tensor`), and the interchange law holds up to isomorphism
(`IDNet.interchange_iso`), by the same reordering of the four summands of generators and of
utility generators.

**Wiring and coherence.** Pure wiring (`IDNet.wire`) has no generators and no utilities.
Wiring composes and tensors as functions on ports do (`wire_comp`, `wire_tensor`), and a
diagram slides through wiring whenever a bijection of generators and of utilities matches
labels, ordered parents, outputs and scopes read through the ports (`IDNet.slide`,
`wire_slide`). The associator, unitors and symmetry are wiring along the canonical
bijections of ports (`assocIso`, `leftIso`, `rightIso`, `swapIso`); their naturality is a
slide, and the pentagon, triangle, hexagons and involutivity reduce to equations between
functions on ports. So `IDCat S` is a symmetric monoidal category (`IDCat.monoidal`,
`IDCat.symmetric`), with no equations in the quotient beyond isomorphism.

**A strong monoidal semantics.** For every behavioural strategy the semantic functor
`interpretFunctor β : IDCat S ⥤ FinRew` is strong monoidal and braided
(`IDInterpretation.monoidalFunctor`, `braidedFunctor`): the comparison maps are the
canonical bijections between pairs of boundary assignments and assignments of a disjoint
union (`stateTensor`, `stateUnit`), lifted with zero reward, and their naturality is
`interpretB_tensor`. Wiring is interpreted as the deterministic reindexing with zero reward
(`interpretB_wire`).
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open CategoryTheory MonoidalCategory OpenNet FiniteKernelsProofs.Finite

variable {S : IDSignature} {X Y Z W X' Y' Z' : S.Iface}

namespace IDNet

/-- Pure wiring: no generators and no utilities. -/
def wire (p : Y.Port → X.Port) (hp : ∀ y, X.type (p y) = Y.type y) : IDNet X Y :=
  ofNet (Net.wire p hp)

/-- The tensor respects isomorphism. -/
def Iso.tensor {f f' : IDNet X Y} {g g' : IDNet X' Y'} (a : Iso f f') (b : Iso g g') :
    Iso (f.tensor g) (f'.tensor g') where
  net := a.net.tensor b.net
  ugen := Equiv.sumCongr a.ugen b.ugen
  ulabel u := by
    cases u with
    | inl u => exact a.ulabel u
    | inr u => exact b.ulabel u
  uparents u := by
    cases u with
    | inl u =>
      change (f'.uparents (a.ugen u)).map _ = ((f.uparents u).map _).map _
      rw [a.uparents, List.map_map, List.map_map]
      congr 1; funext v; cases v <;> rfl
    | inr u =>
      change (g'.uparents (b.ugen u)).map _ = ((g.uparents u).map _).map _
      rw [b.uparents, List.map_map, List.map_map]
      congr 1; funext v; cases v <;> rfl

/-- **The interchange law up to isomorphism.** -/
def interchange_iso (f : IDNet X Y) (g : IDNet X' Y') (h : IDNet Y Z) (k : IDNet Y' Z') :
    Iso ((f.tensor g).comp (h.tensor k)) ((f.comp h).tensor (g.comp k)) where
  net := Net.interchange_iso f.net g.net h.net k.net
  ugen := Net.exchange f.UGen g.UGen h.UGen k.UGen
  ulabel u := by rcases u with (a | b) | (c | d) <;> rfl
  uparents u := by
    rcases u with (a | b) | (c | d)
    · change ((f.uparents a).map _).map _ = (((f.uparents a).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((g.uparents b).map _).map _ = (((g.uparents b).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((h.uparents c).map _).map _ = (((h.uparents c).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        cases e : f.net.output y <;>
          (simp [Net.comp, Net.tensor, Net.right, Net.left, Net.tinl, Function.comp_def, e];
            try rfl)
      | inr c => rfl
    · change ((k.uparents d).map _).map _ = (((k.uparents d).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        cases e : g.net.output y <;>
          (simp [Net.comp, Net.tensor, Net.right, Net.left, Net.tinr, Function.comp_def, e];
            try rfl)
      | inr d => rfl

/-- **Sliding through wiring**: a bijection of generators and of utility generators that
matches labels, ordered parents, outputs and scopes read through the ports gives an
isomorphism `f ; wire o ≅ wire i ; g`. -/
def slide (f : IDNet X Y) (g : IDNet X' Y') (i : X'.Port → X.Port) (o : Y'.Port → Y.Port)
    (hi : ∀ x, X.type (i x) = X'.type x) (ho : ∀ y, Y.type (o y) = Y'.type y)
    (e : f.net.Gen ≃ g.net.Gen) (hl : ∀ a, g.net.label (e a) = f.net.label a)
    (hp : ∀ a, (g.net.parents (e a)).map (Sum.map i id) = (f.net.parents a).map (Sum.map id e))
    (hout : ∀ y, Sum.map i id (g.net.output y) = Sum.map id e (f.net.output (o y)))
    (eu : f.UGen ≃ g.UGen) (hul : ∀ u, g.ulabel (eu u) = f.ulabel u)
    (hup : ∀ u, (g.uparents (eu u)).map (Sum.map i id) = (f.uparents u).map (Sum.map id e)) :
    Iso (f.comp (wire o ho)) ((wire i hi).comp g) where
  net := Net.slide f.net g.net i o hi ho e hl hp hout
  ugen := ((Equiv.sumEmpty f.UGen Empty).trans eu).trans (Equiv.emptySum Empty g.UGen).symm
  ulabel u := by
    rcases u with u | u
    · exact hul u
    · exact u.elim
  uparents u := by
    rcases u with u | u
    · change (g.uparents (eu u)).map _ = (((f.uparents u).map _).map _)
      have h := congrArg (List.map (Sum.map id (Sum.inr : g.net.Gen → Empty ⊕ g.net.Gen)))
        (hup u)
      simp only [List.map_map] at h ⊢
      have L : Net.right (Net.wire i hi) g.net =
          (Sum.map id (Sum.inr : g.net.Gen → Empty ⊕ g.net.Gen)) ∘ Sum.map i id := by
        funext v; cases v <;> rfl
      have R : (Sum.map id (((Equiv.sumEmpty f.net.Gen Empty).trans e).trans
          (Equiv.emptySum Empty g.net.Gen).symm)) ∘ Net.left f.net (Net.wire o ho) =
          (Sum.map id (Sum.inr : g.net.Gen → Empty ⊕ g.net.Gen)) ∘ Sum.map id e := by
        funext v; cases v <;> rfl
      exact (congrArg (fun k => (g.uparents (eu u)).map k) L).trans
        (h.trans (congrArg (fun k => (f.uparents u).map k) R).symm)
    · exact u.elim

end IDNet

/-! ### The tensor and wiring on classes -/

/-- The tensor of classes. -/
def IDHom.tensor (f : IDHom X Y) (g : IDHom X' Y') : IDHom (X.sum X') (Y.sum Y') :=
  Quotient.liftOn₂ f g (fun a b => IDHom.mk (a.tensor b))
    (fun _ _ _ _ ⟨a⟩ ⟨b⟩ => Quotient.sound ⟨a.tensor b⟩)

@[simp] theorem IDHom.tensor_mk (f : IDNet X Y) (g : IDNet X' Y') :
    IDHom.tensor (IDHom.mk f) (IDHom.mk g) = IDHom.mk (f.tensor g) := rfl

theorem IDHom.tensor_comp (f : IDHom X Y) (g : IDHom X' Y') (h : IDHom Y Z) (k : IDHom Y' Z') :
    IDHom.comp (IDHom.tensor f g) (IDHom.tensor h k) =
      IDHom.tensor (IDHom.comp f h) (IDHom.comp g k) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    induction h, k using Quotient.inductionOn₂ with | _ h k =>
      exact Quotient.sound ⟨IDNet.interchange_iso f g h k⟩

/-- Wiring as a class. -/
def IDHom.wire (p : Y.Port → X.Port) (hp : ∀ y, X.type (p y) = Y.type y) : IDHom X Y :=
  IDHom.mk (IDNet.wire p hp)

theorem IDHom.wire_congr {p q : Y.Port → X.Port} {hp hq} (h : p = q) :
    IDHom.wire p hp = IDHom.wire q hq := by subst q; rfl

theorem IDHom.wire_id (X : S.Iface) :
    IDHom.wire (id : X.Port → X.Port) (fun _ => rfl) = IDHom.mk (IDNet.identity X) := rfl

theorem IDHom.wire_comp (p : Y.Port → X.Port) (q : Z.Port → Y.Port) (hp hq) :
    IDHom.comp (IDHom.wire p hp) (IDHom.wire q hq) =
      IDHom.wire (p ∘ q) (fun z => (hp (q z)).trans (hq z)) := by
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.emptySum Empty Empty, ?_, ?_, ?_⟩, Equiv.emptySum Empty Empty, ?_, ?_⟩⟩
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim
  · intro z; rfl
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim

theorem IDHom.wire_tensor (p : Y.Port → X.Port) (q : Y'.Port → X'.Port) (hp hq) :
    IDHom.tensor (IDHom.wire p hp) (IDHom.wire q hq) =
      IDHom.wire (Sum.map p q) (fun y => by
        cases y with
        | inl y => exact hp y
        | inr y => exact hq y) := by
  apply Quotient.sound
  refine ⟨⟨⟨Equiv.emptySum Empty Empty, ?_, ?_, ?_⟩, Equiv.emptySum Empty Empty, ?_, ?_⟩⟩
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim
  · rintro (y | y) <;> rfl
  · rintro (a | a) <;> exact a.elim
  · rintro (a | a) <;> exact a.elim

theorem IDHom.wire_slide (f : IDNet X Y) (g : IDNet X' Y') (i : X'.Port → X.Port)
    (o : Y'.Port → Y.Port) (hi ho) (e : f.net.Gen ≃ g.net.Gen)
    (hl : ∀ a, g.net.label (e a) = f.net.label a)
    (hp : ∀ a, (g.net.parents (e a)).map (Sum.map i id) = (f.net.parents a).map (Sum.map id e))
    (hout : ∀ y, Sum.map i id (g.net.output y) = Sum.map id e (f.net.output (o y)))
    (eu : f.UGen ≃ g.UGen) (hul : ∀ u, g.ulabel (eu u) = f.ulabel u)
    (hup : ∀ u, (g.uparents (eu u)).map (Sum.map i id) = (f.uparents u).map (Sum.map id e)) :
    IDHom.comp (IDHom.mk f) (IDHom.wire o ho) = IDHom.comp (IDHom.wire i hi) (IDHom.mk g) :=
  Quotient.sound ⟨IDNet.slide f g i o hi ho e hl hp hout eu hul hup⟩

/-! ### The structure isomorphisms and their naturality -/

namespace IDCat

/-- The tensor of objects. -/
def tensorObj (A B : IDCat S) : IDCat S := ⟨A.iface.sum B.iface⟩

/-- The unit object: the empty interface. -/
def unit (S : IDSignature) : IDCat S := ⟨Interface.empty S.toSignature⟩

/-- Wiring between objects. -/
def wireHom {A B : IDCat S} (p : B.iface.Port → A.iface.Port)
    (hp : ∀ y, A.iface.type (p y) = B.iface.type y) : A ⟶ B := IDHom.wire p hp

/-- A type-preserving bijection of ports is an isomorphism of objects. -/
def portIso {A B : IDCat S} (e : A.iface.Port ≃ B.iface.Port)
    (he : ∀ x, B.iface.type (e x) = A.iface.type x) : A ≅ B where
  hom := wireHom e.symm (fun y => by simpa using (he (e.symm y)).symm)
  inv := wireHom e he
  hom_inv_id := by
    change IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _) = IDHom.wire id _
    rw [IDHom.wire_comp]
    apply IDHom.wire_congr; funext x; exact e.symm_apply_apply x
  inv_hom_id := by
    change IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _) = IDHom.wire id _
    rw [IDHom.wire_comp]
    apply IDHom.wire_congr; funext y; exact e.apply_symm_apply y

def assocIso (A B C : IDCat S) : tensorObj (tensorObj A B) C ≅ tensorObj A (tensorObj B C) :=
  portIso (Equiv.sumAssoc A.iface.Port B.iface.Port C.iface.Port)
    (fun x => by rcases x with (x | y) | z <;> rfl)

def leftIso (A : IDCat S) : tensorObj (unit S) A ≅ A :=
  portIso (Equiv.emptySum Empty A.iface.Port)
    (fun x => by rcases x with x | x; exact x.elim; rfl)

def rightIso (A : IDCat S) : tensorObj A (unit S) ≅ A :=
  portIso (Equiv.sumEmpty A.iface.Port Empty)
    (fun x => by rcases x with x | x; rfl; exact x.elim)

def swapIso (A B : IDCat S) : tensorObj A B ≅ tensorObj B A :=
  portIso (Equiv.sumComm A.iface.Port B.iface.Port) (fun x => by cases x <;> rfl)

/-- The tensor of morphisms. -/
def tensorHom {A B A' B' : IDCat S} (f : A ⟶ B) (g : A' ⟶ B') :
    tensorObj A A' ⟶ tensorObj B B' := IDHom.tensor f g

theorem assoc_natural {A₁ A₂ A₃ B₁ B₂ B₃ : IDCat S} (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂)
    (h : A₃ ⟶ B₃) :
    tensorHom (tensorHom f g) h ≫ (assocIso B₁ B₂ B₃).hom =
      (assocIso A₁ A₂ A₃).hom ≫ tensorHom f (tensorHom g h) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    induction h using Quotient.inductionOn with | _ h =>
      refine IDHom.wire_slide ((f.tensor g).tensor h) (f.tensor (g.tensor h))
        _ _ _ _ (Equiv.sumAssoc f.net.Gen g.net.Gen h.net.Gen) ?_ ?_ ?_
        (Equiv.sumAssoc f.UGen g.UGen h.UGen) ?_ ?_
      · rintro ((a | b) | c) <;> rfl
      · rintro ((a | b) | c)
        · change ((f.net.parents a).map _).map _ = (((f.net.parents a).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((g.net.parents b).map _).map _).map _ =
            (((g.net.parents b).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((h.net.parents c).map _).map _).map _ = ((h.net.parents c).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
      · rintro (y | (y | y))
        · change Sum.map _ _ (Net.tinl f.net (g.net.tensor h.net) (f.net.output y)) =
            Sum.map _ _ (Net.tinl (f.net.tensor g.net) h.net
              (Net.tinl f.net g.net (f.net.output y)))
          cases f.net.output y <;> rfl
        · change Sum.map _ _ (Net.tinr f.net (g.net.tensor h.net)
              (Net.tinl g.net h.net (g.net.output y))) =
            Sum.map _ _ (Net.tinl (f.net.tensor g.net) h.net
              (Net.tinr f.net g.net (g.net.output y)))
          cases g.net.output y <;> rfl
        · change Sum.map _ _ (Net.tinr f.net (g.net.tensor h.net)
              (Net.tinr g.net h.net (h.net.output y))) =
            Sum.map _ _ (Net.tinr (f.net.tensor g.net) h.net (h.net.output y))
          cases h.net.output y <;> rfl
      · rintro ((a | b) | c) <;> rfl
      · rintro ((a | b) | c)
        · change ((f.uparents a).map _).map _ = (((f.uparents a).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((g.uparents b).map _).map _).map _ = (((g.uparents b).map _).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl
        · change (((h.uparents c).map _).map _).map _ = ((h.uparents c).map _).map _
          simp only [List.map_map]
          congr 1; funext v; cases v <;> rfl

theorem left_natural {A B : IDCat S} (f : A ⟶ B) :
    tensorHom (𝟙 (unit S)) f ≫ (leftIso B).hom = (leftIso A).hom ≫ f := by
  induction f using Quotient.inductionOn with | _ f =>
    refine IDHom.wire_slide ((IDNet.identity (Interface.empty S.toSignature)).tensor f) f
      _ _ _ _ (Equiv.emptySum Empty f.net.Gen) ?_ ?_ ?_ (Equiv.emptySum Empty f.UGen) ?_ ?_
    · rintro (a | a); exact a.elim; rfl
    · rintro (a | a)
      · exact a.elim
      · change (f.net.parents a).map _ = ((f.net.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
    · intro y
      change Sum.map _ _ (f.net.output y) = Sum.map _ _ (Net.tinr _ _ (f.net.output y))
      cases f.net.output y <;> rfl
    · rintro (a | a); exact a.elim; rfl
    · rintro (a | a)
      · exact a.elim
      · change (f.uparents a).map _ = ((f.uparents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl

theorem right_natural {A B : IDCat S} (f : A ⟶ B) :
    tensorHom f (𝟙 (unit S)) ≫ (rightIso B).hom = (rightIso A).hom ≫ f := by
  induction f using Quotient.inductionOn with | _ f =>
    refine IDHom.wire_slide (f.tensor (IDNet.identity (Interface.empty S.toSignature))) f
      _ _ _ _ (Equiv.sumEmpty f.net.Gen Empty) ?_ ?_ ?_ (Equiv.sumEmpty f.UGen Empty) ?_ ?_
    · rintro (a | a); rfl; exact a.elim
    · rintro (a | a)
      · change (f.net.parents a).map _ = ((f.net.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · exact a.elim
    · intro y
      change Sum.map _ _ (f.net.output y) = Sum.map _ _ (Net.tinl _ _ (f.net.output y))
      cases f.net.output y <;> rfl
    · rintro (a | a); rfl; exact a.elim
    · rintro (a | a)
      · change (f.uparents a).map _ = ((f.uparents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · exact a.elim

theorem swap_natural {A B A' B' : IDCat S} (f : A ⟶ B) (g : A' ⟶ B') :
    tensorHom f g ≫ (swapIso B B').hom = (swapIso A A').hom ≫ tensorHom g f := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    refine IDHom.wire_slide (f.tensor g) (g.tensor f)
      _ _ _ _ (Equiv.sumComm f.net.Gen g.net.Gen) ?_ ?_ ?_ (Equiv.sumComm f.UGen g.UGen) ?_ ?_
    · rintro (a | b) <;> rfl
    · rintro (a | b)
      · change ((f.net.parents a).map _).map _ = ((f.net.parents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · change ((g.net.parents b).map _).map _ = ((g.net.parents b).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
    · rintro (y | y)
      · change Sum.map _ _ (Net.tinl _ _ (g.net.output y)) =
          Sum.map _ _ (Net.tinr _ _ (g.net.output y))
        cases g.net.output y <;> rfl
      · change Sum.map _ _ (Net.tinr _ _ (f.net.output y)) =
          Sum.map _ _ (Net.tinl _ _ (f.net.output y))
        cases f.net.output y <;> rfl
    · rintro (a | b) <;> rfl
    · rintro (a | b)
      · change ((f.uparents a).map _).map _ = ((f.uparents a).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl
      · change ((g.uparents b).map _).map _ = ((g.uparents b).map _).map _
        simp only [List.map_map]
        congr 1; funext v; cases v <;> rfl

instance monoidalStruct : MonoidalCategoryStruct (IDCat S) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft A _ _ f := tensorHom (𝟙 A) f
  whiskerRight f B := tensorHom f (𝟙 B)
  tensorUnit := unit S
  associator := assocIso
  leftUnitor := leftIso
  rightUnitor := rightIso

theorem tensor_id (A B : IDCat S) : tensorHom (𝟙 A) (𝟙 B) = 𝟙 (tensorObj A B) := by
  change IDHom.tensor (IDHom.wire id _) (IDHom.wire id _) = IDHom.wire id _
  rw [IDHom.wire_tensor]
  apply IDHom.wire_congr
  funext v; cases v <;> rfl

/-- **Open influence diagrams up to isomorphism form a monoidal category.** -/
instance monoidal : MonoidalCategory (IDCat S) :=
  MonoidalCategory.ofTensorHom
    tensor_id
    (by intros; rfl)
    (by intros; rfl)
    (fun f g h k => IDHom.tensor_comp f g h k)
    assoc_natural
    left_natural
    right_natural
    (by
      intro A B C D
      change IDHom.comp (IDHom.tensor (IDHom.wire _ _) (IDHom.wire id _))
          (IDHom.comp (IDHom.wire _ _) (IDHom.tensor (IDHom.wire id _) (IDHom.wire _ _))) =
        IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _)
      simp only [IDHom.wire_tensor, IDHom.wire_comp]
      apply IDHom.wire_congr
      funext v
      rcases v with a | (b | (c | d)) <;> rfl)
    (by
      intro A B
      change IDHom.comp (IDHom.wire _ _) (IDHom.tensor (IDHom.wire id _) (IDHom.wire _ _)) =
        IDHom.tensor (IDHom.wire _ _) (IDHom.wire id _)
      simp only [IDHom.wire_tensor, IDHom.wire_comp]
      apply IDHom.wire_congr
      funext v
      cases v <;> rfl)

/-- **Open influence diagrams up to isomorphism form a symmetric monoidal category.** -/
instance symmetric : SymmetricCategory (IDCat S) where
  braiding := swapIso
  braiding_naturality_right := by intros A B C f; exact swap_natural (𝟙 A) f
  braiding_naturality_left := by intros A B f C; exact swap_natural f (𝟙 C)
  hexagon_forward := by
    intro A B C
    change IDHom.comp (IDHom.wire _ _) (IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _)) =
      IDHom.comp (IDHom.tensor (IDHom.wire _ _) (IDHom.wire id _))
        (IDHom.comp (IDHom.wire _ _) (IDHom.tensor (IDHom.wire id _) (IDHom.wire _ _)))
    simp only [IDHom.wire_tensor, IDHom.wire_comp]
    apply IDHom.wire_congr
    funext v
    rcases v with b | (c | a) <;> rfl
  hexagon_reverse := by
    intro A B C
    change IDHom.comp (IDHom.wire _ _) (IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _)) =
      IDHom.comp (IDHom.tensor (IDHom.wire id _) (IDHom.wire _ _))
        (IDHom.comp (IDHom.wire _ _) (IDHom.tensor (IDHom.wire _ _) (IDHom.wire id _)))
    simp only [IDHom.wire_tensor, IDHom.wire_comp]
    apply IDHom.wire_congr
    funext v
    rcases v with (c | a) | b <;> rfl
  symmetry := by
    intro A B
    change IDHom.comp (IDHom.wire _ _) (IDHom.wire _ _) = IDHom.wire id _
    rw [IDHom.wire_comp]
    apply IDHom.wire_congr
    funext v
    cases v <;> rfl

end IDCat

/-! ### The semantics is strong monoidal -/

namespace IDInterpretation

variable (M : IDInterpretation S) (β : M.Behaviour)

/-- Wiring is interpreted as the deterministic reindexing, with zero reward. -/
theorem interpretB_wire (p : Y.Port → X.Port) (hp : ∀ y, X.type (p y) = Y.type y) :
    M.interpretB β (IDNet.wire p hp) = RewardKernel.ofFun ((M.interpB β).wireRead p hp) := by
  ext1
  · exact (M.interpB β).kernel_wire p hp
  · funext x y
    have hr : ∀ z, M.rewardB β (IDNet.wire p hp) x z = 0 :=
      fun z => Finset.sum_eq_zero (fun u _ => (u : Empty).elim)
    change M.rewardTableB β (IDNet.wire p hp) x y = 0
    unfold rewardTableB
    simp [hr]

theorem map_wire {A B : IDCat S} (p : B.iface.Port → A.iface.Port) (hp) :
    (M.interpretFunctor β).map (IDCat.wireHom p hp) =
      FinRew.det ((M.interpB β).wireRead p hp) :=
  Subtype.ext (M.interpretB_wire β p hp)

/-- The tensor of interpretations, read through the canonical bijections, as naturality. -/
theorem interpretB_tensor_natural (f : IDNet X Y) (g : IDNet X' Y') :
    ((M.interpretB β f).tensor (M.interpretB β g)).comp
        (RewardKernel.ofFun (M.joinB β Y Y')) =
      (RewardKernel.ofFun (M.joinB β X X')).comp (M.interpretB β (f.tensor g)) := by
  rw [← M.interpretB_tensor β f g]
  ext1
  · simp only [RewardKernel.comp_K, RewardKernel.ofFun, RewardKernel.lift_K,
      Kernel.comp_ofEquiv_right, Kernel.comp_ofFun_left, RewardKernel.reindex]
    funext p q
    simp
  · simp only [RewardKernel.comp_W, RewardKernel.ofFun, RewardKernel.lift_K,
      RewardKernel.lift_W, KernelAlgebra.kcomp_zero_left, KernelAlgebra.kcomp_zero_right,
      add_zero, zero_add, Kernel.comp_ofEquiv_right, Kernel.comp_ofFun_left,
      RewardKernel.reindex]
    funext p q
    simp

/-- The comparison of tensors: pairs of boundary assignments are assignments of the
disjoint union. -/
def stateTensor (A B : IDCat S) :
    (M.interpretFunctor β).obj A ⊗ (M.interpretFunctor β).obj B ≅
      (M.interpretFunctor β).obj (A ⊗ B) :=
  FinRew.isoOfEquiv (M.joinB β A.iface B.iface)

/-- The comparison of units: the empty interface has one assignment. -/
def stateUnit : 𝟙_ FinRew ≅ (M.interpretFunctor β).obj (𝟙_ (IDCat S)) := by
  letI : Unique ((M.interpB β).Boundary (Interface.empty S.toSignature)) := by
    change Unique ((M.interpB β).Assignment (Empty.elim : Empty → S.Ty))
    infer_instance
  exact FinRew.isoOfEquiv
    (Equiv.ofUnique Unit ((M.interpB β).Boundary (Interface.empty S.toSignature)))

theorem tensor_natural {A B A' B' : IDCat S} (f : A ⟶ B) (g : A' ⟶ B') :
    ((M.interpretFunctor β).map f ⊗ₘ (M.interpretFunctor β).map g) ≫
        (M.stateTensor β B B').hom =
      (M.stateTensor β A A').hom ≫ (M.interpretFunctor β).map (f ⊗ₘ g) := by
  induction f, g using Quotient.inductionOn₂ with | _ f g =>
    exact Subtype.ext (M.interpretB_tensor_natural β f g)

/-- **The semantics is strong monoidal.** -/
def monoidalCore : (M.interpretFunctor β).CoreMonoidal where
  εIso := M.stateUnit β
  μIso := M.stateTensor β
  μIso_hom_natural_left := by
    intro A B f A'
    have h := M.tensor_natural β f (𝟙 A')
    rw [(M.interpretFunctor β).map_id] at h
    exact h
  μIso_hom_natural_right := by
    intro A B A' f
    have h := M.tensor_natural β (𝟙 A') f
    rw [(M.interpretFunctor β).map_id] at h
    exact h
  associativity := by
    intro A B C
    change _ ≫ _ ≫ (M.interpretFunctor β).map (IDCat.wireHom _ _) = _
    rw [M.map_wire β]
    apply Subtype.ext
    change ((RewardKernel.lift _).tensor (RewardKernel.id _)).comp
        ((RewardKernel.lift _).comp (RewardKernel.lift _)) =
      (RewardKernel.lift _).comp
        (((RewardKernel.id _).tensor (RewardKernel.lift _)).comp (RewardKernel.lift _))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply congrArg RewardKernel.lift
    apply Kernel.ofFun_congr
    rintro ⟨⟨x, y⟩, z⟩
    apply Interpretation.Assignment.ext
    funext v
    rcases v with a | (b | c) <;> rfl
  left_unitality := by
    intro A
    change _ = _ ≫ _ ≫ (M.interpretFunctor β).map (IDCat.wireHom _ _)
    rw [M.map_wire β]
    apply Subtype.ext
    change RewardKernel.lift _ = ((RewardKernel.lift _).tensor (RewardKernel.id _)).comp
      ((RewardKernel.lift _).comp (RewardKernel.lift _))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply congrArg RewardKernel.lift
    apply Kernel.ofFun_congr
    intro x
    apply Interpretation.Assignment.ext
    funext v
    rfl
  right_unitality := by
    intro A
    change _ = _ ≫ _ ≫ (M.interpretFunctor β).map (IDCat.wireHom _ _)
    rw [M.map_wire β]
    apply Subtype.ext
    change RewardKernel.lift _ = ((RewardKernel.id _).tensor (RewardKernel.lift _)).comp
      ((RewardKernel.lift _).comp (RewardKernel.lift _))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    apply congrArg RewardKernel.lift
    apply Kernel.ofFun_congr
    intro x
    apply Interpretation.Assignment.ext
    funext v
    rfl

instance monoidalFunctor : (M.interpretFunctor β).Monoidal := (M.monoidalCore β).toMonoidal

/-- **The semantics is a braided (symmetric) monoidal functor.** -/
instance braidedFunctor : (M.interpretFunctor β).Braided where
  braided := by
    intro A B
    change (M.stateTensor β A B).hom ≫
        (M.interpretFunctor β).map (IDCat.wireHom _ _) =
      (β_ ((M.interpretFunctor β).obj A) ((M.interpretFunctor β).obj B)).hom ≫
        (M.stateTensor β B A).hom
    rw [M.map_wire β]
    apply Subtype.ext
    change (RewardKernel.lift _).comp (RewardKernel.lift _) =
      (RewardKernel.lift _).comp (RewardKernel.lift _)
    simp only [RewardKernel.lift_comp_lift, Kernel.ofFun_comp_ofFun]
    apply congrArg RewardKernel.lift
    apply Kernel.ofFun_congr
    rintro ⟨x, y⟩
    apply Interpretation.Assignment.ext
    funext v
    cases v <;> rfl

end IDInterpretation

end OpenInfluence
