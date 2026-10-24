import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# Open influence diagrams up to isomorphism, and the semantics as a functor

`Syntax.lean` does not quotient `IDNet` by isomorphism, so `Interpretation.lean` states
functoriality as equations on representatives. This module adds the quotient.

**Isomorphism.** An isomorphism of open influence diagrams `f ≅ g : X → Y` (`IDNet.Iso`) is
an isomorphism of the underlying nets (CategoricalBayesianNetworks' `Net.Iso`: a bijection of
generators preserving labels, ordered parent lists and the output leg, fixing the boundary)
together with a bijection of utility generators preserving their labels and their ordered
scopes, read through the bijection of variables. It is an equivalence relation
(`IDNet.setoid`), a congruence for serial composition (`Iso.comp`), and the unit and
associativity laws of serial composition hold up to isomorphism (`id_comp_iso`,
`comp_id_iso`, `assoc_iso`), by the same empty-sum and sum-associativity bijections as for
nets, extended to utilities.

**Invariance.** Isomorphic diagrams have the same semantics, under every behavioural
strategy (`interpretB_iso`) and so under every deterministic strategy (`interpret_iso`): the
bijection of generators carries internal assignments to internal assignments with the same
joint weight, output and reward.

**The syntax category and the semantic functor.** Typed interfaces, with open influence
diagrams up to isomorphism as morphisms, form a category (`IDCat`); there are no equations
in the quotient beyond isomorphism. For every behavioural strategy `β` the semantics is a
functor `IDCat S ⥤ FinRew` (`interpretFunctor`), and for a deterministic strategy `σ`
`interpretFunctor (pointMass σ)` sends a diagram to `interpret σ f`
(`interpretFunctor_pointMass`). So the functoriality theorems of `Interpretation.lean` and
`Behaviour.lean` are now about a Mathlib `Functor`, not only about representatives.

**Scope.** Serial composition only: the monoidal structure of the quotient (tensor up to
isomorphism, its associator and unitors) is not developed here; `interpret_tensor` stays an
equation on representatives.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open CategoryTheory OpenNet

variable {S : IDSignature} {X Y Z W : S.Iface}

namespace IDNet

/-- An isomorphism of open influence diagrams: an isomorphism of the underlying nets with a
bijection of utility generators preserving labels and ordered scopes. -/
structure Iso (f g : IDNet X Y) where
  /-- The isomorphism of the underlying nets. -/
  net : Net.Iso f.net g.net
  /-- The bijection of utility generators. -/
  ugen : f.UGen ≃ g.UGen
  /-- Utility labels are preserved. -/
  ulabel : ∀ u, g.ulabel (ugen u) = f.ulabel u
  /-- Ordered scopes are preserved, read through the bijection of variables. -/
  uparents : ∀ u, g.uparents (ugen u) = (f.uparents u).map (Sum.map id net.gen)

theorem map_sum_refl {A B : Type} (l : List (A ⊕ B)) :
    l.map (Sum.map id (Equiv.refl B)) = l := by
  have h : (Sum.map id (Equiv.refl B) : A ⊕ B → A ⊕ B) = id := by
    funext v
    cases v <;> rfl
  rw [h, List.map_id]

def Iso.refl (f : IDNet X Y) : Iso f f where
  net := Net.Iso.refl f.net
  ugen := Equiv.refl _
  ulabel _ := rfl
  uparents _ := (map_sum_refl _).symm

def Iso.trans {f g h : IDNet X Y} (a : Iso f g) (b : Iso g h) : Iso f h where
  net := a.net.trans b.net
  ugen := a.ugen.trans b.ugen
  ulabel u := (b.ulabel _).trans (a.ulabel _)
  uparents u := by
    change h.uparents (b.ugen (a.ugen u)) = _
    rw [b.uparents, a.uparents, List.map_map]
    congr 1
    funext v
    cases v <;> rfl

def Iso.symm {f g : IDNet X Y} (a : Iso f g) : Iso g f where
  net := a.net.symm
  ugen := a.ugen.symm
  ulabel u := by simpa using (a.ulabel (a.ugen.symm u)).symm
  uparents u := by
    have h := congrArg (List.map (Sum.map id a.net.gen.symm)) (a.uparents (a.ugen.symm u))
    simp only [Equiv.apply_symm_apply, List.map_map] at h
    have hid : (Sum.map id a.net.gen.symm ∘ Sum.map id a.net.gen : f.net.Var → f.net.Var) =
        id := by
      funext v
      cases v <;> simp
    rw [hid, List.map_id] at h
    exact h.symm

instance setoid (X Y : S.Iface) : Setoid (IDNet X Y) where
  r f g := Nonempty (Iso f g)
  iseqv := ⟨fun f => ⟨Iso.refl f⟩, fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩⟩

theorem left_iso {f f' : Net X Y} {g g' : Net Y Z} (a : Net.Iso f f') (b : Net.Iso g g')
    (v : f.Var) :
    Net.left f' g' (Sum.map id a.gen v) =
      Sum.map id (Equiv.sumCongr a.gen b.gen) (Net.left f g v) := by
  cases v <;> rfl

theorem right_iso {f f' : Net X Y} {g g' : Net Y Z} (a : Net.Iso f f') (b : Net.Iso g g')
    (v : g.Var) :
    Net.right f' g' (Sum.map id b.gen v) =
      Sum.map id (Equiv.sumCongr a.gen b.gen) (Net.right f g v) := by
  cases v with
  | inl y =>
    simp only [Sum.map_inl, id_eq, Net.right, Sum.elim_inl, a.output]
    cases f.output y <;> rfl
  | inr c => rfl

/-- Serial composition respects isomorphism. -/
def Iso.comp {f f' : IDNet X Y} {g g' : IDNet Y Z} (a : Iso f f') (b : Iso g g') :
    Iso (f.comp g) (f'.comp g') where
  net := a.net.comp b.net
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
      exact congrArg (fun k => (f.uparents u).map k) (funext (left_iso a.net b.net))
    | inr u =>
      change (g'.uparents (b.ugen u)).map _ = ((g.uparents u).map _).map _
      rw [b.uparents, List.map_map, List.map_map]
      exact congrArg (fun k => (g.uparents u).map k) (funext (right_iso a.net b.net))

/-- The identity is a left unit up to isomorphism. -/
def id_comp_iso (f : IDNet X Y) : Iso ((identity X).comp f) f where
  net := Net.id_comp_iso f.net
  ugen := Equiv.emptySum Empty f.UGen
  ulabel u := by rcases u with u | u; exact u.elim; rfl
  uparents u := by
    rcases u with u | u
    · exact u.elim
    · change f.uparents u = ((f.uparents u).map (Net.right (Net.identity X) f.net)).map _
      rw [List.map_map]
      have h : (Sum.map id (Equiv.emptySum Empty f.net.Gen)) ∘
          Net.right (Net.identity X) f.net = id := by
        funext v
        cases v <;> rfl
      exact ((congrArg (fun k => (f.uparents u).map k) h).trans (List.map_id _)).symm

/-- The identity is a right unit up to isomorphism. -/
def comp_id_iso (f : IDNet X Y) : Iso (f.comp (identity Y)) f where
  net := Net.comp_id_iso f.net
  ugen := Equiv.sumEmpty f.UGen Empty
  ulabel u := by rcases u with u | u; rfl; exact u.elim
  uparents u := by
    rcases u with u | u
    · change f.uparents u = ((f.uparents u).map (Net.left f.net (Net.identity Y))).map _
      rw [List.map_map]
      have h : (Sum.map id (Equiv.sumEmpty f.net.Gen Empty)) ∘
          Net.left f.net (Net.identity Y) = id := by
        funext v
        cases v <;> rfl
      exact ((congrArg (fun k => (f.uparents u).map k) h).trans (List.map_id _)).symm
    · exact u.elim

/-- Serial composition is associative up to isomorphism. -/
def assoc_iso (f : IDNet X Y) (g : IDNet Y Z) (h : IDNet Z W) :
    Iso ((f.comp g).comp h) (f.comp (g.comp h)) where
  net := Net.assoc_iso f.net g.net h.net
  ugen := Equiv.sumAssoc f.UGen g.UGen h.UGen
  ulabel u := by rcases u with (u | u) | u <;> rfl
  uparents u := by
    rcases u with (u | u) | u
    · change (f.uparents u).map _ = (((f.uparents u).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v; cases v <;> rfl
    · change ((g.uparents u).map _).map _ = (((g.uparents u).map _).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl y =>
        change Net.right f.net (g.net.comp h.net) (Sum.inl y) = _
        cases e : f.net.output y <;>
          simp [Net.right, Net.left, e, Function.comp_def] <;> rfl
      | inr b => rfl
    · change ((h.uparents u).map _).map _ = ((h.uparents u).map _).map _
      simp only [List.map_map]
      congr 1; funext v
      cases v with
      | inl z =>
        cases eg : g.net.output z with
        | inl y =>
          cases ef : f.net.output y <;>
            (simp [Net.comp, Net.right, Net.left, eg, ef, Function.comp_def]; try rfl)
        | inr b => simp [Net.comp, Net.right, Net.left, eg, Function.comp_def]; rfl
      | inr c => rfl

end IDNet

/-! ### Invariance of the semantics -/

namespace IDInterpretation

variable (M : IDInterpretation S) (β : M.Behaviour)

theorem rewardB_iso {f g : IDNet X Y} (a : f.Iso g) (x : (M.interpB β).Boundary X)
    (z : (M.interpB β).Internal f.net) :
    M.rewardB β g x ((M.interpB β).internalEquiv a.net z) = M.rewardB β f x z := by
  unfold rewardB
  symm
  refine Fintype.sum_equiv a.ugen _ _ fun u => ?_
  rw [a.ulabel, a.uparents, List.map_map]
  congr 1
  exact congrArg (fun k => (f.uparents u).map k)
    (funext fun v => ((M.interpB β).valuation_iso a.net x z v).symm)

/-- **Isomorphic diagrams have the same semantics** under every behavioural strategy. -/
theorem interpretB_iso {f g : IDNet X Y} (a : f.Iso g) :
    M.interpretB β f = M.interpretB β g := by
  ext1
  · exact (M.interpB β).kernel_iso a.net
  · funext x y
    change M.rewardTableB β f x y = M.rewardTableB β g x y
    unfold rewardTableB
    refine Fintype.sum_equiv ((M.interpB β).internalEquiv a.net) _ _ fun z => ?_
    rw [(M.interpB β).read_iso, (M.interpB β).joint_iso, M.rewardB_iso β a]

/-- **Isomorphic diagrams have the same semantics** under every deterministic strategy. -/
theorem interpret_iso (σ : M.Strategy) {f g : IDNet X Y} (a : f.Iso g) :
    M.interpret σ f = M.interpret σ g :=
  M.interpretB_iso (M.pointMass σ) a

end IDInterpretation

/-! ### The syntax category and the semantic functor -/

/-- The syntax category of open influence diagrams: its objects are typed interfaces. -/
structure IDCat (S : IDSignature) where
  /-- The interface. -/
  iface : S.Iface

/-- Open influence diagrams `X → Y` up to isomorphism. -/
abbrev IDHom (X Y : S.Iface) := Quotient (IDNet.setoid X Y)

/-- The class of an open influence diagram. -/
def IDHom.mk (f : IDNet X Y) : IDHom X Y := Quotient.mk _ f

theorem IDHom.mk_eq_iff (f g : IDNet X Y) : IDHom.mk f = IDHom.mk g ↔ Nonempty (f.Iso g) :=
  Quotient.eq

/-- Serial composition of classes. -/
def IDHom.comp (f : IDHom X Y) (g : IDHom Y Z) : IDHom X Z :=
  Quotient.liftOn₂ f g (fun a b => IDHom.mk (a.comp b))
    (fun _ _ _ _ ⟨a⟩ ⟨b⟩ => Quotient.sound ⟨a.comp b⟩)

@[simp] theorem IDHom.comp_mk (f : IDNet X Y) (g : IDNet Y Z) :
    IDHom.comp (IDHom.mk f) (IDHom.mk g) = IDHom.mk (f.comp g) := rfl

instance IDCat.category : Category (IDCat S) where
  Hom A B := IDHom A.iface B.iface
  id A := IDHom.mk (IDNet.identity A.iface)
  comp := IDHom.comp
  id_comp := by
    intro A B f
    induction f using Quotient.inductionOn with | _ f =>
      exact Quotient.sound ⟨IDNet.id_comp_iso f⟩
  comp_id := by
    intro A B f
    induction f using Quotient.inductionOn with | _ f =>
      exact Quotient.sound ⟨IDNet.comp_id_iso f⟩
  assoc := by
    intro A B C D f g h
    induction f, g using Quotient.inductionOn₂ with | _ f g =>
      induction h using Quotient.inductionOn with | _ h =>
        exact Quotient.sound ⟨IDNet.assoc_iso f g h⟩

namespace IDInterpretation

variable (M : IDInterpretation S) (β : M.Behaviour)

/-- The semantics of a class: the semantics of any representative. -/
def interpretClass {X Y : S.Iface} (f : IDHom X Y) :
    (⟨(M.interpB β).Boundary X⟩ : FinRew) ⟶ ⟨(M.interpB β).Boundary Y⟩ :=
  Quotient.liftOn f (fun a => ⟨M.interpretB β a, M.interpretB_stochastic β a⟩)
    (fun _ _ ⟨i⟩ => Subtype.ext (M.interpretB_iso β i))

/-- **The semantics is a functor** from the syntax category of open influence diagrams up to
isomorphism to `FinRew`, for every behavioural strategy. -/
def interpretFunctor : IDCat S ⥤ FinRew where
  obj A := ⟨(M.interpB β).Boundary A.iface⟩
  map f := M.interpretClass β f
  map_id A := Subtype.ext (M.interpretB_identity β A.iface)
  map_comp := by
    intro A B C f g
    induction f, g using Quotient.inductionOn₂ with | _ f g =>
      exact Subtype.ext (M.interpretB_comp β f g)

/-- The functor sends the class of a diagram to its semantics. -/
theorem interpretFunctor_map {A B : IDCat S} (f : IDNet A.iface B.iface) :
    ((M.interpretFunctor β).map (IDHom.mk f : A ⟶ B)).val = M.interpretB β f := rfl

/-- For a deterministic strategy, the functor of its point masses sends a diagram to
`interpret σ f`. -/
theorem interpretFunctor_pointMass (σ : M.Strategy) {A B : IDCat S}
    (f : IDNet A.iface B.iface) :
    ((M.interpretFunctor (M.pointMass σ)).map (IDHom.mk f : A ⟶ B)).val = M.interpret σ f :=
  rfl

end IDInterpretation

end OpenInfluence
