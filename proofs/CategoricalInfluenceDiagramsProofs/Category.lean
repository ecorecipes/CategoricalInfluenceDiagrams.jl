import CategoricalInfluenceDiagramsProofs.RewardKernel
import FiniteKernelsProofs.Theory.FinStoch
import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# The expectation-semiring kernel category

`FinRew` packages the laws of `RewardKernel.lean` as Mathlib instances. Objects are finite
types with decidable equality (the empty type included), as in `FinStoch`. A morphism is a
reward kernel whose probability component `K` is stochastic; the reward component `W` is an
arbitrary real table, of either sign. Composition, identity and tensor are those of
`RewardKernel`; the associator, unitors and symmetry are the deterministic reindexings of
`FinStoch`, lifted with zero reward.

The instances are a `Category`, a `MonoidalCategory`, a `SymmetricCategory` and a
`CopyDiscardCategory` (every object a commutative comonoid, copy and discard lifted with
zero reward, coherent with the tensor). There is deliberately no `MarkovCategory`
instance: discard is not natural, because `f ≫ ε` keeps the expected reward of `f`
(`FinRew.discard_not_natural`).

`FinRew.lift` is the faithful embedding of `FinStoch` with zero reward; it preserves
composition, identities and tensor, so `FinStoch` is the reward-free part of `FinRew`.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open CategoryTheory MonoidalCategory FiniteKernelsProofs FiniteKernelsProofs.Finite

/-- Finite state types with decidable equality, including the empty type. -/
structure FinRew where
  /-- The finite set of boundary states. -/
  carrier : Type
  [fintype : Fintype carrier]
  [decEq : DecidableEq carrier]

attribute [instance] FinRew.fintype FinRew.decEq

namespace FinRew

instance instCategory : Category FinRew where
  Hom X Y := {r : RewardKernel X.carrier Y.carrier // r.Stochastic}
  id X := ⟨RewardKernel.id X.carrier, RewardKernel.Stochastic.id⟩
  comp f g := ⟨f.1.comp g.1, f.2.comp g.2⟩
  id_comp f := Subtype.ext (RewardKernel.id_comp f.1)
  comp_id f := Subtype.ext (RewardKernel.comp_id f.1)
  assoc f g h := Subtype.ext (RewardKernel.comp_assoc f.1 g.1 h.1)

variable {X Y Z : FinRew}

@[simp] theorem comp_val (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val.comp g.val := rfl

@[simp] theorem id_val (X : FinRew) : (𝟙 X : X ⟶ X).val = RewardKernel.id X.carrier := rfl

/-- A stochastic kernel with zero reward. -/
def lift (k : Kernel X.carrier Y.carrier) (hk : Kernel.Stochastic k) : X ⟶ Y :=
  ⟨RewardKernel.lift k, hk⟩

/-- The deterministic morphism of a function, with zero reward. -/
def det (f : X.carrier → Y.carrier) : X ⟶ Y := lift (Kernel.ofFun f) (Kernel.Stochastic.ofFun f)

/-- A state-space equivalence induces an isomorphism with zero reward. -/
def isoOfEquiv (e : X.carrier ≃ Y.carrier) : X ≅ Y where
  hom := det e
  inv := det e.symm
  hom_inv_id := Subtype.ext (by
    change (RewardKernel.lift _).comp (RewardKernel.lift _) = RewardKernel.lift _
    rw [RewardKernel.lift_comp_lift, Kernel.ofFun_comp_ofFun]
    exact congrArg RewardKernel.lift (Kernel.ofFun_congr fun x => e.symm_apply_apply x))
  inv_hom_id := Subtype.ext (by
    change (RewardKernel.lift _).comp (RewardKernel.lift _) = RewardKernel.lift _
    rw [RewardKernel.lift_comp_lift, Kernel.ofFun_comp_ofFun]
    exact congrArg RewardKernel.lift (Kernel.ofFun_congr fun y => e.apply_symm_apply y))

instance instMonoidalCategoryStruct : MonoidalCategoryStruct FinRew where
  tensorObj X Y := ⟨X.carrier × Y.carrier⟩
  tensorUnit := ⟨Unit⟩
  tensorHom f g := ⟨f.1.tensor g.1, f.2.tensor g.2⟩
  whiskerLeft X _ _ g := ⟨(RewardKernel.id X.carrier).tensor g.1,
    RewardKernel.Stochastic.id.tensor g.2⟩
  whiskerRight f Y := ⟨f.1.tensor (RewardKernel.id Y.carrier),
    f.2.tensor RewardKernel.Stochastic.id⟩
  associator X Y Z := isoOfEquiv (Equiv.prodAssoc X.carrier Y.carrier Z.carrier)
  leftUnitor X := isoOfEquiv (Equiv.punitProd X.carrier)
  rightUnitor X := isoOfEquiv (Equiv.prodPUnit X.carrier)

@[simp] theorem tensorHom_val {X Y X' Y' : FinRew} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g).val = f.val.tensor g.val := rfl

instance instMonoidalCategory : MonoidalCategory FinRew :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => Subtype.ext RewardKernel.tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' =>
      Subtype.ext (RewardKernel.tensor_comp_tensor f.1 g.1 f'.1 g'.1))
    (associator_naturality := fun f g h => Subtype.ext (RewardKernel.tensor_assoc f.1 g.1 h.1))
    (leftUnitor_naturality := fun f => Subtype.ext (RewardKernel.tensor_unit_left f.1))
    (rightUnitor_naturality := fun f => Subtype.ext (RewardKernel.tensor_unit_right f.1))
    (pentagon := by
      intro W X Y Z
      apply Subtype.ext
      change ((RewardKernel.lift _).tensor (RewardKernel.id _)).comp
        ((RewardKernel.lift _).comp ((RewardKernel.id _).tensor (RewardKernel.lift _))) =
          (RewardKernel.lift _).comp (RewardKernel.lift _)
      simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
        Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
      rfl)
    (triangle := by
      intro X Y
      apply Subtype.ext
      change (RewardKernel.lift _).comp ((RewardKernel.id _).tensor (RewardKernel.lift _)) =
          (RewardKernel.lift _).tensor (RewardKernel.id _)
      simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
        Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
      rfl)

instance instSymmetricCategory : SymmetricCategory FinRew where
  braiding X Y := isoOfEquiv (Equiv.prodComm X.carrier Y.carrier)
  braiding_naturality_left := by
    intro X Y f Z
    exact Subtype.ext (RewardKernel.tensor_swap f.1 (RewardKernel.id _))
  braiding_naturality_right := by
    intro X Y Z f
    exact Subtype.ext (RewardKernel.tensor_swap (RewardKernel.id _) f.1)
  hexagon_forward := by
    intro X Y Z
    apply Subtype.ext
    change (RewardKernel.lift _).comp ((RewardKernel.lift _).comp (RewardKernel.lift _)) =
      ((RewardKernel.lift _).tensor (RewardKernel.id _)).comp
        ((RewardKernel.lift _).comp ((RewardKernel.id _).tensor (RewardKernel.lift _)))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    rfl
  hexagon_reverse := by
    intro X Y Z
    apply Subtype.ext
    change (RewardKernel.lift _).comp ((RewardKernel.lift _).comp (RewardKernel.lift _)) =
      ((RewardKernel.id _).tensor (RewardKernel.lift _)).comp
        ((RewardKernel.lift _).comp ((RewardKernel.lift _).tensor (RewardKernel.id _)))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    rfl
  symmetry := by
    intro X Y
    apply Subtype.ext
    change (RewardKernel.lift _).comp (RewardKernel.lift _) = RewardKernel.lift _
    simp only [RewardKernel.lift_comp_lift, Kernel.ofFun_comp_ofFun]
    rfl

/-- Copy and discard, lifted with zero reward. -/
instance instComonObj (X : FinRew) : ComonObj X where
  counit := lift (Kernel.discard X.carrier) ⟨Kernel.Nonneg.discard, Kernel.Normalised.discard⟩
  comul := det fun x => (x, x)
  counit_comul := Subtype.ext (by
    change (RewardKernel.lift _).comp ((RewardKernel.lift _).tensor (RewardKernel.id _)) =
      RewardKernel.lift _
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift]
    exact congrArg RewardKernel.lift Kernel.copy_discard_left)
  comul_counit := Subtype.ext (by
    change (RewardKernel.lift _).comp ((RewardKernel.id _).tensor (RewardKernel.lift _)) =
      RewardKernel.lift _
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift]
    exact congrArg RewardKernel.lift Kernel.copy_discard_right)
  comul_assoc := Subtype.ext (by
    change (RewardKernel.lift _).comp ((RewardKernel.id _).tensor (RewardKernel.lift _)) =
      (RewardKernel.lift _).comp
        (((RewardKernel.lift _).tensor (RewardKernel.id _)).comp (RewardKernel.lift _))
    simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
      Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun]
    rfl)

instance instIsCommComonObj (X : FinRew) : IsCommComonObj X where
  comul_comm := Subtype.ext (by
    change (RewardKernel.lift _).comp (RewardKernel.lift _) = RewardKernel.lift _
    simp only [RewardKernel.lift_comp_lift, Kernel.ofFun_comp_ofFun]
    rfl)

open scoped ComonObj

/-- The structural `tensorμ` of Mathlib is the middle-swap reindexing with zero reward. -/
theorem tensorμ_val (X Y : FinRew) :
    (MonoidalCategory.tensorμ X X Y Y).val =
      RewardKernel.lift (Kernel.tensorμ X.carrier Y.carrier) := by
  simp only [MonoidalCategory.tensorμ]
  change (RewardKernel.lift _).comp
    (((RewardKernel.id _).tensor (RewardKernel.lift _)).comp
      (((RewardKernel.id _).tensor ((RewardKernel.lift _).tensor (RewardKernel.id _))).comp
        (((RewardKernel.id _).tensor (RewardKernel.lift _)).comp (RewardKernel.lift _)))) = _
  simp only [RewardKernel.id, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift,
    Kernel.idK, Kernel.tensor_ofFun, Kernel.ofFun_comp_ofFun, Kernel.tensorμ]
  rfl

instance instCopyDiscardCategory : CopyDiscardCategory FinRew where
  copy_tensor X Y := Subtype.ext (by
    change RewardKernel.lift (Kernel.copy (X.carrier × Y.carrier)) =
      ((RewardKernel.lift (Kernel.copy X.carrier)).tensor
        (RewardKernel.lift (Kernel.copy Y.carrier))).comp
        (MonoidalCategory.tensorμ X X Y Y).val
    rw [tensorμ_val, RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift]
    exact congrArg RewardKernel.lift Kernel.copy_prod)
  discard_tensor X Y := Subtype.ext (by
    change RewardKernel.lift (Kernel.discard (X.carrier × Y.carrier)) =
      ((RewardKernel.lift (Kernel.discard X.carrier)).tensor
        (RewardKernel.lift (Kernel.discard Y.carrier))).comp
        (RewardKernel.lift (Kernel.ofFun (Equiv.punitProd Unit)))
    rw [RewardKernel.lift_tensor_lift, RewardKernel.lift_comp_lift]
    exact congrArg RewardKernel.lift Kernel.discard_prod)
  copy_unit := Subtype.ext rfl
  discard_unit := Subtype.ext (by
    change RewardKernel.lift (Kernel.discard Unit) = RewardKernel.lift (Kernel.idK Unit)
    exact congrArg RewardKernel.lift Kernel.discard_unit)

/-- Composing with discard sums the reward over the output. -/
theorem comp_discard_val (f : X ⟶ Y) :
    (f ≫ ε[Y]).val = ⟨Kernel.discard X.carrier, fun x _ => ∑ y, f.val.W x y⟩ := by
  change f.val.comp (RewardKernel.discard Y.carrier) = _
  rw [RewardKernel.comp_discard]
  congr 1
  exact Kernel.Normalised.comp_discard f.2.2

/-- Discard is natural exactly for the morphisms whose total reward from every input is
zero. -/
theorem comp_discard_eq_iff (f : X ⟶ Y) : f ≫ ε[Y] = ε[X] ↔ ∀ x, ∑ y, f.val.W x y = 0 := by
  rw [← Subtype.coe_inj, comp_discard_val]
  constructor
  · intro h x
    exact congrFun (congrFun (congrArg RewardKernel.W h) x) ()
  · intro h
    ext1
    · rfl
    · funext x u
      exact h x

/-- The one-point object. -/
abbrev unitObj : FinRew := ⟨Unit⟩

/-- The morphism that stays put and earns reward one. -/
def unitReward : unitObj ⟶ unitObj :=
  ⟨RewardKernel.Examples.unitReward, RewardKernel.Examples.unitReward_stochastic⟩

/-- `FinRew` is a copy-discard category but not a Markov category: discard is not natural.
The witness is the morphism `unitObj ⟶ unitObj` that stays put and earns reward one. -/
theorem discard_not_natural : unitReward ≫ ε[unitObj] ≠ ε[unitObj] := by
  rw [Ne, comp_discard_eq_iff]
  intro h
  have := h ()
  simp [unitReward, RewardKernel.Examples.unitReward] at this

/-- The embedding of `FinStoch` with zero reward. -/
def ofFinStoch (X : FinStoch) : FinRew := ⟨X.carrier⟩

/-- A stochastic kernel as a morphism with zero reward. -/
def liftHom {X Y : FinStoch} (f : X ⟶ Y) : ofFinStoch X ⟶ ofFinStoch Y := lift f.1 f.2

theorem liftHom_comp {X Y Z : FinStoch} (f : X ⟶ Y) (g : Y ⟶ Z) :
    liftHom (f ≫ g) = liftHom f ≫ liftHom g :=
  Subtype.ext (RewardKernel.lift_comp_lift f.1 g.1).symm

theorem liftHom_id (X : FinStoch) : liftHom (𝟙 X) = 𝟙 (ofFinStoch X) := rfl

theorem liftHom_tensor {X Y X' Y' : FinStoch} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (liftHom (f ⊗ₘ g) : ofFinStoch (X ⊗ X') ⟶ ofFinStoch (Y ⊗ Y')) =
      (liftHom f ⊗ₘ liftHom g : ofFinStoch X ⊗ ofFinStoch X' ⟶ _) :=
  Subtype.ext (RewardKernel.lift_tensor_lift f.1 g.1).symm

theorem liftHom_injective {X Y : FinStoch} : Function.Injective (liftHom (X := X) (Y := Y)) :=
  fun _ _ h => Subtype.ext (congrArg (fun r : ofFinStoch X ⟶ ofFinStoch Y => r.1.K) h)

end FinRew

end OpenInfluence
