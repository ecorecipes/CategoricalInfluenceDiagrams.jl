import FiniteKernelsProofs.Finite.Kernel
import Mathlib.Tactic.Abel

/-!
# Reward kernels: kernels over the expectation semiring

A **reward kernel** `X → Y` between finite types is a pair `(K, W)` of real tables. `K x y`
is the probability of reaching boundary state `y` from `x`, and `W x y` is the
probability-weighted reward earned on the way (ADR 0018, decision 3). Composition,
identity and tensor are those of `CategoricalInfluenceDiagrams.jl`'s `RewardKernel`
(`src/semantics.jl`):

* `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)`;
* `id = (id, 0)`;
* `(K₁, W₁) ⊗ (K₂, W₂) = (K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`.

This is kernel composition over the expectation semiring `(p, r)·(q, s) = (pq, ps + rq)`.
`K` reuses `FiniteKernelsProofs.Finite.Kernel` unchanged; only the reward component is new.

This module proves, for arbitrary real tables (no nonnegativity or normalisation is
needed for any of them):

* the category laws: `id_comp`, `comp_id` and `comp_assoc`;
* the functoriality of the tensor: `tensor_comp_tensor` (the interchange law
  `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')`) and `tensor_id`;
* the naturality of the structural maps, all lifted from `FiniteKernels` with zero
  reward: `tensor_assoc` (associator), `tensor_unit_left` and `tensor_unit_right`
  (unitors) and `tensor_swap` (symmetry);
* that copy and discard lifted with zero reward satisfy the comonoid laws, and that
  stochasticity of `K` is preserved by composition and tensor (`Stochastic.comp`,
  `Stochastic.tensor`).

Discard is **not** natural: `comp_discard` computes `f ; discard = (K ; discard, row sums
of W)`, and `Examples.discard_not_natural` exhibits a stochastic reward kernel whose
composite with discard is not discard. The Mathlib packaging of these laws as a symmetric
monoidal category is `Category.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

/-! ### Bilinearity of kernel composition and tensor -/

namespace KernelAlgebra

variable {X Y Z X₁ X₂ Y₁ Y₂ : Type}

theorem kcomp_add_left [Fintype Y] (k k' : Kernel X Y) (l : Kernel Y Z) :
    Kernel.comp (k + k') l = Kernel.comp k l + Kernel.comp k' l := by
  funext x z
  simp [Kernel.comp, add_mul, Finset.sum_add_distrib]

theorem kcomp_add_right [Fintype Y] (k : Kernel X Y) (l l' : Kernel Y Z) :
    Kernel.comp k (l + l') = Kernel.comp k l + Kernel.comp k l' := by
  funext x z
  simp [Kernel.comp, mul_add, Finset.sum_add_distrib]

theorem kcomp_zero_left [Fintype Y] (l : Kernel Y Z) :
    Kernel.comp (0 : Kernel X Y) l = 0 := by
  funext x z
  simp [Kernel.comp]

theorem kcomp_zero_right [Fintype Y] (k : Kernel X Y) :
    Kernel.comp k (0 : Kernel Y Z) = 0 := by
  funext x z
  simp [Kernel.comp]

theorem ktensor_add_left (k k' : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) :
    Kernel.tensor (k + k') l = Kernel.tensor k l + Kernel.tensor k' l := by
  funext x y
  simp [Kernel.tensor, add_mul]

theorem ktensor_add_right (k : Kernel X₁ Y₁) (l l' : Kernel X₂ Y₂) :
    Kernel.tensor k (l + l') = Kernel.tensor k l + Kernel.tensor k l' := by
  funext x y
  simp [Kernel.tensor, mul_add]

theorem ktensor_zero_left (l : Kernel X₂ Y₂) :
    Kernel.tensor (0 : Kernel X₁ Y₁) l = 0 := by
  funext x y
  simp [Kernel.tensor]

theorem ktensor_zero_right (k : Kernel X₁ Y₁) :
    Kernel.tensor k (0 : Kernel X₂ Y₂) = 0 := by
  funext x y
  simp [Kernel.tensor]

end KernelAlgebra

open KernelAlgebra

/-- A reward kernel `X → Y`: a probability table `K` and a probability-weighted reward
table `W` of the same shape (Julia `RewardKernel(K, W)`). -/
@[ext] structure RewardKernel (X Y : Type) where
  /-- `K x y`: the probability of reaching `y` from `x`. -/
  K : Kernel X Y
  /-- `W x y`: the reward earned on the way from `x` to `y`, weighted by its probability. -/
  W : Kernel X Y

namespace RewardKernel

variable {X Y Z V X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : Type}

/-! ### Constructions -/

/-- Serial composition `(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` (diagrammatic order). -/
def comp [Fintype Y] (f : RewardKernel X Y) (g : RewardKernel Y Z) : RewardKernel X Z :=
  ⟨Kernel.comp f.K g.K, Kernel.comp f.W g.K + Kernel.comp f.K g.W⟩

/-- A kernel with zero reward. Identities and all structural maps are of this form. -/
def lift (k : Kernel X Y) : RewardKernel X Y := ⟨k, 0⟩

/-- The identity `(id, 0)`. -/
def id (X : Type) [DecidableEq X] : RewardKernel X X := lift (Kernel.idK X)

/-- The tensor `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`. -/
def tensor (f : RewardKernel X₁ Y₁) (g : RewardKernel X₂ Y₂) :
    RewardKernel (X₁ × X₂) (Y₁ × Y₂) :=
  ⟨Kernel.tensor f.K g.K, Kernel.tensor f.W g.K + Kernel.tensor f.K g.W⟩

/-- The deterministic reward kernel of a function, with zero reward. -/
def ofFun [DecidableEq Y] (e : X → Y) : RewardKernel X Y := lift (Kernel.ofFun e)

/-- Copy, lifted with zero reward. -/
def copy (X : Type) [DecidableEq X] : RewardKernel X (X × X) := lift (Kernel.copy X)

/-- Discard, lifted with zero reward. -/
def discard (X : Type) : RewardKernel X Unit := lift (Kernel.discard X)

/-- The probability component is stochastic (nonnegative and normalised); the reward
component is unconstrained. -/
def Stochastic [Fintype Y] (f : RewardKernel X Y) : Prop := Kernel.Stochastic f.K

@[simp] theorem comp_K [Fintype Y] (f : RewardKernel X Y) (g : RewardKernel Y Z) :
    (f.comp g).K = Kernel.comp f.K g.K := rfl

@[simp] theorem comp_W [Fintype Y] (f : RewardKernel X Y) (g : RewardKernel Y Z) :
    (f.comp g).W = Kernel.comp f.W g.K + Kernel.comp f.K g.W := rfl

@[simp] theorem tensor_K (f : RewardKernel X₁ Y₁) (g : RewardKernel X₂ Y₂) :
    (f.tensor g).K = Kernel.tensor f.K g.K := rfl

@[simp] theorem tensor_W (f : RewardKernel X₁ Y₁) (g : RewardKernel X₂ Y₂) :
    (f.tensor g).W = Kernel.tensor f.W g.K + Kernel.tensor f.K g.W := rfl

@[simp] theorem lift_K (k : Kernel X Y) : (lift k).K = k := rfl
@[simp] theorem lift_W (k : Kernel X Y) : (lift k).W = 0 := rfl

/-! ### Category laws -/

theorem id_comp [Fintype X] [DecidableEq X] (f : RewardKernel X Y) : (id X).comp f = f := by
  ext1
  · exact Kernel.idK_comp f.K
  · change Kernel.comp 0 f.K + Kernel.comp (Kernel.idK X) f.W = f.W
    rw [kcomp_zero_left, Kernel.idK_comp, zero_add]

theorem comp_id [Fintype Y] [DecidableEq Y] (f : RewardKernel X Y) : f.comp (id Y) = f := by
  ext1
  · exact Kernel.comp_idK f.K
  · change Kernel.comp f.W (Kernel.idK Y) + Kernel.comp f.K 0 = f.W
    rw [kcomp_zero_right, Kernel.comp_idK, add_zero]

theorem comp_assoc [Fintype Y] [Fintype Z] (f : RewardKernel X Y) (g : RewardKernel Y Z)
    (h : RewardKernel Z V) : (f.comp g).comp h = f.comp (g.comp h) := by
  ext1
  · exact Kernel.comp_assoc f.K g.K h.K
  · simp only [comp_W, comp_K, kcomp_add_left, kcomp_add_right, Kernel.comp_assoc]
    abel

/-! ### Lifted kernels -/

theorem lift_comp_lift [Fintype Y] (k : Kernel X Y) (l : Kernel Y Z) :
    (lift k).comp (lift l) = lift (Kernel.comp k l) := by
  ext1
  · rfl
  · simp [kcomp_zero_left, kcomp_zero_right]

theorem lift_tensor_lift (k : Kernel X₁ Y₁) (l : Kernel X₂ Y₂) :
    (lift k).tensor (lift l) = lift (Kernel.tensor k l) := by
  ext1
  · rfl
  · simp [ktensor_zero_left, ktensor_zero_right]

/-! ### Functoriality of the tensor -/

/-- The interchange law `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')`. -/
theorem tensor_comp_tensor [Fintype Y₁] [Fintype Y₂] (f : RewardKernel X₁ Y₁)
    (g : RewardKernel X₂ Y₂) (f' : RewardKernel Y₁ Z₁) (g' : RewardKernel Y₂ Z₂) :
    (f.tensor g).comp (f'.tensor g') = (f.comp f').tensor (g.comp g') := by
  ext1
  · exact Kernel.comp_tensor f.K g.K f'.K g'.K
  · simp only [comp_W, comp_K, tensor_W, tensor_K, kcomp_add_left, kcomp_add_right,
      ktensor_add_left, ktensor_add_right, Kernel.comp_tensor]
    abel

/-- The tensor of identities is the identity. -/
theorem tensor_id [DecidableEq X] [DecidableEq Y] :
    (id X).tensor (id Y) = id (X × Y) := by
  simp only [id, lift_tensor_lift, Kernel.tensor_idK]

/-! ### Naturality of the structural maps -/

/-- Associativity of the tensor up to the associator (lifted with zero reward). -/
theorem tensor_assoc [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype Y₁] [Fintype Y₂]
    [Fintype Y₃] [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq Y₁]
    [DecidableEq Y₂] [DecidableEq Y₃] (f : RewardKernel X₁ Y₁) (g : RewardKernel X₂ Y₂)
    (h : RewardKernel X₃ Y₃) :
    ((f.tensor g).tensor h).comp (lift (Kernel.assoc Y₁ Y₂ Y₃)) =
      (lift (Kernel.assoc X₁ X₂ X₃)).comp (f.tensor (g.tensor h)) := by
  ext1
  · exact Kernel.tensor_assoc f.K g.K h.K
  · simp only [comp_W, tensor_W, tensor_K, lift_W, lift_K, kcomp_add_left,
      kcomp_add_right, kcomp_zero_left, kcomp_zero_right, ktensor_add_left, ktensor_add_right,
      Kernel.tensor_assoc]
    abel

/-- Left unit of the tensor up to the left unitor. -/
theorem tensor_unit_left [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : RewardKernel X Y) :
    ((id Unit).tensor f).comp (lift (Kernel.leftUnitor Y)) =
      (lift (Kernel.leftUnitor X)).comp f := by
  ext1
  · exact Kernel.tensor_unit_left f.K
  · simp only [id, comp_W, tensor_W, tensor_K, lift_W, lift_K, kcomp_add_left,
      kcomp_zero_left, kcomp_zero_right, ktensor_zero_left, Kernel.tensor_unit_left]
    simp

/-- Right unit of the tensor up to the right unitor. -/
theorem tensor_unit_right [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : RewardKernel X Y) :
    (f.tensor (id Unit)).comp (lift (Kernel.rightUnitor Y)) =
      (lift (Kernel.rightUnitor X)).comp f := by
  ext1
  · exact Kernel.tensor_unit_right f.K
  · simp only [id, comp_W, tensor_W, tensor_K, lift_W, lift_K, kcomp_add_left,
      kcomp_zero_left, kcomp_zero_right, ktensor_zero_right, Kernel.tensor_unit_right]
    simp

/-- Naturality of the symmetry. -/
theorem tensor_swap [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] [DecidableEq X₁]
    [DecidableEq X₂] [DecidableEq Y₁] [DecidableEq Y₂] (f : RewardKernel X₁ Y₁)
    (g : RewardKernel X₂ Y₂) :
    (f.tensor g).comp (lift (Kernel.swap Y₁ Y₂)) =
      (lift (Kernel.swap X₁ X₂)).comp (g.tensor f) := by
  ext1
  · exact Kernel.tensor_swap f.K g.K
  · simp only [comp_W, tensor_W, tensor_K, lift_W, lift_K, kcomp_add_left,
      kcomp_add_right, kcomp_zero_left, kcomp_zero_right, Kernel.tensor_swap]
    abel

/-! ### Copy and discard with zero reward -/

/-- Coassociativity of the lifted copy. -/
theorem copy_assoc [Fintype X] [DecidableEq X] :
    (copy X).comp ((id X).tensor (copy X)) =
      ((copy X).comp ((copy X).tensor (id X))).comp (lift (Kernel.assoc X X X)) := by
  simp only [copy, id, lift_tensor_lift, lift_comp_lift, Kernel.copy_assoc]

/-- Left counit law of the lifted copy and discard. -/
theorem copy_discard_left [Fintype X] [DecidableEq X] :
    (copy X).comp ((discard X).tensor (id X)) = lift (Kernel.leftUnitorInv X) := by
  simp only [copy, discard, id, lift_tensor_lift, lift_comp_lift, Kernel.copy_discard_left]

/-- Right counit law of the lifted copy and discard. -/
theorem copy_discard_right [Fintype X] [DecidableEq X] :
    (copy X).comp ((id X).tensor (discard X)) = lift (Kernel.rightUnitorInv X) := by
  simp only [copy, discard, id, lift_tensor_lift, lift_comp_lift, Kernel.copy_discard_right]

/-- Cocommutativity of the lifted copy. -/
theorem copy_swap [Fintype X] [DecidableEq X] :
    (copy X).comp (lift (Kernel.swap X X)) = copy X := by
  simp only [copy, lift_comp_lift, Kernel.copy_swap]

/-- Composing with discard keeps the discarded probability and sums the reward over the
output: `f ; discard = (K ; discard, x ↦ Σ_y W x y)`. -/
theorem comp_discard [Fintype Y] (f : RewardKernel X Y) :
    f.comp (discard Y) = ⟨Kernel.comp f.K (Kernel.discard Y), fun x _ => ∑ y, f.W x y⟩ := by
  ext1
  · rfl
  · funext x u
    simp [comp, discard, lift, Kernel.comp]

/-- Discard is natural exactly for the reward kernels with normalised `K` and zero total
reward from every input. In particular it is not natural in general. -/
theorem comp_discard_eq_discard_iff [Fintype Y] (f : RewardKernel X Y) :
    f.comp (discard Y) = discard X ↔ Kernel.Normalised f.K ∧ ∀ x, ∑ y, f.W x y = 0 := by
  rw [comp_discard]
  constructor
  · intro h
    have hK := congrArg RewardKernel.K h
    have hW := congrArg RewardKernel.W h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have := congrFun (congrFun hK x) ()
      simpa [Kernel.comp, discard, lift] using this
    · exact congrFun (congrFun hW x) ()
  · rintro ⟨hK, hW⟩
    ext1
    · funext x u
      simpa [Kernel.comp, discard, lift] using hK x
    · funext x u
      exact hW x

/-! ### Stochasticity -/

theorem Stochastic.comp [Fintype Y] [Fintype Z] {f : RewardKernel X Y}
    {g : RewardKernel Y Z} (hf : f.Stochastic) (hg : g.Stochastic) : (f.comp g).Stochastic :=
  Kernel.Stochastic.comp hf hg

theorem Stochastic.tensor [Fintype Y₁] [Fintype Y₂] {f : RewardKernel X₁ Y₁}
    {g : RewardKernel X₂ Y₂} (hf : f.Stochastic) (hg : g.Stochastic) :
    (f.tensor g).Stochastic :=
  Kernel.Stochastic.tensor hf hg

theorem Stochastic.ofFun [Fintype Y] [DecidableEq Y] (e : X → Y) : (ofFun e).Stochastic :=
  Kernel.Stochastic.ofFun e

theorem Stochastic.id [Fintype X] [DecidableEq X] : (id X).Stochastic :=
  Kernel.Stochastic.ofFun _

theorem Stochastic.discard : (discard X).Stochastic :=
  ⟨Kernel.Nonneg.discard, Kernel.Normalised.discard⟩

end RewardKernel

/-! ### Discard is not natural -/

namespace RewardKernel.Examples

/-- A one-point process that is certain to stay put and earns reward one. -/
def unitReward : RewardKernel Unit Unit := ⟨Kernel.idK Unit, fun _ _ => 1⟩

theorem unitReward_stochastic : unitReward.Stochastic :=
  Kernel.Stochastic.ofFun (fun u : Unit => u)

/-- Discard, lifted with zero reward, is not natural: a stochastic reward kernel that earns
reward one, followed by discard, still carries that reward, so it is not discard (as ADR 0010
recorded `discard_not_natural` for the open-network syntax). -/
theorem discard_not_natural :
    unitReward.Stochastic ∧ unitReward.comp (discard Unit) ≠ discard Unit := by
  refine ⟨unitReward_stochastic, fun h => ?_⟩
  have hW := congrFun (congrFun (congrArg RewardKernel.W h) ()) ()
  rw [comp_discard] at hW
  simp [unitReward, discard, lift] at hW

end RewardKernel.Examples

end OpenInfluence
