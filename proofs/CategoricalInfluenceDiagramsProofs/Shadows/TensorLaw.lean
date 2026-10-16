import CategoricalInfluenceDiagramsProofs.RewardKernel

/-!
# SA-Pass shadow module: the tensor of reward kernels is a functor

Claim `cid.tensor`, from `RewardKernel.tensor_comp_tensor` and `RewardKernel.tensor_id`.
The shadows spell out the prose's tensor `(K₁ ⊗ K₂, W₁ ⊗ K₂ + K₁ ⊗ W₂)`, together with the
serial composition and identity it is a functor for, on pairs of tables.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.TensorLaw

open OpenInfluence FiniteKernelsProofs.Finite

/-- Serial composition on pairs of tables. -/
abbrev seq {X Y Z : Type} [Fintype Y] (p : Kernel X Y × Kernel X Y)
    (q : Kernel Y Z × Kernel Y Z) : Kernel X Z × Kernel X Z :=
  (Kernel.comp p.1 q.1, Kernel.comp p.2 q.1 + Kernel.comp p.1 q.2)

/-- The prose's tensor on pairs of tables. -/
abbrev par {X₁ X₂ Y₁ Y₂ : Type} (p : Kernel X₁ Y₁ × Kernel X₁ Y₁)
    (q : Kernel X₂ Y₂ × Kernel X₂ Y₂) :
    Kernel (X₁ × X₂) (Y₁ × Y₂) × Kernel (X₁ × X₂) (Y₁ × Y₂) :=
  (Kernel.tensor p.1 q.1, Kernel.tensor p.2 q.1 + Kernel.tensor p.1 q.2)

/-- The identity `(id, 0)`. -/
abbrev unit (X : Type) [DecidableEq X] : Kernel X X × Kernel X X := (Kernel.idK X, 0)

/-- `tensor_comp_tensor` and `tensor_id`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type) [Fintype Y₁] [Fintype Y₂] (f : RewardKernel X₁ Y₁)
      (g : RewardKernel X₂ Y₂) (f' : RewardKernel Y₁ Z₁) (g' : RewardKernel Y₂ Z₂),
      (f.tensor g).comp (f'.tensor g') = (f.comp f').tensor (g.comp g')) ∧
    ∀ (X Y : Type) [DecidableEq X] [DecidableEq Y],
      (RewardKernel.id X).tensor (RewardKernel.id Y) = RewardKernel.id (X × Y)

/-- "the interchange law `(f ⊗ g) ; (f' ⊗ g') = (f ; f') ⊗ (g ; g')`". -/
abbrev Shadow1 : Prop :=
  ∀ (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type) [Fintype Y₁] [Fintype Y₂] (p : Kernel X₁ Y₁ × Kernel X₁ Y₁)
    (q : Kernel X₂ Y₂ × Kernel X₂ Y₂) (p' : Kernel Y₁ Z₁ × Kernel Y₁ Z₁)
    (q' : Kernel Y₂ Z₂ × Kernel Y₂ Z₂), seq (par p q) (par p' q') = par (seq p p') (seq q q')

/-- "sends a pair of identities to the identity". -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : Type) [DecidableEq X] [DecidableEq Y], par (unit X) (unit Y) = unit (X × Y)

/-- Pairs of tables are reward kernels. -/
abbrev pair {X Y : Type} (f : RewardKernel X Y) : Kernel X Y × Kernel X Y := (f.K, f.W)

theorem pair_injective {X Y : Type} {f g : RewardKernel X Y} (h : pair f = pair g) : f = g :=
  RewardKernel.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem forward1 : Candidate → Shadow1 := fun h X₁ X₂ Y₁ Y₂ Z₁ Z₂ _ _ p q p' q' =>
  congrArg pair (h.1 X₁ X₂ Y₁ Y₂ Z₁ Z₂ ⟨p.1, p.2⟩ ⟨q.1, q.2⟩ ⟨p'.1, p'.2⟩ ⟨q'.1, q'.2⟩)

theorem forward2 : Candidate → Shadow2 := fun h X Y _ _ => congrArg pair (h.2 X Y)

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun X₁ X₂ Y₁ Y₂ Z₁ Z₂ _ _ f g f' g' =>
      pair_injective (h1 X₁ X₂ Y₁ Y₂ Z₁ Z₂ (pair f) (pair g) (pair f') (pair g')),
    fun X Y _ _ => pair_injective (h2 X Y)⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ _ _ f g f' g' => RewardKernel.tensor_comp_tensor f g f' g',
    fun _ _ _ _ => RewardKernel.tensor_id⟩

end CategoricalInfluenceDiagramsProofs.Shadows.TensorLaw
