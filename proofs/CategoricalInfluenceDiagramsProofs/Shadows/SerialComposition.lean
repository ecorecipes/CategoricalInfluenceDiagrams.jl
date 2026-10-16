import CategoricalInfluenceDiagramsProofs.RewardKernel

/-!
# SA-Pass shadow module: reward kernels form a category

Claim `cid.serial-composition`, from `RewardKernel.id_comp`, `RewardKernel.comp_id` and
`RewardKernel.comp_assoc`. The shadows spell out the prose's formula
`(K₁, W₁) ; (K₂, W₂) = (K₁K₂, W₁K₂ + K₁W₂)` and identity `(id, 0)` on pairs of tables, so
they also pin that the library's composition is that formula.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SerialComposition

open OpenInfluence FiniteKernelsProofs.Finite

/-- The prose's serial composition on pairs of tables. -/
abbrev seq {X Y Z : Type} [Fintype Y] (p : Kernel X Y × Kernel X Y)
    (q : Kernel Y Z × Kernel Y Z) : Kernel X Z × Kernel X Z :=
  (Kernel.comp p.1 q.1, Kernel.comp p.2 q.1 + Kernel.comp p.1 q.2)

/-- The prose's identity `(id, 0)`. -/
abbrev unit (X : Type) [DecidableEq X] : Kernel X X × Kernel X X := (Kernel.idK X, 0)

/-- The three category laws of `RewardKernel`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y : Type) [Fintype X] [DecidableEq X] (f : RewardKernel X Y),
      (RewardKernel.id X).comp f = f) ∧
    (∀ (X Y : Type) [Fintype Y] [DecidableEq Y] (f : RewardKernel X Y),
      f.comp (RewardKernel.id Y) = f) ∧
    ∀ (X Y Z V : Type) [Fintype Y] [Fintype Z] (f : RewardKernel X Y) (g : RewardKernel Y Z)
      (h : RewardKernel Z V), (f.comp g).comp h = f.comp (g.comp h)

/-- "`(id, 0)` as a unit": on the left. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype X] [DecidableEq X] (p : Kernel X Y × Kernel X Y), seq (unit X) p = p

/-- "`(id, 0)` as a unit": on the right. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : Type) [Fintype Y] [DecidableEq Y] (p : Kernel X Y × Kernel X Y), seq p (unit Y) = p

/-- "serial composition ... is associative". -/
abbrev Shadow3 : Prop :=
  ∀ (X Y Z V : Type) [Fintype Y] [Fintype Z] (p : Kernel X Y × Kernel X Y)
    (q : Kernel Y Z × Kernel Y Z) (r : Kernel Z V × Kernel Z V),
    seq (seq p q) r = seq p (seq q r)

/-- Pairs of tables are reward kernels. -/
abbrev pair {X Y : Type} (f : RewardKernel X Y) : Kernel X Y × Kernel X Y := (f.K, f.W)

theorem pair_injective {X Y : Type} {f g : RewardKernel X Y} (h : pair f = pair g) : f = g :=
  RewardKernel.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem forward1 : Candidate → Shadow1 := fun h X Y _ _ p =>
  congrArg pair (h.1 X Y ⟨p.1, p.2⟩)

theorem forward2 : Candidate → Shadow2 := fun h X Y _ _ p =>
  congrArg pair (h.2.1 X Y ⟨p.1, p.2⟩)

theorem forward3 : Candidate → Shadow3 := fun h X Y Z V _ _ p q r =>
  congrArg pair (h.2.2 X Y Z V ⟨p.1, p.2⟩ ⟨q.1, q.2⟩ ⟨r.1, r.2⟩)

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun X Y _ _ f => pair_injective (h1 X Y (pair f)),
    fun X Y _ _ f => pair_injective (h2 X Y (pair f)),
    fun X Y Z V _ _ f g h => pair_injective (h3 X Y Z V (pair f) (pair g) (pair h))⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ f => RewardKernel.id_comp f, fun _ _ _ _ f => RewardKernel.comp_id f,
    fun _ _ _ _ _ _ f g h => RewardKernel.comp_assoc f g h⟩

end CategoricalInfluenceDiagramsProofs.Shadows.SerialComposition
