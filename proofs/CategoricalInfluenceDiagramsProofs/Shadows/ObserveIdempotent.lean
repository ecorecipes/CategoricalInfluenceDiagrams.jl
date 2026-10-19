import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# SA-Pass shadow module: hard evidence on a boundary is idempotent and commutes

Claim `cid.observe-idempotent`, from `RewardKernel.observe_idem` and
`RewardKernel.observe_comm`. The shadows spell hard evidence as the diagonal indicator
`[x = x' ∧ P x]` with zero reward and composition as `(K₁K₂, W₁K₂ + K₁W₂)`. Both are
statements about explicit indicator tables, provable without the cited theorems, so the claim
is registered as weak (`independently_provable = true`).
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.ObserveIdempotent

open OpenInfluence FiniteKernelsProofs.Finite RewardKernel

/-- The diagonal indicator of `P`. -/
abbrev ind {X : Type} [DecidableEq X] (P : X → Prop) [DecidablePred P] : Kernel X X :=
  fun x x' => if x = x' ∧ P x then 1 else 0

/-- `observe_idem` and `observe_comm`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (P Q : X → Prop) [DecidablePred P]
    [DecidablePred Q],
    (observe P).comp (observe P) = observe P ∧
      (observe P).comp (observe Q) = (observe Q).comp (observe P)

/-- "Hard evidence on a boundary, the diagonal indicator with zero reward": `observe` is
that pair of tables. -/
abbrev Shadow1 : Prop :=
  ∀ (X : Type) [DecidableEq X] (P : X → Prop) [DecidablePred P],
    (observe P).K = ind P ∧ (observe P).W = 0

/-- "is idempotent": the indicator composed with itself is itself. -/
abbrev Shadow2 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (P : X → Prop) [DecidablePred P],
    Kernel.comp (ind P) (ind P) = ind P

/-- "and commutes with other hard evidence". -/
abbrev Shadow3 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (P Q : X → Prop) [DecidablePred P]
    [DecidablePred Q], Kernel.comp (ind P) (ind Q) = Kernel.comp (ind Q) (ind P)

theorem forward1 : Candidate → Shadow1 := fun _ _ _ _ _ => ⟨rfl, rfl⟩

theorem forward2 : Candidate → Shadow2 := fun h X _ _ P _ =>
  congrArg RewardKernel.K (h X P P).1

theorem forward3 : Candidate → Shadow3 := fun h X _ _ P Q _ _ =>
  congrArg RewardKernel.K (h X P Q).2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro h1 h2 h3 X _ _ P Q _ _
  have zP := (h1 X P).2
  have zQ := (h1 X Q).2
  refine ⟨RewardKernel.ext ?_ ?_, RewardKernel.ext ?_ ?_⟩
  · rw [comp_K, (h1 X P).1]
    exact h2 X P
  · rw [comp_W, zP, (h1 X P).1, KernelAlgebra.kcomp_zero_left, KernelAlgebra.kcomp_zero_right,
      add_zero]
  · rw [comp_K, comp_K, (h1 X P).1, (h1 X Q).1]
    exact h3 X P Q
  · rw [comp_W, comp_W, zP, zQ, KernelAlgebra.kcomp_zero_left,
      KernelAlgebra.kcomp_zero_right, KernelAlgebra.kcomp_zero_left,
      KernelAlgebra.kcomp_zero_right]

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ P Q _ _ => ⟨observe_idem P, observe_comm P Q⟩

end CategoricalInfluenceDiagramsProofs.Shadows.ObserveIdempotent
