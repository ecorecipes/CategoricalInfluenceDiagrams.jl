import CategoricalInfluenceDiagramsProofs.RewardKernel

/-!
# SA-Pass shadow module: discard is natural only for reward-free normalised kernels

Claim `cid.discard-not-natural`, from `RewardKernel.comp_discard_eq_discard_iff`. The
candidate is restated abstractly, universally quantified over the reward kernel and its
types. The prose's discard is the one lifted with zero reward, `(discard, 0)`.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.DiscardNatural

open OpenInfluence FiniteKernelsProofs.Finite

/-- Discard lifted with zero reward, as the prose describes it. -/
abbrev zeroDiscard (X : Type) : RewardKernel X Unit := ⟨Kernel.discard X, 0⟩

/-- `comp_discard_eq_discard_iff`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X Y : Type) [Fintype Y] (f : RewardKernel X Y),
    f.comp (RewardKernel.discard Y) = RewardKernel.discard X ↔
      Kernel.Normalised f.K ∧ ∀ x, ∑ y, f.W x y = 0

/-- "natural for exactly the reward kernels ...": if discard is natural for `f`, then `f`'s
probability component is normalised and its reward from every input sums to zero. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : Type) [Fintype Y] (f : RewardKernel X Y),
    f.comp (zeroDiscard Y) = zeroDiscard X →
      Kernel.Normalised f.K ∧ ∀ x, ∑ y, f.W x y = 0

/-- ... and conversely, for every such `f` discard is natural. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y : Type) [Fintype Y] (f : RewardKernel X Y),
    Kernel.Normalised f.K → (∀ x, ∑ y, f.W x y = 0) → f.comp (zeroDiscard Y) = zeroDiscard X

theorem forward1 : Candidate → Shadow1 := fun h X Y _ f hf => (h X Y f).1 hf

theorem forward2 : Candidate → Shadow2 := fun h X Y _ f hK hW => (h X Y f).2 ⟨hK, hW⟩

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 X Y _ f =>
  ⟨h1 X Y f, fun ⟨hK, hW⟩ => h2 X Y f hK hW⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ f => RewardKernel.comp_discard_eq_discard_iff f

end CategoricalInfluenceDiagramsProofs.Shadows.DiscardNatural
