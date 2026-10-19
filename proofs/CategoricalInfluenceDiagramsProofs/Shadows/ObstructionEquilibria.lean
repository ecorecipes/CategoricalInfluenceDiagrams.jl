import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: the equilibria of the obstruction witness

Claim `cid.obstruction-equilibria`, from `Obstruction.obstruction_eq_iff` and
`Obstruction.composite_eu`. The claim is about one finite witness, so every shadow is
decidable by computing it, and the claim is registered as weak
(`independently_provable = true`). The shadows pin "exactly the strategies that take the
early action" as two directions and "each of them attains the joint optimum 4" as a value.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.ObstructionEquilibria

open OpenInfluence OpenInfluence.Obstruction RewardKernel

/-- `obstruction_eq_iff` and the value of the strategies it names, restated. -/
abbrev Candidate : Prop :=
  (∀ (a : Bool) (τ : Bool → Bool), Obstruction.game.Eq unitPrior zeroCont (a, τ) ↔ a = true) ∧
    ∀ τ : Bool → Bool, ((early true).comp (late τ)).eu unitPrior zeroCont = 4

/-- "the equilibria are exactly the strategies that take the early action": every
equilibrium takes it ... -/
abbrev Shadow1 : Prop :=
  ∀ (a : Bool) (τ : Bool → Bool), Obstruction.game.Eq unitPrior zeroCont (a, τ) → a = true

/-- ... and every strategy that takes it is an equilibrium, whatever the late policy. -/
abbrev Shadow2 : Prop :=
  ∀ τ : Bool → Bool, Obstruction.game.Eq unitPrior zeroCont (true, τ)

/-- "each of them attains the joint optimum 4". -/
abbrev Shadow3 : Prop :=
  ∀ τ : Bool → Bool, ((early true).comp (late τ)).eu unitPrior zeroCont = 4

theorem forward1 : Candidate → Shadow1 := fun h a τ => (h.1 a τ).mp

theorem forward2 : Candidate → Shadow2 := fun h τ => (h.1 true τ).mpr rfl

theorem forward3 : Candidate → Shadow3 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun a τ => ⟨h1 a τ, fun ha => ha ▸ h2 τ⟩, h3⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨obstruction_eq_iff, fun τ => by rw [Obstruction.composite_eu]; norm_num⟩

end CategoricalInfluenceDiagramsProofs.Shadows.ObstructionEquilibria
