import CategoricalInfluenceDiagramsProofs.Category

/-!
# SA-Pass shadow module: `FinRew` is a symmetric monoidal copy-discard category

Claim `cid.finrew-instances`, from the `FinRew` instances. The claim is about a
construction, so every shadow holds by the definitions and the claim is registered as weak
(`independently_provable = true`), as `fk.finstoch-markov` is: the shadows pin what "reward
kernels with stochastic probability component" and "lifted ... with zero reward" mean,
without discriminating further.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.FinRewInstances

open CategoryTheory MonoidalCategory OpenInfluence FiniteKernelsProofs.Finite
open scoped ComonObj

/-- The morphisms are the reward kernels with stochastic `K`, composition and tensor are
those of reward kernels, and every structural map has zero reward. -/
abbrev Candidate : Prop :=
  (∀ (X Y : FinRew) (r : RewardKernel X.carrier Y.carrier),
      Kernel.Stochastic r.K ↔ ∃ f : X ⟶ Y, f.val = r) ∧
    (∀ (X Y Z : FinRew) (f : X ⟶ Y) (g : Y ⟶ Z), (f ≫ g).val = f.val.comp g.val) ∧
    (∀ (X Y X' Y' : FinRew) (f : X ⟶ Y) (g : X' ⟶ Y'), (f ⊗ₘ g).val = f.val.tensor g.val) ∧
    ∀ X Y Z : FinRew, (α_ X Y Z).hom.val.W = 0 ∧ (λ_ X).hom.val.W = 0 ∧
      (ρ_ X).hom.val.W = 0 ∧ (β_ X Y).hom.val.W = 0 ∧ Δ[X].val.W = 0 ∧ ε[X].val.W = 0

/-- "Reward kernels with stochastic probability component": every such reward kernel is a
morphism. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y : FinRew) (r : RewardKernel X.carrier Y.carrier), Kernel.Stochastic r.K →
    ∃ f : X ⟶ Y, f.val = r

/-- ... and every morphism is one. -/
abbrev Shadow2 : Prop := ∀ (X Y : FinRew) (f : X ⟶ Y), Kernel.Stochastic f.val.K

/-- The category's composition and tensor are those of reward kernels. -/
abbrev Shadow3 : Prop :=
  (∀ (X Y Z : FinRew) (f : X ⟶ Y) (g : Y ⟶ Z), (f ≫ g).val = f.val.comp g.val) ∧
    ∀ (X Y X' Y' : FinRew) (f : X ⟶ Y) (g : X' ⟶ Y'), (f ⊗ₘ g).val = f.val.tensor g.val

/-- "associator, unitors, symmetry, copy and discard ... with zero reward". -/
abbrev Shadow4 : Prop :=
  ∀ X Y Z : FinRew, (α_ X Y Z).hom.val.W = 0 ∧ (λ_ X).hom.val.W = 0 ∧
    (ρ_ X).hom.val.W = 0 ∧ (β_ X Y).hom.val.W = 0 ∧ Δ[X].val.W = 0 ∧ ε[X].val.W = 0

theorem forward1 : Candidate → Shadow1 := fun h X Y r hr => (h.1 X Y r).1 hr

theorem forward2 : Candidate → Shadow2 := fun h X Y f => (h.1 X Y f.val).2 ⟨f, rfl⟩

theorem forward3 : Candidate → Shadow3 := fun h => ⟨h.2.1, h.2.2.1⟩

theorem forward4 : Candidate → Shadow4 := fun h => h.2.2.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := by
  intro h1 h2 h3 h4
  refine ⟨fun X Y r => ⟨h1 X Y r, ?_⟩, h3.1, h3.2, h4⟩
  rintro ⟨f, rfl⟩
  exact h2 X Y f

/-- SA-Pass anchor: the cited construction proves `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ r => ⟨fun hr => ⟨⟨r, hr⟩, rfl⟩, fun ⟨f, hf⟩ => hf ▸ f.2⟩,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end CategoricalInfluenceDiagramsProofs.Shadows.FinRewInstances
