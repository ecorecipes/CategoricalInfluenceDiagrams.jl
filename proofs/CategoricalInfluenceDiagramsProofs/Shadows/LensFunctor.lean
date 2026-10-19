import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: the lens of a reward kernel is functorial

Claim `cid.lens-functor`, from `RewardKernel.lens_comp` and `RewardKernel.lens_id`. The
shadows spell the forward map as the boundary law `ν y = Σ_x μ x K x y` and the backward map
as the value function `c' x = Σ_y (W x y + K x y c y)`, so they pin `pushforward` and
`continuation` to the formulas of ADR 0020.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.LensFunctor

open OpenInfluence FiniteKernelsProofs.Finite

/-- The boundary law `ν y = Σ_x μ x K x y`. -/
abbrev nu {X Y : Type} [Fintype X] (K : Kernel X Y) (μ : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, μ x * K x y

/-- The value function `c' x = Σ_y (W x y + K x y c y)`. -/
abbrev cont {X Y : Type} [Fintype Y] (K W : Kernel X Y) (c : Y → ℝ) : X → ℝ :=
  fun x => ∑ y, (W x y + K x y * c y)

/-- `lens_comp` and `lens_id`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z), Kernel.Normalised g.K → (f.comp g).lens = f.lens.comp g.lens) ∧
    ∀ (X : Type) [Fintype X] [DecidableEq X], (RewardKernel.id X).lens = Lens.id X

/-- "sends serial composition with a normalised suffix to composition of lenses": forward,
the boundary law of the composite is the suffix's boundary law of the prefix's. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf : Kernel X Y) (Kg : Kernel Y Z),
    Kernel.Normalised Kg → ∀ μ : X → ℝ, nu (Kernel.comp Kf Kg) μ = nu Kg (nu Kf μ)

/-- ... and backward, the value function of the composite is the prefix's value function of
the suffix's, in the opposite order. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y)
    (Kg Wg : Kernel Y Z), Kernel.Normalised Kg → ∀ c : Z → ℝ,
    cont (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) c =
      cont Kf Wf (cont Kg Wg c)

/-- "and the identity to the identity lens": the identity `(id, 0)` leaves priors and
continuations unchanged. -/
abbrev Shadow3 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X],
    (∀ μ : X → ℝ, nu (Kernel.idK X) μ = μ) ∧ ∀ c : X → ℝ, cont (Kernel.idK X) 0 c = c

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ Kf Kg hg μ =>
  congrFun (congrArg Lens.fwd (h.1 X Y Z ⟨Kf, 0⟩ ⟨Kg, 0⟩ hg)) μ

theorem forward2 : Candidate → Shadow2 := fun h X Y Z _ _ _ Kf Wf Kg Wg hg c =>
  congrFun (congrArg Lens.bwd (h.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ hg)) c

theorem forward3 : Candidate → Shadow3 := fun h X _ _ =>
  ⟨fun μ => congrFun (congrArg Lens.fwd (h.2 X)) μ,
    fun c => congrFun (congrArg Lens.bwd (h.2 X)) c⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun X Y Z _ _ _ f g hg => by
      simp only [RewardKernel.lens, Lens.comp, Lens.mk.injEq]
      exact ⟨funext fun μ => h1 X Y Z f.K g.K hg μ,
        funext fun c => h2 X Y Z f.K f.W g.K g.W hg c⟩,
    fun X _ _ => by
      simp only [RewardKernel.lens, Lens.id, Lens.mk.injEq]
      exact ⟨funext fun μ => (h3 X).1 μ, funext fun c => (h3 X).2 c⟩⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ f g hg => RewardKernel.lens_comp f g hg, fun _ _ _ => RewardKernel.lens_id⟩

end CategoricalInfluenceDiagramsProofs.Shadows.LensFunctor
