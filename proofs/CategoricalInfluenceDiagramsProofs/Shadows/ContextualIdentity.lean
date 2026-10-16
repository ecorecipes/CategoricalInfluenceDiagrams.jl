import CategoricalInfluenceDiagramsProofs.Interpretation

/-!
# SA-Pass shadow module: the contextual identity

Claim `cid.contextual-identity`, from `RewardKernel.contextual_identity` and
`IDInterpretation.contextual_identity`. The shadows spell out the prose's `EU_f(μ, c)`,
`c_g`, `ν_f` and `L_f` as the finite sums of ADR 0018, so they pin the library's `eu`,
`continuation`, `pushforward` and `prefixReward` to those formulas.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.ContextualIdentity

open OpenInfluence OpenInfluence.IDInterpretation FiniteKernelsProofs.Finite

/-- `EU(μ, c) = Σ_x μ x Σ_y (W x y + K x y c y)`. -/
abbrev EU {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ℝ := ∑ x, μ x * ∑ y, (W x y + K x y * c y)

/-- The suffix's value function `c_g y = Σ_z (W_g y z + K_g y z c z)`. -/
abbrev cont {Y Z : Type} [Fintype Z] (K W : Kernel Y Z) (c : Z → ℝ) : Y → ℝ :=
  fun y => ∑ z, (W y z + K y z * c z)

/-- The induced boundary law `ν_f y = Σ_x μ x K_f x y`. -/
abbrev nu {X Y : Type} [Fintype X] (K : Kernel X Y) (μ : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, μ x * K x y

/-- The prefix reward `L_f = Σ_x μ x Σ_y W_f x y`. -/
abbrev L {X Y : Type} [Fintype X] [Fintype Y] (W : Kernel X Y) (μ : X → ℝ) : ℝ :=
  ∑ x, μ x * ∑ y, W x y

/-- The two contextual identities, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z), Kernel.Normalised g.K → ∀ (μ : X → ℝ) (c : Z → ℝ),
      (f.comp g).eu μ c = f.eu μ (g.continuation c) ∧
        f.eu μ (g.continuation c) = f.prefixReward μ + g.eu (f.pushforward μ) c) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y Z : S.Iface)
      (f : IDNet X Y) (g : IDNet Y Z) (μ : (M.interp σ).Boundary X → ℝ)
      (c : (M.interp σ).Boundary Z → ℝ),
      (M.interpret σ (f.comp g)).eu μ c =
          (M.interpret σ f).eu μ ((M.interpret σ g).continuation c) ∧
        (M.interpret σ f).eu μ ((M.interpret σ g).continuation c) =
          (M.interpret σ f).prefixReward μ +
            (M.interpret σ g).eu ((M.interpret σ f).pushforward μ) c

/-- "For reward kernels whose suffix has a normalised probability component ...
`EU_{f;g}(μ, c) = EU_f(μ, c_g)`". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y) (Kg Wg : Kernel Y Z),
    Kernel.Normalised Kg → ∀ (μ : X → ℝ) (c : Z → ℝ),
    EU (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) μ c =
      EU Kf Wf μ (cont Kg Wg c)

/-- "... `EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`". -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y) (Kg Wg : Kernel Y Z),
    Kernel.Normalised Kg → ∀ (μ : X → ℝ) (c : Z → ℝ),
    EU Kf Wf μ (cont Kg Wg c) = L Wf μ + EU Kg Wg (nu Kf μ) c

/-- "and so for all open influence diagrams under a fixed strategy": both equations, for the
interpretations of the two components, with no hypothesis. -/
abbrev Shadow3 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y Z : S.Iface)
    (f : IDNet X Y) (g : IDNet Y Z) (μ : (M.interp σ).Boundary X → ℝ)
    (c : (M.interp σ).Boundary Z → ℝ),
    EU (M.interpret σ (f.comp g)).K (M.interpret σ (f.comp g)).W μ c =
        EU (M.interpret σ f).K (M.interpret σ f).W μ
          (cont (M.interpret σ g).K (M.interpret σ g).W c) ∧
      EU (M.interpret σ f).K (M.interpret σ f).W μ
          (cont (M.interpret σ g).K (M.interpret σ g).W c) =
        L (M.interpret σ f).W μ +
          EU (M.interpret σ g).K (M.interpret σ g).W (nu (M.interpret σ f).K μ) c

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ Kf Wf Kg Wg hg μ c =>
  (h.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ hg μ c).1

theorem forward2 : Candidate → Shadow2 := fun h X Y Z _ _ _ Kf Wf Kg Wg hg μ c =>
  (h.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ hg μ c).2

theorem forward3 : Candidate → Shadow3 := fun h S M σ X Y Z f g μ c => h.2 S M σ X Y Z f g μ c

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun X Y Z _ _ _ f g hg μ c =>
      ⟨h1 X Y Z f.K f.W g.K g.W hg μ c, h2 X Y Z f.K f.W g.K g.W hg μ c⟩,
    fun S M σ X Y Z f g μ c => h3 S M σ X Y Z f g μ c⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ f g hg μ c => RewardKernel.contextual_identity f g hg μ c,
    fun _ M σ _ _ _ f g μ c => M.contextual_identity σ f g μ c⟩

end CategoricalInfluenceDiagramsProofs.Shadows.ContextualIdentity
