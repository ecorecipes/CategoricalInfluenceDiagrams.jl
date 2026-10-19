import CategoricalInfluenceDiagramsProofs.GameTensor

/-!
# SA-Pass shadow module: the tensor of decision games with a product prior

Claim `cid.game-tensor`, from `Game.tensor_decision_eq_iff`. The shadows spell the prior as
the product `μ₁ x μ₂ x'` of two probability vectors and the composite's expected utility as
that of the tensor of the two plays, and split "exactly when neither factor can raise the
composite's expected utility by changing its own strategy alone" into its three directions.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.GameTensorProduct

open OpenInfluence OpenInfluence.Game FiniteKernelsProofs.Finite

/-- The composite's expected utility under the product prior. -/
abbrev joint {X Y X' Y' S T : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (pf : S → RewardKernel X Y) (pg : T → RewardKernel X' Y') (μ₁ : X → ℝ) (μ₂ : X' → ℝ)
    (c : Y × Y' → ℝ) (s : S) (t : T) : ℝ :=
  ((pf s).tensor (pg t)).eu (fun p => μ₁ p.1 * μ₂ p.2) c

/-- `tensor_decision_eq_iff`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X Y X' Y' S T : Type) [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (pf : S → RewardKernel X Y) (hf : ∀ s, Kernel.Normalised (pf s).K)
    (pg : T → RewardKernel X' Y') (hg : ∀ t, Kernel.Normalised (pg t).K) (μ₁ : X → ℝ)
    (μ₂ : X' → ℝ), ∑ x, μ₁ x = 1 → ∑ x', μ₂ x' = 1 → ∀ (c : Y × Y' → ℝ) (s : S) (t : T),
    ((decision pf hf).tensor (decision pg hg)).Eq (fun p => μ₁ p.1 * μ₂ p.2) c (s, t) ↔
      (∀ s', joint pf pg μ₁ μ₂ c s' t ≤ joint pf pg μ₁ μ₂ c s t) ∧
        ∀ t', joint pf pg μ₁ μ₂ c s t' ≤ joint pf pg μ₁ μ₂ c s t

/-- An equilibrium's first strategy is a best response, holding the second fixed. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y X' Y' S T : Type) [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (pf : S → RewardKernel X Y) (hf : ∀ s, Kernel.Normalised (pf s).K)
    (pg : T → RewardKernel X' Y') (hg : ∀ t, Kernel.Normalised (pg t).K) (μ₁ : X → ℝ)
    (μ₂ : X' → ℝ), ∑ x, μ₁ x = 1 → ∑ x', μ₂ x' = 1 → ∀ (c : Y × Y' → ℝ) (s : S) (t : T),
    ((decision pf hf).tensor (decision pg hg)).Eq (fun p => μ₁ p.1 * μ₂ p.2) c (s, t) →
      ∀ s', joint pf pg μ₁ μ₂ c s' t ≤ joint pf pg μ₁ μ₂ c s t

/-- An equilibrium's second strategy is a best response, holding the first fixed. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y X' Y' S T : Type) [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (pf : S → RewardKernel X Y) (hf : ∀ s, Kernel.Normalised (pf s).K)
    (pg : T → RewardKernel X' Y') (hg : ∀ t, Kernel.Normalised (pg t).K) (μ₁ : X → ℝ)
    (μ₂ : X' → ℝ), ∑ x, μ₁ x = 1 → ∑ x', μ₂ x' = 1 → ∀ (c : Y × Y' → ℝ) (s : S) (t : T),
    ((decision pf hf).tensor (decision pg hg)).Eq (fun p => μ₁ p.1 * μ₂ p.2) c (s, t) →
      ∀ t', joint pf pg μ₁ μ₂ c s t' ≤ joint pf pg μ₁ μ₂ c s t

/-- A pair of mutual best responses is an equilibrium. -/
abbrev Shadow3 : Prop :=
  ∀ (X Y X' Y' S T : Type) [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (pf : S → RewardKernel X Y) (hf : ∀ s, Kernel.Normalised (pf s).K)
    (pg : T → RewardKernel X' Y') (hg : ∀ t, Kernel.Normalised (pg t).K) (μ₁ : X → ℝ)
    (μ₂ : X' → ℝ), ∑ x, μ₁ x = 1 → ∑ x', μ₂ x' = 1 → ∀ (c : Y × Y' → ℝ) (s : S) (t : T),
    (∀ s', joint pf pg μ₁ μ₂ c s' t ≤ joint pf pg μ₁ μ₂ c s t) →
      (∀ t', joint pf pg μ₁ μ₂ c s t' ≤ joint pf pg μ₁ μ₂ c s t) →
      ((decision pf hf).tensor (decision pg hg)).Eq (fun p => μ₁ p.1 * μ₂ p.2) c (s, t)

theorem forward1 : Candidate → Shadow1 := fun h X Y X' Y' S T _ _ _ _ pf hf pg hg μ₁ μ₂ h₁ h₂
    c s t he => ((h X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t).mp he).1

theorem forward2 : Candidate → Shadow2 := fun h X Y X' Y' S T _ _ _ _ pf hf pg hg μ₁ μ₂ h₁ h₂
    c s t he => ((h X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t).mp he).2

theorem forward3 : Candidate → Shadow3 := fun h X Y X' Y' S T _ _ _ _ pf hf pg hg μ₁ μ₂ h₁ h₂
    c s t hs ht => (h X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t).mpr ⟨hs, ht⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate :=
  fun h1 h2 h3 X Y X' Y' S T _ _ _ _ pf hf pg hg μ₁ μ₂ h₁ h₂ c s t =>
    ⟨fun he => ⟨h1 X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t he,
        h2 X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t he⟩,
      fun hb => h3 X Y X' Y' S T pf hf pg hg μ₁ μ₂ h₁ h₂ c s t hb.1 hb.2⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ _ _ _ _ _ _ _ pf hf pg hg μ₁ μ₂ h₁ h₂ c s t =>
  tensor_decision_eq_iff pf hf pg hg μ₁ μ₂ h₁ h₂ c s t

end CategoricalInfluenceDiagramsProofs.Shadows.GameTensorProduct
