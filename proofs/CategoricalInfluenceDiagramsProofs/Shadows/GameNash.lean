import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: equilibria of two decisions are person-by-person optima

Claim `cid.game-nash`, from `Game.seq_decision_eq_iff`. The shadows write the composite's
expected utility as the finite sum of ADR 0018 over the composite tables
`(K_f K_g, W_f K_g + K_f W_g)`, so "the composite's expected utility" is pinned to the
semantics, and take the two directions of "exactly when" separately.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.GameNash

open OpenInfluence FiniteKernelsProofs.Finite

/-- `EU(μ, c) = Σ_x μ x Σ_y (W x y + K x y c y)`. -/
abbrev EU {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ℝ := ∑ x, μ x * ∑ y, (W x y + K x y * c y)

/-- The expected utility of the serial composite of `f` then `g`. -/
abbrev EUc {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
    (g : RewardKernel Y Z) (μ : X → ℝ) (c : Z → ℝ) : ℝ :=
  EU (Kernel.comp f.K g.K) (Kernel.comp f.W g.K + Kernel.comp f.K g.W) μ c

/-- `seq_decision_eq_iff`, restated abstractly. -/
abbrev Candidate : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (S T : Type)
    (f : S → RewardKernel X Y) (g : T → RewardKernel Y Z)
    (hf : ∀ s, Kernel.Normalised (f s).K) (hg : ∀ t, Kernel.Normalised (g t).K)
    (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T),
    ((Game.decision f hf).seq (Game.decision g hg)).Eq μ c (s, t) ↔
      (∀ s', ((f s').comp (g t)).eu μ c ≤ ((f s).comp (g t)).eu μ c) ∧
        (∀ t', ((f s).comp (g t')).eu μ c ≤ ((f s).comp (g t)).eu μ c)

/-- "a pair of strategies is an equilibrium of their serial composite" only when "neither
component can raise the composite's expected utility by changing its own strategy alone". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (S T : Type)
    (f : S → RewardKernel X Y) (g : T → RewardKernel Y Z)
    (hf : ∀ s, Kernel.Normalised (f s).K) (hg : ∀ t, Kernel.Normalised (g t).K)
    (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T),
    ((Game.decision f hf).seq (Game.decision g hg)).Eq μ c (s, t) →
      (∀ s', EUc (f s') (g t) μ c ≤ EUc (f s) (g t) μ c) ∧
        ∀ t', EUc (f s) (g t') μ c ≤ EUc (f s) (g t) μ c

/-- ... and always when it holds. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (S T : Type)
    (f : S → RewardKernel X Y) (g : T → RewardKernel Y Z)
    (hf : ∀ s, Kernel.Normalised (f s).K) (hg : ∀ t, Kernel.Normalised (g t).K)
    (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T),
    ((∀ s', EUc (f s') (g t) μ c ≤ EUc (f s) (g t) μ c) ∧
        ∀ t', EUc (f s) (g t') μ c ≤ EUc (f s) (g t) μ c) →
      ((Game.decision f hf).seq (Game.decision g hg)).Eq μ c (s, t)

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ S T f g hf hg μ c s t =>
  (h X Y Z S T f g hf hg μ c s t).mp

theorem forward2 : Candidate → Shadow2 := fun h X Y Z _ _ _ S T f g hf hg μ c s t =>
  (h X Y Z S T f g hf hg μ c s t).mpr

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 X Y Z _ _ _ S T f g hf hg μ c s t =>
  ⟨h1 X Y Z S T f g hf hg μ c s t, h2 X Y Z S T f g hf hg μ c s t⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := fun _ _ _ _ _ _ _ _ f g hf hg μ c s t =>
  Game.seq_decision_eq_iff f g hf hg μ c s t

end CategoricalInfluenceDiagramsProofs.Shadows.GameNash
