import CategoricalInfluenceDiagramsProofs.Perfection

/-!
# SA-Pass shadow module: perfection refines equilibrium, by backward induction

Claim `cid.perfect-equilibrium`, from `Game.perfect_eq_decision` and `Game.seq_perfect_eq_iff`.
The shadows spell "optimal from every input state" as the value function `Σ_y (W + K c)` at
each input, "with a nonnegative prior" as `μ ≥ 0`, and backward induction as the two
conditions on the parts of a serial composite, neither mentioning the prior.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.PerfectRefines

open OpenInfluence OpenInfluence.Game FiniteKernelsProofs.Finite

/-- The two theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y S : Type) [Fintype X] [Fintype Y] (play : S → RewardKernel X Y)
      (h : ∀ s, Kernel.Normalised (play s).K) (μ : X → ℝ), (∀ x, 0 ≤ μ x) → ∀ (c : Y → ℝ) (s : S),
      (perfect play h).Eq μ c s → (decision play h).Eq μ c s) ∧
    ∀ (X Y Z S T : Type) [Fintype X] [Fintype Y] [Fintype Z] (pf : S → RewardKernel X Y)
      (hf : ∀ s, Kernel.Normalised (pf s).K) (pg : T → RewardKernel Y Z)
      (hg : ∀ t, Kernel.Normalised (pg t).K) (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T),
      ((perfect pf hf).seq (perfect pg hg)).Eq μ c (s, t) ↔
        (∀ x s', (pf s').continuation ((pg t).continuation c) x ≤
          (pf s).continuation ((pg t).continuation c) x) ∧
        ∀ y t', (pg t').continuation c y ≤ (pg t).continuation c y

/-- "a strategy optimal from every input state is a best response under every nonnegative
prior", with the values spelled out. -/
abbrev Shadow1 : Prop :=
  ∀ (X Y S : Type) [Fintype X] [Fintype Y] (play : S → RewardKernel X Y)
    (_h : ∀ s, Kernel.Normalised (play s).K) (μ : X → ℝ), (∀ x, 0 ≤ μ x) → ∀ (c : Y → ℝ) (s : S),
    (∀ x s', ∑ y, ((play s').W x y + (play s').K x y * c y) ≤
      ∑ y, ((play s).W x y + (play s).K x y * c y)) →
    ∀ s', ∑ x, μ x * ∑ y, ((play s').W x y + (play s').K x y * c y) ≤
      ∑ x, μ x * ∑ y, ((play s).W x y + (play s).K x y * c y)

/-- "backward induction": the composite's perfect equilibria are the suffix perfect against
the continuation and the prefix perfect against the suffix's value function. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z S T : Type) [Fintype X] [Fintype Y] [Fintype Z] (pf : S → RewardKernel X Y)
    (hf : ∀ s, Kernel.Normalised (pf s).K) (pg : T → RewardKernel Y Z)
    (hg : ∀ t, Kernel.Normalised (pg t).K) (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T),
    ((perfect pf hf).seq (perfect pg hg)).Eq μ c (s, t) ↔
      (∀ x s', (pf s').continuation ((pg t).continuation c) x ≤
        (pf s).continuation ((pg t).continuation c) x) ∧
      ∀ y t', (pg t').continuation c y ≤ (pg t).continuation c y

theorem forward1 : Candidate → Shadow1 := fun h X Y S _ _ play hp μ hμ c s hs =>
  h.1 X Y S play hp μ hμ c s hs

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun X Y S _ _ play hp μ hμ c s hs => h1 X Y S play hp μ hμ c s hs, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ play hp μ hμ c s hs => perfect_eq_decision play hp μ hμ c s hs,
    fun _ _ _ _ _ _ _ _ pf hf pg hg μ c s t => seq_perfect_eq_iff pf hf pg hg μ c s t⟩

end CategoricalInfluenceDiagramsProofs.Shadows.PerfectRefines
