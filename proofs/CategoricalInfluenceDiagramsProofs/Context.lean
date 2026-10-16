import CategoricalInfluenceDiagramsProofs.RewardKernel

/-!
# Expected utility in context and the contextual identity

For a reward kernel `f = (K, W) : X → Y`, a boundary prior `μ` on `X` and a terminal
continuation value `c` on `Y` (both arbitrary real functions), the expected utility is

`EU_f(μ, c) = Σ_x μ x · Σ_y (W x y + K x y · c y)`,

the bundle's `Score_{μ,c}(K, W)`. A suffix `g : Y → Z` turns a continuation `c` on `Z` into
the continuation `c_g y = Σ_z (W_g y z + K_g y z · c z)` on `Y`, its value function. A
prefix `f` turns a prior `μ` on `X` into the induced boundary law
`ν_f y = Σ_x μ x · K_f x y` and earns the prefix reward `L_f = Σ_x μ x · Σ_y W_f x y`.

The **contextual identity** (ADR 0018; the bundle's `INF-FIXED-CONTEXT`) is

`EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`.

The second equation holds for arbitrary tables (`eu_continuation`). The first needs the
suffix's probability component to be normalised (`eu_comp`): the prefix reward `W_f x y`
must survive the suffix with total mass one. `eu_comp` shows exactly that the defect is
`Σ_x μ x Σ_y W_f x y (Σ_z K_g y z - 1)` (`eu_comp_general`), so the hypothesis cannot simply
be dropped. For an interpreted diagram, where `f` and `g` are the reward kernels of the two
components under fixed strategies, `Interpretation.lean` applies this through the
functoriality of `interpret`.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

namespace RewardKernel

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Expected utility of a reward kernel under the boundary prior `μ` and the terminal
continuation `c`. -/
def eu (f : RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) : ℝ :=
  ∑ x, μ x * ∑ y, (f.W x y + f.K x y * c y)

/-- The value function `c_g` of a suffix `g` with terminal continuation `c`. -/
def continuation (g : RewardKernel Y Z) (c : Z → ℝ) : Y → ℝ :=
  fun y => ∑ z, (g.W y z + g.K y z * c z)

/-- The boundary law `ν_f = μ K_f` induced by the prefix `f` from the prior `μ`. -/
def pushforward (f : RewardKernel X Y) (μ : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, μ x * f.K x y

/-- The reward `L_f = Σ μ W_f` earned by the prefix `f` from the prior `μ`. -/
def prefixReward (f : RewardKernel X Y) (μ : X → ℝ) : ℝ :=
  ∑ x, μ x * ∑ y, f.W x y

/-- The expected utility with terminal continuation `c` is the prior-weighted continuation
of `f`. -/
theorem eu_eq_continuation (f : RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    f.eu μ c = ∑ x, μ x * f.continuation c x := rfl

/-- Composition without normalisation: the composite's expected utility differs from the
contextual one by the prefix reward times the suffix's missing mass. -/
theorem eu_comp_general (f : RewardKernel X Y) (g : RewardKernel Y Z) (μ : X → ℝ)
    (c : Z → ℝ) :
    (f.comp g).eu μ c =
      f.eu μ (g.continuation c) + ∑ x, μ x * ∑ y, f.W x y * ((∑ z, g.K y z) - 1) := by
  have hL : ∀ x, (∑ z, ((f.comp g).W x z + (f.comp g).K x z * c z)) =
      ∑ y, ∑ z, (f.W x y * g.K y z + f.K x y * g.W y z + f.K x y * g.K y z * c z) := by
    intro x
    simp only [comp_W, comp_K, Kernel.comp, Pi.add_apply, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_comm
  have hR : ∀ x y, (f.W x y + f.K x y * g.continuation c y) +
      f.W x y * ((∑ z, g.K y z) - 1) =
      ∑ z, (f.W x y * g.K y z + f.K x y * g.W y z + f.K x y * g.K y z * c z) := by
    intro x y
    have e : (∑ z, (f.W x y * g.K y z + f.K x y * g.W y z + f.K x y * g.K y z * c z)) =
        f.W x y * ∑ z, g.K y z + f.K x y * g.continuation c y := by
      simp only [continuation, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, mul_assoc,
        add_assoc]
    rw [e]
    ring
  simp only [eu, ← Finset.sum_add_distrib, ← mul_add, hL, ← hR]

/-- First half of the contextual identity: with a normalised suffix, the composite's
expected utility is the prefix's expected utility against the suffix's value function. -/
theorem eu_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (hg : Kernel.Normalised g.K)
    (μ : X → ℝ) (c : Z → ℝ) : (f.comp g).eu μ c = f.eu μ (g.continuation c) := by
  rw [eu_comp_general]
  have h0 : ∀ y, (∑ z, g.K y z) - 1 = 0 := fun y => by rw [hg y, sub_self]
  simp [h0]

/-- Second half of the contextual identity: against any continuation `c'`, the prefix's
expected utility is its own reward plus the continuation's expectation under the induced
boundary law. -/
theorem eu_continuation (f : RewardKernel X Y) (g : RewardKernel Y Z) (μ : X → ℝ)
    (c : Z → ℝ) :
    f.eu μ (g.continuation c) = f.prefixReward μ + g.eu (f.pushforward μ) c := by
  rw [eu_eq_continuation g]
  generalize g.continuation c = C
  simp only [eu, prefixReward, pushforward, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- **Contextual identity** for reward kernels:
`EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`, for a suffix with normalised `K`. -/
theorem contextual_identity (f : RewardKernel X Y) (g : RewardKernel Y Z)
    (hg : Kernel.Normalised g.K) (μ : X → ℝ) (c : Z → ℝ) :
    (f.comp g).eu μ c = f.eu μ (g.continuation c) ∧
      f.eu μ (g.continuation c) = f.prefixReward μ + g.eu (f.pushforward μ) c :=
  ⟨eu_comp f g hg μ c, eu_continuation f g μ c⟩

/-- The normalisation of the suffix cannot be dropped from the first half: here the suffix
loses all mass, and the prefix's reward of one is lost with it. -/
theorem eu_comp_needs_normalised :
    ∃ (f g : RewardKernel Unit Unit) (μ : Unit → ℝ) (c : Unit → ℝ),
      (f.comp g).eu μ c ≠ f.eu μ (g.continuation c) := by
  refine ⟨⟨fun _ _ => 1, fun _ _ => 1⟩, ⟨fun _ _ => 0, fun _ _ => 0⟩, fun _ => 1,
    fun _ => 0, ?_⟩
  simp [eu, comp, continuation, Kernel.comp]

end RewardKernel

end OpenInfluence
