import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# SA-Pass shadow module: randomising over whole strategies does not help

Claim `cid.mixture-sufficiency`, from `RewardKernel.eu_mix_le` and
`RewardKernel.conditionalValue_mix_le`. The shadows spell the mixture as the weighted sums
`(Σ q K, Σ q W)`, the expected utility as `Σ_x μ x Σ_y (W + K c)`, and the conditional value
as the ratio of the weighted value to the weighted mass, so they pin "nonnegative weights
summing to one", "at most that of one of its components" and "of positive mass".
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.MixtureSufficiency

open OpenInfluence FiniteKernelsProofs.Finite
open RewardKernel (Effect pull mass value conditionalValue mix)

/-- The expected utility of `(K, W)`. -/
abbrev euF {X Y : Type} [Fintype X] [Fintype Y] (K W : Kernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ℝ :=
  ∑ x, μ x * ∑ y, (W x y + K x y * c y)

/-- `eu_mix_le` and `conditionalValue_mix_le`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y ι : Type) [Fintype X] [Fintype Y] [Fintype ι] [Nonempty ι] (q : ι → ℝ),
      (∀ i, 0 ≤ q i) → ∑ i, q i = 1 → ∀ (f : ι → RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ),
      ∃ i, (mix q f).eu μ c ≤ (f i).eu μ c) ∧
    ∀ (X Y ι : Type) [Fintype X] [Fintype Y] [Fintype ι] (q : ι → ℝ), (∀ i, 0 ≤ q i) →
      ∀ (f : ι → RewardKernel X Y) (s : RewardKernel.State X) (e : Effect Y),
      (∀ i, 0 ≤ mass s ((f i).pull e)) →
      (∀ i, mass s ((f i).pull e) = 0 → value s ((f i).pull e) = 0) →
      0 < mass s ((mix q f).pull e) →
      ∃ i, 0 < mass s ((f i).pull e) ∧
        conditionalValue s ((mix q f).pull e) ≤ conditionalValue s ((f i).pull e)

/-- "A mixture of reward kernels with nonnegative weights summing to one has expected utility
at most that of one of its components." -/
abbrev Shadow1 : Prop :=
  ∀ (X Y ι : Type) [Fintype X] [Fintype Y] [Fintype ι] [Nonempty ι] (q : ι → ℝ),
    (∀ i, 0 ≤ q i) → ∑ i, q i = 1 → ∀ (K W : ι → Kernel X Y) (μ : X → ℝ) (c : Y → ℝ),
    ∃ i, euF (fun x y => ∑ j, q j * K j x y) (fun x y => ∑ j, q j * W j x y) μ c ≤
      euF (K i) (W i) μ c

/-- "... and conditional value at most that of one of its components of positive mass",
under the stated conditions on masses. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y ι : Type) [Fintype X] [Fintype Y] [Fintype ι] (q : ι → ℝ), (∀ i, 0 ≤ q i) →
    ∀ (K W : ι → Kernel X Y) (s : RewardKernel.State X) (e : Effect Y),
    (∀ i, 0 ≤ mass s ((⟨K i, W i⟩ : RewardKernel X Y).pull e)) →
    (∀ i, mass s ((⟨K i, W i⟩ : RewardKernel X Y).pull e) = 0 →
      value s ((⟨K i, W i⟩ : RewardKernel X Y).pull e) = 0) →
    0 < mass s ((⟨fun x y => ∑ j, q j * K j x y, fun x y => ∑ j, q j * W j x y⟩ :
      RewardKernel X Y).pull e) →
    ∃ i, 0 < mass s ((⟨K i, W i⟩ : RewardKernel X Y).pull e) ∧
      value s ((⟨fun x y => ∑ j, q j * K j x y, fun x y => ∑ j, q j * W j x y⟩ :
          RewardKernel X Y).pull e) /
        mass s ((⟨fun x y => ∑ j, q j * K j x y, fun x y => ∑ j, q j * W j x y⟩ :
          RewardKernel X Y).pull e) ≤
      value s ((⟨K i, W i⟩ : RewardKernel X Y).pull e) /
        mass s ((⟨K i, W i⟩ : RewardKernel X Y).pull e)

theorem forward1 : Candidate → Shadow1 := fun h X Y ι _ _ _ _ q hq hs K W μ c =>
  h.1 X Y ι q hq hs (fun i => ⟨K i, W i⟩) μ c

theorem forward2 : Candidate → Shadow2 := fun h X Y ι _ _ _ q hq K W s e hm hz hp =>
  h.2 X Y ι q hq (fun i => ⟨K i, W i⟩) s e hm hz hp

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun X Y ι _ _ _ _ q hq hs f μ c => h1 X Y ι q hq hs (fun i => (f i).K) (fun i => (f i).W) μ c,
    fun X Y ι _ _ _ q hq f s e hm hz hp =>
      h2 X Y ι q hq (fun i => (f i).K) (fun i => (f i).W) s e hm hz hp⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ _ q hq hs f μ c => RewardKernel.eu_mix_le q hq hs f μ c,
    fun _ _ _ _ _ _ q hq f s e hm hz hp => RewardKernel.conditionalValue_mix_le q hq f s e hm hz hp⟩

end CategoricalInfluenceDiagramsProofs.Shadows.MixtureSufficiency
