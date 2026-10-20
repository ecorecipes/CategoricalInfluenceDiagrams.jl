import CategoricalInfluenceDiagramsProofs.Certificate.Composition

/-!
# SA-Pass shadow module: composition certificates are sound

Claim `cid.composition-certificate`, from `Composition.composition_sound_K` and
`Composition.composition_sound_W`. The shadows spell the recorded cells as `cellQ` of the
result tables at `resultIndex`, the composite of the parts as the sums over the middle
coordinates `Σ_y K_L K_R` and `Σ_y (W_L K_R + K_L W_R)`, and the bounds in full, so they pin
"within ... of the composite, in the category of reward kernels, of the decoded parts".
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.CompositionSound

open OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Composition

/-- The two theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (cc : Composition) (τ : ℚ), cc.check τ = true →
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactK (inC h x) (outC h z) -
          ∑ y, cc.left.exactK x y * cc.right.exactK (mid h y) z| ≤
        2 * τ + τ * ∑ y, (|kHat cc.left x y| + |kHat cc.right (mid h y) z| + τ)) ∧
  ∀ (cc : Composition) (τ : ℚ), cc.check τ = true →
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactW (inC h x) (outC h z) -
          ∑ y, (cc.left.exactW x y * cc.right.exactK (mid h y) z +
            cc.left.exactK x y * cc.right.exactW (mid h y) z)| ≤
        2 * τ + τ * ∑ y, (|wHat cc.left x y| + |kHat cc.right (mid h y) z| +
          |kHat cc.left x y| + |wHat cc.right (mid h y) z| + 2 * τ)

/-- "the decoded composite's exact probability ... is within the bound of the composite of
the decoded parts' exact probabilities", the recorded cells spelled out. -/
abbrev Shadow1 : Prop :=
  ∀ (cc : Composition) (τ : ℚ), cc.check τ = true →
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactK (inC h x) (outC h z) -
          ∑ y, cc.left.exactK x y * cc.right.exactK (mid h y) z| ≤
        2 * τ + τ * ∑ y, (|cellQ cc.left.result.K (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.K (cc.right.resultIndex (mid h y) z)| + τ)

/-- "... and its exact reward within the corresponding bound of the expectation-semiring
composite". -/
abbrev Shadow2 : Prop :=
  ∀ (cc : Composition) (τ : ℚ), cc.check τ = true →
    ∃ h : cc.Aligned, ∀ (x : cc.left.InCoord) (z : cc.right.OutCoord),
      |cc.composite.exactW (inC h x) (outC h z) -
          ∑ y, (cc.left.exactW x y * cc.right.exactK (mid h y) z +
            cc.left.exactK x y * cc.right.exactW (mid h y) z)| ≤
        2 * τ + τ * ∑ y, (|cellQ cc.left.result.W (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.K (cc.right.resultIndex (mid h y) z)| +
          |cellQ cc.left.result.K (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.W (cc.right.resultIndex (mid h y) z)| + 2 * τ)

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 => ⟨h1, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ hc => composition_sound_K hc, fun _ _ hc => composition_sound_W hc⟩

end CategoricalInfluenceDiagramsProofs.Shadows.CompositionSound
