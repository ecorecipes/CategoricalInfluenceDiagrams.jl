import CategoricalInfluenceDiagramsProofs.Certificate.Composition

/-!
# SA-Pass shadow module: tensor certificates are sound

Claim `cid.tensor-certificate`, from `Composition.tensor_sound_K` and
`Composition.tensor_sound_W`. The shadows spell the recorded cells as `cellQ` of the result
tables at `resultIndex` and the tensor of the parts as the products `K_L K_R` and
`W_L K_R + K_L W_R`, with the bounds in full.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.TensorSound

open OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Composition

/-- The two theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (cc : Composition) (τ : ℚ), cc.checkTensor τ = true →
    ∃ h : cc.TensorAligned, ∀ (x : cc.left.InCoord) (x' : cc.right.InCoord)
      (y : cc.left.OutCoord) (y' : cc.right.OutCoord),
      |cc.composite.exactK (joinIn h x x') (joinOut h y y') -
          cc.left.exactK x y * cc.right.exactK x' y'| ≤
        2 * τ + τ * (|kHat cc.left x y| + |kHat cc.right x' y'| + τ)) ∧
  ∀ (cc : Composition) (τ : ℚ), cc.checkTensor τ = true →
    ∃ h : cc.TensorAligned, ∀ (x : cc.left.InCoord) (x' : cc.right.InCoord)
      (y : cc.left.OutCoord) (y' : cc.right.OutCoord),
      |cc.composite.exactW (joinIn h x x') (joinOut h y y') -
          (cc.left.exactW x y * cc.right.exactK x' y' +
            cc.left.exactK x y * cc.right.exactW x' y')| ≤
        2 * τ + τ * (|wHat cc.left x y| + |kHat cc.right x' y'| + |kHat cc.left x y| +
          |wHat cc.right x' y'| + 2 * τ)

/-- "the decoded tensor's exact probability ... is within the bound of the product of the
decoded parts' exact probabilities", the recorded cells spelled out. -/
abbrev Shadow1 : Prop :=
  ∀ (cc : Composition) (τ : ℚ), cc.checkTensor τ = true →
    ∃ h : cc.TensorAligned, ∀ (x : cc.left.InCoord) (x' : cc.right.InCoord)
      (y : cc.left.OutCoord) (y' : cc.right.OutCoord),
      |cc.composite.exactK (joinIn h x x') (joinOut h y y') -
          cc.left.exactK x y * cc.right.exactK x' y'| ≤
        2 * τ + τ * (|cellQ cc.left.result.K (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.K (cc.right.resultIndex x' y')| + τ)

/-- "... and its exact reward within the corresponding bound of `W ⊗ K + K ⊗ W`". -/
abbrev Shadow2 : Prop :=
  ∀ (cc : Composition) (τ : ℚ), cc.checkTensor τ = true →
    ∃ h : cc.TensorAligned, ∀ (x : cc.left.InCoord) (x' : cc.right.InCoord)
      (y : cc.left.OutCoord) (y' : cc.right.OutCoord),
      |cc.composite.exactW (joinIn h x x') (joinOut h y y') -
          (cc.left.exactW x y * cc.right.exactK x' y' +
            cc.left.exactK x y * cc.right.exactW x' y')| ≤
        2 * τ + τ * (|cellQ cc.left.result.W (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.K (cc.right.resultIndex x' y')| +
          |cellQ cc.left.result.K (cc.left.resultIndex x y)| +
          |cellQ cc.right.result.W (cc.right.resultIndex x' y')| + 2 * τ)

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 => ⟨h1, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ hc => tensor_sound_K hc, fun _ _ hc => tensor_sound_W hc⟩

end CategoricalInfluenceDiagramsProofs.Shadows.TensorSound
