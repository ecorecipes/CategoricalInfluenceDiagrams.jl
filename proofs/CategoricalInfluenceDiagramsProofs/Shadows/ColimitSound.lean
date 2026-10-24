import CategoricalInfluenceDiagramsProofs.Certificate.Colimit

/-!
# SA-Pass shadow module: colimit certificates give the composite's exact semantics

Claim `cid.colimit-certificate`, from `Colimit.colimit_sound_K` and
`Colimit.colimit_sound_W`. The shadows split the claim into its probability and reward
halves.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.ColimitSound

open OpenInfluence.RewardCertificate

open Classical in
/-- "its decoded probability is the sum, over the boundary coordinates of the parts consistent
with them, of the product of the parts' decoded probabilities". -/
abbrev Shadow1 : Prop :=
  ∀ (cc : Colimit) (τ : ℚ), cc.check τ = true →
    ∀ (x : cc.composite.InCoord) (y : cc.composite.OutCoord),
      cc.composite.exactK x y = ∑ t : cc.Ports,
        if cc.Consistent x y t then ∏ i, (cc.part i).exactK (t i).1 (t i).2 else 0

open Classical in
/-- "and its decoded reward is the corresponding sum of each part's reward times the other
parts' probabilities". -/
abbrev Shadow2 : Prop :=
  ∀ (cc : Colimit) (τ : ℚ), cc.check τ = true →
    ∀ (x : cc.composite.InCoord) (y : cc.composite.OutCoord),
      cc.composite.exactW x y = ∑ t : cc.Ports,
        if cc.Consistent x y t then ∑ i, (cc.part i).exactW (t i).1 (t i).2 *
          ∏ j ∈ Finset.univ.erase i, (cc.part j).exactK (t j).1 (t j).2 else 0

/-- The two theorems. -/
abbrev Candidate : Prop := Shadow1 ∧ Shadow2

theorem forward1 : Candidate → Shadow1 := fun h => h.1

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 => ⟨h1, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ h x y => Colimit.colimit_sound_K h x y, fun _ _ h x y => Colimit.colimit_sound_W h x y⟩

end CategoricalInfluenceDiagramsProofs.Shadows.ColimitSound
