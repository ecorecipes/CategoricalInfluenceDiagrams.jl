import CategoricalInfluenceDiagramsProofs.SharedPolicy

/-!
# SA-Pass shadow module: per-use gains at the absent-minded driver's optimum

Claim `cid.per-use-gains`, from `AbsentMinded.per_use_gains`. The claim is about one finite
witness, so the shadow is decidable by computing it, and the claim is registered as weak
(`independently_provable = true`). The shadow pins the sentence through the value of the
drive, `p (4 (1 - q) + q)`.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.PerUseGains

open OpenInfluence OpenInfluence.AbsentMinded

/-- The value of the drive. -/
abbrev drive (p q : ℝ) : ℝ := ((first p).comp (second q)).eu (fun _ => 1) (fun _ => 0)

/-- `per_use_gains`, restated. -/
abbrev Candidate : Prop :=
  drive 1 (2 / 3) - drive (2 / 3) (2 / 3) = 2 / 3 ∧
    drive (2 / 3) 1 - drive (2 / 3) (2 / 3) = -(2 / 3)

/-- "at the shared optimum of continuing with probability 2/3, continuing for sure at the
first junction alone gains 2/3 and at the second junction alone loses 2/3". -/
abbrev Shadow1 : Prop :=
  drive 1 (2 / 3) = drive (2 / 3) (2 / 3) + 2 / 3 ∧
    drive (2 / 3) 1 = drive (2 / 3) (2 / 3) - 2 / 3

theorem forward1 : Candidate → Shadow1 := fun h => ⟨by linarith [h.1], by linarith [h.2]⟩

theorem backward : Shadow1 → Candidate := fun h => ⟨by linarith [h.1], by linarith [h.2]⟩

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := per_use_gains

end CategoricalInfluenceDiagramsProofs.Shadows.PerUseGains
