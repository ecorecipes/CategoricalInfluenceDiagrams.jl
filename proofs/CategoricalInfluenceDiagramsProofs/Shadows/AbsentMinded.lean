import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# SA-Pass shadow module: randomising helps when decisions share a policy

Claim `cid.absent-minded`, from `AbsentMinded.randomising_helps` and
`AbsentMinded.independent_deterministic_optimal`. The claim is about one finite witness, so
every shadow is decidable by computing it, and the claim is registered as weak
(`independently_provable = true`). The shadows still pin the sentence: the value of the drive
is `p (4 (1 - q) + q)` for continuation probabilities `p` and `q`, the shared policy `2/3` is
worth `4/3` while both deterministic shared policies are worth at most `1`, and with a policy
each the deterministic pair is worth `4` and bounds every pair of probabilities.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.AbsentMinded

open OpenInfluence OpenInfluence.AbsentMinded

/-- The value of the drive. -/
abbrev drive (p q : ℝ) : ℝ := ((first p).comp (second q)).eu (fun _ => 1) (fun _ => 0)

/-- `randomising_helps` and `independent_deterministic_optimal`, restated. -/
abbrev Candidate : Prop :=
  (drive (2 / 3) (2 / 3) = 4 / 3 ∧ ∀ p ∈ ({0, 1} : Set ℝ), drive p p ≤ 1) ∧
    drive 1 0 = 4 ∧ ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → drive p q ≤ 4

/-- The witness: continuing at the first junction with probability `p` and at the second
with probability `q` is worth `p (4 (1 - q) + q)`. -/
abbrev Shadow1 : Prop := ∀ p q : ℝ, drive p q = p * (4 * (1 - q) + q)

/-- "continuing with probability 2/3 at both junctions is worth 4/3, while either
deterministic policy is worth at most 1". -/
abbrev Shadow2 : Prop := drive (2 / 3) (2 / 3) = 4 / 3 ∧ drive 0 0 ≤ 1 ∧ drive 1 1 ≤ 1

/-- "with a policy each, the deterministic pair that continues and then exits is worth 4 and
no pair of probabilities does better". -/
abbrev Shadow3 : Prop :=
  drive 1 0 = 4 ∧ ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → drive p q ≤ 4

theorem forward1 : Candidate → Shadow1 := fun _ p q => drive_eu p q

theorem forward2 : Candidate → Shadow2 := fun h =>
  ⟨h.1.1, h.1.2 0 (by simp), h.1.2 1 (by simp)⟩

theorem forward3 : Candidate → Shadow3 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun _ h2 h3 =>
  ⟨⟨h2.1, fun p hp => by rcases hp with rfl | rfl; exacts [h2.2.1, h2.2.2]⟩, h3⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate := ⟨randomising_helps, independent_deterministic_optimal⟩

end CategoricalInfluenceDiagramsProofs.Shadows.AbsentMinded
