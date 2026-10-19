import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: an equilibrium need not be optimal

Claim `cid.game-coordination`, from `Coordination.coordination_equilibrium_not_optimal`. The
claim is about one finite witness, so every shadow is decidable by computing it, and the
claim is registered as weak (`independently_provable = true`). The shadows still pin what
"an equilibrium is worth 1 where the optimum is 2" means: an equilibrium of value 1 exists,
the value 2 is attained, and nothing exceeds it.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.GameCoordination

open OpenInfluence OpenInfluence.Coordination OpenInfluence.Obstruction RewardKernel

/-- `coordination_equilibrium_not_optimal`, restated. -/
abbrev Candidate : Prop :=
  Coordination.game.Eq unitPrior zeroCont (false, false) ∧
    Coordination.game.Eq unitPrior zeroCont (true, true) ∧
    ((first false).comp (second false)).eu unitPrior zeroCont = 1 ∧
    ((first true).comp (second true)).eu unitPrior zeroCont = 2 ∧
    (∀ a b, ((first a).comp (second b)).eu unitPrior zeroCont ≤ 2) ∧ (1 : ℝ) < 2

/-- "an equilibrium is worth 1": there is an equilibrium whose composite value is 1. -/
abbrev Shadow1 : Prop :=
  ∃ a b, Coordination.game.Eq unitPrior zeroCont (a, b) ∧
    ((first a).comp (second b)).eu unitPrior zeroCont = 1

/-- "the optimum is 2": the value 2 is attained ... -/
abbrev Shadow2 : Prop :=
  ∃ a b, ((first a).comp (second b)).eu unitPrior zeroCont = 2

/-- ... and not exceeded. -/
abbrev Shadow3 : Prop :=
  ∀ a b, ((first a).comp (second b)).eu unitPrior zeroCont ≤ 2

theorem forward1 : Candidate → Shadow1 := fun h => ⟨false, false, h.1, h.2.2.1⟩

theorem forward2 : Candidate → Shadow2 := fun h => ⟨true, true, h.2.2.2.1⟩

theorem forward3 : Candidate → Shadow3 := fun h => h.2.2.2.2.1

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := by
  intro _ _ h3
  -- Shadows 1 and 2 say that such strategies exist; the candidate names them, so its
  -- equilibrium and value conjuncts are checked on the witness.
  refine ⟨(game_eq_iff _ _).mpr ⟨fun a => ?_, fun b => ?_⟩,
    (game_eq_iff _ _).mpr ⟨fun a => ?_, fun b => ?_⟩, ?_, ?_, h3, by norm_num⟩
  · cases a <;> norm_num [payoff]
  · cases b <;> norm_num [payoff]
  · cases a <;> norm_num [payoff]
  · cases b <;> norm_num [payoff]
  · rw [Coordination.composite_eu]; simp [payoff]
  · rw [Coordination.composite_eu]; simp [payoff]

/-- SA-Pass anchor: the cited theorem proves `Candidate` as stated. -/
theorem anchor : Candidate := coordination_equilibrium_not_optimal

end CategoricalInfluenceDiagramsProofs.Shadows.GameCoordination
