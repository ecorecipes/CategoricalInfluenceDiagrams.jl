import CategoricalInfluenceDiagramsProofs.Lens
import Mathlib.Tactic.Linarith

/-!
# Perfect equilibria (ADR 0020, amended)

An equilibrium of decision games can rest on choices at information states the equilibrium
never reaches: a later component's policy there is a best response whatever it is, because
those states have probability zero, and it can still deter an earlier component. This is the
equilibrium refinement problem that subgame perfection answers.

**Perfect decision games.** A *perfect* decision game (`Game.perfect`) is in equilibrium in a
context when its strategy maximises the value from *every* input state, against the context's
continuation, whatever the prior. It refines the decision game: for a nonnegative prior a
perfect strategy is a best response (`perfect_eq_decision`). Serial composites of perfect
games ask the suffix to be perfect against the continuation and the prefix against the
suffix's value function: backward induction, independent of the prior
(`seq_perfect_eq_iff`).

**The threat witness** (`Threat`). An earlier decision chooses whether to act, worth `1` if it
does not; a later one, observing it, chooses whether to cooperate, worth `4` if both act and
`0` if only the first does. Not acting, with a later policy that would refuse to cooperate,
is an equilibrium of the decision games worth `1` (`threat_equilibrium`): the refusal is
never tested. The perfect equilibria are exactly the strategies in which the first acts and
the second cooperates when it does, worth `4`, the optimum (`threat_perfect_iff`,
`threat_optimum`).
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

namespace Game

open RewardKernel

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- A perfect decision game: in equilibrium when its strategy maximises the value from every
input state against the continuation, whatever the prior. -/
def perfect {S : Type} (play : S → RewardKernel X Y) (h : ∀ s, Kernel.Normalised (play s).K) :
    Game X Y where
  Strat := S
  play := play
  normalised := h
  Eq _ c s := ∀ x s', (play s').continuation c x ≤ (play s).continuation c x

/-- **Perfection refines equilibrium**: with a nonnegative prior, a perfect strategy is a best
response. -/
theorem perfect_eq_decision {S : Type} (play : S → RewardKernel X Y)
    (h : ∀ s, Kernel.Normalised (play s).K) (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (c : Y → ℝ)
    (s : S) (hs : (perfect play h).Eq μ c s) : (decision play h).Eq μ c s := by
  intro s'
  rw [eu_eq_continuation, eu_eq_continuation]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hs x s') (hμ x)

/-- **Backward induction**: a strategy of two perfect games in series is an equilibrium exactly
when the suffix is perfect against the continuation and the prefix against the suffix's value
function, whatever the prior. -/
theorem seq_perfect_eq_iff {S T : Type} (pf : S → RewardKernel X Y)
    (hf : ∀ s, Kernel.Normalised (pf s).K) (pg : T → RewardKernel Y Z)
    (hg : ∀ t, Kernel.Normalised (pg t).K) (μ : X → ℝ) (c : Z → ℝ) (s : S) (t : T) :
    ((perfect pf hf).seq (perfect pg hg)).Eq μ c (s, t) ↔
      (∀ x s', (pf s').continuation ((pg t).continuation c) x ≤
        (pf s).continuation ((pg t).continuation c) x) ∧
      ∀ y t', (pg t').continuation c y ≤ (pg t).continuation c y :=
  Iff.rfl

end Game

/-! ### The threat witness -/

namespace Threat

open RewardKernel

/-- The first decision: act (`true`) or not, a point mass on the choice. -/
def first (a : Bool) : RewardKernel Unit Bool :=
  ⟨fun _ y => if y = a then 1 else 0, fun _ _ => 0⟩

/-- The payoff: `1` if the first does not act, `4` if both act, `0` if only the first does. -/
def payoff (a b : Bool) : ℝ := if a then (if b then 4 else 0) else 1

/-- The second decision, observing the first: a policy `b` from the first's choice to
cooperating, paying the payoff. -/
def second (b : Bool → Bool) : RewardKernel Bool Unit :=
  ⟨fun _ _ => 1, fun a _ => payoff a (b a)⟩

theorem first_normalised (a : Bool) : Kernel.Normalised (first a).K := by
  intro x
  simp [first]

theorem second_normalised (b : Bool → Bool) : Kernel.Normalised (second b).K := by
  intro x
  simp [second]

/-- The composite's value. -/
theorem composite_eu (a : Bool) (b : Bool → Bool) :
    ((first a).comp (second b)).eu (fun _ => 1) (fun _ => 0) = payoff a (b a) := by
  cases a <;> simp [eu, first, second, comp, Kernel.comp]

/-- The first decision's value against the second's value function. -/
theorem first_value (a : Bool) (b : Bool → Bool) :
    (first a).eu (fun _ => 1) ((second b).continuation (fun _ => 0)) = payoff a (b a) := by
  simp only [eu, continuation, first, second, Fintype.sum_bool, Fintype.univ_unit,
    Finset.sum_singleton]
  cases a <;> simp

/-- The second decision's value against the first's boundary law. -/
theorem second_value (a : Bool) (b : Bool → Bool) :
    (second b).eu ((first a).pushforward (fun _ => 1)) (fun _ => 0) = payoff a (b a) := by
  simp only [eu, pushforward, first, second, Fintype.sum_bool, Fintype.univ_unit,
    Finset.sum_singleton]
  cases a <;> simp

/-- The threat: refuse to cooperate if the first acts. -/
def threat : Bool → Bool := fun _ => false

/-- **An equilibrium sustained by an untested threat.** Not acting, against a second decision
that would refuse to cooperate, is an equilibrium of the decision games, worth `1`. -/
theorem threat_equilibrium :
    ((Game.decision first first_normalised).seq
        (Game.decision second second_normalised)).Eq (fun _ => 1) (fun _ => 0)
        (false, threat) ∧
      ((first false).comp (second threat)).eu (fun _ => 1) (fun _ => 0) = 1 := by
  refine ⟨⟨fun a' => ?_, fun b' => ?_⟩, by rw [composite_eu]; simp [payoff]⟩
  · show (first a').eu (fun _ => 1) ((second threat).continuation (fun _ => 0)) ≤
      (first false).eu (fun _ => 1) ((second threat).continuation (fun _ => 0))
    rw [first_value, first_value]
    cases a' <;> simp [payoff, threat]
  · show (second b').eu ((first false).pushforward (fun _ => 1)) (fun _ => 0) ≤
      (second threat).eu ((first false).pushforward (fun _ => 1)) (fun _ => 0)
    rw [second_value, second_value]
    simp [payoff]

/-- **Perfect equilibria**: the first acts and the second cooperates when it does. -/
theorem threat_perfect_iff (a : Bool) (b : Bool → Bool) :
    ((Game.perfect first first_normalised).seq
        (Game.perfect second second_normalised)).Eq (fun _ => 1) (fun _ => 0) (a, b) ↔
      a = true ∧ b true = true := by
  rw [Game.seq_perfect_eq_iff]
  have hsecond : ∀ (b' : Bool → Bool) (y : Bool),
      (second b').continuation (fun _ => 0) y = payoff y (b' y) := by
    intro b' y
    simp [continuation, second]
  have hfirst : ∀ (x : Unit) (a' : Bool) (b' : Bool → Bool),
      (first a').continuation ((second b').continuation (fun _ => 0)) x = payoff a' (b' a') := by
    intro x a' b'
    simp only [continuation, first, second, Fintype.sum_bool]
    cases a' <;> simp
  simp only [hsecond, hfirst]
  constructor
  · rintro ⟨hf, hs⟩
    have hb : b true = true := by
      have h4 := hs true (fun _ => true)
      revert h4
      cases b true <;> norm_num [payoff]
    refine ⟨?_, hb⟩
    have h1 := hf () true
    rw [hb] at h1
    revert h1
    cases a <;> norm_num [payoff]
  · rintro ⟨rfl, hb⟩
    refine ⟨fun _ a' => ?_, fun y b' => ?_⟩
    · rw [hb]
      cases a' <;> norm_num [payoff, hb]
    · cases y
      · norm_num [payoff]
      · rw [hb]
        cases b' true <;> norm_num [payoff]

/-- The perfect equilibria attain the optimum, `4`. -/
theorem threat_optimum :
    (∀ a b, ((first a).comp (second b)).eu (fun _ => 1) (fun _ => 0) ≤ 4) ∧
      ((first true).comp (second fun _ => true)).eu (fun _ => 1) (fun _ => 0) = 4 := by
  refine ⟨fun a b => ?_, by rw [composite_eu]; simp [payoff]⟩
  rw [composite_eu]
  cases a <;> cases b _ <;> norm_num [payoff]

end Threat

end OpenInfluence
