import CategoricalInfluenceDiagramsProofs.Lens
import CategoricalInfluenceDiagramsProofs.Interpretation

/-!
# Evidence across a boundary (ADR 0021)

Evidence makes the probability component of a reward kernel substochastic: conditioning an
open influence diagram on observed states keeps, for each input `x` and output `y`, the
probability `K x y` of reaching `y` *and* seeing the evidence, and the reward `W x y` earned
on those paths. The category of reward kernels does not need normalisation, so serial
composition still holds; what fails is the normalised lens of ADR 0020, whose backward map
loses the reward of the prefix when the suffix loses mass (`eu_comp_needs_normalised`).

The repair is to carry the mass. A context on the boundary becomes a pair in the
expectation semiring on each side:

* an **effect** `(m, c)` on the outputs, the likelihood `m y` of the evidence still to come
  and the evidence-weighted value `c y` of what follows (`Effect`), carried backward by
  `pull`;
* a **state** `(ν, ρ)` on the inputs, the unnormalised law `ν x` of reaching `x` with the
  evidence seen so far and the reward-weighted law `ρ x` (`State`), carried forward by
  `push`.

**Results.**
- Both actions are functorial with no hypothesis (`pull_comp`, `push_comp`, `pull_id`,
  `push_id`), and the pairing of a state with an effect, the evidence mass
  `Σ_x ν x m x` and the evidence-weighted value `Σ_x (ρ x m x + ν x c x)`, is the same at
  every boundary (`mass_push`, `value_push`). So the composite's evidence mass is the
  pairing of the prefix's unnormalised boundary law with the suffix's likelihood
  (`mass_comp`), and its conditional value, their ratio, is computed at any cut
  (`conditionalValue_comp`).
- The plain contexts are the case of mass one: a prior is a state with zero reward, a
  continuation an effect with mass one, and against them the pairing is the expected
  utility of ADR 0018 (`value_ofPrior`). With a normalised suffix, pulling a continuation
  back keeps the mass one and is the value function of ADR 0020 (`pull_ofValue`); without
  normalisation the first half of the contextual identity still holds once the mass is
  carried (`eu_comp_pull`).
- Hard evidence on a boundary variable is composition with a diagonal indicator
  (`observe`), which is idempotent and commutes with other evidence
  (`observe_idem`, `observe_comm`): stating the same evidence on both sides of a boundary
  changes nothing.
- Normalising each component on its own evidence before composing is not sound
  (`local_normalisation_obstruction`): with a uniform prior on a binary state worth `1` when
  true, and evidence nine times likelier when it is true, the conditional value is `9/10`,
  while the components normalised one by one give `1/2`. The evidence mass must cross the
  boundary.
- For the syntax, a likelihood on the values of the generators, keyed by label as
  strategies are, weights the sum-product interpretation (`interpretE`). Weighting is
  functorial under serial composition (`interpretE_comp`) and tensor (`interpretE_tensor`),
  and the constant likelihood one gives back `interpret` (`interpretE_one`). Hard evidence
  is the indicator likelihood.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite

namespace RewardKernel

variable {X Y Z : Type}

/-- A context on the output side carrying evidence: the likelihood `m` of the evidence still
to come, and the evidence-weighted value `c` of what follows. -/
@[ext] structure Effect (Y : Type) where
  /-- `m y`: the probability of the evidence still to come, from the boundary state `y`. -/
  m : Y → ℝ
  /-- `c y`: the expected value still to come times the indicator of that evidence. -/
  c : Y → ℝ

/-- A context on the input side carrying evidence: the unnormalised law `ν` and the
reward-weighted law `ρ`. -/
@[ext] structure State (X : Type) where
  /-- `ν x`: the probability of reaching `x` with the evidence seen so far. -/
  ν : X → ℝ
  /-- `ρ x`: the reward earned so far, weighted as `ν x` is. -/
  ρ : X → ℝ

/-- A continuation with no evidence still to come. -/
def Effect.ofValue (c : Y → ℝ) : Effect Y := ⟨fun _ => 1, c⟩

/-- A prior with no reward earned yet. -/
def State.ofPrior (μ : X → ℝ) : State X := ⟨μ, fun _ => 0⟩

/-- The backward action of a reward kernel on effects. -/
def pull [Fintype Z] (g : RewardKernel Y Z) (e : Effect Z) : Effect Y :=
  ⟨fun y => ∑ z, g.K y z * e.m z, fun y => ∑ z, (g.W y z * e.m z + g.K y z * e.c z)⟩

/-- The forward action of a reward kernel on states. -/
def push [Fintype X] (f : RewardKernel X Y) (s : State X) : State Y :=
  ⟨fun y => ∑ x, s.ν x * f.K x y, fun y => ∑ x, (s.ρ x * f.K x y + s.ν x * f.W x y)⟩

/-- The evidence mass of a state against an effect. -/
def mass [Fintype X] (s : State X) (e : Effect X) : ℝ := ∑ x, s.ν x * e.m x

/-- The evidence-weighted value of a state against an effect. -/
def value [Fintype X] (s : State X) (e : Effect X) : ℝ := ∑ x, (s.ρ x * e.m x + s.ν x * e.c x)

/-- The conditional value: the evidence-weighted value divided by the evidence mass. -/
def conditionalValue [Fintype X] (s : State X) (e : Effect X) : ℝ := value s e / mass s e

variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] in
/-- The backward action is functorial, with no normalisation hypothesis. -/
theorem pull_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (e : Effect Z) :
    (f.comp g).pull e = f.pull (g.pull e) := by
  ext x
  · simp only [pull, comp_K, Kernel.comp_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [pull, comp_K, comp_W, Kernel.comp_apply, Pi.add_apply, Finset.sum_mul,
      Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun z y => f.W x y * g.K y z * e.m z),
      Finset.sum_comm (f := fun z y => f.K x y * g.W y z * e.m z),
      Finset.sum_comm (f := fun z y => f.K x y * g.K y z * e.c z)]
    simp only [mul_assoc, add_assoc]

omit [Fintype Z] in
/-- The forward action is functorial, with no normalisation hypothesis. -/
theorem push_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (s : State X) :
    (f.comp g).push s = g.push (f.push s) := by
  ext z
  · simp only [push, comp_K, Kernel.comp_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [push, comp_K, comp_W, Kernel.comp_apply, Pi.add_apply, Finset.sum_mul,
      Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x y => s.ρ x * (f.K x y * g.K y z)),
      Finset.sum_comm (f := fun x y => s.ν x * (f.W x y * g.K y z)),
      Finset.sum_comm (f := fun x y => s.ν x * (f.K x y * g.W y z))]
    simp only [mul_assoc, add_assoc]

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem pull_id [Fintype X] [DecidableEq X] (e : Effect X) : (id X).pull e = e := by
  ext x <;> simp [pull, id, lift, Kernel.idK_apply, ite_mul]

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem push_id [Fintype X] [DecidableEq X] (s : State X) : (id X).push s = s := by
  ext x <;> simp [push, id, lift, Kernel.idK_apply, mul_ite]

omit [Fintype Z] in
/-- The evidence mass is the same on either side of a reward kernel. -/
theorem mass_push (f : RewardKernel X Y) (s : State X) (e : Effect Y) :
    mass (f.push s) e = mass s (f.pull e) := by
  simp only [mass, push, pull, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
/-- The evidence-weighted value is the same on either side of a reward kernel. -/
theorem value_push (f : RewardKernel X Y) (s : State X) (e : Effect Y) :
    value (f.push s) e = value s (f.pull e) := by
  simp only [value, push, pull, Finset.sum_mul, Finset.mul_sum, add_mul, mul_add,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun y x => s.ρ x * f.K x y * e.m y),
    Finset.sum_comm (f := fun y x => s.ν x * f.W x y * e.m y),
    Finset.sum_comm (f := fun y x => s.ν x * f.K x y * e.c y)]
  simp only [mul_assoc, add_assoc]

/-- The evidence mass of a composite is the pairing, at the boundary, of the prefix's
unnormalised boundary law with the suffix's likelihood. -/
theorem mass_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (s : State X) (e : Effect Z) :
    mass s ((f.comp g).pull e) = ∑ y, (f.push s).ν y * (g.pull e).m y := by
  rw [pull_comp, ← mass_push]
  rfl

/-- The conditional value of a composite can be computed at the boundary between its parts:
the prefix's state pushed forward, against the suffix's effect pulled back. -/
theorem conditionalValue_comp (f : RewardKernel X Y) (g : RewardKernel Y Z) (s : State X)
    (e : Effect Z) :
    conditionalValue s ((f.comp g).pull e) = conditionalValue (f.push s) (g.pull e) := by
  simp only [conditionalValue, pull_comp, mass_push, value_push]

omit [Fintype Z] in
/-- Against a prior and a continuation, the pairing is the expected utility of ADR 0018. -/
theorem value_ofPrior (f : RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    value (State.ofPrior μ) (f.pull (Effect.ofValue c)) = f.eu μ c := by
  simp [value, State.ofPrior, Effect.ofValue, pull, eu, mul_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- With a normalised suffix, pulling a continuation back keeps the mass one and gives the
value function of ADR 0020. -/
theorem pull_ofValue [Fintype Z] (g : RewardKernel Y Z) (hg : Kernel.Normalised g.K)
    (c : Z → ℝ) : g.pull (Effect.ofValue c) = Effect.ofValue (g.continuation c) := by
  ext y
  · simp [pull, Effect.ofValue, hg y]
  · simp [pull, Effect.ofValue, continuation]

/-- The first half of the contextual identity without normalisation: carrying the mass, the
composite's expected utility is the prefix's value against the suffix's effect. -/
theorem eu_comp_pull (f : RewardKernel X Y) (g : RewardKernel Y Z) (μ : X → ℝ)
    (c : Z → ℝ) :
    (f.comp g).eu μ c = value (State.ofPrior μ) (f.pull (g.pull (Effect.ofValue c))) := by
  rw [← pull_comp, value_ofPrior]

/-! ### Hard evidence on a boundary variable -/

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Observing that the boundary state satisfies `P`: the diagonal indicator, with zero
reward. -/
def observe (P : X → Prop) [DecidablePred P] [DecidableEq X] : RewardKernel X X :=
  lift fun x x' => if x = x' ∧ P x then 1 else 0

omit [Fintype Y] [Fintype Z] in
theorem observe_comp_observe (P Q : X → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidableEq X] :
    (observe P).comp (observe Q) = observe fun x => P x ∧ Q x := by
  ext x x'
  · simp only [observe, lift, comp_K, Kernel.comp_apply]
    rw [Finset.sum_eq_single x']
    · by_cases h : x = x' <;> by_cases hp : P x <;> by_cases hq : Q x' <;> simp_all
    · intro b _ hb
      simp [hb]
    · simp
  · simp [observe, lift, comp_W, Kernel.comp]

omit [Fintype Y] [Fintype Z] in
/-- Observing twice is observing once: the same evidence stated on both sides of a boundary
changes nothing. -/
theorem observe_idem (P : X → Prop) [DecidablePred P] [DecidableEq X] :
    (observe P).comp (observe P) = observe P := by
  rw [observe_comp_observe]
  simp

omit [Fintype Y] [Fintype Z] in
/-- Evidence on a boundary commutes. -/
theorem observe_comm (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] [DecidableEq X] :
    (observe P).comp (observe Q) = (observe Q).comp (observe P) := by
  rw [observe_comp_observe, observe_comp_observe]
  congr 1
  funext x
  exact propext and_comm

end RewardKernel

/-! ### Normalising each component is not sound -/

namespace LocalNormalisation

open RewardKernel

/-- Normalise each row of a reward kernel by its probability mass: the component conditioned
on its own evidence, in isolation. -/
def normalise {X Y : Type} [Fintype Y] (f : RewardKernel X Y) : RewardKernel X Y :=
  ⟨fun x y => f.K x y / ∑ y', f.K x y', fun x y => f.W x y / ∑ y', f.K x y'⟩

/-- The prefix: a uniform binary state, worth `1` when it is true. -/
def prior : RewardKernel Unit Bool :=
  ⟨fun _ _ => 1 / 2, fun _ b => if b then 1 / 2 else 0⟩

/-- The suffix: evidence nine times likelier when the state is true. -/
def evidence : RewardKernel Bool Unit :=
  ⟨fun b _ => if b then 9 / 10 else 1 / 10, fun _ _ => 0⟩

/-- The whole context of the closed composite: the unit state and the unit effect. -/
def start : RewardKernel.State Unit := RewardKernel.State.ofPrior fun _ => 1

def finish : RewardKernel.Effect Unit := RewardKernel.Effect.ofValue fun _ => 0

theorem composite_conditionalValue :
    conditionalValue start ((prior.comp evidence).pull finish) = 9 / 10 := by
  simp only [conditionalValue, value, mass, start, finish, RewardKernel.State.ofPrior,
    RewardKernel.Effect.ofValue,
    pull, prior, evidence, comp_K, comp_W, Kernel.comp_apply, Pi.add_apply,
    Fintype.sum_bool, Fintype.univ_unit, Finset.sum_singleton]
  norm_num

theorem normalised_conditionalValue :
    conditionalValue start (((normalise prior).comp (normalise evidence)).pull finish) =
      1 / 2 := by
  simp only [conditionalValue, value, mass, start, finish, RewardKernel.State.ofPrior,
    RewardKernel.Effect.ofValue,
    pull, normalise, prior, evidence, comp_K, comp_W, Kernel.comp_apply, Pi.add_apply,
    Fintype.sum_bool, Fintype.univ_unit, Finset.sum_singleton]
  norm_num

/-- **Local normalisation is not sound.** Conditioning each component on its own evidence
and composing gives `1/2`; the composite conditioned on all of it gives `9/10`. -/
theorem local_normalisation_obstruction :
    conditionalValue start ((prior.comp evidence).pull finish) = 9 / 10 ∧
      conditionalValue start (((normalise prior).comp (normalise evidence)).pull finish) =
        1 / 2 :=
  ⟨composite_conditionalValue, normalised_conditionalValue⟩

end LocalNormalisation

/-! ### Evidence in the syntax -/

namespace IDInterpretation

open OpenNet

variable {S : IDSignature} (M : IDInterpretation S) (σ : M.Strategy)
variable {X Y Z X' Y' : S.Iface}

/-- A likelihood on the values of generators, keyed by label as strategies are. Hard
evidence that a generator takes the value `s` is the indicator of `s`. -/
abbrev Likelihood : Type := S.Label → Sigma M.states → ℝ

variable (ev : M.Likelihood)

/-- The likelihood of an internal assignment: the product over generators. -/
def lik (f : IDNet X Y) (z : (M.interp σ).Internal f.net) : ℝ :=
  ∏ a, ev (f.net.label a) (z a)

/-- The evidence-weighted probability table. -/
def kernelE (f : IDNet X Y) : Kernel ((M.interp σ).Boundary X) ((M.interp σ).Boundary Y) :=
  fun x y => ∑ z, if y = (M.interp σ).read f.net x z then
    (M.interp σ).joint f.net x z * M.lik σ ev f z else 0

/-- The evidence-weighted reward table. -/
def rewardTableE (f : IDNet X Y) :
    Kernel ((M.interp σ).Boundary X) ((M.interp σ).Boundary Y) :=
  fun x y => ∑ z, if y = (M.interp σ).read f.net x z then
    (M.interp σ).joint f.net x z * M.lik σ ev f z * M.reward σ f x z else 0

/-- The fixed-strategy semantics of an open influence diagram weighted by the likelihood
`ev`: a substochastic reward kernel for hard evidence. -/
def interpretE (f : IDNet X Y) :
    RewardKernel ((M.interp σ).Boundary X) ((M.interp σ).Boundary Y) :=
  ⟨M.kernelE σ ev f, M.rewardTableE σ ev f⟩

theorem lik_comp (f : IDNet X Y) (g : IDNet Y Z) (a : (M.interp σ).Internal f.net)
    (b : (M.interp σ).Internal g.net) :
    M.lik σ ev (f.comp g) ((M.interp σ).combine f.net g.net a b) =
      M.lik σ ev f a * M.lik σ ev g b := by
  unfold lik
  erw [Fintype.prod_sum_type]
  rfl

theorem kernelE_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.kernelE σ ev (f.comp g) = Kernel.comp (M.kernelE σ ev f) (M.kernelE σ ev g) := by
  funext x w
  simp only [Kernel.comp]
  unfold kernelE
  rw [M.sum_fibre_mul σ x w (fun a => (M.interp σ).joint f.net x a * M.lik σ ev f a)
      (fun y b => (M.interp σ).joint g.net y b * M.lik σ ev g b)]
  change (∑ z : (M.interp σ).Internal (f.net.comp g.net),
      if w = (M.interp σ).read (f.net.comp g.net) x z then
        (M.interp σ).joint (f.net.comp g.net) x z * M.lik σ ev (f.comp g) z else 0) = _
  erw [← ((M.interp σ).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interp σ).read_comp f.net g.net x a b
  have hj := (M.interp σ).joint_comp f.net g.net x a b
  have hl := M.lik_comp σ ev f g a b
  simp only [Interpretation.combine] at hr hj hl
  rw [hr, hj, hl]
  split_ifs <;> ring

theorem rewardTableE_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.rewardTableE σ ev (f.comp g) =
      Kernel.comp (M.rewardTableE σ ev f) (M.kernelE σ ev g) +
        Kernel.comp (M.kernelE σ ev f) (M.rewardTableE σ ev g) := by
  funext x w
  simp only [Pi.add_apply, Kernel.comp]
  unfold rewardTableE kernelE
  rw [M.sum_fibre_mul σ x w
      (fun a => (M.interp σ).joint f.net x a * M.lik σ ev f a * M.reward σ f x a)
      (fun y b => (M.interp σ).joint g.net y b * M.lik σ ev g b),
    M.sum_fibre_mul σ x w (fun a => (M.interp σ).joint f.net x a * M.lik σ ev f a)
      (fun y b => (M.interp σ).joint g.net y b * M.lik σ ev g b * M.reward σ g y b)]
  rw [← Finset.sum_add_distrib]
  change (∑ z : (M.interp σ).Internal (f.net.comp g.net),
      if w = (M.interp σ).read (f.net.comp g.net) x z then
        (M.interp σ).joint (f.net.comp g.net) x z * M.lik σ ev (f.comp g) z *
          M.reward σ (f.comp g) x z else 0) = _
  erw [← ((M.interp σ).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interp σ).read_comp f.net g.net x a b
  have hj := (M.interp σ).joint_comp f.net g.net x a b
  have hl := M.lik_comp σ ev f g a b
  have hw := M.reward_comp σ f g x a b
  simp only [Interpretation.combine] at hr hj hl hw
  rw [hr, hj, hl, hw]
  split_ifs <;> ring

/-- **Evidence composes**: the evidence-weighted interpretation of a serial composite is the
composite, in the category of reward kernels, of the evidence-weighted interpretations. -/
theorem interpretE_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.interpretE σ ev (f.comp g) = (M.interpretE σ ev f).comp (M.interpretE σ ev g) := by
  ext1
  · exact M.kernelE_comp σ ev f g
  · exact M.rewardTableE_comp σ ev f g

theorem lik_tensor (f : IDNet X Y) (g : IDNet X' Y') (a : (M.interp σ).Internal f.net)
    (b : (M.interp σ).Internal g.net) :
    M.lik σ ev (f.tensor g) ((M.interp σ).combine f.net g.net a b) =
      M.lik σ ev f a * M.lik σ ev g b := by
  unfold lik
  erw [Fintype.prod_sum_type]
  rfl

theorem kernelE_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (y : (M.interp σ).Boundary Y)
    (y' : (M.interp σ).Boundary Y') :
    M.kernelE σ ev (f.tensor g) (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      M.kernelE σ ev f x y * M.kernelE σ ev g x' y' := by
  unfold kernelE
  rw [Finset.sum_mul_sum]
  change (∑ z : (M.interp σ).Internal (f.net.tensor g.net),
      if Interpretation.Assignment.join _ y y' =
          (M.interp σ).read (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z then
        (M.interp σ).joint (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z *
          M.lik σ ev (f.tensor g) z else 0) = _
  erw [← ((M.interp σ).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interp σ).read_tensor f.net g.net x x' a b
  have hj := (M.interp σ).joint_tensor f.net g.net x x' a b
  have hl := M.lik_tensor σ ev f g a b
  simp only [Interpretation.combine] at hr hj hl
  rw [hr, hj, hl]
  by_cases h₁ : y = (M.interp σ).read f.net x a <;>
    by_cases h₂ : y' = (M.interp σ).read g.net x' b <;>
      simp [Interpretation.Assignment.join_injective, h₁, h₂]
  ring

theorem rewardTableE_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (y : (M.interp σ).Boundary Y)
    (y' : (M.interp σ).Boundary Y') :
    M.rewardTableE σ ev (f.tensor g) (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      M.rewardTableE σ ev f x y * M.kernelE σ ev g x' y' +
        M.kernelE σ ev f x y * M.rewardTableE σ ev g x' y' := by
  unfold rewardTableE kernelE
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  change (∑ z : (M.interp σ).Internal (f.net.tensor g.net),
      if Interpretation.Assignment.join _ y y' =
          (M.interp σ).read (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z then
        (M.interp σ).joint (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z *
          M.lik σ ev (f.tensor g) z *
            M.reward σ (f.tensor g) (Interpretation.Assignment.join _ x x') z else 0) = _
  erw [← ((M.interp σ).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interp σ).read_tensor f.net g.net x x' a b
  have hj := (M.interp σ).joint_tensor f.net g.net x x' a b
  have hl := M.lik_tensor σ ev f g a b
  have hw := M.reward_tensor σ f g x x' a b
  simp only [Interpretation.combine] at hr hj hl hw
  rw [hr, hj, hl, hw]
  by_cases h₁ : y = (M.interp σ).read f.net x a <;>
    by_cases h₂ : y' = (M.interp σ).read g.net x' b <;>
      simp [Interpretation.Assignment.join_injective, h₁, h₂]
  ring

/-- **Evidence composes in parallel**: read through the canonical bijections between
assignments of a disjoint-union interface and pairs of assignments, the evidence-weighted
interpretation of a tensor is the tensor of the evidence-weighted interpretations. -/
theorem interpretE_tensor (f : IDNet X Y) (g : IDNet X' Y') :
    (M.interpretE σ ev (f.tensor g)).reindex (M.join σ X X') (M.join σ Y Y') =
      (M.interpretE σ ev f).tensor (M.interpretE σ ev g) := by
  ext1
  · funext p q
    exact M.kernelE_tensor σ ev f g p.1 p.2 q.1 q.2
  · funext p q
    exact M.rewardTableE_tensor σ ev f g p.1 p.2 q.1 q.2

/-- With the likelihood one everywhere, there is no evidence. -/
theorem interpretE_one (f : IDNet X Y) :
    M.interpretE σ (fun _ _ => 1) f = M.interpret σ f := by
  ext x y
  · simp [interpretE, kernelE, interpret, lik, kernel_eq_sum]
  · simp [interpretE, rewardTableE, interpret, rewardTable, lik]

end IDInterpretation

end OpenInfluence
