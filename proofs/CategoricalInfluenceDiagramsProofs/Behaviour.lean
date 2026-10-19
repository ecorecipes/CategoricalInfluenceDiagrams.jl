import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# Behavioural strategies and the value of randomising (ADR 0022)

ADR 0018 kept randomised policies out of the first release "until a theorem covers them".
This module supplies the theorems.

**Behavioural strategies.** A behavioural strategy (`Behaviour`) gives every decision label a
distribution over its result for each list of values on its information ports, normalised on
correctly typed rows. Decisions become generators with those tables (`interpB`), and the
semantics of an open influence diagram is again a reward kernel (`interpretB`), stochastic,
functorial under serial composition (`interpretB_comp`), identities (`interpretB_identity`)
and tensor (`interpretB_tensor`), and the contextual identity holds (`contextual_identityB`).
A deterministic strategy is the behavioural strategy of point masses, with the same
interpretation (`interpB_pointMass`, `interpretB_pointMass`).

**Mixtures.** A mixture of reward kernels (`mix`) composes affinely on either side
(`mix_comp`, `comp_mix`), its expected utility is the mixture of the expected utilities
(`eu_mix`), so it never exceeds the best of them (`eu_mix_le`), and its conditional value
never exceeds the best conditional value among the components of positive mass
(`conditionalValue_mix_le`, the mediant inequality). Randomising over whole strategies of a
component therefore never helps, with or without evidence.

**Shared policies.** Decisions that share a label share one policy. Then randomising can
help: the absent-minded driver (`AbsentMinded`), two decisions with one policy, continue
with probability `p` at both, pays `4p - 3p²`, which is `4/3` at `p = 2/3` and at most `1`
for either deterministic policy (`randomising_helps`). With a policy each, the same payoffs
`p (4 (1 - q) + q)` are maximised by a deterministic pair (`independent_deterministic_optimal`).
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open CategoryTheory FiniteKernelsProofs.Finite OpenNet

namespace IDInterpretation

variable {S : IDSignature} (M : IDInterpretation S)

/-- A behavioural strategy: for every decision label a table of probabilities of its result
given the values on its information ports, nonnegative and normalised on correctly typed
rows. -/
structure Behaviour where
  /-- `policy l h p s`: the probability of the result `s` given the information values `p`. -/
  policy : (l : S.Label) → S.isDecision l = true → List (Sigma M.states) → Sigma M.states → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ l h p s, 0 ≤ policy l h p s
  /-- Probabilities sum to one on every correctly typed row. -/
  normalized : ∀ l h p, p.map Sigma.fst = S.inputs l →
    @Finset.sum (M.states (S.result l)) ℝ _ (@Finset.univ _ (M.finite _))
      (fun s => policy l h p ⟨S.result l, s⟩) = 1

/-- The `OpenNet` interpretation for a behavioural strategy: decisions draw from their
policies, chance mechanisms keep their tables. -/
def interpB (β : M.Behaviour) : OpenNet.Interpretation S.toSignature where
  states := M.states
  finite := M.finite
  weight l p s :=
    if h : S.isDecision l = true then β.policy l h p s else M.chance l p s
  nonneg l p s := by
    by_cases h : S.isDecision l = true
    · simp only [h, dite_true]
      exact β.nonneg l h p s
    · simp only [h]
      exact M.chance_nonneg l p s (by simpa using h)
  normalized l p hp := by
    by_cases h : S.isDecision l = true
    · simp only [h, dite_true]
      exact β.normalized l h p hp
    · simp only [h]
      exact M.chance_normalized l p (by simpa using h) hp

open Classical in
/-- A deterministic strategy as a behavioural one: the point masses of its policies. -/
def pointMass (σ : M.Strategy) : M.Behaviour where
  policy l h p s := if s = ⟨S.result l, σ l h p⟩ then 1 else 0
  nonneg l h p s := by split_ifs <;> norm_num
  normalized l h p _ := by
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    simp

/-- The point masses of a deterministic strategy interpret decisions as `interp` does. -/
theorem interpB_pointMass (σ : M.Strategy) : M.interpB (M.pointMass σ) = M.interp σ := rfl

variable (β : M.Behaviour)
variable {X Y Z X' Y' : S.Iface}

/-- The total utility of the diagram's utility generators, read on their scopes, at the
input assignment `x` and the internal assignment `z`. -/
def rewardB (f : IDNet X Y) (x : (M.interpB β).Boundary X) (z : (M.interpB β).Internal f.net) :
    ℝ :=
  ∑ u, M.utility (f.ulabel u) ((f.uparents u).map ((M.interpB β).valuation f.net x z).value)

/-- The reward table: the probability-weighted total utility of the internal assignments
that produce each output. -/
def rewardTableB (f : IDNet X Y) :
    Kernel ((M.interpB β).Boundary X) ((M.interpB β).Boundary Y) :=
  fun x y => ∑ z, if y = (M.interpB β).read f.net x z then
    (M.interpB β).joint f.net x z * M.rewardB β f x z else 0

/-- The semantics of an open influence diagram under a behavioural strategy: the
sum-product kernel of its net and its reward table. -/
def interpretB (f : IDNet X Y) :
    RewardKernel ((M.interpB β).Boundary X) ((M.interpB β).Boundary Y) :=
  ⟨(M.interpB β).kernel f.net, M.rewardTableB β f⟩

theorem interpretB_stochastic (f : IDNet X Y) : (M.interpretB β f).Stochastic :=
  (M.interpB β).kernel_stochastic f.net


/-! ### Rewards of composites -/

theorem rewardB_comp (f : IDNet X Y) (g : IDNet Y Z) (x : (M.interpB β).Boundary X)
    (a : (M.interpB β).Internal f.net) (b : (M.interpB β).Internal g.net) :
    M.rewardB β (f.comp g) x ((M.interpB β).combine f.net g.net a b) =
      M.rewardB β f x a + M.rewardB β g ((M.interpB β).read f.net x a) b := by
  unfold rewardB
  erw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (f.ulabel u)
      (((f.uparents u).map (Net.left f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (f.uparents u).map k)
      (funext ((M.interpB β).valuation_comp_left f.net g.net x a b))
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (g.ulabel u)
      (((g.uparents u).map (Net.right f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (g.uparents u).map k)
      (funext ((M.interpB β).valuation_comp_right f.net g.net x a b))

theorem rewardB_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interpB β).Boundary X)
    (x' : (M.interpB β).Boundary X') (a : (M.interpB β).Internal f.net)
    (b : (M.interpB β).Internal g.net) :
    M.rewardB β (f.tensor g) (Interpretation.Assignment.join _ x x')
        ((M.interpB β).combine f.net g.net a b) =
      M.rewardB β f x a + M.rewardB β g x' b := by
  unfold rewardB
  erw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (f.ulabel u)
      (((f.uparents u).map (Net.tinl f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (f.uparents u).map k)
      (funext ((M.interpB β).valuation_tensor_left f.net g.net x x' a b))
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (g.ulabel u)
      (((g.uparents u).map (Net.tinr f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (g.uparents u).map k)
      (funext ((M.interpB β).valuation_tensor_right f.net g.net x x' a b))

/-! ### Functoriality under serial composition -/

/-- Summing a product of two output-fibre sums over the middle boundary substitutes the
first component's output into the second. -/
theorem sum_fibre_mulB {f : Net X Y} {g : Net Y Z} (x : (M.interpB β).Boundary X)
    (w : (M.interpB β).Boundary Z) (F : (M.interpB β).Internal f → ℝ)
    (G : (M.interpB β).Boundary Y → (M.interpB β).Internal g → ℝ) :
    (∑ y, (∑ a, if y = (M.interpB β).read f x a then F a else 0) *
        (∑ b, if w = (M.interpB β).read g y b then G y b else 0)) =
      ∑ a, ∑ b, if w = (M.interpB β).read g ((M.interpB β).read f x a) b then
        F a * G ((M.interpB β).read f x a) b else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single ((M.interpB β).read f x a)]
  · simp only [if_true, Finset.mul_sum, mul_ite, mul_zero]
  · intro y _ hy
    simp [hy]
  · simp

theorem kernel_eq_sumB (f : Net X Y) (x : (M.interpB β).Boundary X)
    (y : (M.interpB β).Boundary Y) :
    (M.interpB β).kernel f x y =
      ∑ z, if y = (M.interpB β).read f x z then (M.interpB β).joint f x z else 0 := by
  unfold Interpretation.kernel
  rfl

theorem rewardTableB_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.rewardTableB β (f.comp g) =
      Kernel.comp (M.rewardTableB β f) ((M.interpB β).kernel g.net) +
        Kernel.comp ((M.interpB β).kernel f.net) (M.rewardTableB β g) := by
  funext x w
  simp only [Pi.add_apply, Kernel.comp, kernel_eq_sumB]
  unfold rewardTableB
  rw [M.sum_fibre_mulB β x w (fun a => (M.interpB β).joint f.net x a * M.rewardB β f x a)
      (fun y b => (M.interpB β).joint g.net y b),
    M.sum_fibre_mulB β x w (fun a => (M.interpB β).joint f.net x a)
      (fun y b => (M.interpB β).joint g.net y b * M.rewardB β g y b)]
  rw [← Finset.sum_add_distrib]
  change (∑ z : (M.interpB β).Internal (f.net.comp g.net),
      if w = (M.interpB β).read (f.net.comp g.net) x z then
        (M.interpB β).joint (f.net.comp g.net) x z * M.rewardB β (f.comp g) x z else 0) = _
  erw [← ((M.interpB β).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interpB β).read_comp f.net g.net x a b
  have hj := (M.interpB β).joint_comp f.net g.net x a b
  have hw := M.rewardB_comp β f g x a b
  simp only [Interpretation.combine] at hr hj hw
  rw [hr, hj, hw]
  split_ifs <;> ring

/-- **Functoriality under serial composition**: the interpretation of a composite is the
composite, in the expectation-semiring kernel category, of the interpretations. -/
theorem interpretB_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.interpretB β (f.comp g) = (M.interpretB β f).comp (M.interpretB β g) := by
  ext1
  · exact (M.interpB β).kernel_comp f.net g.net
  · exact M.rewardTableB_comp β f g

theorem interpretB_identity (X : S.Iface) :
    M.interpretB β (IDNet.identity X) = RewardKernel.id ((M.interpB β).Boundary X) := by
  ext1
  · change (M.interpB β).kernel (Net.wire id (fun _ => rfl)) = Kernel.idK _
    rw [(M.interpB β).kernel_wire]
    apply Kernel.ofFun_congr
    intro x
    rfl
  · funext x y
    have hr : ∀ z, M.rewardB β (IDNet.identity X) x z = 0 :=
      fun z => Finset.sum_eq_zero (fun u _ => (u : Empty).elim)
    change M.rewardTableB β (IDNet.identity X) x y = 0
    unfold rewardTableB
    simp [hr]


/-! ### Functoriality under tensor -/

/-- The canonical bijection between pairs of boundary assignments and assignments of the
disjoint-union interface. -/
def joinB (X X' : S.Iface) :
    (M.interpB β).Boundary X × (M.interpB β).Boundary X' ≃ (M.interpB β).Boundary (X.sum X') :=
  (Interpretation.Assignment.sumEquiv (M.interpB β) X.type X'.type).symm

@[simp] theorem joinB_apply (X X' : S.Iface) (p : (M.interpB β).Boundary X ×
    (M.interpB β).Boundary X') :
    M.joinB β X X' p = Interpretation.Assignment.join _ p.1 p.2 := rfl

theorem rewardTableB_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interpB β).Boundary X)
    (x' : (M.interpB β).Boundary X') (y : (M.interpB β).Boundary Y)
    (y' : (M.interpB β).Boundary Y') :
    M.rewardTableB β (f.tensor g) (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      M.rewardTableB β f x y * (M.interpB β).kernel g.net x' y' +
        (M.interpB β).kernel f.net x y * M.rewardTableB β g x' y' := by
  simp only [kernel_eq_sumB]
  unfold rewardTableB
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  change (∑ z : (M.interpB β).Internal (f.net.tensor g.net),
      if Interpretation.Assignment.join _ y y' =
          (M.interpB β).read (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z then
        (M.interpB β).joint (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z *
          M.rewardB β (f.tensor g) (Interpretation.Assignment.join _ x x') z else 0) = _
  erw [← ((M.interpB β).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interpB β).read_tensor f.net g.net x x' a b
  have hj := (M.interpB β).joint_tensor f.net g.net x x' a b
  have hw := M.rewardB_tensor β f g x x' a b
  simp only [Interpretation.combine] at hr hj hw
  rw [hr, hj, hw]
  by_cases h₁ : y = (M.interpB β).read f.net x a <;>
    by_cases h₂ : y' = (M.interpB β).read g.net x' b <;>
      simp [Interpretation.Assignment.join_injective, h₁, h₂]
  ring

theorem kernel_tensor_joinB (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interpB β).Boundary X)
    (x' : (M.interpB β).Boundary X') (y : (M.interpB β).Boundary Y)
    (y' : (M.interpB β).Boundary Y') :
    (M.interpB β).kernel (f.tensor g).net (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      (M.interpB β).kernel f.net x y * (M.interpB β).kernel g.net x' y' :=
  (M.interpB β).kernel_tensor f.net g.net x x' y y'


/-- **Functoriality under tensor** for a behavioural strategy. -/
theorem interpretB_tensor (f : IDNet X Y) (g : IDNet X' Y') :
    (M.interpretB β (f.tensor g)).reindex (M.joinB β X X') (M.joinB β Y Y') =
      (M.interpretB β f).tensor (M.interpretB β g) := by
  ext1
  · funext p q
    exact M.kernel_tensor_joinB β f g p.1 p.2 q.1 q.2
  · funext p q
    exact M.rewardTableB_tensor β f g p.1 p.2 q.1 q.2

/-! ### The contextual identity for interpreted diagrams -/

/-- **Contextual identity** for open influence diagrams under a behavioural strategy: for every
boundary prior `μ` and terminal continuation `c`,
`EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`, where `c_g` is the suffix's value
function, `ν_f` the boundary law induced by the prefix and `L_f` the prefix's reward. -/
theorem contextual_identityB (f : IDNet X Y) (g : IDNet Y Z)
    (μ : (M.interpB β).Boundary X → ℝ) (c : (M.interpB β).Boundary Z → ℝ) :
    (M.interpretB β (f.comp g)).eu μ c =
        (M.interpretB β f).eu μ ((M.interpretB β g).continuation c) ∧
      (M.interpretB β f).eu μ ((M.interpretB β g).continuation c) =
        (M.interpretB β f).prefixReward μ +
          (M.interpretB β g).eu ((M.interpretB β f).pushforward μ) c := by
  rw [M.interpretB_comp β f g]
  exact RewardKernel.contextual_identity _ _ (M.interpretB_stochastic β g).2 μ c

/-- A deterministic strategy has the same semantics as the behavioural strategy of its point
masses. -/
theorem interpretB_pointMass (σ : M.Strategy) (f : IDNet X Y) :
    M.interpretB (M.pointMass σ) f = M.interpret σ f := rfl

end IDInterpretation

/-! ### Mixtures of reward kernels -/

namespace RewardKernel

variable {X Y Z ι : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι]

/-- The mixture `Σ_i q i · f i` of a finite family of reward kernels. -/
def mix (q : ι → ℝ) (f : ι → RewardKernel X Y) : RewardKernel X Y :=
  ⟨fun x y => ∑ i, q i * (f i).K x y, fun x y => ∑ i, q i * (f i).W x y⟩

omit [Fintype X] [Fintype Z] in
/-- Composition after a mixture is the mixture of the composites. -/
theorem mix_comp (q : ι → ℝ) (f : ι → RewardKernel X Y) (g : RewardKernel Y Z) :
    (mix q f).comp g = mix q (fun i => (f i).comp g) := by
  ext x z
  · simp only [mix, comp_K, Kernel.comp_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [mix, comp_W, comp_K, Kernel.comp_apply, Pi.add_apply, Finset.sum_mul,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun y i => q i * (f i).W x y * g.K y z),
      Finset.sum_comm (f := fun y i => q i * (f i).K x y * g.W y z)]
    simp only [mul_assoc]

omit [Fintype X] [Fintype Z] in
/-- Composition before a mixture is the mixture of the composites. -/
theorem comp_mix [Fintype X] (f : RewardKernel X Y) (q : ι → ℝ) (g : ι → RewardKernel Y Z) :
    f.comp (mix q g) = mix q (fun i => f.comp (g i)) := by
  ext x z
  · simp only [mix, comp_K, Kernel.comp_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [mix, comp_W, comp_K, Kernel.comp_apply, Pi.add_apply, Finset.mul_sum,
      mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun y i => f.W x y * (q i * (g i).K y z)),
      Finset.sum_comm (f := fun y i => f.K x y * (q i * (g i).W y z))]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
/-- The expected utility of a mixture is the mixture of the expected utilities. -/
theorem eu_mix (q : ι → ℝ) (f : ι → RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    (mix q f).eu μ c = ∑ i, q i * (f i).eu μ c := by
  have h1 : ∀ x y, (∑ i, q i * (f i).W x y) + (∑ i, q i * (f i).K x y) * c y =
      ∑ i, q i * ((f i).W x y + (f i).K x y * c y) := by
    intro x y
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  calc (mix q f).eu μ c
      = ∑ x, ∑ y, ∑ i, q i * (μ x * ((f i).W x y + (f i).K x y * c y)) := by
        simp only [eu, mix, h1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ x, ∑ i, ∑ y, q i * (μ x * ((f i).W x y + (f i).K x y * c y)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, q i * (μ x * ((f i).W x y + (f i).K x y * c y)) := Finset.sum_comm
    _ = ∑ i, q i * (f i).eu μ c := by
        simp only [eu, Finset.mul_sum]

omit [Fintype Z] in
/-- **Randomising over whole strategies does not help**: the expected utility of a mixture
with nonnegative weights summing to one is at most the best expected utility among its
components. -/
theorem eu_mix_le [Nonempty ι] (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i = 1)
    (f : ι → RewardKernel X Y) (μ : X → ℝ) (c : Y → ℝ) :
    ∃ i, (mix q f).eu μ c ≤ (f i).eu μ c := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => (f i).eu μ c)
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [eu_mix q]
  calc ∑ j, q j * (f j).eu μ c ≤ ∑ j, q j * (f i).eu μ c :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hi j hj) (hq0 j)
    _ = (f i).eu μ c := by rw [← Finset.sum_mul, hq, one_mul]

/-- **The mediant inequality**: a ratio of nonnegatively weighted sums, with positive total
denominator, is at most the best ratio among the terms of positive denominator, provided a
term of zero denominator has zero numerator. -/
theorem mediant_le (w N D : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hD : ∀ i, 0 ≤ D i)
    (hND : ∀ i, D i = 0 → N i = 0) (hpos : 0 < ∑ i, w i * D i) :
    ∃ i, 0 < D i ∧ (∑ j, w j * N j) / (∑ j, w j * D j) ≤ N i / D i := by
  classical
  by_contra hcon
  push Not at hcon
  set T := (∑ j, w j * N j) / (∑ j, w j * D j) with hTdef
  have hT : T * (∑ j, w j * D j) = ∑ j, w j * N j := div_mul_cancel₀ _ hpos.ne'
  have hle : ∀ j, w j * N j ≤ T * (w j * D j) := by
    intro j
    rcases (hD j).lt_or_eq with h | h
    · have h' := hcon j h
      rw [div_lt_iff₀ h] at h'
      nlinarith [hw j]
    · rw [hND j h.symm, ← h]
      simp
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j * D j := by
    by_contra hno
    push Not at hno
    exact absurd hpos (not_lt.mpr (Finset.sum_nonpos fun j _ => hno j))
  have hDj : 0 < D j := by
    rcases (hD j).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hj
      exact absurd hj (lt_irrefl 0)
  have hwj : 0 < w j := by
    rcases (hw j).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hj
      exact absurd hj (lt_irrefl 0)
  have hstrict : w j * N j < T * (w j * D j) := by
    have h' := hcon j hDj
    rw [div_lt_iff₀ hDj] at h'
    nlinarith
  have hsum : ∑ j, w j * N j < T * ∑ j, w j * D j := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, hstrict⟩
  linarith

omit [Fintype X] [Fintype Z] in
theorem pull_mix (q : ι → ℝ) (f : ι → RewardKernel X Y) (e : Effect Y) (x : X) :
    ((mix q f).pull e).m x = ∑ i, q i * ((f i).pull e).m x ∧
      ((mix q f).pull e).c x = ∑ i, q i * ((f i).pull e).c x := by
  constructor
  · simp only [pull, mix, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [pull, mix, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
/-- The evidence mass and the evidence-weighted value of a mixture are the mixtures. -/
theorem mass_value_mix (q : ι → ℝ) (f : ι → RewardKernel X Y) (s : State X) (e : Effect Y) :
    mass s ((mix q f).pull e) = ∑ i, q i * mass s ((f i).pull e) ∧
      value s ((mix q f).pull e) = ∑ i, q i * value s ((f i).pull e) := by
  constructor
  · simp only [mass, (pull_mix q f e _).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp only [value, (pull_mix q f e _).1, (pull_mix q f e _).2, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
/-- **Randomising does not help given evidence either**: the conditional value of a mixture
is at most the conditional value of one of its components of positive evidence mass, when
masses are nonnegative and a component of zero mass has zero evidence-weighted value. -/
theorem conditionalValue_mix_le (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (f : ι → RewardKernel X Y) (s : State X) (e : Effect Y)
    (hmass : ∀ i, 0 ≤ mass s ((f i).pull e))
    (hzero : ∀ i, mass s ((f i).pull e) = 0 → value s ((f i).pull e) = 0)
    (hpos : 0 < mass s ((mix q f).pull e)) :
    ∃ i, 0 < mass s ((f i).pull e) ∧
      conditionalValue s ((mix q f).pull e) ≤ conditionalValue s ((f i).pull e) := by
  rw [(mass_value_mix q f s e).1] at hpos
  unfold conditionalValue
  rw [(mass_value_mix q f s e).1, (mass_value_mix q f s e).2]
  exact mediant_le q _ _ hq0 hmass hzero hpos

end RewardKernel

/-! ### Shared policies: the absent-minded driver -/

namespace AbsentMinded

open RewardKernel

/-- The first junction: continue with probability `p`; exiting here pays nothing. -/
def first (p : ℝ) : RewardKernel Unit Bool :=
  ⟨fun _ b => if b then p else 1 - p, fun _ _ => 0⟩

/-- The second junction, reached only by continuing: continue with probability `q` (paying
`1`) or exit (paying `4`). -/
def second (q : ℝ) : RewardKernel Bool Unit :=
  ⟨fun _ _ => 1, fun b _ => if b then 4 * (1 - q) + q else 0⟩

/-- The value of the drive with continuation probabilities `p` and `q`. -/
theorem drive_eu (p q : ℝ) :
    ((first p).comp (second q)).eu (fun _ => 1) (fun _ => 0) = p * (4 * (1 - q) + q) := by
  simp [eu, first, second, comp, Kernel.comp]

/-- **Randomising helps when two decisions share a policy.** Continuing with probability
`2/3` at both junctions is worth `4/3`; either deterministic policy is worth at most `1`. -/
theorem randomising_helps :
    ((first (2 / 3)).comp (second (2 / 3))).eu (fun _ => 1) (fun _ => 0) = 4 / 3 ∧
      ∀ p ∈ ({0, 1} : Set ℝ), ((first p).comp (second p)).eu (fun _ => 1) (fun _ => 0) ≤ 1 := by
  refine ⟨by rw [drive_eu]; norm_num, fun p hp => ?_⟩
  rw [drive_eu]
  rcases hp with rfl | rfl <;> norm_num

/-- **With a policy each, a deterministic pair is optimal**: continuing at the first junction
and exiting at the second is worth `4`, and no pair of probabilities does better. -/
theorem independent_deterministic_optimal :
    ((first 1).comp (second 0)).eu (fun _ => 1) (fun _ => 0) = 4 ∧
      ∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
        ((first p).comp (second q)).eu (fun _ => 1) (fun _ => 0) ≤ 4 := by
  refine ⟨by rw [drive_eu]; norm_num, fun p q hp0 hp1 hq0 hq1 => ?_⟩
  rw [drive_eu]
  nlinarith

end AbsentMinded

end OpenInfluence
