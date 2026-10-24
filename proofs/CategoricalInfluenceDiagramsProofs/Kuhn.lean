import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# Kuhn's theorem for open influence diagrams (ADR 0022, second amendment)

`Behaviour` proves that one randomised decision in any context never beats the best
deterministic rule. This module proves it for every decision of an open influence diagram at
once, in the syntax (`IDNet`), when no two decision generators share a label, so that no two
decisions share a policy (`DistinctDecisions`).

**The argument.** Fix a decision label `l` and a correctly typed row `p` of values on its
information ports. Only one generator has the label `l`, and it reads one row at each
internal assignment, so the joint weight of every internal assignment is affine in the
distribution that the strategy draws from at `(l, p)` (`jointAt_affine`). Hence the reward
kernel of the diagram is the mixture, weighted by that distribution, of the reward kernels in
which the row `(l, p)` is replaced by a point mass (`setRow`, `kernelAt_eq_mix`). By
`eu_mix_le` one of those point masses does at least as well, and by the mediant inequality
(`conditionalValue_mix_le`) the same holds for conditional values given evidence. Only the
finitely many rows that decisions actually read matter (`rows`). Replacing them one at a time
(`kuhn_induction`) ends at a strategy that is deterministic on every row read, which has the
semantics of a deterministic strategy (`det_joint`).

**The semantics with evidence.** `interpretBE β ev f` is the semantics of `f` under the
behavioural strategy `β` with every internal assignment weighted by the likelihood `ev` of
its generators' values: the behavioural counterpart of `Evidence`'s `interpretE`. With the
constant likelihood `1` it is `interpretB` (`interpretBE_one`), and for the point masses of a
deterministic strategy it is `interpretE` (`interpretBE_pointMass`, by `rfl`), just as
`interpretB` of the point masses is `interpret` (`interpretB_pointMass`).

**The theorems.**

* `kuhn_eu`: for every behavioural strategy `β`, prior `μ` and continuation `c` (signed, as in
  `contextual_identity`), some deterministic strategy `σ` has
  `EU(interpretB β f) ≤ EU(interpretB (pointMass σ) f)`;
* `kuhn_conditional`: suppose the likelihoods `ev` are nonnegative, the state's reward
  vanishes where its mass does, and the effect's value vanishes where its likelihood does.
  If the evidence has positive mass under `β`, then some deterministic `σ` gives it positive
  mass too, and a conditional value at least as large.

Assignments of boundaries and internal variables depend only on the state spaces of an
interpretation, not on its weights. But `OpenNet`'s `Assignment` is indexed by the
interpretation, so the contexts are carried from `β`'s interpretation to `σ`'s by `recast`,
which keeps every value.

**Not claimed.** Nothing for decisions that share a label: the absent-minded driver
(`AbsentMinded`) shows that randomising can then help.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite OpenNet RewardKernel

/-! ### Reindexing contexts, and the evidence pairings of a nonnegative kernel -/

namespace RewardKernel

variable {A A' B B' : Type} [Fintype A] [Fintype A'] [Fintype B] [Fintype B']

/-- Expected utility is invariant under reindexing both boundaries by bijections. -/
theorem eu_reindex (r : RewardKernel A B) (r' : RewardKernel A' B') (ex : A ≃ A') (ey : B ≃ B')
    (hK : ∀ x y, r.K x y = r'.K (ex x) (ey y)) (hW : ∀ x y, r.W x y = r'.W (ex x) (ey y))
    (μ : A' → ℝ) (c : B' → ℝ) :
    r.eu (fun x => μ (ex x)) (fun y => c (ey y)) = r'.eu μ c := by
  unfold eu
  refine Fintype.sum_equiv ex _ _ fun x => ?_
  congr 1
  refine Fintype.sum_equiv ey _ _ fun y => ?_
  rw [hK, hW]

/-- The mass and value of the pullback of an effect are invariant under reindexing both
boundaries by bijections. -/
theorem mass_value_reindex (r : RewardKernel A B) (r' : RewardKernel A' B') (ex : A ≃ A')
    (ey : B ≃ B') (hK : ∀ x y, r.K x y = r'.K (ex x) (ey y))
    (hW : ∀ x y, r.W x y = r'.W (ex x) (ey y)) (s : State A') (e : Effect B') :
    mass ⟨fun x => s.ν (ex x), fun x => s.ρ (ex x)⟩
        (r.pull ⟨fun y => e.m (ey y), fun y => e.c (ey y)⟩) = mass s (r'.pull e) ∧
      value ⟨fun x => s.ν (ex x), fun x => s.ρ (ex x)⟩
        (r.pull ⟨fun y => e.m (ey y), fun y => e.c (ey y)⟩) = value s (r'.pull e) := by
  have hm : ∀ x, (r.pull ⟨fun y => e.m (ey y), fun y => e.c (ey y)⟩).m x =
      (r'.pull e).m (ex x) := fun x =>
    Fintype.sum_equiv ey _ _ fun y => by rw [hK]
  have hc : ∀ x, (r.pull ⟨fun y => e.m (ey y), fun y => e.c (ey y)⟩).c x =
      (r'.pull e).c (ex x) := fun x =>
    Fintype.sum_equiv ey _ _ fun y => by rw [hK, hW]
  constructor
  · unfold mass
    exact Fintype.sum_equiv ex _ _ fun x => by rw [hm]
  · unfold value
    exact Fintype.sum_equiv ex _ _ fun x => by rw [hm, hc]

omit [Fintype A'] [Fintype B'] in
/-- The evidence mass of a nonnegative kernel between a nonnegative state and a nonnegative
effect is nonnegative. -/
theorem mass_pull_nonneg (r : RewardKernel A B) (hK : ∀ x y, 0 ≤ r.K x y) (s : State A)
    (hs : ∀ x, 0 ≤ s.ν x) (e : Effect B) (he : ∀ y, 0 ≤ e.m y) : 0 ≤ mass s (r.pull e) :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (hs x) (Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (he y))

omit [Fintype A'] [Fintype B'] in
/-- **Zero evidence mass means zero evidence-weighted value**, for a nonnegative kernel whose
reward vanishes where its probability does, a nonnegative state whose reward vanishes where
its mass does, and a nonnegative effect whose value vanishes where its likelihood does. -/
theorem value_pull_eq_zero (r : RewardKernel A B) (hK : ∀ x y, 0 ≤ r.K x y)
    (hKW : ∀ x y, r.K x y = 0 → r.W x y = 0) (s : State A) (hs : ∀ x, 0 ≤ s.ν x)
    (hsρ : ∀ x, s.ν x = 0 → s.ρ x = 0) (e : Effect B) (he : ∀ y, 0 ≤ e.m y)
    (hec : ∀ y, e.m y = 0 → e.c y = 0) (h0 : mass s (r.pull e) = 0) :
    value s (r.pull e) = 0 := by
  have hpm : ∀ x, 0 ≤ (r.pull e).m x :=
    fun x => Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (he y)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (hs x) (hpm x)).1 h0
  refine Finset.sum_eq_zero fun x hx => ?_
  by_cases hν : s.ν x = 0
  · rw [hsρ x hν, hν, zero_mul, zero_mul, add_zero]
  · have hm0 : (r.pull e).m x = 0 := (mul_eq_zero.1 (hterm x hx)).resolve_left hν
    have hy := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => mul_nonneg (hK x y) (he y)).1 hm0
    have hc0 : (r.pull e).c x = 0 := by
      refine Finset.sum_eq_zero fun y hym => ?_
      rcases mul_eq_zero.1 (hy y hym) with h | h
      · rw [hKW x y h, h, zero_mul, zero_mul, add_zero]
      · rw [h, hec y h, mul_zero, mul_zero, add_zero]
    rw [hm0, hc0, mul_zero, mul_zero, add_zero]

end RewardKernel

namespace IDInterpretation

variable {S : IDSignature} (M : IDInterpretation S)
variable {X Y : S.Iface}

/-! ### Changing one row of a behavioural strategy -/

open Classical in
/-- `β` with the row `p` of the decision label `l` replaced by the point mass at `s₀`. -/
def setRow (β : M.Behaviour) (l : S.Label) (p : List (Sigma M.states))
    (s₀ : M.states (S.result l)) : M.Behaviour where
  policy l' h p' s := if l' = l ∧ p' = p then (if s = ⟨S.result l, s₀⟩ then 1 else 0)
    else β.policy l' h p' s
  nonneg l' h p' s := by
    split_ifs
    · norm_num
    · norm_num
    · exact β.nonneg l' h p' s
  normalized l' h p' hp := by
    by_cases hc : l' = l ∧ p' = p
    · obtain ⟨rfl, rfl⟩ := hc
      simp
    · simp only [hc, if_false]
      exact β.normalized l' h p' hp

open Classical in
theorem weight_setRow (β : M.Behaviour) (l : S.Label) (p : List (Sigma M.states))
    (s₀ : M.states (S.result l)) (l' : S.Label) (p' : List (Sigma M.states))
    (s : Sigma M.states) :
    (M.interpB (M.setRow β l p s₀)).weight l' p' s =
      if S.isDecision l' = true ∧ l' = l ∧ p' = p then (if s = ⟨S.result l, s₀⟩ then 1 else 0)
      else (M.interpB β).weight l' p' s := by
  change (if h' : S.isDecision l' = true then (M.setRow β l p s₀).policy l' h' p' s
      else M.chance l' p' s) = if S.isDecision l' = true ∧ l' = l ∧ p' = p then _ else
        (if h' : S.isDecision l' = true then β.policy l' h' p' s else M.chance l' p' s)
  by_cases h : S.isDecision l' = true
  · simp only [h, dite_true, true_and, setRow]
  · rw [dif_neg h, dif_neg h, if_neg (fun hc => h hc.1)]

/-- Assignments do not depend on the weights of an interpretation: read an assignment of one
behavioural strategy's interpretation as one of another's, keeping every value. -/
def recast {β β' : M.Behaviour} {A : Type} {τ : A → S.Ty} :
    (M.interpB β).Assignment τ ≃ (M.interpB β').Assignment τ where
  toFun x := ⟨x.value, x.typed⟩
  invFun x := ⟨x.value, x.typed⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The semantics of a behavioural strategy read on a fixed interpretation's assignments -/

section At

variable (β₀ : M.Behaviour) (ev : M.Likelihood)

/-- The joint weight under `β` of the internal assignment `z` from the input `x`, both
assignments of `β₀`'s interpretation. -/
def jointAt (β : M.Behaviour) (f : IDNet X Y) (x : (M.interpB β₀).Boundary X)
    (z : (M.interpB β₀).Internal f.net) : ℝ :=
  ∏ a, (M.interpB β).weight (f.net.label a) ((M.interpB β₀).parents f.net x z a) (z a)

/-- The likelihood of the values of the generators. -/
def likAt (f : IDNet X Y) (z : (M.interpB β₀).Internal f.net) : ℝ :=
  ∏ a, ev (f.net.label a) (z a)

/-- The likelihood-weighted reward kernel of `f` under `β`, on `β₀`'s assignments. -/
def kernelAt (β : M.Behaviour) (f : IDNet X Y) :
    RewardKernel ((M.interpB β₀).Boundary X) ((M.interpB β₀).Boundary Y) :=
  ⟨fun x y => ∑ z, if y = (M.interpB β₀).read f.net x z then
      M.jointAt β₀ β f x z * M.likAt β₀ ev f z else 0,
    fun x y => ∑ z, if y = (M.interpB β₀).read f.net x z then
      M.jointAt β₀ β f x z * M.likAt β₀ ev f z * M.rewardB β₀ f x z else 0⟩

theorem kernelAt_congr {β β' : M.Behaviour} (f : IDNet X Y)
    (h : ∀ x z, M.jointAt β₀ β f x z = M.jointAt β₀ β' f x z) :
    M.kernelAt β₀ ev β f = M.kernelAt β₀ ev β' f := by
  ext x y <;> simp only [kernelAt, h]

theorem jointAt_nonneg (β : M.Behaviour) (f : IDNet X Y) (x : (M.interpB β₀).Boundary X)
    (z : (M.interpB β₀).Internal f.net) : 0 ≤ M.jointAt β₀ β f x z :=
  Finset.prod_nonneg fun _ _ => (M.interpB β).nonneg _ _ _

theorem likAt_nonneg (hev : ∀ l v, 0 ≤ ev l v) (f : IDNet X Y)
    (z : (M.interpB β₀).Internal f.net) : 0 ≤ M.likAt β₀ ev f z :=
  Finset.prod_nonneg fun _ _ => hev _ _

theorem kernelAt_K_nonneg (hev : ∀ l v, 0 ≤ ev l v) (β : M.Behaviour) (f : IDNet X Y)
    (x : (M.interpB β₀).Boundary X) (y : (M.interpB β₀).Boundary Y) :
    0 ≤ (M.kernelAt β₀ ev β f).K x y :=
  Finset.sum_nonneg fun z _ => by
    split_ifs
    · exact mul_nonneg (M.jointAt_nonneg β₀ β f x z) (M.likAt_nonneg β₀ ev hev f z)
    · exact le_rfl

theorem kernelAt_W_eq_zero (hev : ∀ l v, 0 ≤ ev l v) (β : M.Behaviour) (f : IDNet X Y)
    (x : (M.interpB β₀).Boundary X) (y : (M.interpB β₀).Boundary Y)
    (h : (M.kernelAt β₀ ev β f).K x y = 0) : (M.kernelAt β₀ ev β f).W x y = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun z _ => by
    split_ifs
    · exact mul_nonneg (M.jointAt_nonneg β₀ β f x z) (M.likAt_nonneg β₀ ev hev f z)
    · exact le_rfl).1 h
  refine Finset.sum_eq_zero fun z hzm => ?_
  have hzz := hz z hzm
  split_ifs at hzz ⊢
  · rw [hzz, zero_mul]
  · rfl

end At

/-- The semantics of an open influence diagram under the behavioural strategy `β`, every
internal assignment weighted by the likelihood `ev` of its generators' values. -/
def interpretBE (β : M.Behaviour) (ev : M.Likelihood) (f : IDNet X Y) :
    RewardKernel ((M.interpB β).Boundary X) ((M.interpB β).Boundary Y) :=
  M.kernelAt β ev β f

/-- With the constant likelihood `1`, the weighted semantics is `interpretB`. -/
theorem interpretBE_one (β : M.Behaviour) (f : IDNet X Y) :
    M.interpretBE β (fun _ _ => 1) f = M.interpretB β f := by
  have hl : ∀ z, M.likAt β (fun _ _ => 1) f z = 1 := fun z => by simp [likAt]
  ext x y
  · simp only [interpretBE, kernelAt, hl, mul_one]
    rfl
  · simp only [interpretBE, kernelAt, hl, mul_one]
    rfl

/-- For the point masses of a deterministic strategy, the weighted semantics is
`interpretE`. -/
theorem interpretBE_pointMass (σ : M.Strategy) (ev : M.Likelihood) (f : IDNet X Y) :
    M.interpretBE (M.pointMass σ) ev f = M.interpretE σ ev f := rfl

/-- The semantics does not depend on the interpretation whose assignments it is read on. -/
theorem kernelAt_recast (β₀ β : M.Behaviour) (ev : M.Likelihood) (f : IDNet X Y)
    (x : (M.interpB β₀).Boundary X) (y : (M.interpB β₀).Boundary Y) :
    (M.kernelAt β₀ ev β f).K x y = (M.interpretBE β ev f).K (M.recast x) (M.recast y) ∧
      (M.kernelAt β₀ ev β f).W x y = (M.interpretBE β ev f).W (M.recast x) (M.recast y) := by
  have hr : ∀ z : (M.interpB β₀).Internal f.net,
      (M.recast y = (M.interpB β).read f.net (M.recast x) (M.recast z)) ↔
        y = (M.interpB β₀).read f.net x z :=
    fun z => (M.recast (β := β₀) (β' := β)).injective.eq_iff (a := y)
      (b := (M.interpB β₀).read f.net x z)
  constructor
  · simp only [interpretBE, kernelAt]
    refine Fintype.sum_equiv (M.recast (β := β₀) (β' := β)) _ _ fun z => ?_
    by_cases hc : y = (M.interpB β₀).read f.net x z
    · rw [if_pos hc, if_pos ((hr z).2 hc)]
      rfl
    · rw [if_neg hc, if_neg (fun h => hc ((hr z).1 h))]
  · simp only [interpretBE, kernelAt]
    refine Fintype.sum_equiv (M.recast (β := β₀) (β' := β)) _ _ fun z => ?_
    by_cases hc : y = (M.interpB β₀).read f.net x z
    · rw [if_pos hc, if_pos ((hr z).2 hc)]
      rfl
    · rw [if_neg hc, if_neg (fun h => hc ((hr z).1 h))]

/-! ### Affinity in one row -/

/-- No two decision generators share a label, so no two decisions share a policy. -/
def DistinctDecisions (f : IDNet X Y) : Prop :=
  ∀ a b, f.IsDecision a → f.net.label a = f.net.label b → a = b

open Classical in
theorem sum_point (t : S.Ty) (v : Sigma M.states) (hv : v.1 = t) (g : Sigma M.states → ℝ) :
    ∑ s : M.states t, g ⟨t, s⟩ * (if v = ⟨t, s⟩ then 1 else 0) = g v := by
  obtain ⟨t', s'⟩ := v
  simp only at hv
  subst hv
  simp

section Affine

variable (β₀ : M.Behaviour) (ev : M.Likelihood)

/-- **The joint weight is affine in one row of the strategy**: when decision labels are
distinct, the weight under `β` is the mixture, weighted by `β`'s distribution at the row `p`
of `l`, of the weights with that row replaced by each point mass. -/
theorem jointAt_affine (f : IDNet X Y) (hf : DistinctDecisions f) (β : M.Behaviour)
    (l : S.Label) (hl : S.isDecision l = true) (p : List (Sigma M.states))
    (hp : p.map Sigma.fst = S.inputs l) (x : (M.interpB β₀).Boundary X)
    (z : (M.interpB β₀).Internal f.net) :
    M.jointAt β₀ β f x z = ∑ s₀ : M.states (S.result l),
      β.policy l hl p ⟨S.result l, s₀⟩ * M.jointAt β₀ (M.setRow β l p s₀) f x z := by
  classical
  by_cases hex : ∃ a, f.IsDecision a ∧ f.net.label a = l ∧
      (M.interpB β₀).parents f.net x z a = p
  · obtain ⟨a₀, ha₀, hla, hpa⟩ := hex
    subst hla
    subst hpa
    have hR : ∀ s₀, M.jointAt β₀ (M.setRow β (f.net.label a₀)
        ((M.interpB β₀).parents f.net x z a₀) s₀) f x z =
        (if z a₀ = ⟨S.result (f.net.label a₀), s₀⟩ then 1 else 0) *
          ∏ a ∈ Finset.univ.erase a₀, (M.interpB β).weight (f.net.label a)
            ((M.interpB β₀).parents f.net x z a) (z a) := by
      intro s₀
      unfold jointAt
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a₀), weight_setRow,
        if_pos ⟨hl, rfl, rfl⟩]
      congr 1
      refine Finset.prod_congr rfl fun a ha => ?_
      rw [weight_setRow, if_neg]
      rintro ⟨hd, hl', _⟩
      exact Finset.ne_of_mem_erase ha (hf a a₀ hd hl')
    have hw : (M.interpB β).weight (f.net.label a₀) ((M.interpB β₀).parents f.net x z a₀)
        (z a₀) = β.policy (f.net.label a₀) hl ((M.interpB β₀).parents f.net x z a₀) (z a₀) := by
      change (if h' : S.isDecision (f.net.label a₀) = true then β.policy _ h' _ _
        else M.chance _ _ _) = _
      rw [dif_pos hl]
    simp_rw [hR]
    unfold jointAt
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a₀), hw]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    exact (M.sum_point _ (z a₀) (z.typed a₀)
      (fun s => β.policy (f.net.label a₀) hl ((M.interpB β₀).parents f.net x z a₀) s)).symm
  · have hsame : ∀ s₀, M.jointAt β₀ (M.setRow β l p s₀) f x z = M.jointAt β₀ β f x z := by
      intro s₀
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [weight_setRow, if_neg]
      rintro ⟨hd, hl', hp'⟩
      exact hex ⟨a, hd, hl', hp'⟩
    simp only [hsame, ← Finset.sum_mul]
    rw [β.normalized l hl p hp, one_mul]

/-- **The reward kernel is a mixture over one row**: when decision labels are distinct, the
semantics under `β` is the mixture, weighted by `β`'s distribution at the row `p` of `l`, of
the semantics with that row replaced by each point mass. -/
theorem kernelAt_eq_mix (f : IDNet X Y) (hf : DistinctDecisions f) (β : M.Behaviour)
    (l : S.Label) (hl : S.isDecision l = true) (p : List (Sigma M.states))
    (hp : p.map Sigma.fst = S.inputs l) :
    M.kernelAt β₀ ev β f = mix (fun s₀ => β.policy l hl p ⟨S.result l, s₀⟩)
      (fun s₀ => M.kernelAt β₀ ev (M.setRow β l p s₀) f) := by
  ext x y
  · simp only [kernelAt, mix, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs
    · rw [M.jointAt_affine β₀ f hf β l hl p hp x z, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp
  · simp only [kernelAt, mix, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs
    · rw [M.jointAt_affine β₀ f hf β l hl p hp x z, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp

end Affine

/-! ### The rows that decisions read -/

section Rows

variable (β₀ : M.Behaviour)

open Classical in
/-- The rows that the decision generators of `f` read, over all inputs and internal
assignments: finitely many. -/
def rows (f : IDNet X Y) : Finset (S.Label × List (Sigma M.states)) :=
  ((Finset.univ : Finset (f.net.Gen × (M.interpB β₀).Boundary X ×
      (M.interpB β₀).Internal f.net)).filter fun t => f.IsDecision t.1).image
    fun t => (f.net.label t.1, (M.interpB β₀).parents f.net t.2.1 t.2.2 t.1)

theorem mem_rows (f : IDNet X Y) {a : f.net.Gen} (ha : f.IsDecision a)
    (x : (M.interpB β₀).Boundary X) (z : (M.interpB β₀).Internal f.net) :
    (f.net.label a, (M.interpB β₀).parents f.net x z a) ∈ M.rows β₀ f := by
  classical
  unfold rows
  exact Finset.mem_image.2 ⟨(a, x, z), Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩

theorem rows_spec (f : IDNet X Y) {q : S.Label × List (Sigma M.states)}
    (hq : q ∈ M.rows β₀ f) : S.isDecision q.1 = true ∧ q.2.map Sigma.fst = S.inputs q.1 := by
  classical
  unfold rows at hq
  obtain ⟨⟨a, x, z⟩, ht, rfl⟩ := Finset.mem_image.1 hq
  exact ⟨(Finset.mem_filter.1 ht).2, (M.interpB β₀).parents_typed f.net x z a⟩

end Rows

open Classical in
/-- `β` is deterministic at the row `q`: it draws a point mass there. -/
def DetAt (β : M.Behaviour) (q : S.Label × List (Sigma M.states)) : Prop :=
  ∀ h : S.isDecision q.1 = true, ∃ s₀ : M.states (S.result q.1),
    ∀ s, β.policy q.1 h q.2 s = if s = ⟨S.result q.1, s₀⟩ then 1 else 0

theorem detAt_setRow_self (β : M.Behaviour) (l : S.Label) (p : List (Sigma M.states))
    (s₀ : M.states (S.result l)) : M.DetAt (M.setRow β l p s₀) (l, p) :=
  fun _ => ⟨s₀, fun s => by simp [setRow]⟩

theorem detAt_setRow_of_ne (β : M.Behaviour) (l : S.Label) (p : List (Sigma M.states))
    (s₀ : M.states (S.result l)) {q : S.Label × List (Sigma M.states)} (hq : q ≠ (l, p))
    (hd : M.DetAt β q) : M.DetAt (M.setRow β l p s₀) q := by
  intro h
  obtain ⟨s₁, hs₁⟩ := hd h
  refine ⟨s₁, fun s => ?_⟩
  have hne : ¬ (q.1 = l ∧ q.2 = p) := fun ⟨h1, h2⟩ => hq (Prod.ext h1 h2)
  simp only [setRow, hne, if_false]
  exact hs₁ s

open Classical in
/-- **A strategy deterministic on every row read is a deterministic strategy.** -/
theorem det_joint (β₀ : M.Behaviour) (f : IDNet X Y)
    (hne : ∀ l, S.isDecision l = true → Nonempty (M.states (S.result l)))
    (β : M.Behaviour) (hβ : ∀ q ∈ M.rows β₀ f, M.DetAt β q) :
    ∃ σ : M.Strategy, ∀ x z, M.jointAt β₀ β f x z = M.jointAt β₀ (M.pointMass σ) f x z := by
  refine ⟨fun l h p => if hq : ∃ s₀ : M.states (S.result l), ∀ s, β.policy l h p s =
      (if s = ⟨S.result l, s₀⟩ then 1 else 0) then hq.choose else (hne l h).some,
    fun x z => Finset.prod_congr rfl fun a _ => ?_⟩
  by_cases ha : S.isDecision (f.net.label a) = true
  · obtain ⟨s₀, hs₀⟩ := hβ _ (M.mem_rows β₀ f ha x z) ha
    have hq : ∃ s₀ : M.states (S.result (f.net.label a)), ∀ s,
        β.policy (f.net.label a) ha ((M.interpB β₀).parents f.net x z a) s =
          (if s = ⟨S.result (f.net.label a), s₀⟩ then 1 else 0) := ⟨s₀, hs₀⟩
    change (if h' : S.isDecision (f.net.label a) = true then β.policy _ h' _ _
      else M.chance _ _ _) = (if h' : S.isDecision (f.net.label a) = true then
        (M.pointMass _).policy _ h' _ _ else M.chance _ _ _)
    rw [dif_pos ha, dif_pos ha, hq.choose_spec]
    simp only [pointMass, dif_pos hq]
    split_ifs <;> rfl
  · change (if h' : S.isDecision (f.net.label a) = true then β.policy _ h' _ _
      else M.chance _ _ _) = (if h' : S.isDecision (f.net.label a) = true then
        (M.pointMass _).policy _ h' _ _ else M.chance _ _ _)
    rw [dif_neg ha, dif_neg ha]

/-- **Replacing the rows one at a time.** If an objective of the strategy depends only on the
joint weights, and every row read can be made deterministic without lowering it (and keeping
a side condition), then some deterministic strategy does at least as well. -/
theorem kuhn_induction (β₀ : M.Behaviour) (f : IDNet X Y)
    (hne : ∀ l, S.isDecision l = true → Nonempty (M.states (S.result l)))
    (Good : M.Behaviour → Prop) (Φ : M.Behaviour → ℝ)
    (hcongr : ∀ β β', (∀ x z, M.jointAt β₀ β f x z = M.jointAt β₀ β' f x z) →
      (Good β → Good β') ∧ Φ β = Φ β')
    (hstep : ∀ β, Good β → ∀ q ∈ M.rows β₀ f, ∀ _ : S.isDecision q.1 = true,
      ∃ s₀ : M.states (S.result q.1), Good (M.setRow β q.1 q.2 s₀) ∧
        Φ β ≤ Φ (M.setRow β q.1 q.2 s₀))
    (β : M.Behaviour) (hβ : Good β) :
    ∃ σ : M.Strategy, Good (M.pointMass σ) ∧ Φ β ≤ Φ (M.pointMass σ) := by
  classical
  suffices key : ∀ F : Finset (S.Label × List (Sigma M.states)), ∀ β, Good β →
      (∀ q ∈ M.rows β₀ f, q ∉ F → M.DetAt β q) →
      ∃ σ : M.Strategy, Good (M.pointMass σ) ∧ Φ β ≤ Φ (M.pointMass σ) from
    key (M.rows β₀ f) β hβ fun q hq hn => absurd hq hn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro β hβ hdet
    obtain ⟨σ, hσ⟩ := M.det_joint β₀ f hne β fun q hq => hdet q hq (Finset.notMem_empty q)
    obtain ⟨hg, hΦ⟩ := hcongr β (M.pointMass σ) hσ
    exact ⟨σ, hg hβ, hΦ.le⟩
  | insert q F hqF ih =>
    intro β hβ hdet
    by_cases hq : q ∈ M.rows β₀ f
    · obtain ⟨s₀, hg, hΦ⟩ := hstep β hβ q hq (M.rows_spec β₀ f hq).1
      obtain ⟨σ, hgσ, hΦσ⟩ := ih (M.setRow β q.1 q.2 s₀) hg fun q' hq' hq'F => by
        by_cases he : q' = q
        · subst he
          exact M.detAt_setRow_self β q'.1 q'.2 s₀
        · exact M.detAt_setRow_of_ne β q.1 q.2 s₀ (fun h => he (h.trans Prod.mk.eta))
            (hdet q' hq' (by simp [Finset.mem_insert, he, hq'F]))
      exact ⟨σ, hgσ, hΦ.trans hΦσ⟩
    · exact ih β hβ fun q' hq' hq'F => hdet q' hq' (by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hq (h ▸ hq'), hq'F⟩)

/-! ### Kuhn's theorem -/

/-- **Kuhn's theorem for open influence diagrams.** When no two decision generators share a
label, for every behavioural strategy `β`, prior `μ` and continuation `c`, some deterministic
strategy `σ` has at least `β`'s expected utility. (`interpretB (pointMass σ) f` is
`interpret σ f`, by `interpretB_pointMass`.) -/
theorem kuhn_eu (f : IDNet X Y) (hf : DistinctDecisions f)
    (hne : ∀ l, S.isDecision l = true → Nonempty (M.states (S.result l)))
    (β : M.Behaviour) (μ : (M.interpB β).Boundary X → ℝ) (c : (M.interpB β).Boundary Y → ℝ) :
    ∃ σ : M.Strategy, (M.interpretB β f).eu μ c ≤
      (M.interpretB (M.pointMass σ) f).eu (fun x => μ (M.recast x))
        (fun y => c (M.recast y)) := by
  obtain ⟨σ, -, hσ⟩ := M.kuhn_induction β f hne (fun _ => True)
    (fun β' => (M.kernelAt β (fun _ _ => 1) β' f).eu μ c)
    (fun β' β'' h => ⟨id, by simp only [M.kernelAt_congr β _ f h]⟩)
    (fun β' _ q hq hl => by
      haveI := hne q.1 hl
      have hp := (M.rows_spec β f hq).2
      obtain ⟨s₀, hs₀⟩ := eu_mix_le (fun s₀ => β'.policy q.1 hl q.2 ⟨S.result q.1, s₀⟩)
        (fun s => β'.nonneg q.1 hl q.2 _) (β'.normalized q.1 hl q.2 hp)
        (fun s₀ => M.kernelAt β (fun _ _ => 1) (M.setRow β' q.1 q.2 s₀) f) μ c
      refine ⟨s₀, trivial, ?_⟩
      show (M.kernelAt β (fun _ _ => 1) β' f).eu μ c ≤
        (M.kernelAt β (fun _ _ => 1) (M.setRow β' q.1 q.2 s₀) f).eu μ c
      rw [M.kernelAt_eq_mix β _ f hf β' q.1 hl q.2 hp]
      exact hs₀)
    β trivial
  refine ⟨σ, ?_⟩
  have hre := eu_reindex (M.interpretBE (M.pointMass σ) (fun _ _ => 1) f)
    (M.kernelAt β (fun _ _ => 1) (M.pointMass σ) f) M.recast M.recast
    (fun x y => (M.kernelAt_recast β (M.pointMass σ) _ f (M.recast x) (M.recast y)).1.symm)
    (fun x y => (M.kernelAt_recast β (M.pointMass σ) _ f (M.recast x) (M.recast y)).2.symm) μ c
  rw [M.interpretBE_one] at hre
  rw [← M.interpretBE_one β f, hre]
  exact hσ

/-- **Kuhn's theorem given evidence.** When no two decision generators share a label, the
likelihoods are nonnegative, the state's reward vanishes where its mass does and the effect's
value vanishes where its likelihood does: if the evidence has positive mass under the
behavioural strategy `β`, then some deterministic strategy `σ` gives it positive mass and a
conditional value at least as large. (`interpretBE (pointMass σ) ev f` is `interpretE σ ev f`,
by `interpretBE_pointMass`.) -/
theorem kuhn_conditional (f : IDNet X Y) (hf : DistinctDecisions f)
    (hne : ∀ l, S.isDecision l = true → Nonempty (M.states (S.result l)))
    (β : M.Behaviour) (ev : M.Likelihood) (hev : ∀ l v, 0 ≤ ev l v)
    (s : RewardKernel.State ((M.interpB β).Boundary X)) (hs : ∀ x, 0 ≤ s.ν x)
    (hsρ : ∀ x, s.ν x = 0 → s.ρ x = 0)
    (e : RewardKernel.Effect ((M.interpB β).Boundary Y)) (he : ∀ y, 0 ≤ e.m y)
    (hec : ∀ y, e.m y = 0 → e.c y = 0)
    (hpos : 0 < mass s ((M.interpretBE β ev f).pull e)) :
    ∃ σ : M.Strategy,
      0 < mass ⟨fun x => s.ν (M.recast x), fun x => s.ρ (M.recast x)⟩
        ((M.interpretBE (M.pointMass σ) ev f).pull
          ⟨fun y => e.m (M.recast y), fun y => e.c (M.recast y)⟩) ∧
      conditionalValue s ((M.interpretBE β ev f).pull e) ≤
        conditionalValue ⟨fun x => s.ν (M.recast x), fun x => s.ρ (M.recast x)⟩
          ((M.interpretBE (M.pointMass σ) ev f).pull
            ⟨fun y => e.m (M.recast y), fun y => e.c (M.recast y)⟩) := by
  obtain ⟨σ, hgσ, hσ⟩ := M.kuhn_induction β f hne
    (fun β' => 0 < mass s ((M.kernelAt β ev β' f).pull e))
    (fun β' => conditionalValue s ((M.kernelAt β ev β' f).pull e))
    (fun β' β'' h => by
      simp only [M.kernelAt_congr β ev f h]
      exact ⟨id, trivial⟩)
    (fun β' hg q hq hl => by
      have hp := (M.rows_spec β f hq).2
      have hmix := M.kernelAt_eq_mix β ev f hf β' q.1 hl q.2 hp
      change 0 < mass s ((M.kernelAt β ev β' f).pull e) at hg
      rw [hmix] at hg
      obtain ⟨s₀, hs₀, hle⟩ := conditionalValue_mix_le
        (fun s₀ => β'.policy q.1 hl q.2 ⟨S.result q.1, s₀⟩) (fun s => β'.nonneg q.1 hl q.2 _)
        (fun s₀ => M.kernelAt β ev (M.setRow β' q.1 q.2 s₀) f) s e
        (fun i => mass_pull_nonneg _ (M.kernelAt_K_nonneg β ev hev _ f) s hs e he)
        (fun i => value_pull_eq_zero _ (M.kernelAt_K_nonneg β ev hev _ f)
          (M.kernelAt_W_eq_zero β ev hev _ f) s hs hsρ e he hec) hg
      refine ⟨s₀, hs₀, ?_⟩
      show conditionalValue s ((M.kernelAt β ev β' f).pull e) ≤ _
      rw [hmix]
      exact hle)
    β hpos
  have hre := mass_value_reindex (M.interpretBE (M.pointMass σ) ev f)
    (M.kernelAt β ev (M.pointMass σ) f) M.recast M.recast
    (fun x y => (M.kernelAt_recast β (M.pointMass σ) ev f (M.recast x) (M.recast y)).1.symm)
    (fun x y => (M.kernelAt_recast β (M.pointMass σ) ev f (M.recast x) (M.recast y)).2.symm) s e
  refine ⟨σ, ?_, ?_⟩
  · rw [hre.1]
    exact hgσ
  · unfold conditionalValue at hσ ⊢
    rw [hre.1, hre.2]
    exact hσ

end IDInterpretation

end OpenInfluence
