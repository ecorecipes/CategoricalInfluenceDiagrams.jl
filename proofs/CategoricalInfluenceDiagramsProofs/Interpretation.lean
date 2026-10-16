import CategoricalInfluenceDiagramsProofs.Syntax
import CategoricalInfluenceDiagramsProofs.Context
import CategoricalInfluenceDiagramsProofs.Category

/-!
# The fixed-strategy interpretation and its functoriality

An **interpretation** of an influence-diagram signature (`IDInterpretation`) gives every
type a finite state space, every chance label a nonnegative table normalised on every
correctly typed parent row, and every utility label a real-valued table on its ordered
inputs. A **strategy** (`IDInterpretation.Strategy`) gives every decision label a
deterministic policy: a function from the values on the decision's information ports to a
state of its output type. As in `CategoricalInfluenceDiagrams.jl`, policies are keyed by
label, so decision generators with equal labels share a policy, and one strategy covers
both components of a composite (the Julia package's disjoint union of the components'
strategies, when their decision labels are disjoint).

A strategy turns the interpretation into an ordinary `OpenNet.Interpretation`
(`IDInterpretation.interp`): a decision generator becomes the point mass at its policy's
choice, a chance generator keeps its table. Its sum-product kernel (ADR 0010, unchanged) is
the probability component `K` of the interpretation. The reward component `W` sums, over
the same internal assignments, their probability times the total utility of the diagram's
utility generators read on their scopes (`rewardTable`). So the fixed-strategy semantics of
an open influence diagram `f : X → Y` is the reward kernel

`interpret σ f = (K_f, W_f) : RewardKernel (Boundary X) (Boundary Y)`,

ADR 0018's `interpret(o, strategy)`. Its probability component is stochastic
(`interpret_stochastic`), so it is a morphism of `FinRew` (`interpretHom`).

**Functoriality** for a fixed strategy, on representatives (the syntax is not quotiented):

* `interpret_comp`: `interpret σ (f ; g) = interpret σ f ; interpret σ g`;
* `interpret_identity`: `interpret σ (id X) = (id, 0)`;
* `interpret_tensor`: `interpret σ (f ⊗ g)`, read through the canonical bijection between
  assignments of `X ⊔ X'` and pairs of assignments, is `interpret σ f ⊗ interpret σ g`;
  `interpret_tensor_natural` states the same as naturality of that bijection, the shape of
  `OpenNet.Interpretation.tensor_natural`.

The **contextual identity** then holds for interpreted diagrams (`contextual_identity`),
with the normalisation of the suffix supplied by `interpret_stochastic`.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open CategoryTheory FiniteKernelsProofs.Finite OpenNet

/-- A semantics for the chance and utility labels of an influence-diagram signature. -/
structure IDInterpretation (S : IDSignature) where
  /-- The finite state space of each type. -/
  states : S.Ty → Type
  /-- State spaces are finite. -/
  finite : ∀ t, Fintype (states t)
  /-- The table of a chance label, on ordered typed parent values and one child value. -/
  chance : S.Label → List (Sigma states) → Sigma states → ℝ
  /-- Chance tables are nonnegative. -/
  chance_nonneg : ∀ l p s, S.isDecision l = false → 0 ≤ chance l p s
  /-- Chance tables are normalised on every correctly typed parent row. -/
  chance_normalized : ∀ l p, S.isDecision l = false → p.map Sigma.fst = S.inputs l →
    @Finset.sum (states (S.result l)) ℝ _ (@Finset.univ _ (finite _))
      (fun s => chance l p ⟨S.result l, s⟩) = 1
  /-- The table of a utility label, on ordered typed input values. -/
  utility : S.ULabel → List (Sigma states) → ℝ

attribute [instance] IDInterpretation.finite

namespace IDInterpretation

variable {S : IDSignature} (M : IDInterpretation S)

/-- A deterministic strategy: for each decision label, a policy mapping the values on the
decision's information ports to a state of its output type. -/
def Strategy : Type :=
  (l : S.Label) → S.isDecision l = true → List (Sigma M.states) → M.states (S.result l)

open Classical in
/-- The `OpenNet` interpretation for a fixed strategy: decisions are the point masses of
their policies, chance mechanisms keep their tables. -/
def interp (σ : M.Strategy) : OpenNet.Interpretation S.toSignature where
  states := M.states
  finite := M.finite
  weight l p s :=
    if h : S.isDecision l = true then (if s = ⟨S.result l, σ l h p⟩ then 1 else 0)
    else M.chance l p s
  nonneg l p s := by
    by_cases h : S.isDecision l = true
    · simp only [h, dite_true]
      split_ifs <;> norm_num
    · simp only [h]
      exact M.chance_nonneg l p s (by simpa using h)
  normalized l p hp := by
    by_cases h : S.isDecision l = true
    · simp only [h, dite_true, Sigma.mk.injEq, heq_eq_eq, true_and]
      simp
    · simp only [h]
      exact M.chance_normalized l p (by simpa using h) hp

variable (σ : M.Strategy)
variable {X Y Z X' Y' : S.Iface}

/-- The total utility of the diagram's utility generators, read on their scopes, at the
input assignment `x` and the internal assignment `z`. -/
def reward (f : IDNet X Y) (x : (M.interp σ).Boundary X) (z : (M.interp σ).Internal f.net) :
    ℝ :=
  ∑ u, M.utility (f.ulabel u) ((f.uparents u).map ((M.interp σ).valuation f.net x z).value)

/-- The reward table: the probability-weighted total utility of the internal assignments
that produce each output. -/
def rewardTable (f : IDNet X Y) :
    Kernel ((M.interp σ).Boundary X) ((M.interp σ).Boundary Y) :=
  fun x y => ∑ z, if y = (M.interp σ).read f.net x z then
    (M.interp σ).joint f.net x z * M.reward σ f x z else 0

/-- The fixed-strategy semantics of an open influence diagram: the sum-product kernel of
its net and its reward table. -/
def interpret (f : IDNet X Y) :
    RewardKernel ((M.interp σ).Boundary X) ((M.interp σ).Boundary Y) :=
  ⟨(M.interp σ).kernel f.net, M.rewardTable σ f⟩

theorem interpret_stochastic (f : IDNet X Y) : (M.interpret σ f).Stochastic :=
  (M.interp σ).kernel_stochastic f.net

/-- The boundary assignments of an interface, as an object of `FinRew`. -/
def space (X : S.Iface) : FinRew := ⟨(M.interp σ).Boundary X⟩

/-- The interpretation as a morphism of `FinRew`. -/
def interpretHom (f : IDNet X Y) : M.space σ X ⟶ M.space σ Y :=
  ⟨M.interpret σ f, M.interpret_stochastic σ f⟩

/-! ### The atomic generators -/

open Classical in
/-- A decision generator is the point mass at its policy's choice, read on the values of
its information ports. -/
theorem interp_weight_decision (l : S.Label) (h : S.isDecision l = true)
    (p : List (Sigma M.states)) (s : Sigma M.states) :
    (M.interp σ).weight l p s = if s = ⟨S.result l, σ l h p⟩ then 1 else 0 := by
  simp [interp, h]

/-- A chance generator keeps its table. -/
theorem interp_weight_chance (l : S.Label) (h : S.isDecision l = false)
    (p : List (Sigma M.states)) (s : Sigma M.states) :
    (M.interp σ).weight l p s = M.chance l p s := by
  simp [interp, h]

/-- A utility generator passes its interface through unchanged. -/
theorem interpret_utility_K (X : S.Iface) (u : S.ULabel) (scope : List X.Port)
    (h : scope.map X.type = S.uinputs u) :
    (M.interpret σ (IDNet.utility X u scope h)).K = Kernel.idK _ := by
  change (M.interp σ).kernel (Net.wire id (fun _ => rfl)) = Kernel.idK _
  rw [(M.interp σ).kernel_wire]
  apply Kernel.ofFun_congr
  intro x
  rfl

/-- A utility generator earns, on the diagonal, the utility of its label read on its
scope. -/
theorem interpret_utility_W (X : S.Iface) (u : S.ULabel) (scope : List X.Port)
    (h : scope.map X.type = S.uinputs u) (x y : (M.interp σ).Boundary X) :
    (M.interpret σ (IDNet.utility X u scope h)).W x y =
      if y = x then M.utility u (scope.map x.value) else 0 := by
  letI : Unique ((M.interp σ).Internal (Net.wire (id : X.Port → X.Port) (fun _ => rfl))) := by
    change Unique ((M.interp σ).Assignment (S.result ∘ (Empty.elim : Empty → S.Label)))
    infer_instance
  change (∑ z, if y = (M.interp σ).read (Net.wire id (fun _ => rfl)) x z then
      (M.interp σ).joint (Net.wire id (fun _ => rfl)) x z *
        M.reward σ (IDNet.utility X u scope h) x z else 0) = _
  rw [Fintype.sum_unique, (M.interp σ).joint_wire, one_mul]
  have hread : (M.interp σ).read (Net.wire id (fun _ => rfl)) x default = x := rfl
  have hrew : M.reward σ (IDNet.utility X u scope h) x
      (default : (M.interp σ).Internal (Net.wire (id : X.Port → X.Port) (fun _ => rfl))) =
      M.utility u (scope.map x.value) := by
    unfold reward
    change (∑ _v : Unit, M.utility u ((scope.map Sum.inl).map _)) = _
    rw [Fintype.sum_unique, List.map_map]
    rfl
  rw [hread, hrew]

/-! ### Rewards of composites -/

theorem reward_comp (f : IDNet X Y) (g : IDNet Y Z) (x : (M.interp σ).Boundary X)
    (a : (M.interp σ).Internal f.net) (b : (M.interp σ).Internal g.net) :
    M.reward σ (f.comp g) x ((M.interp σ).combine f.net g.net a b) =
      M.reward σ f x a + M.reward σ g ((M.interp σ).read f.net x a) b := by
  unfold reward
  erw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (f.ulabel u)
      (((f.uparents u).map (Net.left f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (f.uparents u).map k)
      (funext ((M.interp σ).valuation_comp_left f.net g.net x a b))
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (g.ulabel u)
      (((g.uparents u).map (Net.right f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (g.uparents u).map k)
      (funext ((M.interp σ).valuation_comp_right f.net g.net x a b))

theorem reward_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (a : (M.interp σ).Internal f.net)
    (b : (M.interp σ).Internal g.net) :
    M.reward σ (f.tensor g) (Interpretation.Assignment.join _ x x')
        ((M.interp σ).combine f.net g.net a b) =
      M.reward σ f x a + M.reward σ g x' b := by
  unfold reward
  erw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (f.ulabel u)
      (((f.uparents u).map (Net.tinl f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (f.uparents u).map k)
      (funext ((M.interp σ).valuation_tensor_left f.net g.net x x' a b))
  · apply Finset.sum_congr rfl
    intro u _
    change M.utility (g.ulabel u)
      (((g.uparents u).map (Net.tinr f.net g.net)).map _) = _
    rw [List.map_map]
    congr 1
    exact congrArg (fun k => (g.uparents u).map k)
      (funext ((M.interp σ).valuation_tensor_right f.net g.net x x' a b))

/-! ### Functoriality under serial composition -/

/-- Summing a product of two output-fibre sums over the middle boundary substitutes the
first component's output into the second. -/
theorem sum_fibre_mul {f : Net X Y} {g : Net Y Z} (x : (M.interp σ).Boundary X)
    (w : (M.interp σ).Boundary Z) (F : (M.interp σ).Internal f → ℝ)
    (G : (M.interp σ).Boundary Y → (M.interp σ).Internal g → ℝ) :
    (∑ y, (∑ a, if y = (M.interp σ).read f x a then F a else 0) *
        (∑ b, if w = (M.interp σ).read g y b then G y b else 0)) =
      ∑ a, ∑ b, if w = (M.interp σ).read g ((M.interp σ).read f x a) b then
        F a * G ((M.interp σ).read f x a) b else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single ((M.interp σ).read f x a)]
  · simp only [if_true, Finset.mul_sum, mul_ite, mul_zero]
  · intro y _ hy
    simp [hy]
  · simp

theorem kernel_eq_sum (f : Net X Y) (x : (M.interp σ).Boundary X)
    (y : (M.interp σ).Boundary Y) :
    (M.interp σ).kernel f x y =
      ∑ z, if y = (M.interp σ).read f x z then (M.interp σ).joint f x z else 0 := by
  unfold Interpretation.kernel
  rfl

theorem rewardTable_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.rewardTable σ (f.comp g) =
      Kernel.comp (M.rewardTable σ f) ((M.interp σ).kernel g.net) +
        Kernel.comp ((M.interp σ).kernel f.net) (M.rewardTable σ g) := by
  funext x w
  simp only [Pi.add_apply, Kernel.comp, kernel_eq_sum]
  unfold rewardTable
  rw [M.sum_fibre_mul σ x w (fun a => (M.interp σ).joint f.net x a * M.reward σ f x a)
      (fun y b => (M.interp σ).joint g.net y b),
    M.sum_fibre_mul σ x w (fun a => (M.interp σ).joint f.net x a)
      (fun y b => (M.interp σ).joint g.net y b * M.reward σ g y b)]
  rw [← Finset.sum_add_distrib]
  change (∑ z : (M.interp σ).Internal (f.net.comp g.net),
      if w = (M.interp σ).read (f.net.comp g.net) x z then
        (M.interp σ).joint (f.net.comp g.net) x z * M.reward σ (f.comp g) x z else 0) = _
  erw [← ((M.interp σ).sumLabelsEquiv f.net.label g.net.label).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have hr := (M.interp σ).read_comp f.net g.net x a b
  have hj := (M.interp σ).joint_comp f.net g.net x a b
  have hw := M.reward_comp σ f g x a b
  simp only [Interpretation.combine] at hr hj hw
  rw [hr, hj, hw]
  split_ifs <;> ring

/-- **Functoriality under serial composition**: the interpretation of a composite is the
composite, in the expectation-semiring kernel category, of the interpretations. -/
theorem interpret_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.interpret σ (f.comp g) = (M.interpret σ f).comp (M.interpret σ g) := by
  ext1
  · exact (M.interp σ).kernel_comp f.net g.net
  · exact M.rewardTable_comp σ f g

theorem interpretHom_comp (f : IDNet X Y) (g : IDNet Y Z) :
    M.interpretHom σ (f.comp g) = M.interpretHom σ f ≫ M.interpretHom σ g :=
  Subtype.ext (M.interpret_comp σ f g)

/-- **Identities**: pure wiring with no utilities is interpreted as `(id, 0)`. -/
theorem interpret_identity (X : S.Iface) :
    M.interpret σ (IDNet.identity X) = RewardKernel.id ((M.interp σ).Boundary X) := by
  ext1
  · change (M.interp σ).kernel (Net.wire id (fun _ => rfl)) = Kernel.idK _
    rw [(M.interp σ).kernel_wire]
    apply Kernel.ofFun_congr
    intro x
    rfl
  · funext x y
    have hr : ∀ z, M.reward σ (IDNet.identity X) x z = 0 :=
      fun z => Finset.sum_eq_zero (fun u _ => (u : Empty).elim)
    change M.rewardTable σ (IDNet.identity X) x y = 0
    unfold rewardTable
    simp [hr]

theorem interpretHom_identity (X : S.Iface) :
    M.interpretHom σ (IDNet.identity X) = 𝟙 (M.space σ X) :=
  Subtype.ext (M.interpret_identity σ X)

/-! ### Functoriality under tensor -/

/-- The canonical bijection between pairs of boundary assignments and assignments of the
disjoint-union interface. -/
def join (X X' : S.Iface) :
    (M.interp σ).Boundary X × (M.interp σ).Boundary X' ≃ (M.interp σ).Boundary (X.sum X') :=
  (Interpretation.Assignment.sumEquiv (M.interp σ) X.type X'.type).symm

@[simp] theorem join_apply (X X' : S.Iface) (p : (M.interp σ).Boundary X ×
    (M.interp σ).Boundary X') :
    M.join σ X X' p = Interpretation.Assignment.join _ p.1 p.2 := rfl

theorem rewardTable_tensor (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (y : (M.interp σ).Boundary Y)
    (y' : (M.interp σ).Boundary Y') :
    M.rewardTable σ (f.tensor g) (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      M.rewardTable σ f x y * (M.interp σ).kernel g.net x' y' +
        (M.interp σ).kernel f.net x y * M.rewardTable σ g x' y' := by
  simp only [kernel_eq_sum]
  unfold rewardTable
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  change (∑ z : (M.interp σ).Internal (f.net.tensor g.net),
      if Interpretation.Assignment.join _ y y' =
          (M.interp σ).read (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z then
        (M.interp σ).joint (f.net.tensor g.net) (Interpretation.Assignment.join _ x x') z *
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
  have hw := M.reward_tensor σ f g x x' a b
  simp only [Interpretation.combine] at hr hj hw
  rw [hr, hj, hw]
  by_cases h₁ : y = (M.interp σ).read f.net x a <;>
    by_cases h₂ : y' = (M.interp σ).read g.net x' b <;>
      simp [Interpretation.Assignment.join_injective, h₁, h₂]
  ring

theorem kernel_tensor_join (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (y : (M.interp σ).Boundary Y)
    (y' : (M.interp σ).Boundary Y') :
    (M.interp σ).kernel (f.tensor g).net (Interpretation.Assignment.join _ x x')
        (Interpretation.Assignment.join _ y y') =
      (M.interp σ).kernel f.net x y * (M.interp σ).kernel g.net x' y' :=
  (M.interp σ).kernel_tensor f.net g.net x x' y y'

/-- Read a reward kernel through maps on its input and output states. -/
def _root_.OpenInfluence.RewardKernel.reindex {A B C D : Type} (r : RewardKernel C D)
    (i : A → C) (o : B → D) : RewardKernel A B :=
  ⟨fun a b => r.K (i a) (o b), fun a b => r.W (i a) (o b)⟩

/-- **Functoriality under tensor**: read through the canonical bijections between
assignments of a disjoint-union interface and pairs of assignments, the interpretation of
a tensor is the tensor of the interpretations. -/
theorem interpret_tensor (f : IDNet X Y) (g : IDNet X' Y') :
    (M.interpret σ (f.tensor g)).reindex (M.join σ X X') (M.join σ Y Y') =
      (M.interpret σ f).tensor (M.interpret σ g) := by
  ext1
  · funext p q
    exact M.kernel_tensor_join σ f g p.1 p.2 q.1 q.2
  · funext p q
    exact M.rewardTable_tensor σ f g p.1 p.2 q.1 q.2

/-- **Functoriality under tensor**, as naturality of the canonical bijection (the shape of
`OpenNet.Interpretation.tensor_natural`). -/
theorem interpret_tensor_natural (f : IDNet X Y) (g : IDNet X' Y') :
    ((M.interpret σ f).tensor (M.interpret σ g)).comp (RewardKernel.ofFun (M.join σ Y Y')) =
      (RewardKernel.ofFun (M.join σ X X')).comp (M.interpret σ (f.tensor g)) := by
  rw [← M.interpret_tensor σ f g]
  ext1
  · simp only [RewardKernel.comp_K, RewardKernel.ofFun, RewardKernel.lift_K,
      Kernel.comp_ofEquiv_right, Kernel.comp_ofFun_left, RewardKernel.reindex]
    funext p q
    simp
  · simp only [RewardKernel.comp_W, RewardKernel.ofFun, RewardKernel.lift_K,
      RewardKernel.lift_W, KernelAlgebra.kcomp_zero_left, KernelAlgebra.kcomp_zero_right,
      add_zero, zero_add, Kernel.comp_ofEquiv_right, Kernel.comp_ofFun_left,
      RewardKernel.reindex]
    funext p q
    simp

/-! ### The contextual identity for interpreted diagrams -/

/-- **Contextual identity** for open influence diagrams under a fixed strategy: for every
boundary prior `μ` and terminal continuation `c`,
`EU_{f;g}(μ, c) = EU_f(μ, c_g) = L_f + EU_g(ν_f, c)`, where `c_g` is the suffix's value
function, `ν_f` the boundary law induced by the prefix and `L_f` the prefix's reward. -/
theorem contextual_identity (f : IDNet X Y) (g : IDNet Y Z)
    (μ : (M.interp σ).Boundary X → ℝ) (c : (M.interp σ).Boundary Z → ℝ) :
    (M.interpret σ (f.comp g)).eu μ c =
        (M.interpret σ f).eu μ ((M.interpret σ g).continuation c) ∧
      (M.interpret σ f).eu μ ((M.interpret σ g).continuation c) =
        (M.interpret σ f).prefixReward μ +
          (M.interpret σ g).eu ((M.interpret σ f).pushforward μ) c := by
  rw [M.interpret_comp σ f g]
  exact RewardKernel.contextual_identity _ _ (M.interpret_stochastic σ g).2 μ c

end IDInterpretation

end OpenInfluence
