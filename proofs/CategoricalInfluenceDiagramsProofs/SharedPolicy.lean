import CategoricalInfluenceDiagramsProofs.Behaviour
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Shared policies: the first-order condition at an optimum (ADR 0024)

When several decisions share one policy (the absent-minded driver of `Behaviour`), the
optimum can be randomised, and the equilibria of ADR 0020, in which each component best
responds on its own, are the wrong notion: at the optimum of the absent-minded driver the
first junction alone would gain by continuing for sure (`AbsentMinded.per_use_gains`).
What holds instead is the first-order condition of Piccione and Rubinstein's multi-self
consistency, as made precise by Aumann, Hart and Perry: change the shared policy towards
another one, and the sum, over the uses of the policy, of the gain from changing that use
alone (each in the context the others induce) is at most zero.

**Paths of reward kernels.** A path `F : ℝ → RewardKernel X Y` has first-order term `D` at
`0` (`HasDeriv F D`) when every cell of `K` and `W` is differentiable at `0` with that
derivative. A segment `t ↦ (1 - t) A + t B` has first-order term `B - A`
(`hasDeriv_segment`), a constant path `0`, and serial composition obeys the product rule
(`HasDeriv.comp`: `(F ; G)' = F' ; G(0) + F(0) ; G'`). So along a chain in which each use of
a policy moves along a segment, the first-order term is the sum, over the uses, of the chain
with that use alone replaced by its direction, which is the sum of the uses' unilateral
gains (`eu_lin`, `lin_comp`, `comp_lin`).

**The first-order condition.** If the expected utility along a path is largest at `t = 0`,
its first-order term has nonpositive expected utility (`first_order_optimum`). For two uses
of a policy, separated by any fixed kernels, this reads: at an optimum of the shared policy,
the two unilateral gains of a change sum to at most zero (`shared_optimum_first_order`).

**The absent-minded driver.** At the optimum, continuing with probability `2/3` at both
junctions, continuing for sure at the first junction alone gains `2/3` and at the second
alone loses `2/3` (`per_use_gains`): the per-use gains sum to zero, as the first-order
condition requires, while the first is positive, so the strategy is not an equilibrium in the
per-component sense of ADR 0020.
-/

set_option autoImplicit false

noncomputable section

namespace OpenInfluence

open FiniteKernelsProofs.Finite Filter Topology

namespace RewardKernel

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-! ### Linear combinations of reward kernels -/

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- The linear combination `a f + b g` of two pairs of tables (a mixture with two weights,
which need not be a stochastic kernel). -/
def lin (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y) : RewardKernel X Y :=
  mix (fun i : Bool => if i then a else b) (fun i => if i then f else g)

omit [Fintype X] [Fintype Y] [Fintype Z] in
@[simp] theorem lin_K (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y) (x : X)
    (y : Y) : (lin a f b g).K x y = a * f.K x y + b * g.K x y := by
  simp [lin, mix]

omit [Fintype X] [Fintype Y] [Fintype Z] in
@[simp] theorem lin_W (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y) (x : X)
    (y : Y) : (lin a f b g).W x y = a * f.W x y + b * g.W x y := by
  simp [lin, mix]

omit [Fintype X] [Fintype Z] in
theorem lin_comp (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y)
    (h : RewardKernel Y Z) : (lin a f b g).comp h = lin a (f.comp h) b (g.comp h) := by
  rw [lin, mix_comp, lin]
  congr 1
  funext i
  cases i <;> rfl

omit [Fintype Z] in
theorem comp_lin (f : RewardKernel X Y) (a : ℝ) (g : RewardKernel Y Z) (b : ℝ)
    (h : RewardKernel Y Z) : f.comp (lin a g b h) = lin a (f.comp g) b (f.comp h) := by
  rw [lin, comp_mix, lin]
  congr 1
  funext i
  cases i <;> rfl

omit [Fintype Z] in
theorem eu_lin (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y) (μ : X → ℝ)
    (c : Y → ℝ) : (lin a f b g).eu μ c = a * f.eu μ c + b * g.eu μ c := by
  rw [lin, eu_mix, Fintype.sum_bool]
  simp

/-! ### Paths and their first-order terms -/

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- The path `F` has first-order term `D` at `0`: every cell of `K` and of `W` is
differentiable at `0`, with the corresponding cell of `D` as derivative. -/
def HasDeriv (F : ℝ → RewardKernel X Y) (D : RewardKernel X Y) : Prop :=
  ∀ x y, HasDerivAt (fun t => (F t).K x y) (D.K x y) 0 ∧
    HasDerivAt (fun t => (F t).W x y) (D.W x y) 0

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- The segment from `A` (at `t = 0`) to `B` (at `t = 1`). -/
def segment (A B : RewardKernel X Y) (t : ℝ) : RewardKernel X Y := lin (1 - t) A t B

omit [Fintype X] [Fintype Y] [Fintype Z] in
@[simp] theorem segment_zero (A B : RewardKernel X Y) : segment A B 0 = A := by
  ext x y <;> simp [segment]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- A segment has first-order term `B - A`. -/
theorem hasDeriv_segment (A B : RewardKernel X Y) : HasDeriv (segment A B) (lin (-1) A 1 B) := by
  intro x y
  constructor
  · have h := ((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const (A.K x y) |>.add
      ((hasDerivAt_id (0 : ℝ)).mul_const (B.K x y))
    simp only [segment, lin_K, lin_K]
    convert h using 1
  · have h := ((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const (A.W x y) |>.add
      ((hasDerivAt_id (0 : ℝ)).mul_const (B.W x y))
    simp only [segment, lin_W, lin_W]
    convert h using 1

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- A constant path has first-order term `0`. -/
theorem hasDeriv_const (A : RewardKernel X Y) : HasDeriv (fun _ => A) (lin 0 A 0 A) := by
  intro x y
  constructor
  · simpa using hasDerivAt_const (0 : ℝ) (A.K x y)
  · simpa using hasDerivAt_const (0 : ℝ) (A.W x y)

omit [Fintype X] [Fintype Z] in
/-- **The product rule for serial composition**: `(F ; G)' = F' ; G(0) + F(0) ; G'`. -/
theorem HasDeriv.comp {F : ℝ → RewardKernel X Y} {G : ℝ → RewardKernel Y Z}
    {DF : RewardKernel X Y} {DG : RewardKernel Y Z} (hF : HasDeriv F DF) (hG : HasDeriv G DG) :
    HasDeriv (fun t => (F t).comp (G t)) (lin 1 (DF.comp (G 0)) 1 ((F 0).comp DG)) := by
  intro x z
  constructor
  · have h := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => (hF x y).1.mul (hG y z).1)
    simp only [comp_K, Kernel.comp_apply, lin_K, one_mul]
    convert h using 1
    rw [← Finset.sum_add_distrib]
  · have h := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ =>
      ((hF x y).2.mul (hG y z).1).add ((hF x y).1.mul (hG y z).2))
    simp only [comp_W, Kernel.comp_apply, Pi.add_apply, lin_W, one_mul]
    convert h using 1
    · funext t
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [← Finset.sum_add_distrib]
    · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype Z] in
/-- The expected utility along a path has the expected utility of its first-order term as
derivative. -/
theorem HasDeriv.eu {F : ℝ → RewardKernel X Y} {D : RewardKernel X Y} (hF : HasDeriv F D)
    (μ : X → ℝ) (c : Y → ℝ) : HasDerivAt (fun t => (F t).eu μ c) (D.eu μ c) 0 := by
  unfold RewardKernel.eu
  exact HasDerivAt.fun_sum fun x _ => (HasDerivAt.fun_sum fun y _ =>
    (hF x y).2.add ((hF x y).1.mul_const (c y))).const_mul (μ x)

/-- **A derivative at a one-sided maximum is nonpositive**: if `g` is largest at `0` on
`(0, 1)`, its derivative at `0` is at most zero. -/
theorem deriv_nonpos_of_le {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hmax : ∀ t ∈ Set.Ioo (0 : ℝ) 1, g t ≤ g 0) : d ≤ 0 := by
  have hs := hg.tendsto_slope_zero_right
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have h1 : g (0 + t) - g 0 ≤ 0 := by rw [zero_add]; linarith [hmax t ht]
  exact smul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.1.le) h1

omit [Fintype Z] in
/-- **The first-order condition at an optimum**: if the expected utility along a path is
largest at `t = 0`, its first-order term has nonpositive expected utility. -/
theorem first_order_optimum {F : ℝ → RewardKernel X Y} {D : RewardKernel X Y}
    (hF : HasDeriv F D) (μ : X → ℝ) (c : Y → ℝ)
    (hmax : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (F t).eu μ c ≤ (F 0).eu μ c) : D.eu μ c ≤ 0 :=
  deriv_nonpos_of_le (hF.eu μ c) hmax

/-- **The per-use gains of a change of a shared policy sum to at most zero at an optimum.**
Two uses of one policy, the first moving from `A₀` towards `A₁` and the second from `B₀`
towards `B₁` (any fixed kernels before, between and after them can be composed into
these): if no point of the joint change does better than `A₀ ; B₀`, then the gain of the
first change alone plus the gain of the second change alone is at most zero. -/
theorem shared_optimum_first_order (A₀ A₁ : RewardKernel X Y) (B₀ B₁ : RewardKernel Y Z)
    (μ : X → ℝ) (c : Z → ℝ)
    (hopt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ((segment A₀ A₁ t).comp (segment B₀ B₁ t)).eu μ c ≤ (A₀.comp B₀).eu μ c) :
    ((A₁.comp B₀).eu μ c - (A₀.comp B₀).eu μ c) +
      ((A₀.comp B₁).eu μ c - (A₀.comp B₀).eu μ c) ≤ 0 := by
  have hd := (hasDeriv_segment A₀ A₁).comp (hasDeriv_segment B₀ B₁)
  have h := first_order_optimum hd μ c (by simpa using hopt)
  simp only [segment_zero, eu_lin, lin_comp, comp_lin] at h
  linarith

/-! ### Given evidence -/

omit [Fintype Z] in
/-- The evidence mass along a path has the mass of its first-order term as derivative. -/
theorem HasDeriv.mass {F : ℝ → RewardKernel X Y} {D : RewardKernel X Y} (hF : HasDeriv F D)
    (s : RewardKernel.State X) (e : RewardKernel.Effect Y) :
    HasDerivAt (fun t => RewardKernel.mass s ((F t).pull e)) (RewardKernel.mass s (D.pull e))
      0 := by
  simp only [RewardKernel.mass, RewardKernel.pull]
  exact HasDerivAt.fun_sum fun x _ =>
    (HasDerivAt.fun_sum fun y _ => (hF x y).1.mul_const (e.m y)).const_mul (s.ν x)

omit [Fintype Z] in
/-- The evidence-weighted value along a path has the value of its first-order term as
derivative. -/
theorem HasDeriv.value {F : ℝ → RewardKernel X Y} {D : RewardKernel X Y} (hF : HasDeriv F D)
    (s : RewardKernel.State X) (e : RewardKernel.Effect Y) :
    HasDerivAt (fun t => RewardKernel.value s ((F t).pull e))
      (RewardKernel.value s (D.pull e)) 0 := by
  simp only [RewardKernel.value, RewardKernel.pull]
  exact HasDerivAt.fun_sum fun x _ =>
    ((HasDerivAt.fun_sum fun y _ => (hF x y).1.mul_const (e.m y)).const_mul (s.ρ x)).add
      ((HasDerivAt.fun_sum fun y _ =>
        ((hF x y).2.mul_const (e.m y)).add ((hF x y).1.mul_const (e.c y))).const_mul (s.ν x))

omit [Fintype Z] in
/-- **The first-order condition for a conditional value.** If the evidence has positive mass
at `t = 0` and the conditional value along a path is largest there, the first-order term's
evidence-weighted value, less the conditional value times its mass, is at most zero: the
derivative of the ratio, times the mass. -/
theorem first_order_conditional {F : ℝ → RewardKernel X Y} {D : RewardKernel X Y}
    (hF : HasDeriv F D) (s : RewardKernel.State X) (e : RewardKernel.Effect Y)
    (hpos : 0 < RewardKernel.mass s ((F 0).pull e))
    (hmax : ∀ t ∈ Set.Ioo (0 : ℝ) 1, RewardKernel.conditionalValue s ((F t).pull e) ≤
      RewardKernel.conditionalValue s ((F 0).pull e)) :
    RewardKernel.value s (D.pull e) -
      RewardKernel.conditionalValue s ((F 0).pull e) * RewardKernel.mass s (D.pull e) ≤ 0 := by
  have hq := HasDerivAt.div (hF.value s e) (hF.mass s e) hpos.ne'
  have h := deriv_nonpos_of_le hq hmax
  have hD2 : 0 < RewardKernel.mass s ((F 0).pull e) ^ 2 := by positivity
  have h1 := (div_le_iff₀ hD2).1 h
  rw [zero_mul] at h1
  have e1 : RewardKernel.value s (D.pull e) -
      RewardKernel.conditionalValue s ((F 0).pull e) * RewardKernel.mass s (D.pull e) =
      (RewardKernel.value s (D.pull e) * RewardKernel.mass s ((F 0).pull e) -
        RewardKernel.value s ((F 0).pull e) * RewardKernel.mass s (D.pull e)) /
        RewardKernel.mass s ((F 0).pull e) := by
    unfold RewardKernel.conditionalValue
    field_simp
  rw [e1]
  exact div_nonpos_iff.2 (Or.inr ⟨h1, hpos.le⟩)

omit [Fintype Z] in
theorem mass_value_lin (a : ℝ) (f : RewardKernel X Y) (b : ℝ) (g : RewardKernel X Y)
    (s : RewardKernel.State X) (e : RewardKernel.Effect Y) :
    RewardKernel.mass s ((lin a f b g).pull e) =
        a * RewardKernel.mass s (f.pull e) + b * RewardKernel.mass s (g.pull e) ∧
      RewardKernel.value s ((lin a f b g).pull e) =
        a * RewardKernel.value s (f.pull e) + b * RewardKernel.value s (g.pull e) := by
  rw [lin, (mass_value_mix _ _ s e).1, (mass_value_mix _ _ s e).2, Fintype.sum_bool,
    Fintype.sum_bool]
  simp

/-- **Given evidence, the per-use first-order changes of a shared policy sum to at most zero
at an optimum of the conditional value.** With positive evidence mass at `A₀ ; B₀` and `V` its
conditional value, if no point of the joint change has a larger conditional value, then the
first-order changes of the conditional value from changing each use alone, `(N_u - V Z_u)`
divided by the mass, sum to at most zero; `N_u` and `Z_u` are the evidence-weighted value and
the evidence mass with that use changed. -/
theorem shared_optimum_first_order_conditional (A₀ A₁ : RewardKernel X Y)
    (B₀ B₁ : RewardKernel Y Z) (s : RewardKernel.State X) (e : RewardKernel.Effect Z)
    (hpos : 0 < RewardKernel.mass s ((A₀.comp B₀).pull e))
    (hopt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      RewardKernel.conditionalValue s (((segment A₀ A₁ t).comp (segment B₀ B₁ t)).pull e) ≤
        RewardKernel.conditionalValue s ((A₀.comp B₀).pull e)) :
    (RewardKernel.value s ((A₁.comp B₀).pull e) -
        RewardKernel.conditionalValue s ((A₀.comp B₀).pull e) *
          RewardKernel.mass s ((A₁.comp B₀).pull e)) /
        RewardKernel.mass s ((A₀.comp B₀).pull e) +
      (RewardKernel.value s ((A₀.comp B₁).pull e) -
        RewardKernel.conditionalValue s ((A₀.comp B₀).pull e) *
          RewardKernel.mass s ((A₀.comp B₁).pull e)) /
        RewardKernel.mass s ((A₀.comp B₀).pull e) ≤ 0 := by
  have hd := (hasDeriv_segment A₀ A₁).comp (hasDeriv_segment B₀ B₁)
  have h := first_order_conditional hd s e (by simpa using hpos) (by simpa using hopt)
  simp only [segment_zero, lin_comp, comp_lin] at h
  rw [(mass_value_lin _ _ _ _ s e).1, (mass_value_lin _ _ _ _ s e).2,
    (mass_value_lin _ _ _ _ s e).1, (mass_value_lin _ _ _ _ s e).1,
    (mass_value_lin _ _ _ _ s e).2, (mass_value_lin _ _ _ _ s e).2] at h
  have hv : RewardKernel.conditionalValue s ((A₀.comp B₀).pull e) *
      RewardKernel.mass s ((A₀.comp B₀).pull e) = RewardKernel.value s ((A₀.comp B₀).pull e) :=
    div_mul_cancel₀ _ hpos.ne'
  rw [← add_div]
  refine div_nonpos_iff.2 (Or.inr ⟨?_, hpos.le⟩)
  nlinarith [h, hv]

end RewardKernel

/-! ### The absent-minded driver -/

namespace AbsentMinded

open RewardKernel

/-- **At the shared optimum the per-use gains sum to zero, but are not each zero.** With
continuation probability `2/3` at both junctions, continuing for sure at the first junction
alone gains `2/3`, and at the second alone loses `2/3`. -/
theorem per_use_gains :
    ((first 1).comp (second (2 / 3))).eu (fun _ => 1) (fun _ => 0) -
        ((first (2 / 3)).comp (second (2 / 3))).eu (fun _ => 1) (fun _ => 0) = 2 / 3 ∧
      ((first (2 / 3)).comp (second 1)).eu (fun _ => 1) (fun _ => 0) -
        ((first (2 / 3)).comp (second (2 / 3))).eu (fun _ => 1) (fun _ => 0) = -(2 / 3) := by
  simp only [drive_eu]
  constructor <;> norm_num

end AbsentMinded

end OpenInfluence
