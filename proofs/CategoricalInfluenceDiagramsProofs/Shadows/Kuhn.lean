import CategoricalInfluenceDiagramsProofs.Kuhn

/-!
# SA-Pass shadow module: Kuhn's theorem for open influence diagrams

Claim `cid.kuhn`, from `IDInterpretation.kuhn_eu` and `IDInterpretation.kuhn_conditional`.
The shadows spell distinct labels as injectivity of the label on decision generators, and the
deterministic strategy's semantics as `interpret σ f`, the interpretation of its point masses
by definition.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.Kuhn

open OpenInfluence OpenInfluence.IDInterpretation OpenInfluence.RewardKernel

/-- `kuhn_eu`, restated. -/
abbrev EUCandidate : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (X Y : S.Iface) (f : IDNet X Y),
    DistinctDecisions f → (∀ l, S.isDecision l = true → Nonempty (M.states (S.result l))) →
    ∀ (β : M.Behaviour) (μ : (M.interpB β).Boundary X → ℝ) (c : (M.interpB β).Boundary Y → ℝ),
      ∃ σ : M.Strategy, (M.interpretB β f).eu μ c ≤
        (M.interpretB (M.pointMass σ) f).eu (fun x => μ (M.recast x)) (fun y => c (M.recast y))

/-- `kuhn_conditional`, restated. -/
abbrev ConditionalCandidate : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (X Y : S.Iface) (f : IDNet X Y),
    DistinctDecisions f → (∀ l, S.isDecision l = true → Nonempty (M.states (S.result l))) →
    ∀ (β : M.Behaviour) (ev : M.Likelihood), (∀ l v, 0 ≤ ev l v) →
    ∀ (s : RewardKernel.State ((M.interpB β).Boundary X)), (∀ x, 0 ≤ s.ν x) →
      (∀ x, s.ν x = 0 → s.ρ x = 0) →
    ∀ (e : RewardKernel.Effect ((M.interpB β).Boundary Y)), (∀ y, 0 ≤ e.m y) →
      (∀ y, e.m y = 0 → e.c y = 0) →
    0 < mass s ((M.interpretBE β ev f).pull e) →
    ∃ σ : M.Strategy,
      0 < mass ⟨fun x => s.ν (M.recast x), fun x => s.ρ (M.recast x)⟩
        ((M.interpretBE (M.pointMass σ) ev f).pull
          ⟨fun y => e.m (M.recast y), fun y => e.c (M.recast y)⟩) ∧
      conditionalValue s ((M.interpretBE β ev f).pull e) ≤
        conditionalValue ⟨fun x => s.ν (M.recast x), fun x => s.ρ (M.recast x)⟩
          ((M.interpretBE (M.pointMass σ) ev f).pull
            ⟨fun y => e.m (M.recast y), fun y => e.c (M.recast y)⟩)

/-- The two theorems. -/
abbrev Candidate : Prop := EUCandidate ∧ ConditionalCandidate

/-- "When no two decision generators of an open influence diagram share a label ... for every
prior and continuation some deterministic strategy has at least its expected utility". -/
abbrev Shadow1 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (X Y : S.Iface) (f : IDNet X Y),
    (∀ a b, f.IsDecision a → f.net.label a = f.net.label b → a = b) →
    (∀ l, S.isDecision l = true → Nonempty (M.states (S.result l))) →
    ∀ (β : M.Behaviour) (μ : (M.interpB β).Boundary X → ℝ) (c : (M.interpB β).Boundary Y → ℝ),
      ∃ σ : M.Strategy, (M.interpretB β f).eu μ c ≤
        (M.interpret σ f).eu (fun x => μ (M.recast (β := M.pointMass σ) x))
          (fun y => c (M.recast (β := M.pointMass σ) y))

/-- "if the evidence has positive mass some deterministic strategy gives it positive mass and
at least the same conditional value". -/
abbrev Shadow2 : Prop := ConditionalCandidate

theorem forward1 : Candidate → Shadow1 := fun h S M X Y f hf hne β μ c =>
  h.1 S M X Y f hf hne β μ c

theorem forward2 : Candidate → Shadow2 := fun h => h.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun S M X Y f hf hne β μ c => h1 S M X Y f hf hne β μ c, h2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ M _ _ f hf hne β μ c => M.kuhn_eu f hf hne β μ c,
    fun _ M _ _ f hf hne β ev hev s hs hsρ e he hec hpos =>
      M.kuhn_conditional f hf hne β ev hev s hs hsρ e he hec hpos⟩

end CategoricalInfluenceDiagramsProofs.Shadows.Kuhn
