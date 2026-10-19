import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# SA-Pass shadow module: evidence composes

Claim `cid.evidence-functor`, from `IDInterpretation.interpretE_comp` and
`IDInterpretation.interpretE_one`. The shadows spell the composite of reward kernels as
`(K₁K₂, W₁K₂ + K₁W₂)` on the evidence-weighted tables, and "the likelihood one" as the
constant function, so they pin both what is composed and what is given back.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.EvidenceFunctor

open OpenInfluence FiniteKernelsProofs.Finite

/-- `interpretE_comp` and `interpretE_one`, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (ev : M.Likelihood)
      (X Y Z : S.Iface) (f : IDNet X Y) (g : IDNet Y Z),
      M.interpretE σ ev (f.comp g) = (M.interpretE σ ev f).comp (M.interpretE σ ev g)) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
      (f : IDNet X Y), M.interpretE σ (fun _ _ => 1) f = M.interpret σ f

/-- "sends serial composition to composition of reward kernels": the probability tables
compose as kernels ... -/
abbrev Shadow1 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (ev : M.Likelihood)
    (X Y Z : S.Iface) (f : IDNet X Y) (g : IDNet Y Z),
    M.kernelE σ ev (f.comp g) = Kernel.comp (M.kernelE σ ev f) (M.kernelE σ ev g)

/-- ... and the reward tables as `W₁K₂ + K₁W₂`. -/
abbrev Shadow2 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (ev : M.Likelihood)
    (X Y Z : S.Iface) (f : IDNet X Y) (g : IDNet Y Z),
    M.rewardTableE σ ev (f.comp g) =
      Kernel.comp (M.rewardTableE σ ev f) (M.kernelE σ ev g) +
        Kernel.comp (M.kernelE σ ev f) (M.rewardTableE σ ev g)

/-- "the likelihood one gives back the unweighted interpretation": both tables. -/
abbrev Shadow3 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
    (f : IDNet X Y),
    M.kernelE σ (fun _ _ => 1) f = (M.interp σ).kernel f.net ∧
      M.rewardTableE σ (fun _ _ => 1) f = M.rewardTable σ f

theorem forward1 : Candidate → Shadow1 := fun h S M σ ev X Y Z f g =>
  congrArg RewardKernel.K (h.1 S M σ ev X Y Z f g)

theorem forward2 : Candidate → Shadow2 := fun h S M σ ev X Y Z f g =>
  congrArg RewardKernel.W (h.1 S M σ ev X Y Z f g)

theorem forward3 : Candidate → Shadow3 := fun h S M σ X Y f =>
  ⟨congrArg RewardKernel.K (h.2 S M σ X Y f), congrArg RewardKernel.W (h.2 S M σ X Y f)⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun S M σ ev X Y Z f g =>
      RewardKernel.ext (h1 S M σ ev X Y Z f g) (h2 S M σ ev X Y Z f g),
    fun S M σ X Y f => RewardKernel.ext (h3 S M σ X Y f).1 (h3 S M σ X Y f).2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ M σ ev _ _ _ f g => M.interpretE_comp σ ev f g,
    fun _ M σ _ _ f => M.interpretE_one σ f⟩

end CategoricalInfluenceDiagramsProofs.Shadows.EvidenceFunctor
