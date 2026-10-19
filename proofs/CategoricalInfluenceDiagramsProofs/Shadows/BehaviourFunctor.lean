import CategoricalInfluenceDiagramsProofs.Behaviour

/-!
# SA-Pass shadow module: behavioural strategies compose

Claim `cid.behaviour-functor`, from `IDInterpretation.interpretB_comp`, `interpretB_identity`,
`interpretB_tensor` and `interpretB_pointMass`. The shadows spell composition as
`(K₁K₂, W₁K₂ + K₁W₂)`, the identity as `(id, 0)`, the tensor cellwise on paired assignments,
and the point masses of a deterministic strategy through the deterministic kernel and reward
table, so they pin each part of the sentence.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.BehaviourFunctor

open OpenInfluence FiniteKernelsProofs.Finite

/-- The four theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y Z : S.Iface)
      (f : IDNet X Y) (g : IDNet Y Z),
      M.interpretB β (f.comp g) = (M.interpretB β f).comp (M.interpretB β g)) ∧
    (∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X : S.Iface),
      M.interpretB β (IDNet.identity X) = RewardKernel.id ((M.interpB β).Boundary X)) ∧
    (∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y X' Y' : S.Iface)
      (f : IDNet X Y) (g : IDNet X' Y'),
      (M.interpretB β (f.tensor g)).reindex (M.joinB β X X') (M.joinB β Y Y') =
        (M.interpretB β f).tensor (M.interpretB β g)) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
      (f : IDNet X Y), M.interpretB (M.pointMass σ) f = M.interpret σ f

/-- "sends serial composition to composition of reward kernels". -/
abbrev Shadow1 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y Z : S.Iface)
    (f : IDNet X Y) (g : IDNet Y Z),
    (M.interpretB β (f.comp g)).K =
        Kernel.comp (M.interpretB β f).K (M.interpretB β g).K ∧
      (M.interpretB β (f.comp g)).W =
        Kernel.comp (M.interpretB β f).W (M.interpretB β g).K +
          Kernel.comp (M.interpretB β f).K (M.interpretB β g).W

/-- "identities to `(id, 0)`". -/
abbrev Shadow2 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X : S.Iface),
    (M.interpretB β (IDNet.identity X)).K = Kernel.idK _ ∧
      (M.interpretB β (IDNet.identity X)).W = 0

/-- "and tensor to the tensor of reward kernels", cellwise on paired assignments. -/
abbrev Shadow3 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y X' Y' : S.Iface)
    (f : IDNet X Y) (g : IDNet X' Y') x x' y y',
    (M.interpretB β (f.tensor g)).K (M.joinB β X X' (x, x')) (M.joinB β Y Y' (y, y')) =
        (M.interpretB β f).K x y * (M.interpretB β g).K x' y' ∧
      (M.interpretB β (f.tensor g)).W (M.joinB β X X' (x, x')) (M.joinB β Y Y' (y, y')) =
        (M.interpretB β f).W x y * (M.interpretB β g).K x' y' +
          (M.interpretB β f).K x y * (M.interpretB β g).W x' y'

/-- "a deterministic strategy has the interpretation of its point masses": the kernel and
the reward table of the deterministic semantics. -/
abbrev Shadow4 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
    (f : IDNet X Y),
    (M.interpretB (M.pointMass σ) f).K = (M.interp σ).kernel f.net ∧
      (M.interpretB (M.pointMass σ) f).W = M.rewardTable σ f

theorem forward1 : Candidate → Shadow1 := fun h S M β X Y Z f g =>
  ⟨congrArg RewardKernel.K (h.1 S M β X Y Z f g), congrArg RewardKernel.W (h.1 S M β X Y Z f g)⟩

theorem forward2 : Candidate → Shadow2 := fun h S M β X =>
  ⟨congrArg RewardKernel.K (h.2.1 S M β X), congrArg RewardKernel.W (h.2.1 S M β X)⟩

theorem forward3 : Candidate → Shadow3 := fun h S M β X Y X' Y' f g x x' y y' =>
  ⟨congrFun (congrFun (congrArg RewardKernel.K (h.2.2.1 S M β X Y X' Y' f g)) (x, x')) (y, y'),
    congrFun (congrFun (congrArg RewardKernel.W (h.2.2.1 S M β X Y X' Y' f g)) (x, x'))
      (y, y')⟩

theorem forward4 : Candidate → Shadow4 := fun h S M σ X Y f =>
  ⟨congrArg RewardKernel.K (h.2.2.2 S M σ X Y f), congrArg RewardKernel.W (h.2.2.2 S M σ X Y f)⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := fun h1 h2 h3 h4 =>
  ⟨fun S M β X Y Z f g => RewardKernel.ext (h1 S M β X Y Z f g).1 (h1 S M β X Y Z f g).2,
    fun S M β X => RewardKernel.ext (h2 S M β X).1 (h2 S M β X).2,
    fun S M β X Y X' Y' f g => RewardKernel.ext
      (funext fun p => funext fun q => (h3 S M β X Y X' Y' f g p.1 p.2 q.1 q.2).1)
      (funext fun p => funext fun q => (h3 S M β X Y X' Y' f g p.1 p.2 q.1 q.2).2),
    fun S M σ X Y f => RewardKernel.ext (h4 S M σ X Y f).1 (h4 S M σ X Y f).2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ M β _ _ _ f g => M.interpretB_comp β f g, fun _ M β X => M.interpretB_identity β X,
    fun _ M β _ _ _ _ f g => M.interpretB_tensor β f g,
    fun _ M σ _ _ f => M.interpretB_pointMass σ f⟩

end CategoricalInfluenceDiagramsProofs.Shadows.BehaviourFunctor
