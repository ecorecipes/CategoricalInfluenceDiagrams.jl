import CategoricalInfluenceDiagramsProofs.Interpretation

/-!
# SA-Pass shadow module: functoriality of the fixed-strategy interpretation

Claim `cid.functoriality`, from `IDInterpretation.interpret_comp`,
`IDInterpretation.interpret_identity` and `IDInterpretation.interpret_tensor`. The
candidate quantifies over every influence-diagram signature, interpretation, strategy and
pair of open influence diagrams. The shadows spell out composition, identity and tensor of
reward kernels on the two tables, so they pin the prose's "composition of reward kernels",
"`(id, 0)`" and "tensor of reward kernels" to the formulas of ADR 0018.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.Functoriality

open OpenInfluence OpenInfluence.IDInterpretation FiniteKernelsProofs.Finite

/-- The three functoriality theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y Z : S.Iface)
      (f : IDNet X Y) (g : IDNet Y Z),
      M.interpret σ (f.comp g) = (M.interpret σ f).comp (M.interpret σ g)) ∧
    (∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X : S.Iface),
      M.interpret σ (IDNet.identity X) = RewardKernel.id _) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y X' Y' : S.Iface)
      (f : IDNet X Y) (g : IDNet X' Y'),
      (M.interpret σ (f.tensor g)).reindex (M.join σ X X') (M.join σ Y Y') =
        (M.interpret σ f).tensor (M.interpret σ g)

/-- "sends serial composition to composition of reward kernels":
`(K, W)` of `f ; g` is `(K_f K_g, W_f K_g + K_f W_g)`. -/
abbrev Shadow1 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y Z : S.Iface)
    (f : IDNet X Y) (g : IDNet Y Z),
    (M.interpret σ (f.comp g)).K = Kernel.comp (M.interpret σ f).K (M.interpret σ g).K ∧
      (M.interpret σ (f.comp g)).W =
        Kernel.comp (M.interpret σ f).W (M.interpret σ g).K +
          Kernel.comp (M.interpret σ f).K (M.interpret σ g).W

/-- "identities to `(id, 0)`". -/
abbrev Shadow2 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X : S.Iface),
    (M.interpret σ (IDNet.identity X)).K = Kernel.idK _ ∧
      (M.interpret σ (IDNet.identity X)).W = 0

/-- "tensor to the tensor of reward kernels": on assignments of the two sides of a
disjoint-union interface, `(K, W)` of `f ⊗ g` is `(K_f K_g, W_f K_g + K_f W_g)` pointwise. -/
abbrev Shadow3 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y X' Y' : S.Iface)
    (f : IDNet X Y) (g : IDNet X' Y') (x : (M.interp σ).Boundary X)
    (x' : (M.interp σ).Boundary X') (y : (M.interp σ).Boundary Y)
    (y' : (M.interp σ).Boundary Y'),
    (M.interpret σ (f.tensor g)).K (OpenNet.Interpretation.Assignment.join _ x x')
        (OpenNet.Interpretation.Assignment.join _ y y') =
      (M.interpret σ f).K x y * (M.interpret σ g).K x' y' ∧
    (M.interpret σ (f.tensor g)).W (OpenNet.Interpretation.Assignment.join _ x x')
        (OpenNet.Interpretation.Assignment.join _ y y') =
      (M.interpret σ f).W x y * (M.interpret σ g).K x' y' +
        (M.interpret σ f).K x y * (M.interpret σ g).W x' y'

theorem forward1 : Candidate → Shadow1 := fun h S M σ X Y Z f g =>
  ⟨congrArg RewardKernel.K (h.1 S M σ X Y Z f g), congrArg RewardKernel.W (h.1 S M σ X Y Z f g)⟩

theorem forward2 : Candidate → Shadow2 := fun h S M σ X =>
  ⟨congrArg RewardKernel.K (h.2.1 S M σ X), congrArg RewardKernel.W (h.2.1 S M σ X)⟩

theorem forward3 : Candidate → Shadow3 := fun h S M σ X Y X' Y' f g x x' y y' =>
  ⟨congrFun (congrFun (congrArg RewardKernel.K (h.2.2 S M σ X Y X' Y' f g)) (x, x')) (y, y'),
    congrFun (congrFun (congrArg RewardKernel.W (h.2.2 S M σ X Y X' Y' f g)) (x, x')) (y, y')⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun S M σ X Y Z f g => RewardKernel.ext (h1 S M σ X Y Z f g).1 (h1 S M σ X Y Z f g).2,
    fun S M σ X => RewardKernel.ext (h2 S M σ X).1 (h2 S M σ X).2,
    fun S M σ X Y X' Y' f g => RewardKernel.ext
      (funext fun p => funext fun q => (h3 S M σ X Y X' Y' f g p.1 p.2 q.1 q.2).1)
      (funext fun p => funext fun q => (h3 S M σ X Y X' Y' f g p.1 p.2 q.1 q.2).2)⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ M σ _ _ _ f g => M.interpret_comp σ f g, fun _ M σ X => M.interpret_identity σ X,
    fun _ M σ _ _ _ _ f g => M.interpret_tensor σ f g⟩

end CategoricalInfluenceDiagramsProofs.Shadows.Functoriality
