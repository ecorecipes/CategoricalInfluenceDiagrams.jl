import CategoricalInfluenceDiagramsProofs.SyntaxCategory

/-!
# SA-Pass shadow module: the semantics is a functor on diagrams up to isomorphism

Claim `cid.syntax-functor`, from `IDInterpretation.interpretB_iso`,
`IDInterpretation.interpret_iso` and `IDInterpretation.interpretFunctor`. The shadows spell
isomorphism as a nonempty type of `IDNet.Iso`, and the functor as a Mathlib functor out of
`IDCat` whose action on the class of a diagram is its semantics.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SyntaxFunctor

open CategoryTheory OpenInfluence OpenInfluence.IDInterpretation

/-- The invariance theorems and the functor, restated. -/
abbrev Candidate : Prop :=
  (∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y : S.Iface)
      (f g : IDNet X Y), f.Iso g → M.interpretB β f = M.interpretB β g) ∧
    (∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
      (f g : IDNet X Y), f.Iso g → M.interpret σ f = M.interpret σ g) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (A B : IDCat S)
      (f : IDNet A.iface B.iface),
      ((M.interpretFunctor β).map (IDHom.mk f : A ⟶ B)).val = M.interpretB β f

/-- "Isomorphic open influence diagrams have the same semantics under every behavioural
strategy, and so under every deterministic one". -/
abbrev Shadow1 : Prop :=
  (∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (X Y : S.Iface)
      (f g : IDNet X Y), Nonempty (f.Iso g) → M.interpretB β f = M.interpretB β g) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (σ : M.Strategy) (X Y : S.Iface)
      (f g : IDNet X Y), Nonempty (f.Iso g) → M.interpret σ f = M.interpret σ g

/-- "the semantics is a functor to `FinRew` from the category of typed interfaces and open
influence diagrams up to isomorphism under serial composition": the functor's action on the
class of a diagram is its semantics, and it preserves composition. -/
abbrev Shadow2 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour) (A B C : IDCat S)
    (f : IDNet A.iface B.iface) (g : IDNet B.iface C.iface),
    ((M.interpretFunctor β).map (IDHom.mk f : A ⟶ B)).val = M.interpretB β f ∧
      (M.interpretFunctor β).map ((IDHom.mk f : A ⟶ B) ≫ (IDHom.mk g : B ⟶ C)) =
        (M.interpretFunctor β).map (IDHom.mk f : A ⟶ B) ≫
          (M.interpretFunctor β).map (IDHom.mk g : B ⟶ C)

theorem forward1 : Candidate → Shadow1 := fun h =>
  ⟨fun S M β X Y f g ⟨a⟩ => h.1 S M β X Y f g a, fun S M σ X Y f g ⟨a⟩ => h.2.1 S M σ X Y f g a⟩

theorem forward2 : Candidate → Shadow2 := fun h S M β A B _ f _ =>
  ⟨h.2.2 S M β A B f, Functor.map_comp _ _ _⟩

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 =>
  ⟨fun S M β X Y f g a => h1.1 S M β X Y f g ⟨a⟩,
    fun S M σ X Y f g a => h1.2 S M σ X Y f g ⟨a⟩,
    fun S M β A B f => (h2 S M β A B B f (IDNet.identity B.iface)).1⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ M β _ _ _ _ a => M.interpretB_iso β a, fun _ M σ _ _ _ _ a => M.interpret_iso σ a,
    fun _ M β _ _ f => M.interpretFunctor_map β f⟩

end CategoricalInfluenceDiagramsProofs.Shadows.SyntaxFunctor
