import CategoricalInfluenceDiagramsProofs.SyntaxMonoidal

/-!
# SA-Pass shadow module: diagrams up to isomorphism are symmetric monoidal

Claim `cid.syntax-monoidal`, from `IDCat.symmetric` and `IDInterpretation.braidedFunctor`.
The shadows spell the tensor of the category as the tensor of diagrams on classes, and the
semantics as a braided monoidal structure on the semantic functor.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.SyntaxMonoidal

open CategoryTheory MonoidalCategory OpenInfluence OpenInfluence.IDInterpretation

/-- A diagram as a morphism between objects of `IDCat`. -/
abbrev hom {S : IDSignature} (A B : IDCat S) (f : IDNet A.iface B.iface) : A ⟶ B := IDHom.mk f

/-- The instances, restated. -/
abbrev Candidate : Prop :=
  (∀ S : IDSignature, Nonempty (SymmetricCategory (IDCat S))) ∧
    (∀ (S : IDSignature) (A B A' B' : IDCat S) (f : IDNet A.iface B.iface)
      (g : IDNet A'.iface B'.iface),
      (hom A B f ⊗ₘ hom A' B' g) = hom (A ⊗ A') (B ⊗ B') (f.tensor g)) ∧
    ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour),
      Nonempty (M.interpretFunctor β).Braided

/-- "Open influence diagrams up to isomorphism, with serial composition and the tensor, form
a symmetric monoidal category". -/
abbrev Shadow1 : Prop :=
  (∀ S : IDSignature, Nonempty (SymmetricCategory (IDCat S))) ∧
    ∀ (S : IDSignature) (A B A' B' : IDCat S) (f : IDNet A.iface B.iface)
      (g : IDNet A'.iface B'.iface),
      MonoidalCategory.tensorHom (hom A B f) (hom A' B' g) =
        hom (MonoidalCategory.tensorObj A A') (MonoidalCategory.tensorObj B B') (f.tensor g)

/-- "for every behavioural strategy the semantics is a braided strong monoidal functor from
it to `FinRew`". -/
abbrev Shadow2 : Prop :=
  ∀ (S : IDSignature) (M : IDInterpretation S) (β : M.Behaviour),
    Nonempty (M.interpretFunctor β).Braided

theorem forward1 : Candidate → Shadow1 := fun h => ⟨h.1, h.2.1⟩

theorem forward2 : Candidate → Shadow2 := fun h => h.2.2

theorem backward : Shadow1 → Shadow2 → Candidate := fun h1 h2 => ⟨h1.1, h1.2, h2⟩

/-- SA-Pass anchor: the cited instances prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ => ⟨IDCat.symmetric⟩, fun _ _ _ _ _ _ _ => rfl,
    fun _ M β => ⟨M.braidedFunctor β⟩⟩

end CategoricalInfluenceDiagramsProofs.Shadows.SyntaxMonoidal
