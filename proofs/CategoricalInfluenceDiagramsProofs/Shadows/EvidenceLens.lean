import CategoricalInfluenceDiagramsProofs.Evidence

/-!
# SA-Pass shadow module: the evidence lens

Claim `cid.evidence-lens`, from `RewardKernel.pull_comp`, `push_comp`, `pull_id`, `push_id`,
`mass_push` and `value_push`. The shadows spell an effect as a pair `(m, c)` and a state as a
pair `(ν, ρ)` of real functions, the backward action as `(K m, W m + K c)`, the forward
action as `(ν K, ρ K + ν W)`, the evidence mass as `Σ ν m` and the evidence-weighted value as
`Σ (ρ m + ν c)`, on arbitrary real tables: no normalisation hypothesis anywhere.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.EvidenceLens

open OpenInfluence FiniteKernelsProofs.Finite
open RewardKernel (Effect pull push mass value conditionalValue)

/-- The backward action on a pair `(m, c)`. -/
abbrev pullF {Y Z : Type} [Fintype Z] (K W : Kernel Y Z) (p : (Z → ℝ) × (Z → ℝ)) :
    (Y → ℝ) × (Y → ℝ) :=
  (fun y => ∑ z, K y z * p.1 z, fun y => ∑ z, (W y z * p.1 z + K y z * p.2 z))

/-- The forward action on a pair `(ν, ρ)`. -/
abbrev pushF {X Y : Type} [Fintype X] (K W : Kernel X Y) (p : (X → ℝ) × (X → ℝ)) :
    (Y → ℝ) × (Y → ℝ) :=
  (fun y => ∑ x, p.1 x * K x y, fun y => ∑ x, (p.2 x * K x y + p.1 x * W x y))

/-- The evidence mass of a state against an effect. -/
abbrev massF {X : Type} [Fintype X] (s e : (X → ℝ) × (X → ℝ)) : ℝ := ∑ x, s.1 x * e.1 x

/-- The evidence-weighted value of a state against an effect. -/
abbrev valueF {X : Type} [Fintype X] (s e : (X → ℝ) × (X → ℝ)) : ℝ :=
  ∑ x, (s.2 x * e.1 x + s.1 x * e.2 x)

/-- The six theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z) (e : Effect Z), (f.comp g).pull e = f.pull (g.pull e)) ∧
    (∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (f : RewardKernel X Y)
      (g : RewardKernel Y Z) (s : RewardKernel.State X), (f.comp g).push s = g.push (f.push s)) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] (e : Effect X), (RewardKernel.id X).pull e = e) ∧
    (∀ (X : Type) [Fintype X] [DecidableEq X] (s : RewardKernel.State X), (RewardKernel.id X).push s = s) ∧
    ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : RewardKernel X Y) (s : RewardKernel.State X)
      (e : Effect Y), mass (f.push s) e = mass s (f.pull e) ∧
        value (f.push s) e = value s (f.pull e)

/-- "the backward action ... on effects is functorial with no normalisation hypothesis". -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y)
    (Kg Wg : Kernel Y Z) (p : (Z → ℝ) × (Z → ℝ)),
    pullF (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) p =
      pullF Kf Wf (pullF Kg Wg p)

/-- "the forward action on states" likewise, in the order of composition. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] (Kf Wf : Kernel X Y)
    (Kg Wg : Kernel Y Z) (p : (X → ℝ) × (X → ℝ)),
    pushF (Kernel.comp Kf Kg) (Kernel.comp Wf Kg + Kernel.comp Kf Wg) p =
      pushF Kg Wg (pushF Kf Wf p)

/-- Functorial includes the identity `(id, 0)`, on both sides. -/
abbrev Shadow3 : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : (X → ℝ) × (X → ℝ)),
    pullF (Kernel.idK X) 0 p = p ∧ pushF (Kernel.idK X) 0 p = p

/-- "the evidence mass and the evidence-weighted value of a state against an effect are the
same on either side of a reward kernel". -/
abbrev Shadow4 : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (K W : Kernel X Y) (s : (X → ℝ) × (X → ℝ))
    (e : (Y → ℝ) × (Y → ℝ)),
    massF (pushF K W s) e = massF s (pullF K W e) ∧
      valueF (pushF K W s) e = valueF s (pullF K W e)

theorem forward1 : Candidate → Shadow1 := fun h X Y Z _ _ _ Kf Wf Kg Wg p =>
  congrArg (fun e : Effect X => (e.m, e.c)) (h.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ ⟨p.1, p.2⟩)

theorem forward2 : Candidate → Shadow2 := fun h X Y Z _ _ _ Kf Wf Kg Wg p =>
  congrArg (fun s : RewardKernel.State Z => (s.ν, s.ρ)) (h.2.1 X Y Z ⟨Kf, Wf⟩ ⟨Kg, Wg⟩ ⟨p.1, p.2⟩)

theorem forward3 : Candidate → Shadow3 := fun h X _ _ p =>
  ⟨congrArg (fun e : Effect X => (e.m, e.c)) (h.2.2.1 X ⟨p.1, p.2⟩),
    congrArg (fun s : RewardKernel.State X => (s.ν, s.ρ)) (h.2.2.2.1 X ⟨p.1, p.2⟩)⟩

theorem forward4 : Candidate → Shadow4 := fun h X Y _ _ K W s e =>
  h.2.2.2.2 X Y ⟨K, W⟩ ⟨s.1, s.2⟩ ⟨e.1, e.2⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Candidate := by
  intro h1 h2 h3 h4
  refine ⟨fun X Y Z _ _ _ f g e => ?_, fun X Y Z _ _ _ f g s => ?_, fun X _ _ e => ?_,
    fun X _ _ s => ?_, fun X Y _ _ f s e => h4 X Y f.K f.W (s.ν, s.ρ) (e.m, e.c)⟩
  · have h := h1 X Y Z f.K f.W g.K g.W (e.m, e.c)
    exact RewardKernel.Effect.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have h := h2 X Y Z f.K f.W g.K g.W (s.ν, s.ρ)
    exact RewardKernel.State.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have h := (h3 X (e.m, e.c)).1
    exact RewardKernel.Effect.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have h := (h3 X (s.ν, s.ρ)).2
    exact RewardKernel.State.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ f g e => RewardKernel.pull_comp f g e, fun _ _ _ _ _ _ f g s => RewardKernel.push_comp f g s,
    fun _ _ _ e => RewardKernel.pull_id e, fun _ _ _ s => RewardKernel.push_id s,
    fun _ _ _ _ f s e => ⟨RewardKernel.mass_push f s e, RewardKernel.value_push f s e⟩⟩

end CategoricalInfluenceDiagramsProofs.Shadows.EvidenceLens
