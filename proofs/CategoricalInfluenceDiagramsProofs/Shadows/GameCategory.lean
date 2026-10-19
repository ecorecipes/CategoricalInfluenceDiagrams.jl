import CategoricalInfluenceDiagramsProofs.Lens

/-!
# SA-Pass shadow module: serial composition of games is a category on equilibria

Claim `cid.game-category`, from `Game.seq_seq_eq_iff`, `Game.seq_assoc_eq`,
`Game.idGame_seq_eq` and `Game.seq_idGame_eq`. The shadows spell out "the context that the
lenses of the other two transport to it" with the boundary law `ν` and value function `cont`
written as sums over the plays' tables, for each bracketing separately; the backward checker
recovers associativity from the two.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.GameCategory

open OpenInfluence FiniteKernelsProofs.Finite

/-- The boundary law `ν y = Σ_x μ x K x y`. -/
abbrev nu {X Y : Type} [Fintype X] (K : Kernel X Y) (μ : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, μ x * K x y

/-- The value function `c' x = Σ_y (W x y + K x y c y)`. -/
abbrev cont {X Y : Type} [Fintype Y] (K W : Kernel X Y) (c : Y → ℝ) : X → ℝ :=
  fun x => ∑ y, (W x y + K x y * c y)

/-- The flat condition on a strategy `(s, t, u)` of three games in series: each is an
equilibrium in the context transported to it by the others. -/
abbrev Flat {X Y Z V : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype V] (G : Game X Y)
    (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ) (s : G.Strat) (t : H.Strat)
    (u : J.Strat) : Prop :=
  G.Eq μ (cont (H.play t).K (H.play t).W (cont (J.play u).K (J.play u).W c)) s ∧
    H.Eq (nu (G.play s).K μ) (cont (J.play u).K (J.play u).W c) t ∧
    J.Eq (nu (H.play t).K (nu (G.play s).K μ)) c u

/-- The four cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (X Y Z V : Type) [Fintype X] [Fintype Y] [Fintype Z] [Fintype V] (G : Game X Y)
      (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ) (s : G.Strat) (t : H.Strat)
      (u : J.Strat),
      ((G.seq H).seq J).Eq μ c ((s, t), u) ↔
        G.Eq μ ((H.play t).continuation ((J.play u).continuation c)) s ∧
          H.Eq ((G.play s).pushforward μ) ((J.play u).continuation c) t ∧
          J.Eq ((H.play t).pushforward ((G.play s).pushforward μ)) c u) ∧
    (∀ (X Y Z V : Type) [Fintype X] [Fintype Y] [Fintype Z] [Fintype V] (G : Game X Y)
      (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ) (s : G.Strat) (t : H.Strat)
      (u : J.Strat),
      ((G.seq H).seq J).Eq μ c ((s, t), u) ↔ (G.seq (H.seq J)).Eq μ c (s, (t, u))) ∧
    (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] (G : Game X Y) (μ : X → ℝ)
      (c : Y → ℝ) (s : G.Strat), ((Game.idGame X).seq G).Eq μ c ((), s) ↔ G.Eq μ c s) ∧
    ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y] (G : Game X Y) (μ : X → ℝ)
      (c : Y → ℝ) (s : G.Strat), (G.seq (Game.idGame Y)).Eq μ c (s, ()) ↔ G.Eq μ c s

/-- "a strategy of three games in series is an equilibrium, under either bracketing, exactly
when each game's strategy is an equilibrium in the context that the lenses of the other two
transport to it": the left bracketing ... -/
abbrev Shadow1 : Prop :=
  ∀ (X Y Z V : Type) [Fintype X] [Fintype Y] [Fintype Z] [Fintype V] (G : Game X Y)
    (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ) (s : G.Strat) (t : H.Strat)
    (u : J.Strat), ((G.seq H).seq J).Eq μ c ((s, t), u) ↔ Flat G H J μ c s t u

/-- ... and the right bracketing. -/
abbrev Shadow2 : Prop :=
  ∀ (X Y Z V : Type) [Fintype X] [Fintype Y] [Fintype Z] [Fintype V] (G : Game X Y)
    (H : Game Y Z) (J : Game Z V) (μ : X → ℝ) (c : V → ℝ) (s : G.Strat) (t : H.Strat)
    (u : J.Strat), (G.seq (H.seq J)).Eq μ c (s, (t, u)) ↔ Flat G H J μ c s t u

/-- "unital": composing with the identity game on either side changes no equilibrium. -/
abbrev Shadow3 : Prop :=
  (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] (G : Game X Y) (μ : X → ℝ)
      (c : Y → ℝ) (s : G.Strat), ((Game.idGame X).seq G).Eq μ c ((), s) ↔ G.Eq μ c s) ∧
    ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y] (G : Game X Y) (μ : X → ℝ)
      (c : Y → ℝ) (s : G.Strat), (G.seq (Game.idGame Y)).Eq μ c (s, ()) ↔ G.Eq μ c s

theorem forward1 : Candidate → Shadow1 := fun h X Y Z V _ _ _ _ G H J μ c s t u =>
  h.1 X Y Z V G H J μ c s t u

theorem forward2 : Candidate → Shadow2 := fun h X Y Z V _ _ _ _ G H J μ c s t u =>
  (h.2.1 X Y Z V G H J μ c s t u).symm.trans (h.1 X Y Z V G H J μ c s t u)

theorem forward3 : Candidate → Shadow3 := fun h => ⟨h.2.2.1, h.2.2.2⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Candidate := fun h1 h2 h3 =>
  ⟨fun X Y Z V _ _ _ _ G H J μ c s t u => h1 X Y Z V G H J μ c s t u,
    fun X Y Z V _ _ _ _ G H J μ c s t u =>
      (h1 X Y Z V G H J μ c s t u).trans (h2 X Y Z V G H J μ c s t u).symm,
    h3.1, h3.2⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ _ _ _ _ _ _ G H J μ c s t u => Game.seq_seq_eq_iff G H J μ c s t u,
    fun _ _ _ _ _ _ _ _ G H J μ c s t u => Game.seq_assoc_eq G H J μ c s t u,
    fun _ _ _ _ _ G μ c s => Game.idGame_seq_eq G μ c s,
    fun _ _ _ _ _ G μ c s => Game.seq_idGame_eq G μ c s⟩

end CategoricalInfluenceDiagramsProofs.Shadows.GameCategory
