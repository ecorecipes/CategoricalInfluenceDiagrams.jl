import CategoricalInfluenceDiagramsProofs.Certificate.Sound

/-!
# SA-Pass shadow module: soundness of the reward-certificate checker

Claim `cid.certificate-sound`, from `RewardCertificate.Certificate.check_sound`,
`diagram_informationLocal`, `boundaryIndex_bijective`, `reward_certificate_sound_K` and
`reward_certificate_sound_W`:
"If the reward-certificate checker accepts a decoded certificate at tolerance `τ`, its
network is valid, no decision of the decoded open influence diagram reads an input flagged
hidden, and for every pair of boundary assignments `(x, y)` the recorded `K` and `W` cells at
the flat index of `(x, y)`, which is a bijection onto the cells of `K`, are within `τ` of
`interpret σ f` at `(x, y)`, for the decoded diagram `f` and strategy `σ`."

"Accepts at tolerance `τ`" is `c.check τ = true`; "the decoded open influence diagram",
"`σ`" and "`interpret σ f`" are `diagramOf h`, `strategyOfCheck h` and `semantics h`. The
candidate quantifies over every certificate and tolerance. The shadows state "flagged hidden"
as a flag different from `hidden` (the theorem says the flag is `observed`), split the
bijection into injectivity, range and surjectivity, and split each cell bound into the
existence of the cell and the bound on it.
-/

set_option autoImplicit false

namespace CategoricalInfluenceDiagramsProofs.Shadows.CertificateSound

open OpenInfluence OpenInfluence.RewardCertificate OpenInfluence.RewardCertificate.Certificate
open InfluenceDiagramsProofs.DVECertificate (Value.toRat)

/-- Boundary assignments of the decoded diagram's inputs. -/
abbrev InB {c : Certificate} {τ : ℚ} (h : c.check τ = true) : Type :=
  ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.dom

/-- Boundary assignments of the decoded diagram's outputs. -/
abbrev OutB {c : Certificate} {τ : ℚ} (h : c.check τ = true) : Type :=
  ((modelOf h).interp (strategyOfCheck h)).Boundary c.network.cod

/-- The cited theorems, restated abstractly. -/
abbrev Candidate : Prop :=
  (∀ (c : Certificate) (τ : ℚ), c.check τ = true → c.network.Valid) ∧
  (∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (a : (diagramOf h).net.Gen),
    (diagramOf h).IsDecision a → ∀ p : c.network.dom.Port, Sum.inl p ∈ (diagramOf h).info a →
      c.observedDom.flag p = .observed) ∧
  (∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true),
    Function.Bijective (fun p : InB h × OutB h =>
      (⟨boundaryIndex h p.1 p.2, boundaryIndex_lt_K h p.1 p.2⟩ : Fin c.result.K.length))) ∧
  (∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (x : InB h) (y : OutB h),
    ∃ v, c.result.K[boundaryIndex h x y]? = some v ∧
      |(v.toRat : ℝ) - (semantics h).K x y| ≤ τ) ∧
  ∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (x : InB h) (y : OutB h),
    ∃ v, c.result.W[boundaryIndex h x y]? = some v ∧
      |(v.toRat : ℝ) - (semantics h).W x y| ≤ τ

/-- "its network is valid". -/
abbrev Shadow1 : Prop := ∀ (c : Certificate) (τ : ℚ), c.check τ = true → c.network.Valid

/-- "no decision of the decoded open influence diagram reads an input flagged hidden". -/
abbrev Shadow2 : Prop :=
  ∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (a : (diagramOf h).net.Gen),
    (diagramOf h).IsDecision a → ∀ p : c.network.dom.Port, Sum.inl p ∈ (diagramOf h).info a →
      c.observedDom.flag p ≠ .hidden

/-- "the flat index of `(x, y)`, which is a bijection onto the cells of `K`": it is below
the number of cells, distinct pairs have distinct indices, and every cell is reached. -/
abbrev Shadow3 : Prop :=
  ∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true),
    (∀ (x : InB h) (y : OutB h), boundaryIndex h x y < c.result.K.length) ∧
    (∀ (x x' : InB h) (y y' : OutB h), boundaryIndex h x y = boundaryIndex h x' y' →
      x = x' ∧ y = y') ∧
    ∀ k < c.result.K.length, ∃ (x : InB h) (y : OutB h), boundaryIndex h x y = k

/-- "the recorded `K` cell at the flat index of `(x, y)` is within `τ` of `interpret σ f`". -/
abbrev Shadow4 : Prop :=
  ∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (x : InB h) (y : OutB h),
    (∃ v, c.result.K[boundaryIndex h x y]? = some v) ∧
      ∀ v, c.result.K[boundaryIndex h x y]? = some v →
        |(v.toRat : ℝ) - (semantics h).K x y| ≤ τ

/-- "the recorded `W` cell at the flat index of `(x, y)` is within `τ` of `interpret σ f`". -/
abbrev Shadow5 : Prop :=
  ∀ (c : Certificate) (τ : ℚ) (h : c.check τ = true) (x : InB h) (y : OutB h),
    (∃ v, c.result.W[boundaryIndex h x y]? = some v) ∧
      ∀ v, c.result.W[boundaryIndex h x y]? = some v →
        |(v.toRat : ℝ) - (semantics h).W x y| ≤ τ

theorem forward1 : Candidate → Shadow1 := fun hc => hc.1

theorem forward2 : Candidate → Shadow2 := fun hc c τ h a ha p hp => by
  rw [hc.2.1 c τ h a ha p hp]
  exact Observability.noConfusion

theorem forward3 : Candidate → Shadow3 := fun hc c τ h =>
  ⟨fun x y => boundaryIndex_lt_K h x y,
    fun x x' y y' e => by
      have := (hc.2.2.1 c τ h).1 (a₁ := (x, y)) (a₂ := (x', y')) (Fin.ext e)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩,
    fun k hk => by
      obtain ⟨⟨x, y⟩, e⟩ := (hc.2.2.1 c τ h).2 ⟨k, hk⟩
      exact ⟨x, y, congrArg Fin.val e⟩⟩

theorem forward4 : Candidate → Shadow4 := fun hc c τ h x y => by
  obtain ⟨v, hv, hb⟩ := hc.2.2.2.1 c τ h x y
  exact ⟨⟨v, hv⟩, fun w hw => by rw [hv, Option.some.injEq] at hw; exact hw ▸ hb⟩

theorem forward5 : Candidate → Shadow5 := fun hc c τ h x y => by
  obtain ⟨v, hv, hb⟩ := hc.2.2.2.2 c τ h x y
  exact ⟨⟨v, hv⟩, fun w hw => by rw [hv, Option.some.injEq] at hw; exact hw ▸ hb⟩

theorem backward : Shadow1 → Shadow2 → Shadow3 → Shadow4 → Shadow5 → Candidate :=
  fun s1 s2 s3 s4 s5 =>
    ⟨s1,
      fun c τ h a ha p hp => by
        have := s2 c τ h a ha p hp
        cases e : c.observedDom.flag p
        · rfl
        · exact absurd e this,
      fun c τ h =>
        ⟨fun p q e => by
          obtain ⟨h1, h2⟩ := (s3 c τ h).2.1 p.1 q.1 p.2 q.2 (congrArg Fin.val e)
          exact Prod.ext h1 h2,
        fun k => by
          obtain ⟨x, y, e⟩ := (s3 c τ h).2.2 k.val k.isLt
          exact ⟨(x, y), Fin.ext e⟩⟩,
      fun c τ h x y => by
        obtain ⟨⟨v, hv⟩, hb⟩ := s4 c τ h x y
        exact ⟨v, hv, hb v hv⟩,
      fun c τ h x y => by
        obtain ⟨⟨v, hv⟩, hb⟩ := s5 c τ h x y
        exact ⟨v, hv, hb v hv⟩⟩

/-- SA-Pass anchor: the cited theorems prove `Candidate` as stated. -/
theorem anchor : Candidate :=
  ⟨fun _ _ h => (check_sound h).1, fun _ _ h => diagram_informationLocal h,
    fun _ _ h => boundaryIndex_bijective h, fun _ _ h => reward_certificate_sound_K h,
    fun _ _ h => reward_certificate_sound_W h⟩

end CategoricalInfluenceDiagramsProofs.Shadows.CertificateSound
