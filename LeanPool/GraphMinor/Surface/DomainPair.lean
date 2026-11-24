/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Mesh

/-!
# Matching cuts of two Jordan domains

`IsPairing` is the state of the proof of the Schoenflies theorem: finitely many pairs of `O`-arcs
`(G, G')`, a homeomorphism from each `G` to `G'` given by one global pair of maps, such that the
closed domains cover the two given closed domains and meet only along their boundaries.
`IsPairing.cut` cuts one pair: a cross-cut of `G` is matched with a cross-cut of `G'`, which exists
because every point of an `O`-arc is accessible. `IsPairing.refine` follows a whole tree of cuts.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

/-- `h` and `k` are inverse homeomorphisms between `F` and `F'`. -/
def BdMatch (F F' : Set ℂ) (h k : ℂ → ℂ) : Prop :=
  MapsTo h F F' ∧ MapsTo k F' F ∧ LeftInvOn k h F ∧ RightInvOn k h F' ∧
    ContinuousOn h F ∧ ContinuousOn k F'

theorem BdMatch.symm {F F' : Set ℂ} {h k : ℂ → ℂ} (m : BdMatch F F' h k) : BdMatch F' F k h :=
  ⟨m.2.1, m.1, m.2.2.2.1, m.2.2.1, m.2.2.2.2.2, m.2.2.2.2.1⟩

theorem BdMatch.congr {F F' : Set ℂ} {h k h' k' : ℂ → ℂ} (m : BdMatch F F' h k) (e : EqOn h' h F)
    (e' : EqOn k' k F') : BdMatch F F' h' k' := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := m
  refine ⟨fun x hx => e hx ▸ m1 hx, fun x hx => e' hx ▸ m2 hx, ?_, ?_, m5.congr e, m6.congr e'⟩
  · intro x hx
    show k' (h' x) = x
    rw [e hx, e' (m1 hx)]
    exact m3 hx
  · intro x hx
    show h' (k' x) = x
    rw [e' hx, e (m2 hx)]
    exact m4 hx

/-- An injective path has a continuous inverse on its range. -/
theorem IsArcMap.exists_inv {e : 𝕀 → ℂ} (he : IsArcMap e) :
    ∃ ι : ℂ → 𝕀, (∀ t, ι (e t) = t) ∧ ContinuousOn ι (range e) := by
  classical
  have hemb := (he.1.isClosedEmbedding he.2).isEmbedding
  let E := hemb.toHomeomorph
  refine ⟨fun z => if hz : z ∈ range e then E.symm ⟨z, hz⟩ else 0, fun t => ?_, ?_⟩
  · have hm : e t ∈ range e := ⟨t, rfl⟩
    simp only [hm, dite_true]
    exact E.symm_apply_apply t
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (range e).domRestrict (fun z => if hz : z ∈ range e then E.symm ⟨z, hz⟩ else 0) =
        fun z : range e => E.symm z := by
      ext z
      simp [Set.domRestrict, z.2]
    rw [this]
    exact E.symm.continuous

/-- Two arcs with values prescribed along them give a homeomorphism of their unions. -/
theorem bdMatch_of_arcs {c e c' e' : 𝕀 → ℂ} (hc : IsArcMap c) (he : IsArcMap e) (hc' : IsArcMap c')
    (he' : IsArcMap e') {h k : ℂ → ℂ} (h1 : ∀ s, h (c s) = c' s) (h2 : ∀ s, h (e s) = e' s)
    (k1 : ∀ s, k (c' s) = c s) (k2 : ∀ s, k (e' s) = e s) :
    BdMatch (range c ∪ range e) (range c' ∪ range e') h k := by
  have hclosed : ∀ {d : 𝕀 → ℂ}, IsArcMap d → IsClosed (range d) := fun hd =>
    (isCompact_range hd.1).isClosed
  have hcont : ∀ {d d' : 𝕀 → ℂ} {f : ℂ → ℂ}, IsArcMap d → IsArcMap d' → (∀ s, f (d s) = d' s) →
      ContinuousOn f (range d) := by
    intro d d' f hd hd' hf
    obtain ⟨ι, hι, hιc⟩ := hd.exists_inv
    refine (hd'.1.comp_continuousOn hιc).congr ?_
    rintro _ ⟨s, rfl⟩
    change f (d s) = d' (ι (d s))
    rw [hι, hf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inl ⟨s, (h1 s).symm⟩
    · exact Or.inr ⟨s, (h2 s).symm⟩
  · rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inl ⟨s, (k1 s).symm⟩
    · exact Or.inr ⟨s, (k2 s).symm⟩
  · rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · show k (h (c s)) = c s
      rw [h1, k1]
    · show k (h (e s)) = e s
      rw [h2, k2]
  · rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · show h (k (c' s)) = c' s
      rw [k1, h1]
    · show h (k (e' s)) = e' s
      rw [k2, h2]
  · exact (hcont hc hc' h1).union_of_isClosed (hcont he he' h2) (hclosed hc) (hclosed he)
  · exact (hcont hc' hc k1).union_of_isClosed (hcont he' he k2) (hclosed hc') (hclosed he')

/-- The state of the construction, for fixed outer curves and boundary maps. -/
structure IsPairing (F₀ F₀' : Set ℂ) (h₀ k₀ : ℂ → ℂ) (S : Set (Set ℂ × Set ℂ)) (h k : ℂ → ℂ) :
    Prop where
  fin : S.Finite
  oarc : ∀ q ∈ S, Nonempty (Circle ≃ₜ q.1)
  oarc' : ∀ q ∈ S, Nonempty (Circle ≃ₜ q.2)
  bd : ∀ q ∈ S, BdMatch q.1 q.2 h k
  cov : ⋃ q ∈ S, closedInner q.1 = closedInner F₀
  cov' : ⋃ q ∈ S, closedInner q.2 = closedInner F₀'
  meet : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → closedInner q.1 ∩ closedInner q'.1 ⊆ q.1 ∩ q'.1
  meet' : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → closedInner q.2 ∩ closedInner q'.2 ⊆ q.2 ∩ q'.2
  top : ∀ q ∈ S, closedInner q.1 ∩ F₀ ⊆ q.1
  top' : ∀ q ∈ S, closedInner q.2 ∩ F₀' ⊆ q.2
  ext : EqOn h h₀ F₀
  ext' : EqOn k k₀ F₀'

variable {F₀ F₀' : Set ℂ} {h₀ k₀ : ℂ → ℂ} {S : Set (Set ℂ × Set ℂ)} {h k : ℂ → ℂ}

/-- The state seen from the other side. -/
theorem IsPairing.swap (P : IsPairing F₀ F₀' h₀ k₀ S h k) :
    IsPairing F₀' F₀ k₀ h₀ (Prod.swap '' S) k h := by
  refine ⟨P.fin.image _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, P.ext', P.ext⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact P.oarc' q hq
  · rintro _ ⟨q, hq, rfl⟩
    exact P.oarc q hq
  · rintro _ ⟨q, hq, rfl⟩
    exact (P.bd q hq).symm
  · rw [biUnion_image]
    exact P.cov'
  · rw [biUnion_image]
    exact P.cov
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ hne
    exact P.meet' q hq q' hq' fun e => hne (e ▸ rfl)
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ hne
    exact P.meet q hq q' hq' fun e => hne (e ▸ rfl)
  · rintro _ ⟨q, hq, rfl⟩
    exact P.top' q hq
  · rintro _ ⟨q, hq, rfl⟩
    exact P.top q hq

/-- The closed domain of a side of a cut lies in the closed domain, and the sides fill it. -/
theorem IsCut.closedInner_facts {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e)
    (J : IsJordanParts F) :
    closedInner (side a e) ∪ closedInner (side b e) = closedInner F ∧
    closedInner (side a e) ⊆ closedInner F ∧ closedInner (side b e) ⊆ closedInner F ∧
    closedInner (side a e) ∩ closedInner (side b e) ⊆ range e ∧
    closedInner (side a e) ∩ F ⊆ range a ∧ closedInner (side b e) ∩ F ⊆ range b := by
  have T := c.isTheta J
  have hrange : range e ⊆ closedInner F := by
    rintro _ ⟨t, rfl⟩
    by_cases h0 : t = 0
    · exact Or.inr (by rw [h0, ← c.a_zero]; exact c.a_mem 0)
    · by_cases h1 : t = 1
      · exact Or.inr (by rw [h1, ← c.a_one]; exact c.a_mem 1)
      · exact Or.inl (c.inside t h0 h1)
  have hsub : ∀ {d : 𝕀 → ℂ}, (range d ⊆ F) → inner (side d e) ⊆ inner F →
      closedInner (side d e) ⊆ closedInner F := by
    intro d hd hin z hz
    rcases hz with hz | hz | hz
    · exact Or.inl (hin hz)
    · exact Or.inr (hd hz)
    · exact hrange hz
  have ha : range a ⊆ F := by rintro _ ⟨s, rfl⟩; exact c.a_mem s
  have hb : range b ⊆ F := by rintro _ ⟨s, rfl⟩; exact c.b_mem s
  have h1 := hsub ha T.inner_subset₁
  have h2 := hsub hb T.symm.inner_subset₁
  have hnotF : ∀ {d : 𝕀 → ℂ} {z : ℂ}, z ∈ closedInner (side d e) → z ∈ F → z ∉ inner (side d e) →
      z ∈ range d ∨ z ∈ range e := fun hz _ hn => hz.resolve_left hn
  refine ⟨?_, h1, h2, ?_, ?_, ?_⟩
  · refine Subset.antisymm (union_subset h1 h2) ?_
    intro z hz
    by_cases hze : z ∈ range e
    · exact Or.inl (Or.inr (Or.inr hze))
    rcases hz with hz | hz
    · have hmem : z ∈ inner F \ range e := ⟨hz, hze⟩
      rw [T.inner_sdiff] at hmem
      rcases hmem with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')
    · rw [← c.union] at hz
      rcases hz with h' | h'
      · exact Or.inl (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inl h'))
  · rintro z ⟨hz1, hz2⟩
    rcases hz1 with hz1 | hz1 | hz1
    · rcases hz2 with hz2 | hz2 | hz2
      · exact absurd hz2 (Set.disjoint_left.mp T.disjoint_inner hz1)
      · exact absurd (hb hz2) (Set.disjoint_left.mp T.inner_disjoint_F hz1)
      · exact absurd (Or.inr hz2) hz1.1
    · rcases hz2 with hz2 | hz2 | hz2
      · exact absurd (ha hz1) (Set.disjoint_left.mp T.symm.inner_disjoint_F hz2)
      · rcases c.meet _ _ (show a (Classical.choose hz1) = b (Classical.choose hz2) by
          rw [Classical.choose_spec hz1, Classical.choose_spec hz2]) with ⟨h3, -⟩ | ⟨h3, -⟩
        · refine ⟨0, ?_⟩
          rw [← c.a_zero, ← h3, Classical.choose_spec hz1]
        · refine ⟨1, ?_⟩
          rw [← c.a_one, ← h3, Classical.choose_spec hz1]
      · exact hz2
    · exact hz1
  · rintro z ⟨hz1, hzF⟩
    rcases hz1 with hz1 | hz1 | hz1
    · exact absurd hzF (Set.disjoint_left.mp T.inner_disjoint_F hz1)
    · exact hz1
    · obtain ⟨t, rfl⟩ := hz1
      by_cases h0 : t = 0
      · exact ⟨0, by rw [h0, c.a_zero]⟩
      · by_cases h3 : t = 1
        · exact ⟨1, by rw [h3, c.a_one]⟩
        · exact absurd hzF (c.e_notMem h0 h3)
  · rintro z ⟨hz1, hzF⟩
    rcases hz1 with hz1 | hz1 | hz1
    · exact absurd hzF (Set.disjoint_left.mp T.symm.inner_disjoint_F hz1)
    · exact hz1
    · obtain ⟨t, rfl⟩ := hz1
      by_cases h0 : t = 0
      · exact ⟨0, by rw [h0, c.b_zero]⟩
      · by_cases h3 : t = 1
        · exact ⟨1, by rw [h3, c.b_one]⟩
        · exact absurd hzF (c.e_notMem h0 h3)

/-- The side of a cut meets an outside set only on the side. -/
theorem IsCut.meet_side {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e) (J : IsJordanParts F)
    {G : Set ℂ} (hG : closedInner F ∩ closedInner G ⊆ F ∩ G) :
    closedInner (side a e) ∩ closedInner G ⊆ side a e ∩ G := by
  obtain ⟨-, h1, -, -, h5, -⟩ := c.closedInner_facts J
  rintro z ⟨hz1, hz2⟩
  have hz := hG ⟨h1 hz1, hz2⟩
  exact ⟨Or.inl (h5 ⟨hz1, hz.1⟩), hz.2⟩

theorem IsCut.meet_sides {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e) (J : IsJordanParts F) :
    closedInner (side a e) ∩ closedInner (side b e) ⊆ side a e ∩ side b e := by
  obtain ⟨-, -, -, h4, -, -⟩ := c.closedInner_facts J
  exact fun z hz => ⟨Or.inr (h4 hz), Or.inr (h4 hz)⟩

theorem IsCut.mem_range_of_mem {F : Set ℂ} {a b e : 𝕀 → ℂ} (c : IsCut F a b e) {z : ℂ} (hz : z ∈ F)
    (he : z ∈ range e) : z = e 0 ∨ z = e 1 := by
  obtain ⟨t, rfl⟩ := he
  by_cases h0 : t = 0
  · left
    rw [h0]
  · by_cases h1 : t = 1
    · right
      rw [h1]
    · exact absurd hz (c.e_notMem h0 h1)

private theorem cover_replace {Q : Type*} {S : Set Q} (region : Q → Set ℂ)
    {q a b : Q} {U : Set ℂ} (hq : q ∈ S)
    (hsplit : closedInner (region q) = closedInner (region a) ∪ closedInner (region b))
    (ha : closedInner (region a) ⊆ closedInner (region q))
    (hb : closedInner (region b) ⊆ closedInner (region q))
    (hcover : (⋃ r ∈ S, closedInner (region r)) = U) :
    (⋃ r ∈ insert a (insert b (S \ {q})), closedInner (region r)) = U := by
  refine Subset.antisymm ?_ ?_
  · refine iUnion₂_subset ?_
    rintro r (rfl | rfl | hr)
    · exact ha.trans ((subset_iUnion₂_of_subset q hq Subset.rfl).trans hcover.subset)
    · exact hb.trans ((subset_iUnion₂_of_subset q hq Subset.rfl).trans hcover.subset)
    · exact (subset_iUnion₂_of_subset r hr.1 Subset.rfl).trans hcover.subset
  · rw [← hcover]
    refine iUnion₂_subset fun r hr => ?_
    by_cases heq : r = q
    · subst r
      intro z hz
      rw [hsplit] at hz
      rcases hz with hz | hz
      · exact mem_iUnion₂.mpr ⟨a, Or.inl rfl, hz⟩
      · exact mem_iUnion₂.mpr ⟨b, Or.inr (Or.inl rfl), hz⟩
    · exact subset_iUnion₂_of_subset r (Or.inr (Or.inr ⟨hr, heq⟩)) Subset.rfl

/-- The cut of one pair of a state, in terms of the maps. -/
theorem IsPairing.cut (P : IsPairing F₀ F₀' h₀ k₀ S h k) {F F' : Set ℂ} (hq : (F, F') ∈ S)
    {a b e : 𝕀 → ℂ} (c : IsCut F a b e) :
    ∃ (e' : 𝕀 → ℂ) (h' k' : ℂ → ℂ), IsPairing F₀ F₀' h₀ k₀
      (insert (side a e, side (h ∘ a) e') (insert (side b e, side (h ∘ b) e') (S \ {(F, F')})))
      h' k' ∧
      closedInner (side (h ∘ a) e') ⊆ closedInner F' ∧
      closedInner (side (h ∘ b) e') ⊆ closedInner F' ∧
      (side a e, side (h ∘ a) e') ≠ (side b e, side (h ∘ b) e') ∧
      (side a e, side (h ∘ a) e') ∉ S \ {(F, F')} ∧
      (side b e, side (h ∘ b) e') ∉ S \ {(F, F')} := by
  classical
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := P.bd _ hq
  obtain ⟨φ⟩ := P.oarc _ hq
  obtain ⟨φ'⟩ := P.oarc' _ hq
  simp only at m1 m2 m3 m4 m5 m6 φ φ'
  have J := isJordanParts φ
  have J' := isJordanParts φ'
  have harc : ∀ {d : 𝕀 → ℂ}, IsArcMap d → (∀ s, d s ∈ F) → IsArcMap (h ∘ d) := by
    intro d hd hmem
    refine ⟨m5.comp_continuous hd.1 hmem, fun s s' he => hd.2 ?_⟩
    have := congrArg k he
    simp only [Function.comp] at this
    rwa [m3 (hmem s), m3 (hmem s')] at this
  have hae : ∀ s, a s ∈ F := c.a_mem
  have hbe : ∀ s, b s ∈ F := c.b_mem
  have he0 : e 0 ∈ F := c.a_zero ▸ hae 0
  have he1 : e 1 ∈ F := c.a_one ▸ hae 1
  have hne' : h (e 0) ≠ h (e 1) := fun he => c.ne (by
    have := congrArg k he
    rwa [m3 he0, m3 he1] at this)
  obtain ⟨x', hx'⟩ := J'.isConnected_inner.nonempty
  have hx'F : x' ∉ F' := hx'.1
  obtain ⟨e', he'c, he'i, he'0, he'1, he'in⟩ := exists_crossCut φ' hx'F (m1 he0) (m1 he1) hne'
  have he'inner : ∀ t, t ≠ 0 → t ≠ 1 → e' t ∈ inner F' := fun t h0 h1 =>
    J'.subset_inner isPreconnected_connectedComponentIn
      (Set.disjoint_left.mpr fun z hz hzF => connectedComponentIn_subset F'ᶜ x' hz hzF)
      ⟨x', mem_connectedComponentIn hx'F, hx'⟩ (he'in t h0 h1)
  have he'arc : IsArcMap e' := ⟨he'c, he'i⟩
  have c' : IsCut F' (h ∘ a) (h ∘ b) e' := by
    refine ⟨harc c.arc_a hae, harc c.arc_b hbe, he'arc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he'inner⟩
    · simp only [Function.comp, c.a_zero, he'0]
    · simp only [Function.comp, c.a_one, he'1]
    · simp only [Function.comp, c.b_zero, he'0]
    · simp only [Function.comp, c.b_one, he'1]
    · rw [he'0, he'1]
      exact hne'
    · ext w
      constructor
      · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
        · exact m1 (hae s)
        · exact m1 (hbe s)
      · intro hw
        have hkw : k w ∈ F := m2 hw
        rw [← c.union] at hkw
        rcases hkw with ⟨s, hs⟩ | ⟨s, hs⟩
        · exact Or.inl ⟨s, by simp only [Function.comp, hs]; exact m4 hw⟩
        · exact Or.inr ⟨s, by simp only [Function.comp, hs]; exact m4 hw⟩
    · intro s t hst
      refine c.meet s t ?_
      have := congrArg k hst
      simp only [Function.comp] at this
      rwa [m3 (hae s), m3 (hbe t)] at this
  obtain ⟨ι, hι, -⟩ := c.arc_e.exists_inv
  obtain ⟨ι', hι', -⟩ := he'arc.exists_inv
  let H : ℂ → ℂ := fun z => if z ∈ range e then e' (ι z) else h z
  let K : ℂ → ℂ := fun w => if w ∈ range e' then e (ι' w) else k w
  have Hrange : ∀ t, H (e t) = e' t := fun t => by
    have : e t ∈ range e := ⟨t, rfl⟩
    simp only [H, this, ite_true, hι]
  have Krange : ∀ t, K (e' t) = e t := fun t => by
    have : e' t ∈ range e' := ⟨t, rfl⟩
    simp only [K, this, ite_true, hι']
  have HF : EqOn H h F := by
    intro z hz
    by_cases hze : z ∈ range e
    · rcases c.mem_range_of_mem hz hze with rfl | rfl
      · rw [Hrange, he'0]
      · rw [Hrange, he'1]
    · simp only [H, hze, ite_false]
  have KF : EqOn K k F' := by
    intro w hw
    by_cases hwe : w ∈ range e'
    · rcases c'.mem_range_of_mem hw hwe with rfl | rfl
      · rw [Krange, he'0, m3 he0]
      · rw [Krange, he'1, m3 he1]
    · simp only [K, hwe, ite_false]
  have hbdside : ∀ {d d' : 𝕀 → ℂ}, IsArcMap d → (∀ s, d s ∈ F) → d' = h ∘ d →
      BdMatch (side d e) (side d' e') H K := by
    rintro d _ hd hmem rfl
    refine bdMatch_of_arcs hd c.arc_e (harc hd hmem) he'arc (fun s => HF (hmem s)) Hrange
      (fun s => ?_) Krange
    change K (h (d s)) = d s
    rw [KF (m1 (hmem s))]
    exact m3 (hmem s)
  have hrangesub : range e ⊆ closedInner F := by
    obtain ⟨-, h1, -, -, -, -⟩ := c.closedInner_facts J
    exact fun z hz => h1 (Or.inr (Or.inr hz))
  have hrangesub' : range e' ⊆ closedInner F' := by
    obtain ⟨-, h1, -, -, -, -⟩ := c'.closedInner_facts J'
    exact fun z hz => h1 (Or.inr (Or.inr hz))
  have hother : ∀ {G : Set ℂ}, closedInner F ∩ G ⊆ F → EqOn H h G := by
    intro G hG z hz
    by_cases hze : z ∈ range e
    · exact HF (hG ⟨hrangesub hze, hz⟩)
    · simp only [H, hze, ite_false]
  have hother' : ∀ {G : Set ℂ}, closedInner F' ∩ G ⊆ F' → EqOn K k G := by
    intro G hG z hz
    by_cases hze : z ∈ range e'
    · exact KF (hG ⟨hrangesub' hze, hz⟩)
    · simp only [K, hze, ite_false]
  have hp1 : (F, F').1 = F := rfl
  have hsubq : ∀ q ∈ S \ {(F, F')}, closedInner F ∩ closedInner q.1 ⊆ F ∩ q.1 ∧
      closedInner F' ∩ closedInner q.2 ⊆ F' ∩ q.2 := by
    rintro q ⟨hqS, hne⟩
    have hne' : (F, F') ≠ q := fun he => hne he.symm
    exact ⟨P.meet _ hq q hqS hne', P.meet' _ hq q hqS hne'⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := c.closedInner_facts J
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := c'.closedInner_facts J'
  have T := c.isTheta J
  obtain ⟨z₁, hz₁⟩ := T.parts₁.isConnected_inner.nonempty
  obtain ⟨z₂, hz₂⟩ := T.parts₂.isConnected_inner.nonempty
  refine ⟨e', H, K, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, g2, g3, ?_, ?_, ?_⟩
  · exact ((P.fin.subset sdiff_subset).insert _).insert _
  · rintro q (rfl | rfl | hq')
    · exact c.oArc_side
    · exact c.symm.oArc_side
    · exact P.oarc q hq'.1
  · rintro q (rfl | rfl | hq')
    · exact c'.oArc_side
    · exact c'.symm.oArc_side
    · exact P.oarc' q hq'.1
  · rintro q (rfl | rfl | hq')
    · exact hbdside c.arc_a hae rfl
    · exact hbdside c.arc_b hbe rfl
    · have hs := hsubq q hq'
      have hz1 : ∀ {G : Set ℂ} {Z : Set ℂ}, closedInner F ∩ closedInner Z ⊆ F ∩ Z → G ⊆ Z →
          closedInner F ∩ G ⊆ F := by
        intro G Z h1 h2 z hz
        exact (h1 ⟨hz.1, Or.inr (h2 hz.2)⟩).1
      have h3 : closedInner F ∩ q.1 ⊆ F := fun z hz => (hs.1 ⟨hz.1, Or.inr hz.2⟩).1
      have h4 : closedInner F' ∩ q.2 ⊆ F' := fun z hz => (hs.2 ⟨hz.1, Or.inr hz.2⟩).1
      exact (P.bd q hq'.1).congr (hother h3) (hother' h4)
  · exact cover_replace Prod.fst hq f1.symm f2 f3 P.cov
  · exact cover_replace Prod.snd hq g1.symm g2 g3 P.cov'
  · rintro q (rfl | rfl | hq1) q' (rfl | rfl | hq2) hne
    · exact absurd rfl hne
    · exact c.meet_sides J
    · exact c.meet_side J (hsubq _ hq2).1
    · rw [inter_comm, inter_comm (side b e)]
      exact c.meet_sides J
    · exact absurd rfl hne
    · exact c.symm.meet_side J (hsubq _ hq2).1
    · rw [inter_comm, inter_comm q.1]
      exact c.meet_side J (hsubq _ hq1).1
    · rw [inter_comm, inter_comm q.1]
      exact c.symm.meet_side J (hsubq _ hq1).1
    · exact P.meet q hq1.1 q' hq2.1 hne
  · rintro q (rfl | rfl | hq1) q' (rfl | rfl | hq2) hne
    · exact absurd rfl hne
    · exact c'.meet_sides J'
    · exact c'.meet_side J' (hsubq _ hq2).2
    · rw [inter_comm, inter_comm (side (h ∘ b) e')]
      exact c'.meet_sides J'
    · exact absurd rfl hne
    · exact c'.symm.meet_side J' (hsubq _ hq2).2
    · rw [inter_comm, inter_comm q.2]
      exact c'.meet_side J' (hsubq _ hq1).2
    · rw [inter_comm, inter_comm q.2]
      exact c'.symm.meet_side J' (hsubq _ hq1).2
    · exact P.meet' q hq1.1 q' hq2.1 hne
  · rintro q (rfl | rfl | hq') z ⟨hz1, hz2⟩
    · exact Or.inl (f5 ⟨hz1, P.top _ hq ⟨f2 hz1, hz2⟩⟩)
    · exact Or.inl (f6 ⟨hz1, P.top _ hq ⟨f3 hz1, hz2⟩⟩)
    · exact P.top q hq'.1 ⟨hz1, hz2⟩
  · rintro q (rfl | rfl | hq') z ⟨hz1, hz2⟩
    · exact Or.inl (g5 ⟨hz1, P.top' _ hq ⟨g2 hz1, hz2⟩⟩)
    · exact Or.inl (g6 ⟨hz1, P.top' _ hq ⟨g3 hz1, hz2⟩⟩)
    · exact P.top' q hq'.1 ⟨hz1, hz2⟩
  · refine (hother fun z hz => ?_).trans P.ext
    exact P.top _ hq ⟨hz.1, hz.2⟩
  · refine (hother' fun z hz => ?_).trans P.ext'
    exact P.top' _ hq ⟨hz.1, hz.2⟩
  · intro he
    have h1 : side a e = side b e := congrArg Prod.fst he
    have hin : z₁ ∈ inner (side b e) := h1 ▸ hz₁
    exact Set.disjoint_left.mp T.disjoint_inner hz₁ hin
  · rintro ⟨hqS, hne⟩
    have hs := hsubq _ ⟨hqS, hne⟩
    have hz := hs.1 ⟨f2 (Or.inl hz₁), Or.inl hz₁⟩
    exact Set.disjoint_left.mp T.inner_disjoint_F hz₁ hz.1
  · rintro ⟨hqS, hne⟩
    have hs := hsubq _ ⟨hqS, hne⟩
    have hz := hs.1 ⟨f3 (Or.inl hz₂), Or.inl hz₂⟩
    exact Set.disjoint_left.mp T.symm.inner_disjoint_F hz₂ hz.1

end GraphMinor.Surface
