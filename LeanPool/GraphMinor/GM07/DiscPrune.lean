/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.DiscPush
public import LeanPool.GraphMinor.GM07.CutEdge
import LeanPool.GraphMinor.GM19.FragmentOuter
import LeanPool.GraphMinor.GM07.CutBounds

/-!
# Deleting what lies in a small disc

Let `Δ` be a closed disc whose boundary is `G`-normal with at most one vertex, and let `G'` be `G`
with the inside of `Δ` removed.
The paper says "it is easy to see that `α(G') = α(G)`" in the proof of (7.3). We prove the
inequality it needs: each candidate for
`α(G')` gives a candidate for `α(G)` with at most as many vertices (`exists_candidate_of_prune`).

The candidate `X'` of `G'` may run inside `Δ`. We first thin it: for each cuff, and for `Σ` itself,
we keep an `O`-arc of `X'` that
shows `X'` is not planar there, and we join these `O`-arcs by lines in `X'`. This thin set misses
some point `p` of the inside of `Δ`,
and we project from `p` to the boundary of `Δ`. The image of each `O`-arc is homotopic to it, so by
(11.2) it holds an `O`-arc with
the same property.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- A line of a connected closed surface holds no open set. This is `GM19.line_subset_closure_compl`
for surfaces in any universe:
we move the line to a model by classification. -/
theorem line_subset_closure_compl_of_closed [ConnectedSpace T] (hT : IsClosedSurface T) {L : Set T}
  {a b : T} (hl : IsLineWithEnds L a b) :
    L ⊆ closure Lᶜ := by
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  have hsurf : IsSurface T := hT.isSurface
  obtain ⟨p, q, c, ⟨e⟩⟩ := classification.{u} T hsurf inferInstance
  have hM : IsClosedSurface (SurfaceModel p q c) := by
    refine ⟨e.surjective.compactSpace e.continuous, e.symm.isEmbedding.t2Space, fun x => ?_⟩
    have h1 := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hT.2.2 _)
    simpa using h1
  have : T2Space (SurfaceModel p q c) := hM.2.1
  have : ConnectedSpace (SurfaceModel p q c) := e.surjective.connectedSpace e.continuous
  have hl' : IsLineWithEnds (e '' L) (e a) (e b) := by
    obtain ⟨f, h0, h1⟩ := hl
    exact ⟨f.trans (e.isEmbedding.homeomorphImage L), congrArg e h0, congrArg e h1⟩
  intro x hx
  have h1 := GM19.line_subset_closure_compl hM hl' (mem_image_of_mem e hx)
  rw [← e.image_compl, ← e.image_closure] at h1
  obtain ⟨y, hy, he⟩ := h1
  rwa [← e.injective he]

/-- A finite union of lines does not hold the inside of a closed disc. -/
theorem exists_mem_discInt_off (hS : IsSurface S) [ConnectedSpace S] {Δ : Set S}
  (hΔ : IsClosedDisc Δ) {𝓛 : Set (Set S)}
    (hf : 𝓛.Finite) (hl : ∀ L ∈ 𝓛, ∃ a b, IsLineWithEnds L a b) : ∃ p ∈ discInt Δ, p ∉ ⋃₀ 𝓛 := by
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, hconn⟩ := exists_capAll S hS
  have : ConnectedSpace T := hconn inferInstance
  have ht2 : T2Space T := hT.2.1
  have hS2 : T2Space S := hS.2.1
  have hman := hS.2.2
  have hgood : ∀ {𝓜 : Set (Set S)}, 𝓜.Finite → (∀ L ∈ 𝓜, ∃ a b, IsLineWithEnds L a b) →
      IsClosed (j '' ⋃₀ 𝓜) ∧ Dense (j '' ⋃₀ 𝓜)ᶜ := fun {𝓜} hf' => by
    induction 𝓜, hf' using Set.Finite.induction_on with
    | empty =>
      intro _
      simp
    | @insert L 𝓜 _ _ ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun L' hL' => h L' (mem_insert_of_mem _ hL')
      obtain ⟨a, b, f, h0, h1'⟩ := h L (mem_insert _ _)
      have hLc : IsCompact L := by
        have h3 := isCompact_range (continuous_subtype_val.comp f.continuous)
        rwa [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
      have hline : IsLineWithEnds (j '' L) (j a) (j b) := by
        refine ⟨f.trans (hj.isEmbedding.homeomorphImage L), ?_, ?_⟩
        · exact congrArg j h0
        · exact congrArg j h1'
      have hcl : IsClosed (j '' L) := (hLc.image hj.continuous).isClosed
      have hd : Dense (j '' L)ᶜ := fun x => by
        by_cases hx : x ∈ j '' L
        · exact line_subset_closure_compl_of_closed hT hline hx
        · exact subset_closure hx
      rw [sUnion_insert, image_union]
      refine ⟨hcl.union h1, ?_⟩
      rw [compl_union]
      exact hd.inter_of_isOpen_left h2 hcl.isOpen_compl
  obtain ⟨-, hd⟩ := hgood hf hl
  obtain ⟨h₁, g₁, cc⟩ := hΔ.exists_isChart
  have hno : (discInt Δ).Nonempty := by
    refine ⟨g₁ 0, cc.gm (by simp), fun hb => ?_⟩
    have h2 : h₁ (g₁ 0) ∈ sphere (0 : ℂ) 1 := cc.bd ▸ mem_image_of_mem h₁ hb
    rw [cc.hg (by simp)] at h2
    simp at h2
  obtain ⟨p₁, hp₁⟩ := hno
  obtain ⟨O, hO, hOe⟩ := hj.isInducing.isOpen_iff.mp (hΔ.isOpen_discInt hman)
  have hoffK : ∀ {y}, y ∈ discInt Δ → j y ∉ K := fun {y} hy hc => by
    have h1 : j y ∈ range j ∩ K := ⟨mem_range_self y, hc⟩
    rw [hi] at h1
    obtain ⟨z, hz, he⟩ := h1
    rw [hj.injective he] at hz
    exact hz (isInteriorPoint_of_mem_discInt hman hΔ hy)
  have hp₁O : j p₁ ∈ O ∩ Kᶜ := ⟨by
    change p₁ ∈ j ⁻¹' O
    rw [hOe]
    exact hp₁, hoffK hp₁⟩
  obtain ⟨t, ⟨htO, htK⟩, htA⟩ := hd.inter_open_nonempty _ (hO.inter hK.isOpen_compl) ⟨_, hp₁O⟩
  have htr : t ∈ range j := (hu.ge (mem_univ t)).resolve_right htK
  obtain ⟨p, rfl⟩ := htr
  refine ⟨p, ?_, fun hc => htA (mem_image_of_mem j hc)⟩
  rw [← hOe]
  exact htO

/-- `O`-arcs split into two lines. -/
theorem exists_two_lines [T2Space S] {F : Set S} (hF : IsOArc F) :
    ∃ A B : Set S, (∃ a b, IsLineWithEnds A a b) ∧ (∃ a b, IsLineWithEnds B a b) ∧ F = A ∪ B := by
  obtain ⟨φ⟩ := id hF
  have hne : (φ 1).1 ≠ (φ (-1)).1 := fun h => by
    have := φ.injective (Subtype.ext h)
    have h' := congrArg (fun z : Circle => (z : ℂ)) this
    norm_num at h'
  obtain ⟨A, B, hA, hB, hu, -⟩ := hF.lines (φ 1).2 (φ (-1)).2 hne
  exact ⟨A, B, ⟨_, _, hA⟩, ⟨_, _, hB⟩, hu.symm⟩

/-- A subset of a finite union of lines. -/
def IsThin (X : Set S) : Prop := ∃ 𝓛 : Set (Set S), 𝓛.Finite ∧ (∀ L ∈ 𝓛, ∃ a b, IsLineWithEnds L a
  b) ∧ X ⊆ ⋃₀ 𝓛

theorem isThin_iUnion {ι : Type*} [Finite ι] {P : ι → Set S} (h : ∀ i, IsThin (P i)) : IsThin
  (⋃ i, P i) := by
  choose 𝓛 h1 h2 h3 using h
  refine ⟨⋃ i, 𝓛 i, finite_iUnion h1, ?_, ?_⟩
  · intro L hL
    obtain ⟨i, hi⟩ := mem_iUnion.mp hL
    exact h2 i L hi
  · refine iUnion_subset fun i x hx => ?_
    obtain ⟨L, hL, hxL⟩ := h3 i hx
    exact ⟨L, mem_iUnion.mpr ⟨i, hL⟩, hxL⟩

theorem isThin_union {A B : Set S} (hA : IsThin A) (hB : IsThin B) : IsThin (A ∪ B) := by
  obtain ⟨𝓛, h1, h2, h3⟩ := hA
  obtain ⟨𝓜, h4, h5, h6⟩ := hB
  refine ⟨𝓛 ∪ 𝓜, h1.union h4, ?_, ?_⟩
  · rintro L (hL | hL)
    · exact h2 L hL
    · exact h5 L hL
  · rw [sUnion_union]
    exact union_subset_union h3 h6

theorem isThin_of_line {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : IsThin L :=
  ⟨{L}, finite_singleton L, fun _ hL => hL ▸ ⟨a, b, h⟩, by simp⟩

theorem isThin_of_isOArc [T2Space S] {F : Set S} (h : IsOArc F) : IsThin F := by
  obtain ⟨A, B, ⟨a, b, hA⟩, ⟨c, d, hB⟩, rfl⟩ := exists_two_lines h
  exact isThin_union (isThin_of_line hA) (isThin_of_line hB)

/-- A set not planar in `T` has an `O`-arc that shows this and survives homotopy. -/
theorem exists_obstruction {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  (hT : IsSurface T) [ConnectedSpace T]
    {j : Y → T} (hj : IsEmbedding j) {X : Set Y} (hX : IsSolid X) (hne : ¬ IsSphere T
      ∨ j '' X ≠ univ)
    (hn : ¬ IsPlanar (j '' X)) :
    ∃ A : Set Y, IsOArc A ∧ A ⊆ X ∧ ∃ f : C(Circle, Y), range f = A ∧ ∀ ψ : C(Circle, Y),
      ClosedCurvesHomotopicIn univ f ψ →
      ∃ A' : Set Y, IsOArc A' ∧ A' ⊆ range ψ ∧ ¬ IsPlanar (j '' A') := by
  have : T2Space T := hT.2.1
  by_contra hno
  refine hn (isPlanar_of_null hT hj hX hne fun F hF hFX f hf hr hc => ?_)
  by_contra hnull
  refine hno ⟨F, hF, hFX, ⟨f, hf⟩, hr, fun ψ hψ => ?_⟩
  have hψc : Continuous fun w => j (ψ w) := hj.continuous.comp ψ.continuous
  have hnn : ¬ ClosedCurveIsNullHomotopicIn univ ⟨fun w => j (ψ w), hψc⟩ := fun h => by
    apply hnull
    refine null_of_homotopic (subset_univ _) ?_ h
    obtain ⟨Ψ, -, h0, h1⟩ := hψ
    refine ⟨⟨fun q => j (Ψ q), hj.continuous.comp Ψ.continuous⟩, fun _ => mem_univ _,
      fun x => ?_, fun x => ?_⟩
    · simp [h0]
    · simp [h1]
  obtain ⟨F', hF', hsub, hnot⟩ := theorem_11_2_proof hT _ hnn
  have hsubr : F' ⊆ range j := fun x hx => by
    obtain ⟨w, hw⟩ := hsub hx
    exact ⟨ψ w, hw⟩
  refine ⟨j ⁻¹' F', IsOArc.pull_of_embedding hj hF' hsubr, ?_, ?_⟩
  · intro y hy
    obtain ⟨w, hw⟩ := hsub hy
    exact ⟨w, hj.injective hw⟩
  · rw [image_preimage_eq_of_subset hsubr, isPlanar_iff_isNullHomotopicOArc_of_isOArc hT hF']
    exact hnot

/-- The sets that show that `X` is not near-planar: for each cuff `C`, and for `none`, an `O`-arc.
-/
theorem exists_obstructions (hS : IsSurface S) [ConnectedSpace S] (hns : ¬ IsSphere S) {X : Set S}
  (hX : IsSolid X)
    (hn : ¬ IsNearPlanar X) :
    ∀ i : Option (cuffs S), ∃ A : Set S, IsOArc A ∧ A ⊆ X ∧ ∃ f : C(Circle, S), range f = A ∧
      ∀ ψ : C(Circle, S), ClosedCurvesHomotopicIn univ f ψ →
        ∃ A' : Set S, IsOArc A' ∧ A' ⊆ range ψ ∧
          ((i = none ∧ ¬ IsPlanar A') ∨ ∃ C : cuffs S, i = some C ∧ ¬ IsPlanarInCappedCuff C.1 A')
            := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  rintro (_ | ⟨C, hC⟩)
  · have hn1 : ¬ IsPlanar (id '' X) := by
      rw [image_id]
      exact fun h => hn (.inl h)
    obtain ⟨A, h1, h2, f, h3, h4⟩ := exists_obstruction hS (j := id) IsEmbedding.id hX
      (.inl hns) hn1
    refine ⟨A, h1, h2, f, h3, fun ψ hψ => ?_⟩
    obtain ⟨A', h5, h6, h7⟩ := h4 ψ hψ
    rw [image_id] at h7
    exact ⟨A', h5, h6, .inl ⟨rfl, h7⟩⟩
  · obtain ⟨T, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC
    have hT := hc.isSurface
    have : ConnectedSpace T := hc.connectedSpace hS
    have hn1 : ¬ IsPlanar (j '' X) := fun h => hn (.inr ⟨C, hC, isPlanarInCappedCuff_of_cap hS hc
      h⟩)
    obtain ⟨A, h1, h2, f, h3, h4⟩ := exists_obstruction hT hc.isEmbedding hX (.inr
      (IsCappedCuff.image_ne_univ hc X)) hn1
    refine ⟨A, h1, h2, f, h3, fun ψ hψ => ?_⟩
    obtain ⟨A', h5, h6, h7⟩ := h4 ψ hψ
    exact ⟨A', h5, h6, .inr ⟨⟨C, hC⟩, rfl, fun hp => h7 (hp.2.2 T j D hc)⟩⟩

/-- A solid connected set is path-connected. -/
theorem isPathConnected_of_solid (hS : IsSurface S) {X : Set S} (hX : IsSolid X)
  (hc : IsConnected X) : IsPathConnected X := by
  have : T2Space S := hS.2.1
  have harc := theorem_11_4_proof hS hc hX.1
  obtain ⟨a, ha⟩ := hc.1
  refine ⟨a, ha, fun b hb => ?_⟩
  by_cases hab : a = b
  · subst hab
    exact JoinedIn.refl ha
  · exact (joinedIn_iff_eq_or_exists_isLineWithEnds ha hb).mpr (.inr (harc a ha b hb hab))

theorem isSolid_empty_set : IsSolid (∅ : Set S) :=
  ⟨fun _ hz => hz.elim, isClosed_empty⟩

theorem isSolid_sUnion_of_finite (hS : IsSurface S) {𝒵 : Set (Set S)} (hf : 𝒵.Finite)
  (h : ∀ Z ∈ 𝒵, IsSolid Z) : IsSolid (⋃₀ 𝒵) := by
  induction 𝒵, hf using Set.Finite.induction_on with
  | empty => simpa using isSolid_empty_set
  | @insert Z 𝒵 _ _ ih =>
    rw [sUnion_insert]
    exact theorem_11_6_proof hS (h Z (mem_insert _ _)) (ih fun Z' hZ' => h Z'
      (mem_insert_of_mem _ hZ'))

theorem isPathConnected_of_isOArc {F : Set S} (hF : IsOArc F) : IsPathConnected F := by
  obtain ⟨φ⟩ := id hF
  have hrange : F = range (fun w : Circle => (φ w).1) := by
    ext x
    exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨w, rfl⟩; exact (φ w).2⟩
  rw [hrange]
  exact isPathConnected_range (continuous_subtype_val.comp φ.continuous)

/-- Join finitely many `O`-arcs of a path-connected set by lines of this set. -/
theorem exists_solid_join (hS : IsSurface S) {ι : Type*} [Finite ι] {i₀ : ι} {Y : Set S}
  (hY : IsPathConnected Y) {B : ι → Set S}
    (hB : ∀ i, IsOArc (B i)) (hs : ∀ i, B i ⊆ Y) :
    ∃ X : Set S, IsSolid X ∧ IsConnected X ∧ (∀ i, B i ⊆ X) ∧ X ⊆ Y ∧ IsThin X := by
  have : T2Space S := hS.2.1
  have hne : ∀ i, (B i).Nonempty := fun i => (isConnected_of_isOArc (hB i)).1
  obtain ⟨b₀, hb₀⟩ := hne i₀
  have hP : ∀ i, ∃ P : Set S, IsThin P ∧ IsSolid P ∧ P ⊆ Y ∧ IsPreconnected (P ∪ B i ∪ B i₀) := by
    intro i
    obtain ⟨b, hb⟩ := hne i
    have hj := hY.joinedIn b₀ (hs i₀ hb₀) b (hs i hb)
    have hu : ∀ {A : Set S}, IsPreconnected A → (b₀ ∈ A ∨ b ∈ A) → b₀ ∈ A ∧ b ∈ A → IsPreconnected
      (A ∪ B i ∪ B i₀) := by
      intro A hA _ hba
      exact (hA.union b hba.2 hb (isConnected_of_isOArc (hB i)).isPreconnected).union b₀
        (.inl hba.1) hb₀
        (isConnected_of_isOArc (hB i₀)).isPreconnected
    rcases (joinedIn_iff_eq_or_exists_isLineWithEnds (hs i₀ hb₀) (hs i hb)).mp hj with rfl | ⟨L,
      hL, hl⟩
    · refine ⟨B i₀, isThin_of_isOArc (hB i₀), isSolid_of_isOArc hS (hB i₀), hs i₀, ?_⟩
      exact hu (isConnected_of_isOArc (hB i₀)).isPreconnected (.inl hb₀) ⟨hb₀, hb₀⟩
    · obtain ⟨f, h0, h1⟩ := id hl
      have hLc : IsPreconnected L := by
        have h3 := isPreconnected_range (continuous_subtype_val.comp f.continuous)
        rwa [range_comp, f.surjective.range_eq, image_univ, Subtype.range_coe] at h3
      have hb0L : b₀ ∈ L := h0 ▸ (f 0).2
      have hbL : b ∈ L := h1 ▸ (f 1).2
      exact ⟨L, isThin_of_line hl, isSolid_of_isLineWithEnds hS hl, hL, hu hLc (.inl hb0L) ⟨hb0L,
        hbL⟩⟩
  choose P h1 h2 h3 h4 using hP
  have hsol : IsSolid (⋃ i, (P i ∪ B i ∪ B i₀)) := by
    rw [← sUnion_range]
    refine isSolid_sUnion_of_finite hS (finite_range _) ?_
    rintro _ ⟨i, rfl⟩
    exact theorem_11_6_proof hS (theorem_11_6_proof hS (h2 i) (isSolid_of_isOArc hS (hB i)))
      (isSolid_of_isOArc hS (hB i₀))
  refine ⟨⋃ i, (P i ∪ B i ∪ B i₀), hsol, ⟨⟨b₀, mem_iUnion.mpr ⟨i₀, .inr hb₀⟩⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact isPreconnected_iUnion ⟨b₀, mem_iInter.mpr fun i => Or.inr hb₀⟩ h4
  · exact fun i x hx => mem_iUnion.mpr ⟨i, .inl (.inr hx)⟩
  · exact iUnion_subset fun i => union_subset (union_subset (h3 i) (hs i)) (hs i₀)
  · exact isThin_iUnion fun i => isThin_union (isThin_union (h1 i) (isThin_of_isOArc (hB i)))
      (isThin_of_isOArc (hB i₀))

/-- A candidate for `α(G')` gives a candidate for `α(G)` with no more vertices, when `G'` is `G`
with the inside of a disc removed.
The disc has a `G`-normal boundary with at most one vertex. -/
theorem exists_candidate_of_prune (hS : IsSurface S) [ConnectedSpace S]
  (hns : ¬ IsSphere S) {G G' : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hF : G.IsNormal (discBd Δ)) (hone : (G.V ∩ discBd Δ).Subsingleton)
    (hU : G.U \ discInt Δ ⊆ G'.U) (hV : G'.V ⊆ G.V) {X' : Set S} (hX' : IsAlphaCandidate G' X') :
    ∃ X : Set S, IsAlphaCandidate G X ∧ X ∩ G.V ⊆ X' ∩ G'.V := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨hsol, hcon, hnorm, hnear⟩ := hX'
  have : Finite (cuffs S) := (cuff_statement.{u} S hS).2.1.to_subtype
  choose A hA hAX f hfr hobs using exists_obstructions hS hns hsol hnear
  obtain ⟨X₀, hX₀s, hX₀c, hAX₀, hX₀X, hthin⟩ :=
    exists_solid_join hS (i₀ := (none : Option (cuffs S))) (isPathConnected_of_solid hS hsol hcon)
      hA hAX
  have hX₀cl : IsClosed X₀ := hX₀s.2
  obtain ⟨h, g, cc⟩ := hΔ.exists_isChart
  have hint := hΔ.isOpen_discInt hman
  -- Choose the centre of the projection.
  have hcentre : ∃ c : ℂ, ‖c‖ < 1 ∧ g c ∉ X₀ ∧ ∀ y ∈ X₀, ∀ v ∈ G.V ∩ discBd Δ, v ∉ X₀ → y ∈ Δ →
      g (mobius (-c) (mobius c (h y) / (‖mobius c (h y)‖ : ℂ))) ≠ v := by
    by_cases hv : ∃ v ∈ G.V ∩ discBd Δ, v ∉ X₀
    · obtain ⟨v, hv, hvX⟩ := hv
      obtain ⟨c, hc, hgc, hpre⟩ := exists_centre_near cc hv.2 hX₀cl.isOpen_compl hvX
      refine ⟨c, hc, hgc, fun y hy v' hv' _ hyD he => ?_⟩
      have hvv : v' = v := hone hv' hv
      subst hvv
      have hne : h y ≠ c := fun hc' => hgc (by rw [← hc', cc.gh hyD]; exact hy)
      refine hpre y hyD hne ?_ hy
      have hvD := Surface.discBd_subset _ hv.2
      have hsp : ‖mobius c (h y) / (‖mobius c (h y)‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div]
        simp only [Complex.norm_real, norm_norm]
        exact div_self_le_one _
      have hmem : mobius (-c) (mobius c (h y) / (‖mobius c (h y)‖ : ℂ)) ∈ closedBall (0 : ℂ) 1 :=
        mem_closedBall_zero_iff.mpr (norm_mobius_le (by simpa using hc) hsp)
      rw [← he, cc.hg hmem, mobius_mobius_neg hc hsp]
    · push Not at hv
      obtain ⟨𝓛, hf, hl, hsub⟩ := hthin
      obtain ⟨p, hp, hpoff⟩ := exists_mem_discInt_off hS hΔ hf hl
      have hpn : ‖h p‖ < 1 := by
        have h1 : ‖h p‖ ≤ 1 := mem_closedBall_zero_iff.mp (cc.hm hp.1)
        refine lt_of_le_of_ne h1 fun he => hp.2 ?_
        have h2 : h p ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr he
        rw [← cc.bd] at h2
        obtain ⟨z, hz, hze⟩ := h2
        have h3 := cc.gh (Surface.discBd_subset _ hz)
        rw [hze, cc.gh hp.1] at h3
        rwa [h3]
      refine ⟨h p, hpn, ?_, fun y _ v hv' hvX => absurd (hv v hv') hvX⟩
      rw [cc.gh hp.1]
      exact fun hc => hpoff (hsub hc)
  obtain ⟨c, hc, hcX, hmiss⟩ := hcentre
  obtain ⟨R, hRc, hR0, hRoff, hRin, hRform⟩ := exists_disc_push hΔ hint hX₀cl cc hc hcX
  let m : S → S := fun y => R (1, y)
  have hmc : ContinuousOn m X₀ := hRc.comp (by fun_prop) fun y hy => ⟨mem_univ _, hy⟩
  have hYp : IsPathConnected (m '' X₀) := (isPathConnected_of_solid hS hX₀s hX₀c).image' hmc
  -- The image of each `O`-arc is homotopic to it.
  have hB : ∀ i, ∃ B : Set S, IsOArc B ∧ B ⊆ m '' X₀ ∧
      ((i = none ∧ ¬ IsPlanar B) ∨ ∃ C : cuffs S, i = some C ∧ ¬ IsPlanarInCappedCuff C.1 B) := by
    intro i
    have hfX : ∀ w, f i w ∈ X₀ := fun w => hAX₀ i (hfr i ▸ mem_range_self w)
    have hHc : Continuous fun q : Circle × 𝕀 => R (q.2, f i q.1) :=
      hRc.comp_continuous (by fun_prop) fun q => ⟨mem_univ _, hfX q.1⟩
    let ψ : C(Circle, S) := ⟨fun w => R (1, f i w), hHc.comp (by fun_prop : Continuous fun w :
      Circle => (w, (1 : 𝕀)))⟩
    have hψ : ClosedCurvesHomotopicIn univ (f i) ψ :=
      ⟨⟨_, hHc⟩, fun _ => mem_univ _, fun x => hR0 _, fun x => rfl⟩
    obtain ⟨B, hB, hBr, hBo⟩ := hobs i ψ hψ
    refine ⟨B, hB, hBr.trans ?_, hBo⟩
    rintro _ ⟨w, rfl⟩
    exact ⟨f i w, hfX w, rfl⟩
  choose B hBo hBY hBn using hB
  obtain ⟨X, hXs, hXc, hBX, hXY, -⟩ := exists_solid_join hS (i₀ := (none : Option
    (cuffs S))) hYp hBo hBY
  -- Points of the image in `G`.
  have hkey : ∀ y ∈ X₀, m y ∈ G.U → m y ∈ X₀ ∧ m y ∈ G'.V := by
    intro y hy hU'
    by_cases hi : y ∈ discInt Δ
    · have hb := hRin y hy hi
      have hmv : m y ∈ G.V := hF ⟨hb, hU'⟩
      have hvX : m y ∈ X₀ := by
        by_contra hn
        exact hmiss y hy _ ⟨hmv, hb⟩ hn hi.1 (hRform y hy hi.1).symm
      have hoff : m y ∉ discInt Δ := fun h' => h'.2 hb
      exact ⟨hvX, hnorm ⟨hX₀X hvX, hU ⟨hU', hoff⟩⟩⟩
    · have he : m y = y := hRoff y hy hi
      rw [he] at hU' ⊢
      exact ⟨hy, hnorm ⟨hX₀X hy, hU ⟨hU', hi⟩⟩⟩
  refine ⟨X, ⟨hXs, hXc, ?_, ?_⟩, ?_⟩
  · rintro x ⟨hxX, hxU⟩
    obtain ⟨y, hy, rfl⟩ := hXY hxX
    exact hV (hkey y hy hxU).2
  · rintro (hp | ⟨C, hC, hp⟩)
    · rcases hBn none with ⟨-, h1⟩ | ⟨C, h1, -⟩
      · exact h1 (IsPlanar.mono hp (hBX none))
      · cases h1
    · rcases hBn (some ⟨C, hC⟩) with ⟨h1, -⟩ | ⟨C', h1, h2⟩
      · cases h1
      · have h3 : (⟨C, hC⟩ : cuffs S) = C' := Option.some.inj h1
        subst h3
        exact h2 (IsPlanarInCappedCuff.mono hp (hBX _))
  · rintro x ⟨hxX, hxV⟩
    obtain ⟨y, hy, rfl⟩ := hXY hxX
    have := hkey y hy (G.V_subset_U hxV)
    exact ⟨hX₀X this.1, this.2⟩

end GraphMinor.GM07
