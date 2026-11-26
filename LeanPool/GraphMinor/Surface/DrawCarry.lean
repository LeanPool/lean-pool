/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs
public import LeanPool.GraphMinor.GM19.FragmentOuter
public import LeanPool.GraphMinor.GM16.Tower
public import LeanPool.GraphMinor.Surface.DiscRemove

/-!
# A drawing carries over to a less simple surface

We show that a graph drawn in `Σ(a, b, c)` can be drawn in `Σ(a', b', c')` whenever `a ≤ a'` and `b
≤ b'` (`canBeDrawn_of_le`).
Graph Minors XVII states this without proof, at the end of the proof of (13.4) (page 207).

The route has three steps. Pasting discs on the cuffs embeds `Σ(a, b, c)` in `Σ(a, b, 0)`. A drawing
is a nowhere dense closed set, so
we can remove the interiors of as many discs as we like and keep the drawing off the boundary. This
gives a drawing in `Σ(a, b, m)`
that misses `bd Σ(a, b, m)`. Finally we paste some of the cuffs of `Σ(a, b, m)`, in the plain way
given by the models. The result
is injective off the cuffs, so the drawing survives.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function GraphMinor.GM17 GraphMinor.GM20.Draw

variable {α' β' : Type*} {H : Hypergraph α' β'}

/-- A drawing of `H` in `S` that stays in the set `K`. -/
def DrawnOn {S : Type*} [TopologicalSpace S] (H : Hypergraph α' β') (K : Set S) : Prop :=
  ∃ (ν : α' → S) (edgeOf : β' → Set S), InjOn ν H.vertexSet ∧
    (∀ e ∈ H.edgeSet, ∀ u v, H.Inc e u → H.Inc e v → u ≠ v → IsLineWithEnds (edgeOf e) (ν u) (ν v))
      ∧
    (∀ e ∈ H.edgeSet, ∀ v, H.ends e = {v} → IsOArc (edgeOf e) ∧ ν v ∈ edgeOf e) ∧
    (∀ e ∈ H.edgeSet, ∀ f ∈ H.edgeSet, e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' H.vertexSet) ∧
    (∀ e ∈ H.edgeSet, ∀ v ∈ H.vertexSet, ν v ∈ edgeOf e → H.Inc e v) ∧
    (∀ v ∈ H.vertexSet, ν v ∈ K) ∧ ∀ e ∈ H.edgeSet, edgeOf e ⊆ K

/-- A map that is an embedding on `K` carries a drawing on `K` to one on the image of `K`. -/
theorem DrawnOn.map {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] {K : Set S} {j : S → T}
  (hj : IsEmbedding (K.domRestrict j))
    (h : DrawnOn H K) : DrawnOn H (j '' K) := by
  obtain ⟨ν, F, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  have hinj : InjOn j K := fun x hx y hy he => by
    have := @hj.injective ⟨x, hx⟩ ⟨y, hy⟩ he
    exact congrArg Subtype.val this
  have hsub : ∀ {L : Set S}, L ⊆ K → IsEmbedding (fun x : L => j x.1) := fun {L} hL => hj.comp
    (IsEmbedding.inclusion hL)
  have hrange : ∀ {L : Set S}, L ⊆ K → range (fun x : L => j x.1) = j '' L := fun {L} _ => by
    ext y
    simp [eq_comm]
  have hhomeo : ∀ {L : Set S}, L ⊆ K → ∃ g : L ≃ₜ (j '' L), ∀ x, (g x).1 = j x.1 := fun {L} hL =>
    ⟨(hsub hL).toHomeomorph.trans (Homeomorph.setCongr (hrange hL)), fun _ => rfl⟩
  refine ⟨j ∘ ν, fun e => j '' F e, ?_, ?_, ?_, ?_, ?_, fun v hv => mem_image_of_mem _ (h₆ v hv),
    fun e he => image_mono (h₇ e he)⟩
  · exact hinj.comp h₁ h₆
  · intro e he u v hu hv huv
    obtain ⟨f, hf0, hf1⟩ := h₂ e he u v hu hv huv
    obtain ⟨g, hg⟩ := hhomeo (h₇ e he)
    exact ⟨f.trans g, by simp [hg, hf0], by simp [hg, hf1]⟩
  · intro e he v hv
    obtain ⟨⟨f⟩, h₈⟩ := h₃ e he v hv
    obtain ⟨g, -⟩ := hhomeo (h₇ e he)
    exact ⟨⟨f.trans g⟩, mem_image_of_mem _ h₈⟩
  · rintro e he f hf hef _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    obtain rfl := hinj (h₇ f hf hy) (h₇ e he hx) hxy
    obtain ⟨v, hv, rfl⟩ := h₄ e he f hf hef ⟨hx, hy⟩
    exact ⟨v, hv, rfl⟩
  · rintro e he v hv ⟨x, hx, hxv⟩
    obtain rfl := hinj (h₇ e he hx) (h₆ v hv) hxv
    exact h₅ e he v hv hx

theorem canBeDrawn_iff {S : Type} [TopologicalSpace S] : CanBeDrawn S H ↔ DrawnOn H (univ : Set S)
  := by
  constructor
  · rintro ⟨ν, F, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨ν, F, h₁, h₂, h₃, h₄, h₅, fun _ _ => mem_univ _, fun _ _ => subset_univ _⟩
  · rintro ⟨ν, F, h₁, h₂, h₃, h₄, h₅, -, -⟩
    exact ⟨ν, F, h₁, h₂, h₃, h₄, h₅⟩

theorem DrawnOn.canBeDrawn {S : Type} [TopologicalSpace S] {K : Set S}
  (h : DrawnOn H K) : CanBeDrawn S H := by
  obtain ⟨ν, F, h₁, h₂, h₃, h₄, h₅, -, -⟩ := h
  exact ⟨ν, F, h₁, h₂, h₃, h₄, h₅⟩

/-- An embedding carries a drawing to a drawing. -/
theorem CanBeDrawn.of_isEmbedding {S T : Type} [TopologicalSpace S] [TopologicalSpace T] {j : S
  → T} (hj : IsEmbedding j)
    (h : CanBeDrawn S H) : CanBeDrawn T H :=
  (DrawnOn.map (K := univ) (j := j) (hj.comp IsEmbedding.subtypeVal) (canBeDrawn_iff.1
    h)).canBeDrawn

/-! ### Discs in a surface -/

/-- A closed disc inside any open set around an interior point. -/
theorem exists_disc_in {S : Type} [TopologicalSpace S] {y : S} (hy : IsInteriorPoint y) {W : Set S}
  (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ D, IsClosedDisc D ∧ D ⊆ W := by
  obtain ⟨U, h, g, c, hU, -⟩ := hy.exists_ballChart hW hyW (R := 2) (by norm_num)
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 2 := Metric.closedBall_subset_ball
    (by norm_num)
  have hD : IsClosedDisc (Metric.closedBall (0 : ℂ) 1) := (isClosedDisc_of_convex
    (convex_closedBall 0 1) (by
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨0, by simp⟩) Metric.isBounded_closedBall Metric.isClosed_closedBall).1
  refine ⟨_, (c.image_disc hD hsub).1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hU (c.gm (hsub hz))

/-- A finite drawing of a graph is a closed set with dense complement, in a closed surface. -/
theorem exists_nowhere_dense (hH : H.IsGraph) {T : Type} [TopologicalSpace T]
  (hT : IsClosedSurface T) (h : CanBeDrawn T H) :
    ∃ K : Set T, IsCompact K ∧ Dense Kᶜ ∧ DrawnOn H K := by
  classical
  have : T2Space T := hT.isSurface.2.1
  have : CompactSpace T := hT.isSurface.1
  obtain ⟨ν, F, h₁, h₂, h₃, h₄, h₅⟩ := h
  let Good : Set T → Prop := fun K => IsClosed K ∧ Dense Kᶜ
  have hunion : ∀ {A B : Set T}, Good A → Good B → Good (A ∪ B) := fun {A B} hA hB => by
    refine ⟨hA.1.union hB.1, ?_⟩
    rw [compl_union]
    exact hA.2.inter_of_isOpen_left hB.2 hA.1.isOpen_compl
  have hline : ∀ {L : Set T} {a b : T}, IsLineWithEnds L a b → Good L := fun {L a b} hl => by
    obtain ⟨f, -, -⟩ := id hl
    have hc : IsCompact L := by
      exact isCompact_iff_compactSpace.mpr (f.surjective.compactSpace f.continuous)
    refine ⟨hc.isClosed, fun x => ?_⟩
    by_cases hx : x ∈ L
    · exact GM19.line_subset_closure_compl hT hl hx
    · exact subset_closure hx
  have hedge : ∀ e ∈ H.edgeSet, Good (F e) := by
    intro e he
    obtain ⟨⟨u, hu⟩, hle⟩ := hH e he
    by_cases hv : H.ends e = {u}
    · obtain ⟨hF, hm⟩ := h₃ e he u hv
      obtain ⟨φ⟩ := id hF
      have hne : (φ 1).1 ≠ (φ (-1)).1 := fun h => by
        have := φ.injective (Subtype.ext h)
        have h' := congrArg (fun z : Circle => (z : ℂ)) this
        norm_num at h'
      obtain ⟨A, B, hA, hB, hu', -⟩ := hF.lines (φ 1).2 (φ (-1)).2 hne
      rw [← hu']
      exact hunion (hline hA) (hline hB)
    · obtain ⟨w, hw, hwu⟩ : ∃ w ∈ H.ends e, w ≠ u := by
        by_contra hn
        push Not at hn
        exact hv (Subset.antisymm (fun w hw => hn w hw) (singleton_subset_iff.2 hu))
      exact hline (h₂ e he u w hu hw hwu.symm)
  have hV : Good (ν '' H.vertexSet) := by
    have hfin := H.vertexSet_finite.image ν
    exact ⟨hfin.isClosed, GM19.dense_compl_finite hT.2.2 hfin⟩
  have hE : Good (⋃ e ∈ H.edgeSet, F e) := by
    have hfin := H.edgeSet_finite
    have hempty : Good (∅ : Set T) := ⟨isClosed_empty, by simp⟩
    refine Set.Finite.induction_on_subset (motive := fun E _ => Good (⋃ e ∈ E,
      F e)) _ hfin (by simpa using hempty) ?_
    intro e E he _ _ hG
    rw [biUnion_insert]
    exact hunion (hedge e he) hG
  have hK := hunion hV hE
  refine ⟨_, hK.1.isCompact, hK.2, ν, F, h₁, h₂, h₃, h₄, h₅, fun v hv => .inl
    (mem_image_of_mem _ hv), fun e he => ?_⟩
  exact (subset_biUnion_of_mem (u := F) he).trans subset_union_right

/-- Removing the interior of a small disc off a drawing gives one more cuff, and the drawing stays
off the boundary. -/
theorem remove_step {Y : Type} [TopologicalSpace Y] [ConnectedSpace Y]
  (hY : IsSurface Y) {a b m : ℕ} (e : Y ≃ₜ SurfaceModel a b m)
    {K : Set Y} (hKc : IsCompact K) (hKd : Dense Kᶜ) (hKb : Disjoint K (bd Y)) (hD : DrawnOn H K) :
    ∃ K' : Set (SurfaceModel a b (m + 1)), IsCompact K' ∧ Dense K'ᶜ ∧ Disjoint K' (bd
      (SurfaceModel a b (m + 1))) ∧ DrawnOn H K' := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have hbc := isClosed_bd Y
  have hW : IsOpen (Kᶜ ∩ (bd Y)ᶜ) := hKc.isClosed.isOpen_compl.inter hbc.isOpen_compl
  obtain ⟨x, hxb, hxK⟩ := hKd.inter_open_nonempty (bd Y)ᶜ hbc.isOpen_compl
    (GM19.dense_interior' hY).nonempty
  have hx : IsInteriorPoint x := by
    by_contra h
    exact hxb h
  obtain ⟨E, hE, hEW⟩ := exists_disc_in hx hW ⟨hxK, hxb⟩
  have hdE : discBd E ⊆ E := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hint : ∀ z ∈ discBd E, IsInteriorPoint z := fun z hz => by
    by_contra h
    exact (hEW (hdE hz)).2 h
  obtain ⟨hcl, hXs, hXb⟩ := remove_disc hY hE hint
  set X : Set Y := (discInt E)ᶜ with hX
  have hdeq : E ∩ X = discBd E := by
    ext z
    simp only [hX, discInt, mem_inter_iff, mem_compl_iff, mem_sdiff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨hdE h, fun _ => h⟩⟩
  have hO : IsOArc (discBd E) := hE.isOArc_discBd
  have hnb : (discBd E).Nonempty := by
    obtain ⟨φ⟩ := hO
    exact ⟨_, (φ 1).2⟩
  have hXne : X.Nonempty := ⟨_, by
    rw [hX]
    exact fun h => h.2 hnb.some_mem⟩
  have hEc : IsClosed E := by
    obtain ⟨d⟩ := id hE
    exact (isCompact_iff_compactSpace.mpr (d.surjective.compactSpace d.continuous)).isClosed
  have hconn : ConnectedSpace ↥X := connected_compl hcl hXne (𝓖 := {E}) (finite_singleton _)
    (by rintro _ rfl; exact hEc)
    (by rintro _ rfl; rw [hdeq]; exact hO.isConnected'.isPreconnected)
    (by rintro _ rfl; rw [hdeq]; exact hnb)
    (by rintro G rfl G' rfl h; exact absurd rfl h)
    (by
      simp only [sUnion_singleton]
      ext z
      by_cases hz : z ∈ discInt E
      · exact ⟨fun _ => mem_univ _, fun _ => .inr hz.1⟩
      · exact ⟨fun _ => mem_univ _, fun _ => .inl hz⟩)
  obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification.{0} ↥X hXs hconn
  have hval : IsClosedEmbedding (Subtype.val : X → Y) := hcl.isClosedEmbedding_subtypeVal
  have hiC : (Subtype.val : X → Y) '' (Subtype.val ⁻¹' discBd E) = discBd E := by
    rw [Subtype.image_preimage_coe, inter_comm, ← hdeq, inter_assoc, inter_self]
  set C : Set ↥X := Subtype.val ⁻¹' discBd E with hC
  have hCc : IsPreconnected C := by
    have hie : (Subtype.val : X → Y) '' C = discBd E := hiC
    rw [← hval.isInducing.isPreconnected_image, hie]
    exact hO.isConnected'.isPreconnected
  obtain ⟨z₀, hz₀⟩ : C.Nonempty := by
    obtain ⟨z, hz⟩ := hnb
    rw [← hiC] at hz
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨w, hw⟩
  have hCb : C ⊆ bd ↥X := fun z hz => by
    rw [hXb]
    exact .inr hz
  have hcuff : IsCuff C := by
    refine ⟨z₀, hCb hz₀, Subset.antisymm ?_ (hCc.subset_connectedComponentIn hz₀ hCb)⟩
    have hp : IsPreconnected (connectedComponentIn (bd ↥X) z₀) :=
      isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn (bd ↥X) z₀ ⊆ bd ↥X := connectedComponentIn_subset _ _
    have h₁ : IsClosed (Subtype.val ⁻¹' E : Set ↥X) := hEc.preimage continuous_subtype_val
    have h₂ : IsClosed (Subtype.val ⁻¹' bd Y : Set ↥X) := hbc.preimage continuous_subtype_val
    have hdisj : ∀ z : ↥X, z.1 ∈ E → z.1 ∉ bd Y := fun z hz hb => (hEW hz).2 hb
    intro z hz
    by_contra hzC
    obtain ⟨w, -, hw₁, hw₂⟩ := isPreconnected_closed_iff.1 hp _ _ h₁ h₂
      (fun u hu => by
        have := hsub hu
        rw [hXb] at this
        exact this.elim .inr fun h => .inl (hdE h))
      ⟨z₀, mem_connectedComponentIn (hCb hz₀), hdE hz₀⟩
      ⟨z, hz, by
        have := hsub hz
        rw [hXb] at this
        exact this.elim id fun h => absurd h hzC⟩
    exact hdisj w hw₁ hw₂
  have hu : range (Subtype.val : X → Y) ∪ E = univ := by
    rw [Subtype.range_coe]
    ext z
    by_cases hz : z ∈ E
    · exact ⟨fun _ => mem_univ _, fun _ => .inr hz⟩
    · exact ⟨fun _ => mem_univ _, fun _ => .inl fun h => hz h.1⟩
  have hm : range (Subtype.val : X → Y) ∩ E = (Subtype.val : X → Y) '' C := by
    rw [Subtype.range_coe, inter_comm, hdeq]
    exact hiC.symm
  obtain ⟨hc₁, ⟨e₂⟩⟩ := paste_model hXs hcuff hY hval hE hu hm hiC.symm e₁
  obtain ⟨h₁, h₂, h₃⟩ := (modelCriterion.2 a₁ b₁ (c₁ - 1) a b m).mp ⟨e₂.symm.trans e⟩
  obtain ⟨g'⟩ := (modelCriterion.2 a₁ b₁ c₁ a b (m + 1)).mpr ⟨by omega, h₂, h₃⟩
  let g : ↥X ≃ₜ SurfaceModel a b (m + 1) := e₁.trans g'
  have hKX : K ⊆ X := fun z hz hi => (hEW hi.1).1 hz
  have hj : IsEmbedding (K.domRestrict fun y => if h : y ∈ X then g ⟨y, h⟩ else g ⟨z₀.1, z₀.2⟩)
    := by
    have : (K.domRestrict fun y => if h : y ∈ X then g ⟨y, h⟩ else g ⟨z₀.1, z₀.2⟩)
      = g ∘ inclusion hKX := by
      funext z
      simp [domRestrict, hKX z.2, inclusion]
    rw [this]
    exact g.isEmbedding.comp (IsEmbedding.inclusion hKX)
  set j : Y → SurfaceModel a b (m + 1) := fun y => if h : y ∈ X then g ⟨y, h⟩ else g ⟨z₀.1, z₀.2⟩
    with hjdef
  have him : j '' K = g '' (Subtype.val ⁻¹' K) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hKX hy⟩, hy, by simp [hjdef, hKX hy]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, by simp [hjdef]⟩
  refine ⟨j '' K, ?_, ?_, ?_, hD.map hj⟩
  · rw [image_eq_range]
    have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKc
    exact isCompact_range hj.continuous
  · rw [him, ← g.image_compl]
    refine g.surjective.denseRange.dense_image g.continuous ?_
    rw [← interior_eq_empty_iff_dense_compl, eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp (isOpen_interior (s :=
      (Subtype.val ⁻¹' K : Set ↥X)))
    have hoff : V ∩ Eᶜ ⊆ K := fun y hy => by
      have hyX : y ∈ X := fun hi => hy.2 hi.1
      have hm : (⟨y, hyX⟩ : ↥X) ∈ interior (Subtype.val ⁻¹' K : Set ↥X) := by
        rw [← hVe]
        exact hy.1
      exact (interior_subset hm : (⟨y, hyX⟩ : ↥X) ∈ (Subtype.val ⁻¹' K : Set ↥X))
    have huV : u.1 ∈ V := by
      have : u ∈ Subtype.val ⁻¹' V := by
        rw [hVe]
        exact hu
      exact this
    have huE : u.1 ∉ E := fun h => (hEW h).1 (interior_subset hu : u ∈ (Subtype.val ⁻¹' K : Set ↥X))
    obtain ⟨y, hy, hyK⟩ := hKd.inter_open_nonempty _ (hV.inter hEc.isOpen_compl) ⟨u.1, huV, huE⟩
    exact hyK (hoff hy)
  · rw [him, Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hb
    have hb' : y ∈ bd ↥X := by
      rw [← image_bd_homeomorph g] at hb
      obtain ⟨w, hw, he⟩ := hb
      exact g.injective he ▸ hw
    rw [hXb] at hb'
    rcases hb' with h | h
    · exact Set.disjoint_left.mp hKb hy h
    · exact (hEW (hdE h)).1 hy

/-! ### The maps between models -/

/-- The points of the circles with index from `m` up to `n`. -/
def holePts (m n : ℕ) : Set (OnePoint EuclideanPlane) :=
  {p | ∃ i, m ≤ i ∧ i < n ∧ ∃ u : EuclideanPlane, ‖u‖ = 1 ∧ p = ((modelCentre i + u :
    EuclideanPlane) : OnePoint EuclideanPlane)}

theorem norm_modelMirror (u : EuclideanPlane) : ‖modelMirror u‖ = ‖u‖ := by
  have h₁ : ‖modelMirror u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    simp [modelMirror]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h₁

theorem not_mem_holePts {j m n : ℕ} (hj : j < m) {u : EuclideanPlane} (hu : ‖u‖ = 1) :
    ((modelCentre j + u : EuclideanPlane) : OnePoint EuclideanPlane) ∉ holePts m n := by
  rintro ⟨i, hi, -, v, hv, he⟩
  have he' : modelCentre j + u = modelCentre i + v := OnePoint.coe_injective he
  refine modelCentre_dist (i := j) (j := i) (x := modelCentre j + u) (by omega)
    (by simpa using hu) ?_
  rw [he']
  simpa using hv

theorem glue_not_mem {a b n : ℕ} {p q : modelBase n} (h : ModelGlue a b n p q) : p.1 ∉ holePts
  (2 * a + b) n ∧ q.1 ∉ holePts (2 * a + b) n := by
  cases h with
  | handle i hi u hu p q hp hq =>
    rw [hp, hq]
    exact ⟨not_mem_holePts (by omega) hu, not_mem_holePts (by omega) (by rw [norm_modelMirror, hu])⟩
  | crosscap i hi u hu p q hp hq =>
    rw [hp, hq, sub_eq_add_neg]
    exact ⟨not_mem_holePts (by omega) hu, not_mem_holePts (by omega) (by rw [norm_neg, hu])⟩

theorem eq_of_eqv_hole {a b n : ℕ} {p q : modelBase n} (h : Relation.EqvGen (ModelGlue a b n) p q) :
    (p.1 ∈ holePts (2 * a + b) n ∨ q.1 ∈ holePts (2 * a + b) n) → p = q := by
  induction h with
  | rel p q h =>
    obtain ⟨h₁, h₂⟩ := glue_not_mem h
    rintro (h | h)
    · exact absurd h h₁
    · exact absurd h h₂
  | refl p => exact fun _ => rfl
  | symm p q _ ih => exact fun h => (ih h.symm).symm
  | trans p q r _ _ ih₁ ih₂ =>
    rintro (h | h)
    · obtain rfl := ih₁ (.inl h)
      exact ih₂ (.inl h)
    · obtain rfl := ih₂ (.inr h)
      exact ih₁ (.inr h)

/-- The two shapes of the pair `(a, b)`, `(a', b')` that we use: handles and cross-caps are kept in
place by the order of the circles. -/
def Keeps (a b a' b' : ℕ) : Prop := (a = a' ∧ b ≤ b') ∨ (b = 0 ∧ a ≤ a')

theorem glue_mono {a b a' b' n : ℕ} (hk : Keeps a b a' b') {p q : modelBase n}
  (h : ModelGlue a b n p q) : ModelGlue a' b' n p q := by
  cases h with
  | handle i hi u hu p q hp hq =>
    have : i < a' := by rcases hk with ⟨h, -⟩ | ⟨-, h⟩ <;> omega
    exact .handle i this u hu p q hp hq
  | crosscap i hi u hu p q hp hq =>
    rcases hk with ⟨rfl, h⟩ | ⟨rfl, -⟩
    · exact .crosscap i (by omega) u hu p q hp hq
    · omega

theorem glue_back {a b a' b' n : ℕ} (hk : Keeps a b a' b') (hn : 2 * a' + b'
  ≤ n) {p q : modelBase n} (h : ModelGlue a' b' n p q) :
    ModelGlue a b n p q ∨ (p.1 ∈ holePts (2 * a + b) n ∧ q.1 ∈ holePts (2 * a + b) n) := by
  cases h with
  | handle i hi u hu p q hp hq =>
    by_cases hia : i < a
    · exact .inl (.handle i hia u hu p q hp hq)
    · have hb : b = 0 := by rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      exact .inr ⟨⟨2 * i, by omega, by omega, u, hu, hp⟩, ⟨2 * i + 1, by omega, by omega, _,
        by rw [norm_modelMirror, hu], hq⟩⟩
  | crosscap i hi u hu p q hp hq =>
    have hq' :
        q.1 = ((modelCentre (2 * a' + i) + -u : EuclideanPlane) : OnePoint EuclideanPlane) := by
      rw [hq, sub_eq_add_neg]
    by_cases hc : a = a' ∧ i < b
    · obtain ⟨rfl, hib⟩ := hc
      exact .inl (.crosscap i hib u hu p q hp hq)
    · have hge : 2 * a + b ≤ 2 * a' + i := by rcases hk with ⟨h, -⟩ | ⟨h, h'⟩ <;> omega
      exact .inr ⟨⟨_, hge, by omega, u, hu, hp⟩, ⟨_, hge, by omega, -u, by rw [norm_neg, hu], hq'⟩⟩

theorem eqv_back {a b a' b' n : ℕ} (hk : Keeps a b a' b') (hn : 2 * a' + b'
  ≤ n) {p q : modelBase n} (h : Relation.EqvGen (ModelGlue a' b' n) p q) :
    Relation.EqvGen (ModelGlue a b n) p q ∨ (p.1 ∈ holePts (2 * a + b) n ∧ q.1 ∈ holePts
      (2 * a + b) n) := by
  induction h with
  | rel p q h =>
    rcases glue_back hk hn h with h | h
    · exact .inl (.rel _ _ h)
    · exact .inr h
  | refl p => exact .inl (.refl _)
  | symm p q _ ih =>
    rcases ih with h | h
    · exact .inl (.symm _ _ h)
    · exact .inr h.symm
  | trans p q r _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁
    · rcases ih₂ with h₂ | h₂
      · exact .inl (.trans _ _ _ h₁ h₂)
      · obtain rfl := eq_of_eqv_hole h₁ (.inr h₂.1)
        exact .inr h₂
    · rcases ih₂ with h₂ | h₂
      · obtain rfl := eq_of_eqv_hole h₂ (.inl h₁.2)
        exact .inr h₁
      · exact .inr ⟨h₁.1, h₂.2⟩

/-- The map between the quotients of the same sphere with holes, and what it glues. -/
theorem exists_quot_map {a b a' b' n₁ n₂ : ℕ} (h : n₁ = n₂) (hk : Keeps a b a' b')
  (hn : 2 * a' + b' ≤ n₂) :
    ∃ φ : Quot (ModelGlue a b n₁) → Quot (ModelGlue a' b' n₂), Continuous φ
      ∧ ∀ p q : modelBase n₁, φ (Quot.mk _ p) = φ (Quot.mk _ q) →
      Quot.mk (ModelGlue a b n₁) p = Quot.mk _ q ∨ (p.1 ∈ holePts (2 * a + b) n₁ ∧ q.1 ∈ holePts
        (2 * a + b) n₁) := by
  subst h
  refine ⟨Quot.lift (Quot.mk _) fun p q r => Quot.sound (glue_mono hk r),
    continuous_quot_lift _ continuous_quot_mk, fun p q he => ?_⟩
  rcases eqv_back hk hn (Quot.eqvGen_exact he) with h | h
  · exact .inl (Quot.eqvGen_sound h)
  · exact .inr h

/-- The points of the circles that are not pasted are boundary points. -/
theorem qq_circle_mem_bd {a b c I : ℕ} (hI : 2 * a + b ≤ I) (hI' : I < 2 * a + b + c) {w : ℂ}
  (hw : ‖w‖ = 1) :
    qq a b c (cp (cz I + w)) ∈ bd (SurfaceModel a b c) := by
  have hB : ∀ ζ ∈ Metric.ball (cz I + w) (1 / 2), ‖ζ - cz I‖ < 3 / 2 := fun ζ hζ ↦ by
    have h₁ : ‖ζ - (cz I + w)‖ < 1 / 2 := by simpa [dist_eq_norm] using hζ
    have h₂ : ζ - cz I = (ζ - (cz I + w)) + w := by ring
    rw [h₂]
    have h₃ := norm_add_le (ζ - (cz I + w)) w
    rw [hw] at h₃
    linarith
  have hj := isOpenEmbedding_chart (a := a) (b := b) (c := c) (B := Metric.ball (cz I + w) (1 / 2))
    Metric.isOpen_ball fun ζ hζ _ ↦ free_near hI (by linarith [hB ζ hζ])
  have hok : Ok a b c (cp (cz I + w)) := by
    have hre : (cp (cz I + w)) = (3 * (I : ℝ) + w.re, w.im) := by simp [cp, cz]
    rw [hre]
    refine ok_circle ?_
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have hw' : cz I + w ∈ chartDom a b c (Metric.ball (cz I + w) (1 / 2)) := ⟨Metric.mem_ball_self
    (by norm_num), hok⟩
  have h₁ := not_interior_of_chart hj ⟨_, hw'⟩ ?_
  · exact h₁
  · intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set t : ℝ := min ε 1 / 2 with ht
    have ht₀ : 0 < t := by positivity
    have ht₁ : t ≤ 1 / 2 := by
      have := min_le_right ε 1
      rw [ht]
      linarith
    have ht₂ : t < ε := by
      have := min_le_left ε 1
      rw [ht]
      linarith [lt_min hε one_pos]
    have hmem : cz I + w - (t : ℂ) * w ∈ Metric.ball (cz I + w) ε := by
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, hw,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀, mul_one]
      exact ht₂
    have hok' := (hball hmem).2 I hI'
    change 1 ≤ ((cp _).1 - 3 * (I : ℝ)) ^ 2 + (cp _).2 ^ 2 at hok'
    rw [← nsq] at hok'
    have h₂ : cz I + w - (t : ℂ) * w - cz I = ((1 - t : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [h₂, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hok'
    nlinarith

theorem hole_mem_bd {a b c : ℕ} (p : modelBase (2 * a + b + c)) (hp : p.1 ∈ holePts (2 * a + b)
  (2 * a + b + c)) :
    (Quot.mk _ p : SurfaceModel a b c) ∈ bd (SurfaceModel a b c) := by
  obtain ⟨I, hI, hI', u, hu, he⟩ := hp
  have hw : ‖(⟨u 0, u 1⟩ : ℂ)‖ = 1 := by
    have h₁ : ‖(⟨u 0, u 1⟩ : ℂ)‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq, Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hu] at h₁
    nlinarith [norm_nonneg (⟨u 0, u 1⟩ : ℂ)]
  have h := qq_circle_mem_bd hI hI' hw
  have hz : cp (cz I + ⟨u 0, u 1⟩) = (3 * (I : ℝ) + u 0, u 1) := by simp [cp, cz]
  have hok : Ok a b c (cp (cz I + ⟨u 0, u 1⟩)) := by
    rw [hz]
    refine ok_circle ?_
    have := norm_sq u
    rw [hu] at this
    linarith
  rw [qq_of_ok hok] at h
  have hpt : p = ⟨_, mem_base hok⟩ := by
    apply Subtype.ext
    rw [he]
    congr 1
    ext i
    fin_cases i <;> simp [pl, modelCentre, hz]
  rw [hpt]
  exact h

/-- A drawing off the boundary carries over to any model that pastes more of the circles. -/
theorem canBeDrawn_of_keeps {a b c a' b' c' : ℕ} (hn : 2 * a + b + c = 2 * a' + b' + c')
  (hk : Keeps a b a' b') {K : Set (SurfaceModel a b c)}
    (hKc : IsCompact K) (hKb : Disjoint K (bd (SurfaceModel a b c))) (hD : DrawnOn H K) :
      CanBeDrawn (SurfaceModel a' b' c') H := by
  obtain ⟨φ, hφ, hinj⟩ := exists_quot_map (a := a) (b := b) (a' := a') (b' := b') hn hk (by omega)
  let φ' : SurfaceModel a b c → SurfaceModel a' b' c' := φ
  have hφ' : Continuous φ' := hφ
  have := (isSurface_model a' b' c').1.2.1
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKc
  have hi : Injective (K.domRestrict φ') := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ he
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    rcases hinj p q he with h | h
    · exact Subtype.ext h
    · exact absurd (hole_mem_bd p h.1) (Set.disjoint_left.mp hKb hx)
  have hj : IsEmbedding (K.domRestrict φ') := (hφ'.comp continuous_subtype_val).isClosedEmbedding
    hi |>.isEmbedding
  exact (hD.map hj).canBeDrawn

/-- Pasting discs on all the cuffs keeps a drawing. -/
theorem canBeDrawn_cap {a b c : ℕ} (h : CanBeDrawn (SurfaceModel a b c) H) : CanBeDrawn
  (SurfaceModel a b 0) H := by
  induction c with
  | zero => exact h
  | succ c ih =>
    refine ih ?_
    have hS := (isSurface_model a b (c + 1)).1
    have := hS.2.1
    obtain ⟨ht, f, hf⟩ := presents_ew a b (c + 1)
    have h1 := ncard_cuffs hf
    obtain ⟨C, hC⟩ := nonempty_of_ncard_ne_zero (s := cuffs (SurfaceModel a b (c + 1))) (by omega)
    obtain ⟨S', _, ι, Δ, hS', hι, hΔ, hu, hm, hb, -⟩ := paste_disc.{0} _ C hS hC
    obtain ⟨-, ⟨e⟩⟩ := paste_model hS hC hS' hι hΔ hu hm hb (Homeomorph.refl _)
    exact CanBeDrawn.of_isEmbedding (e.isEmbedding.comp hι.isEmbedding) h

/-- The closed model is a closed surface. -/
theorem isClosedSurface_model (a b : ℕ) : IsClosedSurface (SurfaceModel a b 0) := by
  have hS := (isSurface_model a b 0).1
  refine ⟨hS.1, hS.2.1, fun x => ?_⟩
  by_contra h
  have h₁ : x ∈ bd (SurfaceModel a b 0) := h
  rw [GM16.bd_model] at h₁
  exact h₁

/-- A drawing in the closed model gives a drawing off the boundary, in the model with `m` cuffs. -/
theorem drawn_off_bd (hH : H.IsGraph) {a b : ℕ} (h : CanBeDrawn (SurfaceModel a b 0) H) (m : ℕ) :
    ∃ K : Set (SurfaceModel a b m), IsCompact K ∧ Dense Kᶜ ∧ Disjoint K (bd (SurfaceModel a b m))
      ∧ DrawnOn H K := by
  induction m with
  | zero =>
    have := (isSurface_model a b 0).2
    obtain ⟨K, h₁, h₂, h₃⟩ := exists_nowhere_dense hH (isClosedSurface_model a b) h
    refine ⟨K, h₁, h₂, ?_, h₃⟩
    rw [GM16.bd_model]
    exact disjoint_empty _
  | succ m ih =>
    obtain ⟨K, h₁, h₂, h₃, h₄⟩ := ih
    have := (isSurface_model a b m).2
    exact remove_step (isSurface_model a b m).1 (Homeomorph.refl _) h₁ h₂ h₃ h₄

/-- **A drawing carries over.** If `a ≤ a'` and `b ≤ b'`, a graph drawn in `Σ(a, b, c)` can be drawn
in `Σ(a', b', c')`. If `b = 0` we
paste handles, then cross-caps. If `b > 0` we write `Σ(a', b', c')` with `a` handles, by the model
criterion, and paste only cross-caps. -/
theorem canBeDrawn_of_le (hH : H.IsGraph) {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
  (h : CanBeDrawn (SurfaceModel a b c) H) :
    CanBeDrawn (SurfaceModel a' b' c') H := by
  have h₀ := canBeDrawn_cap h
  by_cases hb₀ : b = 0
  · subst hb₀
    obtain ⟨K, h₁, -, h₃, h₄⟩ := drawn_off_bd hH h₀ (2 * a' + b' + c' - 2 * a)
    exact canBeDrawn_of_keeps (by omega) (.inr ⟨rfl, ha⟩) h₁ h₃ h₄
  · obtain ⟨K, h₁, -, h₃, h₄⟩ := drawn_off_bd hH h₀ (b' + 2 * (a' - a) + c' - b)
    have hd := canBeDrawn_of_keeps (a' := a) (b' := b' + 2 * (a' - a)) (c' := c')
      (by omega) (.inl ⟨rfl, by omega⟩) h₁ h₃ h₄
    obtain ⟨f⟩ := (modelCriterion.2 a (b' + 2 * (a' - a)) c' a' b' c').mpr ⟨rfl, by omega, by omega⟩
    exact GM20.Draw.CanBeDrawn.map f hd

/-- A graph drawn in a surface can be drawn in any surface that the first is simpler than. -/
theorem IsSimplerThan.canBeDrawn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (hs : IsSimplerThan X Y) (hH : H.IsGraph) (h : CanBeDrawn X H) :
    CanBeDrawn Y H := by
  obtain ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, h₁, h₂, -⟩ := hs
  exact GM20.Draw.CanBeDrawn.map e'.symm (canBeDrawn_of_le hH h₁ h₂ (GM20.Draw.CanBeDrawn.map e h))

end GraphMinor.Surface
