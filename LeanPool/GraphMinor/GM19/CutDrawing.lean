/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutArc
public import LeanPool.GraphMinor.Surface.CutChain
public import LeanPool.GraphMinor.Surface.CutEdges
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# Cutting along several edges of a word

`WordEdges.cut_space` cuts along a set `D` of edges and asks that at most two ends of edges of `D`
meet at a
vertex off the boundary, and only one on the boundary. XIX needs more. It cuts along an `O`-arc that
meets a
cuff in one point, and along circuits joined by a path. Here three points of the cut surface lie
over a
vertex. The word is the same, so `WordEdges.cut_edges` drops the condition. It keeps it only where
it is
needed, which is to tell the two lifts of an edge apart at the ends of that edge.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {W : ℕ → List Letter} {f : ℕ × ℂ
  → S} {V : Set S}
  {E : Set (Set S)} {A : Set S → unitInterval → S} {lab : Set S → ℕ}

/-- At the end `τ` of the edge `e`, the edges of `D` look like those of a line: either one other
edge of `D`
ends there, off the boundary, or no other end of an edge of `D` is there, and the point is on the
boundary. -/
def EndFine (A : Set S → unitInterval → S) (D : Set (Set S)) (e : Set S) (τ : Bool) : Prop :=
  (∃ e' ∈ D, ∃ τ', e' ≠ e ∧ extI (A e') (eo τ') = extI (A e) (eo τ) ∧ extI (A e) (eo τ) ∉ bd S ∧
    ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → (e'' = e ∧ τ'' = τ) ∨ (e'' = e'
      ∧ τ'' = τ')) ∨
  (extI (A e) (eo τ) ∈ bd S ∧ ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A e) (eo τ) → e'' = e
    ∧ τ'' = τ)

/-- Two lifts `r`, `r'` of the edge `a` to the boundary of `Y`. They differ on the open edge and
fill it, and
they do so at an end of the edge if `hend` holds there. -/
def IsEdgeLift {Y : Type u} [TopologicalSpace Y] (ψ : Y → S) (a : ℝ → S) (hend : Bool → Prop)
  (r r' : ℝ → Y) :
    Prop :=
  ContinuousOn r (Icc 0 1) ∧ ContinuousOn r' (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, ψ (r t) = a t ∧ ψ
    (r' t) = a t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, r t ∈ bd Y ∧ r' t ∈ bd Y) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, (t ∈ Ioo (0 : ℝ) 1 ∨ ∃ τ, eo τ = t ∧ hend τ) →
      r t ≠ r' t ∧ ∀ z, ψ z = a t → z = r t ∨ z = r' t)

/-- The cut surface over the union of a set `D` of edges of a word. Each edge has two lifts. -/
theorem WordEdges.cut_edges (h : WordEdges W f V E A lab) {D : Set (Set S)} (hD : D ⊆ E)
    (hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂)
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {g : ℕ × ℂ → Y} (hg : Presents (cutW W
      (lab '' D)) g) :
    ∃ ψ : Y → S, Continuous ψ ∧ Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ D)ᶜ) ∧ IsSurface Y ∧
      (∀ a ∈ Dsk W, ψ (g a) = f a) ∧ (∀ z : Y, ∃ a ∈ Dsk W, g a = z) ∧
      ∀ e ∈ D, ∃ r r', IsEdgeLift ψ (extI (A e)) (EndFine A D e) r r' := by
  classical
  set L := lab '' D with hL
  have hP := h.paired
  have hfW' : FinW (cutW W L) := finW_cut h.fin
  have hP' : IsPaired (cutW W L) := isPaired_cut hP
  obtain ⟨hsurf, hbdY⟩ := surface_of_presents hfW' hP' hg
  have hD' : Dsk (cutW W L) = Dsk W := dsk_cut
  obtain ⟨ψ, hψc, hψ⟩ := exists_descend hfW' hg (hD' ▸ h.pres.1) (fun a ha b hb hab =>
    (h.pres.2.2 a (hD' ▸ ha) b (hD' ▸ hb)).mpr (prel_of_prel_cut hab))
  rw [hD'] at hψ
  have hrep : ∀ z : Y, ∃ a ∈ Dsk W, g a = z := fun z => by
    have hz : z ∈ g '' Dsk (cutW W L) := hg.2.1 ▸ mem_univ z
    rwa [hD'] at hz
  have hgeq : ∀ {a b}, a ∈ Dsk W → b ∈ Dsk W → (g a = g b ↔ PRel (cutW W L) a b) := fun {a b} ha hb
    =>
    hg.2.2 a (hD' ▸ ha) b (hD' ▸ hb)
  have hkey : ∀ e ∈ D, ∃ r r', IsEdgeLift ψ (extI (A e)) (EndFine A D e) r r' := by
    intro e heD
    have heE := hD heD
    obtain ⟨i, p, j, q, e₁, e₂, s⟩ := hsd e heD
    have hL0 : lab e ∈ L := ⟨e, heD, rfl⟩
    have hv := fun τ (hτ : EndFine A D e τ) => h.vertex_cut hD heD hsd s τ hτ
    have hp := lt_length s.one
    have hq := lt_length s.two
    let r : ℝ → Y := fun t => g (spt W i p (ofs e₁ t))
    let r' : ℝ → Y := fun t => g (spt W j q (ofs e₂ t))
    have hm1 : ∀ t, spt W i p (ofs e₁ t) ∈ Dsk W := fun t => spt_mem hp _
    have hm2 : ∀ t, spt W j q (ofs e₂ t) ∈ Dsk W := fun t => spt_mem hq _
    have hrc : ContinuousOn r (Icc 0 1) :=
      hg.1.comp (continuous_spt_ofs W i p e₁).continuousOn fun t _ => hD' ▸ hm1 t
    have hrc' : ContinuousOn r' (Icc 0 1) :=
      hg.1.comp (continuous_spt_ofs W j q e₂).continuousOn fun t _ => hD' ▸ hm2 t
    have hr : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r t) = extI (A e) t := fun t ht => by
      simp only [r]
      rw [hψ _ (hm1 t), h.f_side heE s.one (ofs_mem ht), ofs_ofs]
    have hr' : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r' t) = extI (A e) t := fun t ht => by
      simp only [r']
      rw [hψ _ (hm2 t), h.f_side heE s.two (ofs_mem ht), ofs_ofs]
    have hspe : ∀ τ, spe W (s.end₁ τ) = spt W i p (ofs e₁ (eo τ)) := fun τ
      => by simp only [spe, EdgeSides.end₁, eo_xn]
    have hspe' : ∀ τ, spe W (s.end₂ τ) = spt W j q (ofs e₂ (eo τ)) := fun τ
      => by simp only [spe, EdgeSides.end₂, eo_xn]
    have hneO : ∀ t ∈ Ioo (0 : ℝ) 1, r t ≠ r' t := by
      intro t ht' he
      have hpr := (hgeq (hm1 t) (hm2 t)).mp he
      have hu := ofs_Ioo e₁ ht'
      have hl' : (cutW W L i)[p]? = some (2 * Nat.pair i p + 1, e₁) := cut_get_iff.mpr ⟨_, s.one,
        .inl ⟨hL0, rfl⟩⟩
      have hpr' : PRel (cutW W L) (spt (cutW W L) i p (ofs e₁ t)) (spt W j q (ofs e₂ t)) := by
        rw [spt_cut]
        exact hpr
      have hfree := freeSide_cut (L := L) s.one hL0
      have heqs : spt W j q (ofs e₂ t) = spt W i p (ofs e₁ t) := by
        rcases hpr'.eq_or_stp hP' hl' hu with h1 | h1
        · rw [h1, spt_cut]
        · exfalso
          obtain ⟨j', q', e', h2, h3, -⟩ := stp_of_side hP' hl' hu h1
          exact h3 (hfree _ _ _ _ _ hl' h2)
      have h1 : j = i := congrArg Prod.fst heqs
      subst h1
      have h2 : per (W j).length (q + ofs e₂ t) = per (W j).length (p + ofs e₁ t)
        := congrArg Prod.snd heqs
      obtain ⟨h3, -⟩ := side_unique hq hp (ofs_Ioo e₂ ht') (ofs_mem (Ioo_subset_Icc_self ht')) h2
      exact s.ne (by rw [h3])
    have hfillO : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z, ψ z = extI (A e) t → z = r t ∨ z = r' t := by
      intro t ht' z hzt
      obtain ⟨a, ha, rfl⟩ := hrep z
      rw [hψ a ha] at hzt
      have ht := Ioo_subset_Icc_self ht'
      have hu := ofs_Ioo e₁ ht'
      have hfx : f (spt W i p (ofs e₁ t)) = f a := by
        rw [h.f_side heE s.one (ofs_mem ht), ofs_ofs, hzt]
      have hpr := (h.pres.2.2 _ (hm1 t) _ ha).mp hfx
      rcases hpr.eq_or_stp hP s.one hu with h1 | h1
      · exact .inl (by simp only [r]; rw [h1])
      · obtain ⟨j', q', e', h2, h3, h4⟩ := stp_of_side hP s.one hu h1
        rcases hP.third s.one s.two h2 s.ne with h5 | h5
        · exact absurd h5.symm h3
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
          have he' : e' = e₂ := by
            rw [s.two] at h2
            simpa using h2.symm
          subst he'
          refine .inr ?_
          simp only [r']
          rw [h4, flp_ofs]
    have hbdr : ∀ t ∈ Icc (0 : ℝ) 1, r t ∈ bd Y ∧ r' t ∈ bd Y := by
      intro t ht
      constructor
      · rw [hbdY]
        refine ⟨spt W i p (ofs e₁ t), ⟨i, p, ofs e₁ t, ?_, freeSide_cut s.one hL0, ofs_mem ht,
          (spt_cut _ _ _).symm⟩, rfl⟩
        rw [cutW_length]
        exact hp
      · rw [hbdY]
        refine ⟨spt W j q (ofs e₂ t), ⟨j, q, ofs e₂ t, ?_, freeSide_cut s.two hL0, ofs_mem ht,
          (spt_cut _ _ _).symm⟩, rfl⟩
        rw [cutW_length]
        exact hq
    refine ⟨r, r', hrc, hrc', fun t ht => ⟨hr t ht, hr' t ht⟩, hbdr, ?_⟩
    rintro t ht (ht' | ⟨τ, rfl, hτ⟩)
    · exact ⟨hneO t ht', hfillO t ht'⟩
    · refine ⟨fun he => ?_, fun z hzt => ?_⟩
      · have hpr := (hgeq (hm1 _) (hm2 _)).mp he
        rw [← hspe, ← hspe'] at hpr
        exact (hv τ hτ).1 hpr
      · obtain ⟨a, ha, rfl⟩ := hrep z
        rw [hψ a ha] at hzt
        rcases (hv τ hτ).2 a ha hzt with h1 | h1
        · have := (hgeq (spe_mem _) ha).mpr h1
          rw [hspe] at this
          exact .inl this.symm
        · have := (hgeq (spe_mem _) ha).mpr h1
          rw [hspe'] at this
          exact .inr this.symm
  have hoff : ∀ a b, PRel W a b → f a = f b ∧ (f a ∉ ⋃₀ D → PRel (cutW W L) a b) := by
    intro a b hab
    induction hab with
    | rel a b hs =>
      have hfe := presents_eq_of_stp h.pres hs
      refine ⟨hfe, fun hF => ?_⟩
      obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, rfl, rfl⟩ := stp_iff.mp hs
      refine .rel _ _ (stp_to_cut h1 h2 h3 hu fun hk => ?_)
      obtain ⟨e'', he'', rfl⟩ := hk
      exact hF ⟨e'', he'', by
        rw [h.f_side (hD he'') h1 hu]
        exact h.extI_mem (hD he'') _⟩
    | refl _ => exact ⟨rfl, fun _ => .refl _⟩
    | symm a b _ ih => exact ⟨ih.1.symm, fun hF => .symm _ _ (ih.2 (ih.1 ▸ hF))⟩
    | trans a b c _ _ h1 h2 => exact ⟨h1.1.trans h2.1, fun hF => .trans _ _ _ (h1.2 hF) (h2.2
      (h1.1 ▸ hF))⟩
  refine ⟨ψ, hψc, ?_, ?_, hsurf, hψ, hrep, hkey⟩
  · intro x
    obtain ⟨a, ha, rfl⟩ : x ∈ f '' Dsk W := h.pres.2.1 ▸ mem_univ x
    exact ⟨g a, hψ a ha⟩
  · intro z hz z' hz' he
    obtain ⟨a, ha, rfl⟩ := hrep z
    obtain ⟨b, hb, rfl⟩ := hrep z'
    have h1 : f a = f b := by rw [← hψ a ha, ← hψ b hb, he]
    have h2 : f a ∉ ⋃₀ D := fun h3 => hz (by
      show ψ (g a) ∈ ⋃₀ D
      rw [hψ a ha]
      exact h3)
    exact (hgeq ha hb).mpr ((hoff a b ((h.pres.2.2 a ha b hb).mp h1)).2 h2)

omit [T2Space S] in
/-- A map into a surface, injective on a neighbourhood of an interior point, maps that neighbourhood
to a
neighbourhood of the image, by invariance of domain. The image point may be on the boundary at the
start,
and the lemma then says that it is not. -/
theorem image_mem_nhds_of_injOn {Y : Type*} [TopologicalSpace Y] {ψ : Y → S} {z : Y}
  (hz : IsInteriorPoint z)
    (hm : IsManifoldPoint (ψ z)) (hψ : Continuous ψ) {U : Set Y} (hU : IsOpen U) (hzU : z ∈ U)
      (hinj : InjOn ψ U) :
    ψ '' U ∈ 𝓝 (ψ z) := by
  obtain ⟨C, O, hC, -, hzC, ⟨c⟩⟩ := hm
  obtain ⟨U', hU', hzU', hsub, ⟨e⟩⟩ := hz.exists_subset (hU.inter (hC.preimage hψ)) ⟨hzU, hzC⟩
  have : Nonempty Y := ⟨z⟩
  have : Nonempty S := ⟨ψ z⟩
  have : Nonempty (EuclideanHalfSpace 2) := ⟨(c ⟨ψ z, hzC⟩).1⟩
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  obtain ⟨a, a', h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (b.trans e.symm)
  obtain ⟨k, k', h1', h2', h3', h4', h5', h6'⟩ := exists_functions_of_homeomorph c
  let j : S → ℂ := fun x ↦ complexPlane.symm (k x).1
  have hjc : ContinuousOn j C := complexPlane.symm.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn h1')
  have hji : InjOn j C := fun x hx y hy he ↦
    h5'.injOn hx hy (Subtype.ext (complexPlane.symm.injective he))
  have hGc : ContinuousOn (j ∘ ψ ∘ a) (Metric.ball (0 : ℂ) 1) :=
    hjc.comp (hψ.comp_continuousOn h1) fun w hw ↦ (hsub (h3 hw)).2
  have hGi : InjOn (j ∘ ψ ∘ a) (Metric.ball (0 : ℂ) 1) := fun w hw w' hw' he ↦
    h5.injOn hw hw' (hinj (hsub (h3 hw)).1 (hsub (h3 hw')).1
      (hji (hsub (h3 hw)).2 (hsub (h3 hw')).2 he))
  have hopen := isOpen_image_of_injOn Metric.isOpen_ball hGc hGi
  have hO : IsOpen (C ∩ j ⁻¹' ((j ∘ ψ ∘ a) '' Metric.ball (0 : ℂ) 1)) :=
    hjc.isOpen_inter_preimage hC hopen
  refine Filter.mem_of_superset (hO.mem_nhds ⟨hzC, a' z, h4 hzU', ?_⟩) ?_
  · change j (ψ (a (a' z))) = j (ψ z)
    rw [h6 hzU']
  · rintro y ⟨hyC, w, hw, he⟩
    exact ⟨a w, (hsub (h3 hw)).1, hji (hsub (h3 hw)).2 hyC he⟩

omit [T2Space S] in
/-- A point of `V` on an edge has finitely many points of the polygons over it, which are corners.
-/
theorem WordEdges.subset_range_spe (h : WordEdges W f V E A lab) {a : ℕ × ℂ} (ha : a ∈ Dsk W)
  (hV : f a ∈ V)
    (hE : f a ∈ ⋃₀ E) : a ∈ range (spe W) := by
  obtain ⟨p, e', e, he, u, hu, h1, h2, h3⟩ := h.exists_side ha hE
  have hp : p < (W a.1).length := by
    by_contra hn
    rw [List.getElem?_eq_none (not_lt.mp hn)] at h1
    simp at h1
  have hu01 : u = 0 ∨ u = 1 := by
    by_contra hn
    push Not at hn
    have hI : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hn.1), lt_of_le_of_ne hu.2 hn.2⟩
    exact h.extI_notMem he (ofs_Ioo e' hI) (h3 ▸ hV)
  rcases hu01 with rfl | rfl
  · exact ⟨⟨(a.1, p, false), hp⟩, by simpa [spe, eo] using h2.symm⟩
  · exact ⟨⟨(a.1, p, true), hp⟩, by simpa [spe, eo] using h2.symm⟩

omit [T2Space S] in
/-- A point of an edge is a point of the open edge or an end. -/
theorem WordEdges.exists_param (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E) {x : S}
  (hx : x ∈ e) :
    ∃ t ∈ Icc (0 : ℝ) 1, extI (A e) t = x ∧ (t ∈ Ioo (0 : ℝ) 1 ∨ ∃ τ, eo τ = t) := by
  have hr : extI (A e) '' Icc 0 1 = e := by rw [image_extI, (h.arc e he).2.1]
  obtain ⟨t, ht, rfl⟩ := hr.symm ▸ hx
  refine ⟨t, ht, rfl, ?_⟩
  by_cases h0 : t = 0
  · exact .inr ⟨false, by simp [eo, h0]⟩
  by_cases h1 : t = 1
  · exact .inr ⟨true, by simp [eo, h1]⟩
  exact .inl ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩

/-- **Cutting along a set of edges.** No condition at the vertices is needed. The fibres are finite,
and the
whole lift of the edges lies in the boundary. Off the ends, by invariance of domain, an interior
point over a
vertex would have a neighbourhood mapped onto a neighbourhood of that vertex, but the edge at the
vertex comes
near it, and only boundary points lie over the open edge. -/
theorem WordEdges.exists_cut (h : WordEdges W f V E A lab) (hS : IsSurface S) (hne :
  (Dsk W).Nonempty)
    {D : Set (Set S)} (hD : D ⊆ E) (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S), IsSurface Y ∧ Continuous ψ
      ∧
      Function.Surjective ψ ∧ InjOn ψ (ψ ⁻¹' (⋃₀ D)ᶜ) ∧ (∀ x, (ψ ⁻¹' {x}).Finite) ∧ ψ ⁻¹'
        (⋃₀ D) ⊆ bd Y ∧
      ∀ e ∈ D, ∃ r r', IsEdgeLift ψ (extI (A e)) (EndFine A D e) r r' := by
  classical
  have hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂
    := fun e he ↦ by
    obtain ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩ := h.exists_sides (hD he) (hmid e he)
    exact ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩
  obtain ⟨Y, tY, t2, g, hg⟩ := exists_cut_presented.{u} (W := cutW W (lab '' D)) (finW_cut h.fin)
    (isPaired_cut h.paired) (by rw [dsk_cut]; exact hne)
  obtain ⟨ψ, h1, h2, h3, h4, hψ, hrep, hlift⟩ := WordEdges.cut_edges h hD hsd hg
  have : Finite (SE W) := finite_se h.fin
  have hfinV : ∀ v ∈ V ∩ ⋃₀ E, (ψ ⁻¹' {v}).Finite := fun v hv ↦ by
    refine ((finite_range (spe W)).image g).subset ?_
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hrep z
    have hfa : f a = v := by rw [← hψ a ha]; exact hz
    exact ⟨a, WordEdges.subset_range_spe h ha (hfa ▸ hv.1) (hfa ▸ hv.2), rfl⟩
  have hfin : ∀ x, (ψ ⁻¹' {x}).Finite := fun x ↦ by
    by_cases hx : x ∈ ⋃₀ D
    · obtain ⟨e, he, hxe⟩ := hx
      by_cases hxV : x ∈ V
      · exact hfinV x ⟨hxV, e, hD he, hxe⟩
      obtain ⟨t, ht, rfl, hc⟩ := WordEdges.exists_param h (hD he) hxe
      obtain ⟨r, r', -, -, -, -, hf⟩ := hlift e he
      have hI : t ∈ Ioo (0 : ℝ) 1 := hc.resolve_right (by
        rintro ⟨τ, rfl⟩
        exact hxV (h.extI_mem_V (hD he) τ))
      refine (Set.toFinite {r t, r' t}).subset fun z hz ↦ ?_
      exact (hf t ht (.inl hI)).2 z hz
    · have hoff : ∀ {z}, z ∈ ψ ⁻¹' {x} → z ∈ ψ ⁻¹' (⋃₀ D)ᶜ := fun {z} hz ↦ by
        change ψ z ∉ ⋃₀ D
        rw [show ψ z = x from hz]
        exact hx
      exact Set.Subsingleton.finite fun z hz z' hz' ↦ h3 (hoff hz) (hoff hz') (hz.trans hz'.symm)
  refine ⟨Y, tY, t2, ψ, h4, h1, h2, h3, hfin, ?_, hlift⟩
  rintro z ⟨e, he, hze⟩
  by_contra hz
  have hzi : IsInteriorPoint z := not_not.mp hz
  have hend : ∀ {w t e'}, e' ∈ D → t ∈ Ioo (0 : ℝ) 1 → ψ w = extI (A e') t → w ∈ bd Y
    := fun {w t e'} he' ht hw ↦ by
    obtain ⟨r, r', -, -, -, hb, hf⟩ := hlift e' he'
    have hI := Ioo_subset_Icc_self ht
    rcases (hf t hI (.inl ht)).2 w hw with rfl | rfl
    · exact (hb t hI).1
    · exact (hb t hI).2
  obtain ⟨t, ht, hte, hc⟩ := WordEdges.exists_param h (hD he) hze
  obtain ⟨τ, rfl⟩ : ∃ τ, eo τ = t := hc.resolve_left fun hI ↦ hz (hend he hI hte.symm)
  let P : Set Y := ψ ⁻¹' (V ∩ ⋃₀ E)
  have hP : P.Finite := by
    have : P = ⋃ v ∈ V ∩ ⋃₀ E, ψ ⁻¹' {v} := by
      ext w
      simp [P]
    rw [this]
    exact (h.graph.fin.subset inter_subset_left).biUnion fun v _ ↦ hfin v
  let U : Set Y := (bd Y)ᶜ ∩ (P \ {z})ᶜ
  have hUo : IsOpen U := (isClosed_bd Y).isOpen_compl.inter (hP.subset
    sdiff_subset).isClosed.isOpen_compl
  have hzU : z ∈ U := ⟨hz, fun hc ↦ hc.2 rfl⟩
  have key : ∀ w ∈ U, ψ w ∈ ⋃₀ D → w = z := by
    rintro w hw ⟨e', he', hwe⟩
    obtain ⟨t', ht', hte', hc'⟩ := WordEdges.exists_param h (hD he') hwe
    obtain ⟨τ', rfl⟩ : ∃ τ', eo τ' = t' := hc'.resolve_left fun hI ↦ hw.1 (hend he' hI hte'.symm)
    by_contra hne'
    exact hw.2 ⟨⟨hte' ▸ h.extI_mem_V (hD he') τ', e', hD he', hwe⟩, hne'⟩
  have hinj : InjOn ψ U := by
    intro a ha b hb hab
    by_cases hD' : ψ a ∈ ⋃₀ D
    · rw [key a ha hD', key b hb (hab ▸ hD')]
    · exact h3 hD' (show ψ b ∉ ⋃₀ D from hab ▸ hD') hab
  have hN := image_mem_nhds_of_injOn hzi (hS.2.2 (ψ z)) h1 hUo hzU hinj
  have hN' : extI (A e) ⁻¹' (ψ '' U) ∈ 𝓝 (eo τ) :=
    (continuous_extI (h.arc e (hD he)).1.1).continuousAt.preimage_mem_nhds (hte ▸ hN)
  have hcl : eo τ ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (zero_ne_one' ℝ)]
    exact eo_mem τ
  obtain ⟨t', ht'N, ht'I⟩ := mem_closure_iff_nhds.mp hcl _ hN'
  obtain ⟨w, hw, he'⟩ := ht'N
  exact hw.1 (hend he ht'I he')

end GraphMinor.GM19
