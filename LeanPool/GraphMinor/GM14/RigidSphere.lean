/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidWheel
public import LeanPool.GraphMinor.GM14.Whitney
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# (6.4) on a sphere

Here is the core of the paper's proof of (6.4) (page 34). Let `D₁` and `D₂` be the two closed discs
of a
sphere with common boundary `C`. Let `H₁` and `H₂` be drawings in `D₁` with the same vertices on
`C`, and
let `φ` be an isomorphism between them that fixes those vertices. If `H₁` is rigid in `D₁`, then `φ`
comes
from a homeomorphism of the sphere that keeps `D₁` and fixes `C`.

Add one wheel `W` in `D₂` to both drawings. By `good_of_wheel` and `good_sub`, the first union is a
subdivision of a simple 3-connected graph. Whitney's theorem (`whitney_fixing`) then gives a
homeomorphism
that fixes `W` pointwise. It keeps the sides of `C`, as it fixes `C` and the hub of the wheel.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Two unions with a wheel are isomorphic if the parts are, and the isomorphism fixes the wheel. -/
theorem exists_glueIso {H₁ H₂ W J₁ J₂ : Drawing S} (hu₁ : IsUnion H₁ W J₁) (hu₂ : IsUnion H₂ W J₂)
    (φ : Iso H₁.toGraph H₂.toGraph)
    (hfix : ∀ v : V(H₁.toGraph), v.1 ∈ W.V → (φ.vertexEquiv v).1 = v.1)
    (hfix' : ∀ v : V(H₂.toGraph), v.1 ∈ W.V → (φ.vertexEquiv.symm v).1 = v.1)
    (hd₁ : Disjoint H₁.E W.E) (hd₂ : Disjoint H₂.E W.E) :
    ∃ φ' : Iso J₁.toGraph J₂.toGraph,
      (∀ (v : V(J₁.toGraph)) (h : v.1 ∈ H₁.V), (φ'.vertexEquiv v).1 = (φ.vertexEquiv ⟨v.1, h⟩).1) ∧
      (∀ v : V(J₁.toGraph), v.1 ∈ W.V → (φ'.vertexEquiv v).1 = v.1) ∧
      (∀ (e : E(J₁.toGraph)) (h : e.1 ∈ H₁.E), (φ'.edgeEquiv e).1 = (φ.edgeEquiv ⟨e.1, h⟩).1) ∧
      (∀ e : E(J₁.toGraph), e.1 ∈ W.E → (φ'.edgeEquiv e).1 = e.1) := by
  classical
  let fv : S → S := fun v => if h : v ∈ H₁.V then (φ.vertexEquiv ⟨v, h⟩).1 else v
  let gv : S → S := fun v => if h : v ∈ H₂.V then (φ.vertexEquiv.symm ⟨v, h⟩).1 else v
  let fe : Set S → Set S := fun e => if h : e ∈ H₁.E then (φ.edgeEquiv ⟨e, h⟩).1 else e
  let ge : Set S → Set S := fun e => if h : e ∈ H₂.E then (φ.edgeEquiv.symm ⟨e, h⟩).1 else e
  have fv₁ : ∀ {v} (h : v ∈ H₁.V), fv v = (φ.vertexEquiv ⟨v, h⟩).1 := fun h => dite_eq_left h
  have fv₂ : ∀ {v}, v ∉ H₁.V → fv v = v := fun h => dite_eq_right h
  have gv₁ : ∀ {v} (h : v ∈ H₂.V), gv v = (φ.vertexEquiv.symm ⟨v, h⟩).1 := fun h => dite_eq_left h
  have gv₂ : ∀ {v}, v ∉ H₂.V → gv v = v := fun h => dite_eq_right h
  have fe₁ : ∀ {e} (h : e ∈ H₁.E), fe e = (φ.edgeEquiv ⟨e, h⟩).1 := fun h => dite_eq_left h
  have fe₂ : ∀ {e}, e ∉ H₁.E → fe e = e := fun h => dite_eq_right h
  have ge₁ : ∀ {e} (h : e ∈ H₂.E), ge e = (φ.edgeEquiv.symm ⟨e, h⟩).1 := fun h => dite_eq_left h
  have ge₂ : ∀ {e}, e ∉ H₂.E → ge e = e := fun h => dite_eq_right h
  have hfH : ∀ {v}, v ∈ H₁.V → fv v ∈ H₂.V := fun h => by
    rw [fv₁ h]
    exact (φ.vertexEquiv ⟨_, h⟩).2
  have hgH : ∀ {v}, v ∈ H₂.V → gv v ∈ H₁.V := fun h => by
    rw [gv₁ h]
    exact (φ.vertexEquiv.symm ⟨_, h⟩).2
  have hfW : ∀ {v}, v ∈ W.V → fv v = v := fun {v} h => by
    by_cases h₁ : v ∈ H₁.V
    · rw [fv₁ h₁]
      exact hfix ⟨v, h₁⟩ h
    · exact fv₂ h₁
  have hgW : ∀ {v}, v ∈ W.V → gv v = v := fun {v} h => by
    by_cases h₁ : v ∈ H₂.V
    · rw [gv₁ h₁]
      exact hfix' ⟨v, h₁⟩ h
    · exact gv₂ h₁
  have hgf : ∀ {v}, v ∈ J₁.V → gv (fv v) = v := fun {v} hv => by
    by_cases h₁ : v ∈ H₁.V
    · rw [gv₁ (hfH h₁)]
      simp [fv₁ h₁]
    · have hW : v ∈ W.V := by
        rw [hu₁.hV] at hv
        exact hv.resolve_left h₁
      rw [hfW hW, hgW hW]
  have hfg : ∀ {v}, v ∈ J₂.V → fv (gv v) = v := fun {v} hv => by
    by_cases h₁ : v ∈ H₂.V
    · rw [fv₁ (hgH h₁)]
      simp [gv₁ h₁]
    · have hW : v ∈ W.V := by
        rw [hu₂.hV] at hv
        exact hv.resolve_left h₁
      rw [hgW hW, hfW hW]
  have hfJ : ∀ {v}, v ∈ J₁.V → fv v ∈ J₂.V := fun {v} hv => by
    rw [hu₁.hV] at hv
    rw [hu₂.hV]
    rcases hv with h₁ | h₁
    · exact Or.inl (hfH h₁)
    · exact Or.inr (by rw [hfW h₁]; exact h₁)
  have hgJ : ∀ {v}, v ∈ J₂.V → gv v ∈ J₁.V := fun {v} hv => by
    rw [hu₂.hV] at hv
    rw [hu₁.hV]
    rcases hv with h₁ | h₁
    · exact Or.inl (hgH h₁)
    · exact Or.inr (by rw [hgW h₁]; exact h₁)
  have hfeH : ∀ {e}, e ∈ H₁.E → fe e ∈ H₂.E := fun h => by
    rw [fe₁ h]
    exact (φ.edgeEquiv ⟨_, h⟩).2
  have hgeH : ∀ {e}, e ∈ H₂.E → ge e ∈ H₁.E := fun h => by
    rw [ge₁ h]
    exact (φ.edgeEquiv.symm ⟨_, h⟩).2
  have hfeW : ∀ {e}, e ∈ W.E → fe e = e := fun h => fe₂ fun h₁ => disjoint_left.mp hd₁ h₁ h
  have hgeW : ∀ {e}, e ∈ W.E → ge e = e := fun h => ge₂ fun h₁ => disjoint_left.mp hd₂ h₁ h
  have hgfe : ∀ {e}, e ∈ J₁.E → ge (fe e) = e := fun {e} he => by
    have he' : e ∈ H₁.E ∪ W.E := hu₁.hE ▸ he
    rcases he' with h₁ | h₁
    · rw [ge₁ (hfeH h₁)]
      simp [fe₁ h₁]
    · rw [hfeW h₁, hgeW h₁]
  have hfge : ∀ {e}, e ∈ J₂.E → fe (ge e) = e := fun {e} he => by
    have he' : e ∈ H₂.E ∪ W.E := hu₂.hE ▸ he
    rcases he' with h₁ | h₁
    · rw [fe₁ (hgeH h₁)]
      simp [ge₁ h₁]
    · rw [hgeW h₁, hfeW h₁]
  have hfeJ : ∀ {e}, e ∈ J₁.E → fe e ∈ J₂.E := fun {e} he => by
    have he' : e ∈ H₁.E ∪ W.E := hu₁.hE ▸ he
    rw [hu₂.hE]
    rcases he' with h₁ | h₁
    · exact Or.inl (hfeH h₁)
    · exact Or.inr (by rw [hfeW h₁]; exact h₁)
  have hgeJ : ∀ {e}, e ∈ J₂.E → ge e ∈ J₁.E := fun {e} he => by
    have he' : e ∈ H₂.E ∪ W.E := hu₂.hE ▸ he
    rw [hu₁.hE]
    rcases he' with h₁ | h₁
    · exact Or.inl (hgeH h₁)
    · exact Or.inr (by rw [hgeW h₁]; exact h₁)
  -- If `f(x)` lies in the wheel, then `f(x) = x`.
  have hback : ∀ {x}, x ∈ J₁.V → fv x ∈ W.V → fv x = x := fun {x} hx hW => by
    have := hgf hx
    rw [hgW hW] at this
    exact this
  -- If `f(x)` lies in `H₂`, then `x` lies in `H₁`.
  have hbackH : ∀ {x}, x ∈ J₁.V → fv x ∈ H₂.V → x ∈ H₁.V := fun {x} hx hH => by
    have := hgH hH
    rwa [hgf hx] at this
  refine ⟨⟨⟨fun v => ⟨fv v.1, hfJ v.2⟩, fun v => ⟨gv v.1, hgJ v.2⟩,
    fun v => Subtype.ext (hgf v.2), fun v => Subtype.ext (hfg v.2)⟩,
    ⟨fun e => ⟨fe e.1, hfeJ e.2⟩, fun e => ⟨ge e.1, hgeJ e.2⟩,
    fun e => Subtype.ext (hgfe e.2), fun e => Subtype.ext (hfge e.2)⟩, ?_⟩,
    fun v h => fv₁ h, fun v h => hfW h, fun e h => fe₁ h, fun e h => hfeW h⟩
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  change J₁.toGraph.IsLink e x y ↔ J₂.toGraph.IsLink (fe e) (fv x) (fv y)
  have he' : e ∈ H₁.E ∪ W.E := hu₁.hE ▸ he
  rcases he' with h₁ | h₁
  · rw [hu₁.linkH e h₁ x y, hu₂.linkH _ (hfeH h₁)]
    constructor
    · intro hl
      have hxH : x ∈ H₁.V := hl.left_mem
      have hyH : y ∈ H₁.V := hl.right_mem
      rw [fe₁ h₁, fv₁ hxH, fv₁ hyH]
      exact (φ.isLink_iff ⟨e, h₁⟩ ⟨x, hxH⟩ ⟨y, hyH⟩).mp hl
    · intro hl
      have hxH : x ∈ H₁.V := hbackH hx hl.left_mem
      have hyH : y ∈ H₁.V := hbackH hy hl.right_mem
      rw [fe₁ h₁, fv₁ hxH, fv₁ hyH] at hl
      exact (φ.isLink_iff ⟨e, h₁⟩ ⟨x, hxH⟩ ⟨y, hyH⟩).mpr hl
  · rw [hfeW h₁, hu₁.linkW e h₁ x y, hu₂.linkW e h₁]
    constructor
    · intro hl
      rw [hfW hl.left_mem, hfW hl.right_mem]
      exact hl
    · intro hl
      have h₃ := hback hx hl.left_mem
      have h₄ := hback hy hl.right_mem
      rwa [h₃, h₄] at hl

omit [T2Space S] in
/-- A homeomorphism of the sphere that fixes the common boundary and a point off `D₁` keeps the
complement of `D₁`. -/
theorem image_compl_sub {D₁ D₂ C : Set S} (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂) (hcov : D₁ ∪ D₂
  = univ)
    (hC : D₁ ∩ D₂ = C) (hconn : IsPreconnected D₁ᶜ) {a : S} (ha : a ∉ D₁) (h : S ≃ₜ S)
    (hfix : ∀ x ∈ C, h x = x) (hfa : h a = a) : h '' D₁ᶜ ⊆ D₁ᶜ := by
  have hpre : IsPreconnected (h '' D₁ᶜ) := hconn.image h h.continuous.continuousOn
  refine hpre.subset_left_of_subset_union hc₁.isOpen_compl hc₂.isOpen_compl ?_ ?_ ?_
  · refine disjoint_left.mpr fun x h₁ h₂ => ?_
    have : x ∈ D₁ ∪ D₂ := hcov ▸ mem_univ x
    rcases this with h₃ | h₃
    · exact h₁ h₃
    · exact h₂ h₃
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hn
    have hC' : h x ∈ C := hC ▸ hn
    have : h (h x) = h x := hfix _ hC'
    have hxx : h x = x := h.injective this
    exact hx (hxx ▸ hn.1)
  · exact ⟨a, ⟨a, ha, hfa⟩, ha⟩

/-- A rigid drawing in `D₁`, with a wheel in `D₂`, gives a frame and a radial drawing. -/
theorem exists_frame [ConnectedSpace S] (hS : IsClosedSurface S) (hsph : IsSphere S)
    {D₁ D₂ C : Set S} (hd₁ : IsClosedDisc D₁) (hd₂ : IsClosedDisc D₂) (hb₁ : discBd D₁ = C)
    (hb₂ : discBd D₂ = C) (hcov : D₁ ∪ D₂ = univ) (hcap : D₁ ∩ D₂ = C) {H : Drawing S}
    (hU : H.U ⊆ D₁) (hn : H.U ∩ C ⊆ H.V) (hr : IsRigidIn H D₁) :
    ∃ (W : Drawing S) (a : S) (Γ' : Drawing S) (hm : H.U ∩ W.U ⊆ H.V ∩ W.V),
      Wheel W (H.V ∩ C) D₁ D₂ ∧ Frame H (H.glue W hm) D₁ a ∧ Rad (H.glue W hm) Γ' ∧ a ∈ W.V ∧
      a ∈ D₂ ∧ a ∉ D₁ ∧ IsPreconnected D₁ᶜ ∧ (∀ z ∈ W.V, z ≠ a → ∃ g, W.toGraph.IsLink g a z) := by
  classical
  have hsb : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hB : (H.V ∩ C).Finite := H.finite_V.subset inter_subset_left
  have hpd₁ : IsPreconnected D₁ := hd₁.isPathConnected.isConnected.isPreconnected
  have hCD₁ : discBd D₂ ⊆ D₁ := hb₂ ▸ hb₁ ▸ Surface.discBd_subset D₁
  obtain ⟨W, a, hw, haV, haD, hab, hVsub, hhub⟩ := exists_wheel hd₂ hB
    (inter_subset_right.trans hb₂.symm.subset) hpd₁ hCD₁
  have hm : H.U ∩ W.U ⊆ H.V ∩ W.V := by
    rintro z ⟨hz, hz'⟩
    have hzC : z ∈ C := hcap ▸ ⟨hU hz, hw.Usub hz'⟩
    have hzV : z ∈ H.V := hn ⟨hz, hzC⟩
    exact ⟨hzV, hw.BV ⟨hzV, hzC⟩⟩
  have hu : IsUnion H W (H.glue W hm) := isUnion_glue hm
  have hcompl : D₁ᶜ = D₂ \ frontier D₂ := by
    rw [IsClosedDisc.frontier_eq_discBd hS hd₂, hb₂]
    ext x
    constructor
    · intro hx
      have : x ∈ D₁ ∪ D₂ := hcov ▸ mem_univ x
      refine ⟨this.resolve_left hx, fun h₁ => hx ?_⟩
      rw [← hb₁] at h₁
      exact Surface.discBd_subset D₁ h₁
    · rintro ⟨h₁, h₂⟩ h₃
      exact h₂ (hcap ▸ ⟨h₃, h₁⟩)
  have hpre : IsPreconnected D₁ᶜ := hcompl ▸ IsClosedDisc.isPreconnected_diff_frontier hS hd₂
  have haD₁ : a ∉ D₁ := fun h₁ => hab (hb₂.symm ▸ hcap ▸ ⟨h₁, haD⟩)
  have hWsub : W.U ⊆ (H.glue W hm).U := subset_union_right
  have hCW : C ⊆ W.U := hb₂ ▸ hw.bdU
  have hf : Frame H (H.glue W hm) D₁ a := by
    refine ⟨hd₁, ?_, hU, ?_, subset_union_left, ?_, ?_, ?_, haD₁, hpre, hr⟩
    · rw [hsb]
      exact hCW.trans hWsub
    · rw [hsb]
      exact hn
    · exact fun e he => hu.hE ▸ Or.inl he
    · rintro z ⟨hz | hz, hzD, hzb⟩
      · exact hz
      · exact absurd (hsb ▸ hcap ▸ ⟨hzD, hw.Usub hz⟩) hzb
    · change IsPreconnected (D₁ ∪ (H.U ∪ W.U))
      rw [← union_assoc, union_eq_left.mpr hU]
      exact hw.hconn
  have hJE : (PaintingOrDrawing.drawing (H.glue W hm)).E.Nonempty := by
    obtain ⟨T, -, hT4, hT3⟩ := hw.four
    obtain ⟨t, ht⟩ : T.Nonempty := by
      refine nonempty_iff_ne_empty.mpr fun h₁ => ?_
      rw [h₁, ncard_empty] at hT4
      omega
    have h₃ := hT3 t ht
    obtain ⟨g, hg⟩ : {e | W.toGraph.Inc e t}.Nonempty := by
      refine nonempty_iff_ne_empty.mpr fun h₁ => ?_
      rw [h₁, ncard_empty] at h₃
      omega
    refine ⟨g, ?_⟩
    change g ∈ (H.glue W hm).E
    rw [hu.hE]
    exact Or.inr hg.edge_mem
  obtain ⟨Γ', hrad⟩ := exists_radialDrawing hS (hf.twoCell hS hsph)
  exact ⟨W, a, Γ', hm, hw, hf, ⟨hrad.2.1.1, hrad.2.1.2.1, regionFacts_any hS hJE hrad⟩, haV, haD,
    haD₁,
    hpre, hhub⟩

/-- **(6.4) on a sphere.** -/
theorem sphere_core [ConnectedSpace S] (hSurf : IsSurface S) (hS : IsClosedSurface S)
  (hsph : IsSphere S)
    {D₁ D₂ C : Set S} (hd₁ : IsClosedDisc D₁) (hd₂ : IsClosedDisc D₂) (hb₁ : discBd D₁ = C)
    (hb₂ : discBd D₂ = C) (hcov : D₁ ∪ D₂ = univ) (hcap : D₁ ∩ D₂ = C) {H₁ H₂ : Drawing S}
    (hU₁ : H₁.U ⊆ D₁) (hU₂ : H₂.U ⊆ D₁) (hn₁ : H₁.U ∩ C ⊆ H₁.V) (hn₂ : H₂.U ∩ C ⊆ H₂.V)
    (hV : H₁.V ∩ C = H₂.V ∩ C) (φ : Iso H₁.toGraph H₂.toGraph)
    (hφ : ∀ v : V(H₁.toGraph), v.1 ∈ C → (φ.vertexEquiv v).1 = v.1) (hr : IsRigidIn H₁ D₁) :
    ∃ h : S ≃ₜ S, h '' D₁ = D₁ ∧ (∀ x ∈ C, h x = x) ∧ (∀ v : V(H₁.toGraph), h v.1 =
      (φ.vertexEquiv v).1) ∧
      ∀ e : E(H₁.toGraph), h '' e.1 = (φ.edgeEquiv e).1 := by
  classical
  obtain ⟨W, a, Γ', hm₁, hw, hf, hrr, haV, haD, haD₁, hpre, -⟩ :=
    exists_frame hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap hU₁ hn₁ hr
  have hm₂ : H₂.U ∩ W.U ⊆ H₂.V ∩ W.V := by
    rintro z ⟨hz, hz'⟩
    have hzC : z ∈ C := hcap ▸ ⟨hU₂ hz, hw.Usub hz'⟩
    have hzV : z ∈ H₂.V := hn₂ ⟨hz, hzC⟩
    exact ⟨hzV, hw.BV (hV.symm.subset ⟨hzV, hzC⟩)⟩
  have hu₁ : IsUnion H₁ W (H₁.glue W hm₁) := isUnion_glue hm₁
  have hu₂ : IsUnion H₂ W (H₂.glue W hm₂) := isUnion_glue hm₂
  have hCW : C ⊆ W.U := hb₂ ▸ hw.bdU
  have hgood := good_of_wheel hf hrr hw hu₁
    (fun v hv hvW => ⟨hv, by
      have : v ∈ D₁ ∩ D₂ := ⟨hU₁ (H₁.V_subset_U hv), hw.Usub (W.V_subset_U hvW)⟩
      rwa [hcap] at this⟩) hm₁ hS hsph
  have hsub := good_sub hgood
  -- A wheel vertex in `H₁` or `H₂` lies on `C`.
  have hVC₁ : ∀ {v}, v ∈ H₁.V → v ∈ W.V → v ∈ C := fun hv hvW => by
    have : _ ∈ D₁ ∩ D₂ := ⟨hU₁ (H₁.V_subset_U hv), hw.Usub (W.V_subset_U hvW)⟩
    rwa [hcap] at this
  have hVC₂ : ∀ {v}, v ∈ H₂.V → v ∈ W.V → v ∈ C := fun hv hvW => by
    have : _ ∈ D₁ ∩ D₂ := ⟨hU₂ (H₂.V_subset_U hv), hw.Usub (W.V_subset_U hvW)⟩
    rwa [hcap] at this
  have hdE : ∀ {H : Drawing S}, H.U ∩ W.U ⊆ H.V ∩ W.V → Disjoint H.E W.E := by
    intro H hH
    refine disjoint_left.mpr fun e he he' => ?_
    obtain ⟨z, hz⟩ := he.1
    have hzU : z ∈ H.U := H.closure_subset_U he (subset_closure hz)
    have hzW : z ∈ W.U := W.closure_subset_U he' (subset_closure hz)
    exact edge_notMem_V he hz (hH ⟨hzU, hzW⟩).1
  obtain ⟨φ', hφ₁, hφ₂, hφ₃, hφ₄⟩ := exists_glueIso hu₁ hu₂ φ
    (fun v hv => hφ v (hVC₁ v.2 hv))
    (fun v hv => by
      have hvC := hVC₂ v.2 hv
      have hv₁ : v.1 ∈ H₁.V := (hV.symm.subset ⟨v.2, hvC⟩).1
      have h₁ := hφ ⟨v.1, hv₁⟩ hvC
      have h₂ : φ.vertexEquiv ⟨v.1, hv₁⟩ = v := Subtype.ext h₁
      have h₃ := congrArg Subtype.val (φ.vertexEquiv.symm_apply_apply ⟨v.1, hv₁⟩)
      rw [h₂] at h₃
      exact h₃)
    (hdE hm₁) (hdE hm₂)
  obtain ⟨h, hhV, hhE, hhW⟩ := whitney_fixing hSurf hsph _ _ hsub φ' W.E (by
    intro e he
    refine ⟨hφ₄ e he, fun v hv => hφ₂ v ?_⟩
    have hvW : v.1 ∈ W.U := W.closure_subset_U he hv
    have hvV : v.1 ∈ H₁.V ∪ W.V := hu₁.hV ▸ v.2
    rcases hvV with h₁ | h₁
    · exact (hm₁ ⟨H₁.V_subset_U h₁, hvW⟩).2
    · exact h₁)
  have hWfix : ∀ x ∈ W.U, h x = x := by
    intro x hx
    by_cases hxV : x ∈ W.V
    · have hxJ : x ∈ V((H₁.glue W hm₁).toGraph) := Or.inr hxV
      rw [hhV ⟨x, hxJ⟩]
      exact hφ₂ ⟨x, hxJ⟩ hxV
    · obtain ⟨e, he, hxe⟩ := W.exists_edge_of_mem hx hxV
      exact hhW e he (hu₁.hE ▸ Or.inr he) x (subset_closure hxe)
  have hfixC : ∀ x ∈ C, h x = x := fun x hx => hWfix x (hCW hx)
  have hfa : h a = a := hWfix a (W.V_subset_U haV)
  have hsym₁ : ∀ x ∈ C, h.symm x = x := fun x hx => by
    rw [Homeomorph.symm_apply_eq]
    exact (hfixC x hx).symm
  have hsyma : h.symm a = a := by
    rw [Homeomorph.symm_apply_eq]
    exact hfa.symm
  have hi₁ := image_compl_sub hd₁.isClosed hd₂.isClosed hcov hcap hpre haD₁ h hfixC hfa
  have hi₂ := image_compl_sub hd₁.isClosed hd₂.isClosed hcov hcap hpre haD₁ h.symm hsym₁ hsyma
  refine ⟨h, ?_, hfixC, ?_, ?_⟩
  · have hc : h '' D₁ᶜ = D₁ᶜ := by
      refine subset_antisymm hi₁ fun x hx => ⟨h.symm x, hi₂ (mem_image_of_mem _ hx), by simp⟩
    have := congrArg compl hc
    rwa [compl_compl, ← image_compl_eq h.bijective, compl_compl] at this
  · intro v
    have hvJ : v.1 ∈ V((H₁.glue W hm₁).toGraph) := Or.inl v.2
    rw [hhV ⟨v.1, hvJ⟩]
    exact hφ₁ ⟨v.1, hvJ⟩ v.2
  · intro e
    have heJ : e.1 ∈ E((H₁.glue W hm₁).toGraph) := by
      change e.1 ∈ (H₁.glue W hm₁).E
      rw [hu₁.hE]
      exact Or.inl e.2
    rw [hhE ⟨e.1, heJ⟩]
    exact hφ₃ ⟨e.1, heJ⟩ e.2

end GraphMinor.GM14.Whitney
