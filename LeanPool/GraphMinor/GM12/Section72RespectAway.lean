/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72PushAway
public import LeanPool.GraphMinor.GM12.Section77

/-!
# Respectfulness for circles missing the vertex in XII (7.2)

Divert a circle off the removed disc by a homeomorphism fixing the
outside drawing. The diverted circle is normal for the old drawing
and meets exactly the same vertices. Respectfulness gives its inside
disc. Pull that disc back. Since the outside drawing is fixed, its
separation is unchanged and belongs to the restricted tangle.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Pulling a set back by a homeomorphism fixing the drawing preserves its intersection hypergraph.
-/
theorem inter_preimage_of_fixed {Γ : Drawing S} (h : S ≃ₜ S)
    (hfix : ∀ x ∈ Γ.U, h x = x) (E : Set S) :
    (PaintingOrDrawing.drawing Γ).inter (h ⁻¹' E) = (PaintingOrDrawing.drawing Γ).inter E := by
  have hV : ∀ x ∈ Γ.V, h x = x := fun x hx => hfix x (Γ.V_subset_U hx)
  have hE : ∀ e ∈ Γ.E, ∀ x ∈ e, h x = x := fun e he x hx => hfix x (he.2.1 hx).1
  have heq : ∀ e ∈ Γ.E, e ⊆ h ⁻¹' E ↔ e ⊆ E := by
    intro e he
    constructor
    · intro hs x hx
      have hh := hs hx
      change h x ∈ E at hh
      rwa [hE e he x hx] at hh
    · intro hs x hx
      change h x ∈ E
      rw [hE e he x hx]
      exact hs hx
  apply Hypergraph.ext
  · ext x
    change (x ∈ Γ.V ∧ h x ∈ E) ↔ x ∈ Γ.V ∧ x ∈ E
    exact ⟨fun hx => ⟨hx.1, hV x hx.1 ▸ hx.2⟩,
      fun hx => ⟨hx.1, (hV x hx.1).symm ▸ hx.2⟩⟩
  · ext e
    change (e ∈ Γ.E ∧ e ⊆ h ⁻¹' E) ↔ e ∈ Γ.E ∧ e ⊆ E
    exact ⟨fun hx => ⟨hx.1, (heq e hx.1).mp hx.2⟩,
      fun hx => ⟨hx.1, (heq e hx.1).mpr hx.2⟩⟩
  · funext e x
    apply propext
    change (Γ.toHypergraph.Inc e x ∧ e ⊆ h ⁻¹' E ∧ h x ∈ E) ↔
      Γ.toHypergraph.Inc e x ∧ e ⊆ E ∧ x ∈ E
    constructor
    · rintro ⟨hi, he, hx⟩
      exact ⟨hi, (heq e hi.1).mp he, hV x hi.2.1 ▸ hx⟩
    · rintro ⟨hi, he, hx⟩
      exact ⟨hi, (heq e hi.1).mpr he, (hV x hi.2.1).symm ▸ hx⟩

omit [T2Space S] in
/-- Pulling a set back by a homeomorphism fixing the drawing preserves its outside intersection. -/
theorem interOutside_preimage_of_fixed {Γ : Drawing S} (h : S ≃ₜ S)
    (hfix : ∀ x ∈ Γ.U, h x = x) (E : Set S) :
    (PaintingOrDrawing.drawing Γ).interOutside (h ⁻¹' E) =
      (PaintingOrDrawing.drawing Γ).interOutside E := by
  have heq : univ \ (h ⁻¹' E) = h ⁻¹' (univ \ E) := by ext x; simp
  unfold PaintingOrDrawing.interOutside
  rw [heq, ← h.preimage_closure, inter_preimage_of_fixed h hfix]

omit [T2Space S] in
/-- Pull a selected disc back along a diversion that fixes the smaller drawing and sends every
point of the circle in the old drawing into the smaller drawing. -/
theorem respectful_disc_of_diversion (hS : IsClosedSurface S)
    {Γ Γ' : Drawing S} (hsub : Γ'.IsSubdrawing Γ) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {C : Set S} (hC : IsOArc C)
    (hCn : (PaintingOrDrawing.drawing Γ').IsNormal C) (hcard : (C ∩ Γ'.V).ncard < θ)
    (h : S ≃ₜ S) (hfix : ∀ x ∈ Γ'.U, h x = x)
    (holdU : ∀ {x}, x ∈ h '' C → x ∈ Γ.U → x ∈ Γ'.U) :
    ∃ E : Set S, IsClosedDisc E ∧ subBd E = C ∧
      ((PaintingOrDrawing.drawing Γ').inter E, (PaintingOrDrawing.drawing Γ').interOutside E) ∈
        restrictTangle T Γ'.toHypergraph := by
  have hCnormal : (PaintingOrDrawing.drawing Γ).IsNormal (h '' C) := by
    rintro x ⟨hxC, hxU⟩
    have hxU' := holdU hxC hxU
    obtain ⟨y, hy, hyx⟩ := hxC
    have hyx' : y = x := h.injective (hyx.trans (hfix x hxU').symm)
    exact hsub.1 (hCn ⟨hyx' ▸ hy, hxU'⟩)
  have hverts : (h '' C) ∩ Γ.V = C ∩ Γ'.V := by
    ext x
    constructor
    · rintro ⟨hxC, hxV⟩
      have hxU' := holdU hxC (Γ.V_subset_U hxV)
      obtain ⟨y, hy, hyx⟩ := hxC
      have hyx' : y = x := h.injective (hyx.trans (hfix x hxU').symm)
      exact ⟨hyx' ▸ hy, hCn ⟨hyx' ▸ hy, hxU'⟩⟩
    · rintro ⟨hxC, hxV⟩
      exact ⟨⟨x, hxC, hfix x (Γ'.V_subset_U hxV)⟩, hsub.1 hxV⟩
  have hCO : IsOArc (h '' C) :=
    hC.image h.continuous.continuousOn h.symm.continuous.continuousOn (fun x _
      => h.symm_apply_apply x)
  obtain ⟨D, hD, hDb, hm⟩ := hrespect.2 (h '' C) hCO hCnormal (hverts.symm ▸ hcard)
  have hm' : ((PaintingOrDrawing.drawing Γ').inter D,
      (PaintingOrDrawing.drawing Γ').interOutside D) ∈ restrictTangle T Γ'.toHypergraph := by
    have hmem : (((PaintingOrDrawing.drawing Γ).inter D) ∩ Γ'.toHypergraph,
        ((PaintingOrDrawing.drawing Γ).interOutside D) ∩ Γ'.toHypergraph) ∈
          restrictTangle T Γ'.toHypergraph := ⟨_, _, hm, rfl⟩
    rwa [drawing_inter_inter_subdrawing hsub, drawing_interOutside_inter_subdrawing hsub] at hmem
  obtain ⟨hE, hbE⟩ := hD.image h.symm.continuous.continuousOn h.continuous.continuousOn
    (fun x _ => h.apply_symm_apply x)
  have hpre : h.symm '' D = h ⁻¹' D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, h.apply_symm_apply] using hy
    · intro hx
      exact ⟨h x, hx, h.symm_apply_apply x⟩
  have hb : subBd (h ⁻¹' D) = C := by
    rw [← hpre, subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS hE, hbE,
      ← IsClosedDisc.frontier_eq_discBd hS hD, ← subBd_eq_frontier, hDb]
    rw [image_image]
    have heq : (fun x => h.symm (h x)) = id := funext h.symm_apply_apply
    rw [heq, image_id]
  refine ⟨h ⁻¹' D, hpre ▸ hE, hb, ?_⟩
  rw [inter_preimage_of_fixed h hfix, interOutside_preimage_of_fixed h hfix]
  exact hm'

/-- The respectfulness assertion in the diversion step of XII (7.2), page
260, for a normal circle that does not pass through the boundary vertex. -/
theorem theorem_7_2_respectful_of_notMem (hS : IsClosedSurface S)
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {Δ F C : Set S} {v : S} (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hFV : F ∩ Γ.V = {v})
    (hC : IsOArc C)
    (hCn : (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).IsNormal C)
    (hcard : (C ∩ (Γ.interSet (closure (univ \ Δ))).V).ncard < θ)
    (hvn : v ∉ C) :
    ∃ E : Set S, IsClosedDisc E ∧ subBd E = C ∧
      ((PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).inter E,
        (PaintingOrDrawing.drawing (Γ.interSet (closure (univ \ Δ)))).interOutside E) ∈
          restrictTangle T (Γ.interSet (closure (univ \ Δ))).toHypergraph := by
  let Γ' := Γ.interSet (closure (univ \ Δ))
  have hsub : Γ'.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hfr : frontier Δ = F := (subBd_eq_frontier Δ).symm.trans hbd
  have hdb : discBd Δ = F := (IsClosedDisc.frontier_eq_discBd hS hΔ).symm.trans hfr
  have hvFV : v ∈ F ∩ Γ.V := hFV.symm ▸ mem_singleton v
  have hvb : v ∈ discBd Δ := hdb.symm ▸ hvFV.1
  have hnorm : frontier (closure (univ \ Δ)) ∩ Γ.U ⊆ Γ.V := by
    rw [← compl_eq_univ_sdiff, closure_compl, frontier_compl]
    exact fun x hx => hn ⟨hfr ▸ frontier_interior_subset hx.1, hx.2⟩
  have hUeq := interSet_U_eq_of_normal_frontier isClosed_closure hnorm
  have hGD : Γ'.U ∩ Δ ⊆ {v} := by
    rintro x ⟨hxU, hxD⟩
    rw [hUeq] at hxU
    have hxfr : x ∈ frontier Δ := by
      rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure hxD, hxU.2⟩
    exact hFV ▸ ⟨hfr ▸ hxfr, hn ⟨hfr ▸ hxfr, hxU.1⟩⟩
  obtain ⟨h, hfix, hpush⟩ := theorem_7_2_push_away_of_notMem hS hΔ hvb Γ'.isClosed_U hGD hC hvn
  have holdU : ∀ {x}, x ∈ h '' C → x ∈ Γ.U → x ∈ Γ'.U := by
    intro x hxC hxU
    have hxD : x ∉ Δ := disjoint_left.mp hpush hxC
    exact hUeq.symm ▸ ⟨hxU, subset_closure ⟨mem_univ x, hxD⟩⟩
  exact respectful_disc_of_diversion hS hsub hrespect hC hCn hcard h hfix holdU

end GraphMinor.GM12
