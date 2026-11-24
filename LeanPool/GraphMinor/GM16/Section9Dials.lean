/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM11.Ties
import LeanPool.GraphMinor.GM11.Walks

/-!
# Dials after clearing disjoint zones

In Claim (2) of XVI (8.1), a dial for the drawing with one zone cleared
must avoid every other zone. A dial cannot contain a circle of the
drawing: its drawing part is either on the normal boundary or a line.
A zone disjoint from the dial boundary is therefore outside the dial.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- A dial for a normal circle contains no circle of the drawing.
This supplies the missing justification in XVI (8.1), Claim (2), page 71. -/
theorem dial_contains_no_oArc
    {H : Drawing S} {F Δ J : Set S} (hD : IsDial H F Δ)
    (hNormal : F ∩ H.U ⊆ H.V) (hJ : IsOArc J) (hJU : J ⊆ H.U) (hJΔ : J ⊆ Δ) : False := by
  rcases hD.2.2 with hsmall | ⟨a, b, hab, _, hPath⟩
  · have hJV : J ⊆ H.V := fun x hx => hNormal ⟨hsmall ⟨hJΔ hx, hJU hx⟩, hJU hx⟩
    exact infinite_of_isOArc hJ (H.finite_V.subset hJV)
  · obtain ⟨f, _, _⟩ := GraphMinor.GM11.isLine_of_isPathBetween hPath hab
    exact not_isOArc_of_subset_line ⟨f⟩ hJ (oArc_subset_interSet_U hJ hJU hJΔ)

/-- A dial whose boundary avoids an open disc also avoids the disc if
its boundary circle lies in the drawing. Otherwise the entire boundary
circle of that disc would lie in the dial. -/
theorem dial_disjoint_open_disc
    {H : Drawing S} {F Δ Ω : Set S} (hD : IsDial H F Δ)
    (hNormal : F ∩ H.U ⊆ H.V) (hΩ : IsOpenDisc Ω)
    (hBd : IsOArc (subBd Ω)) (hBdU : subBd Ω ⊆ H.U)
    (hFΩ : Disjoint F Ω) : Disjoint Δ Ω := by
  have hdis : Disjoint Ω (frontier Δ) := by
    rw [← subBd_eq_frontier, hD.2.1]
    exact hFΩ.symm
  rcases subset_or_disjoint_of_frontier hD.1.isClosed hΩ.isPathConnected.isConnected.isPreconnected
    hdis with
    hsub | hdis
  · have hcl : closure Ω ⊆ Δ := closure_minimal hsub hD.1.isClosed
    exact False.elim (dial_contains_no_oArc hD hNormal hBd hBdU (fun _ h => hcl h.1))
  · exact hdis.symm

omit [ConnectedSpace S] in
/-- Restriction to two closed sets is restriction to their intersection. -/
theorem drawing_interSet_inter_closed (H : Drawing S) {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) :
    (H.interSet A).interSet B = H.interSet (A ∩ B) := by
  apply Drawing.ext_of_V_E
  · ext x
    rw [mem_interSet_V_iff hB, mem_interSet_V_iff hA, mem_interSet_V_iff (hA.inter hB)]
    simp only [mem_inter_iff]
    tauto
  · ext e
    rw [mem_interSet_E_iff, mem_interSet_E_iff, mem_interSet_E_iff]
    simp only [subset_inter_iff]
    tauto

omit [ConnectedSpace S] in
/-- Restriction to closed sets preserves inclusion of those sets. -/
theorem drawing_interSet_mono_closed (H : Drawing S) {A B : Set S}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ⊆ B) :
    (H.interSet A).IsSubdrawing (H.interSet B) := by
  constructor
  · intro x hx
    have hx' := (mem_interSet_V_iff hA).mp hx
    exact (mem_interSet_V_iff hB).mpr ⟨hx'.1, hAB hx'.2⟩
  · intro e he
    obtain ⟨heH, heA⟩ := mem_interSet_E_iff.mp he
    exact mem_interSet_E_iff.mpr ⟨heH, heA.trans hAB⟩

omit [ConnectedSpace S] in
/-- Restriction to the whole surface changes no drawing. -/
theorem drawing_interSet_univ (H : Drawing S) : H.interSet univ = H := by
  apply Drawing.ext_of_V_E
  · ext x
    rw [mem_interSet_V_iff isClosed_univ]
    exact and_iff_left (mem_univ x)
  · ext e
    rw [mem_interSet_E_iff]
    simp only [subset_univ, and_true]

omit [ConnectedSpace S] in
/-- A dial remains a dial in a subdrawing when its intersection with the
dial and the vertices on its boundary are unchanged. -/
theorem dial_of_subdrawing_same_inter
    {H K : Drawing S} {F Δ : Set S} (hD : IsDial H F Δ)
    (hKH : K.IsSubdrawing H) (hFV : F ∩ K.V = F ∩ H.V)
    (hinter : H.interSet Δ = K.interSet Δ) : IsDial K F Δ := by
  refine ⟨hD.1, hD.2.1, ?_⟩
  rcases hD.2.2 with hsmall | ⟨a, b, hab, hEnds, hPath⟩
  · exact Or.inl (fun _ h => hsmall ⟨h.1, hKH.U_subset h.2⟩)
  · refine Or.inr ⟨a, b, hab, hFV.trans hEnds, ?_⟩
    exact hinter ▸ hPath

omit [ConnectedSpace S] in
/-- Clearing one disc followed by a family amounts to clearing their
union. This identifies the drawings in the two orders used in XVI (8.1). -/
theorem clearFamily_after_single (H : Drawing S) (Y : Set S) (Λ : S → Set S) (j : S)
    (hOpen : ∀ y ∈ insert j Y, IsOpen (Λ y)) :
    clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) Y Λ =
      clearEnvelopeDrawing H (insert j Y) Λ := by
  unfold clearEnvelopeDrawing clearedSubdrawing
  have hclosed : IsClosed (univ \ ⋃ y ∈ Y, Λ y) :=
    isClosed_univ.sdiff (isOpen_iUnion fun y => isOpen_iUnion fun hy => hOpen y
      (mem_insert_of_mem j hy))
  rw [drawing_interSet_inter_closed H (isClosed_univ.sdiff (hOpen j (mem_insert j Y))) hclosed]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and, mem_iUnion, mem_insert_iff]
  constructor
  · rintro ⟨hxj, hxY⟩ ⟨y, hy, hxy⟩
    rcases hy with rfl | hy
    · exact hxj hxy
    · exact hxY ⟨y, hy, hxy⟩
  · intro hx
    exact ⟨fun hxj => hx ⟨j, Or.inl rfl, hxj⟩,
      fun ⟨y, hy, hxy⟩ => hx ⟨y, Or.inr hy, hxy⟩⟩

end GraphMinor.GM16
