/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import Mathlib.Data.Set.Card

/-!
# The length decrease for the two curves cut off by a chord

Case 2 of XII (2.1), page 244, applies induction to one of the circles
formed by the chord. The chord misses the original drawing. Each of
the two original arcs contains a vertex, and they share no vertex.
Thus either new circle contains strictly fewer vertices than the
original circle. For an embedded normal curve these counts are exactly
the lengths used in the paper.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- For an injective normal curve, its length counts the vertices in
its image. Injectivity identifies parameter hits with their images,
and normality turns hits of the drawing into hits of its vertex set. -/
theorem curveLength_eq_vertex_count {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} (φ : C(Circle, S)) (hinj : Function.Injective φ)
    (hnormal : Γ.IsNormal (range φ)) :
    curveLength Γ φ = (range φ ∩ Γ.V).ncard := by
  have heq : φ '' {t | φ t ∈ Γ.U} = range φ ∩ Γ.V := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨mem_range_self t, hnormal ⟨mem_range_self t, ht⟩⟩
    · rintro ⟨⟨t, rfl⟩, ht⟩
      exact ⟨t, Γ.V_subset_U ht, rfl⟩
  change {t | φ t ∈ Γ.U}.ncard = _
  rw [← heq]
  exact (Set.ncard_image_of_injective _ hinj).symm

/-- The distinct drawing vertices in a normal curve image number
at most its parameter hits. This gives the length bound in the
simple-subcurve reduction of XII (2.1), pages 243--244. -/
theorem vertex_count_le_curveLength {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) :
    (range φ ∩ Γ.V).ncard ≤ curveLength Γ φ := by
  have himage : φ '' {t | φ t ∈ Γ.U} = range φ ∩ Γ.V := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨mem_range_self t, hφ.2 ⟨mem_range_self t, ht⟩⟩
    · rintro ⟨⟨t, rfl⟩, ht⟩
      exact ⟨t, Γ.V_subset_U ht, rfl⟩
  change (range φ ∩ Γ.V).ncard ≤ {t | φ t ∈ Γ.U}.ncard
  rw [← himage]
  exact Set.ncard_image_le hφ.1

/-- A chord missing the vertices adds none to either new circle. If
the other original arc contains a vertex not on this arc, the new
circle has a strictly smaller vertex count. -/
theorem chord_circle_vertex_count_lt {S : Type*} {A B L V : Set S}
    (hV : V.Finite) (hLV : Disjoint L V) (hABV : Disjoint (A ∩ B) V)
    (hB : (B ∩ V).Nonempty) : ((A ∪ L) ∩ V).ncard < ((A ∪ B) ∩ V).ncard := by
  have htarget : (A ∪ L) ∩ V = A ∩ V := by
    rw [union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hLV, union_empty]
  rw [htarget]
  apply Set.ncard_lt_ncard _ (hV.subset inter_subset_right)
  refine ⟨fun x hx => ⟨Or.inl hx.1, hx.2⟩, ?_⟩
  intro hback
  obtain ⟨x, hxB, hxV⟩ := hB
  have hxA : x ∈ A := (hback ⟨Or.inr hxB, hxV⟩).1
  exact Set.disjoint_left.mp hABV ⟨hxA, hxB⟩ hxV

/-- Both circles formed by the chord have smaller vertex counts when
each of the two original arcs contains a vertex. This is the numerical
induction step in XII (2.1), Case 2, page 244. -/
theorem chord_circle_vertex_counts_lt {S : Type*} {A B L V : Set S}
    (hV : V.Finite) (hLV : Disjoint L V) (hABV : Disjoint (A ∩ B) V)
    (hA : (A ∩ V).Nonempty) (hB : (B ∩ V).Nonempty) :
    ((A ∪ L) ∩ V).ncard < ((A ∪ B) ∩ V).ncard ∧
      ((B ∪ L) ∩ V).ncard < ((A ∪ B) ∩ V).ncard := by
  refine ⟨chord_circle_vertex_count_lt hV hLV hABV hB, ?_⟩
  have hBA : Disjoint (B ∩ A) V := by rwa [inter_comm]
  have h := chord_circle_vertex_count_lt hV hLV hBA hA
  rwa [union_comm B A] at h

/-- An embedded curve with normal image has finite length, since its
hits inject into the finite vertex set of the drawing. -/
theorem isNormalCurve_of_injective {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} (φ : C(Circle, S)) (hinj : Function.Injective φ)
    (hnormal : Γ.IsNormal (range φ)) : IsNormalCurve Γ φ := by
  refine ⟨?_, hnormal⟩
  have hfinite : (φ ⁻¹' Γ.V).Finite := Set.Finite.preimage hinj.injOn Γ.finite_V
  exact hfinite.subset fun t ht => hnormal ⟨mem_range_self t, ht⟩

/-- Replacing part of an embedded normal curve by a chord off the
drawing preserves normality and finite length. -/
theorem isNormalCurve_of_chord_replacement {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} (φ ψ : C(Circle, S)) (hψ : Function.Injective ψ)
    (hφ : Γ.IsNormal (range φ)) {L : Set S} (hL : Disjoint L Γ.U)
    (hsub : range ψ ⊆ range φ ∪ L) : IsNormalCurve Γ ψ := by
  apply isNormalCurve_of_injective ψ hψ
  rintro x ⟨hxψ, hxU⟩
  rcases hsub hxψ with hxφ | hxL
  · exact hφ ⟨hxφ, hxU⟩
  · exact (Set.disjoint_left.mp hL hxL hxU).elim

/-- The smaller circle has strictly smaller length, in the exact
length definition of XII (2.1), Case 2. The omitted original arc must
contain a vertex, and the chord meets no point of the drawing. -/
theorem curveLength_lt_of_chord_replacement {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} (φ ψ : C(Circle, S))
    (hφi : Function.Injective φ) (hψi : Function.Injective ψ)
    (hφ : Γ.IsNormal (range φ)) {A B L : Set S}
    (hφrange : range φ = A ∪ B) (hψrange : range ψ = A ∪ L)
    (hL : Disjoint L Γ.U) (hABV : Disjoint (A ∩ B) Γ.V)
    (hB : (B ∩ Γ.V).Nonempty) : curveLength Γ ψ < curveLength Γ φ := by
  have hψ : IsNormalCurve Γ ψ := isNormalCurve_of_chord_replacement φ ψ hψi hφ hL (by
    rw [hφrange, hψrange]
    exact union_subset (fun _ hx => Or.inl (Or.inl hx)) (fun _ hx => Or.inr hx))
  rw [curveLength_eq_vertex_count ψ hψi hψ.2, curveLength_eq_vertex_count φ hφi hφ,
    hψrange, hφrange]
  have hLV : Disjoint L Γ.V := hL.mono_right Γ.V_subset_U
  exact chord_circle_vertex_count_lt Γ.finite_V hLV hABV hB

/-- Parameterize a normal circle injectively, retaining its exact
curve length as the number of drawing vertices on the circle. -/
theorem exists_normal_curve_of_oArc {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {F : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F) :
    ∃ φ : C(Circle, S), IsEmbedding φ ∧ range φ = F ∧ IsNormalCurve Γ φ ∧
      curveLength Γ φ = (Γ.V ∩ F).ncard := by
  obtain ⟨H⟩ := hF
  let φ : C(Circle, S) := ⟨fun t => (H t).val, continuous_subtype_val.comp H.continuous⟩
  have hrange : range φ = F := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (H t).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply ⟨x, hx⟩)⟩
  have hemb : IsEmbedding φ := IsEmbedding.subtypeVal.comp H.isEmbedding
  have hnormal : Γ.IsNormal (range φ) := hrange.symm ▸ hn
  refine ⟨φ, hemb, hrange, isNormalCurve_of_injective φ hemb.injective hnormal, ?_⟩
  rw [curveLength_eq_vertex_count φ hemb.injective hnormal, hrange, inter_comm]

end GraphMinor.GM12
