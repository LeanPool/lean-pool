/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM12.Section1b

public import LeanPool.GraphMinor.GM12.Section1
public import LeanPool.GraphMinor.GM12.Section4CircuitWalk
public import LeanPool.GraphMinor.GM12.Section4WalkMetric
public import LeanPool.GraphMinor.GM11.Section85
public import LeanPool.GraphMinor.GM11.Section810
public import LeanPool.GraphMinor.GM11.ForestRegions
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# Graph Minors XII, (7.11), Part 1: Restraint Union and Connectedness

This file sets up the restraint union `Z = restraintUnion K ins (2 * θ) c (2 * λ)` used in the
proof of (7.11) of Graph Minors XII (pages 271–272), characterizes the edges of the
deleted-neighborhood
subdrawing in terms of radial regions outside `Z`, and proves that the deleted-neighborhood
subdrawing is non-null and has connected point set.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem atom_nonempty {Γ : Drawing S} {x : Set S} (hx : x ∈ Γ.A) : x.Nonempty := by
  rcases hx with (⟨v, -, rfl⟩ | hx) | hx
  · exact singleton_nonempty v
  · exact hx.1
  · exact region_nonempty hx

omit [T2Space S] in
theorem existsUnique_correspondingAtom_t1 {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {x : Set S} (hx : x ∈ H.A) :
    ∃! x' : Set S, IsCorrespondingAtom H K x x' := by
  exact GM12.existsUnique_correspondingAtom hK hx

omit [T2Space S] in
/-- Removing a finite set from an open connected subset of a closed surface leaves it preconnected.
-/
theorem isPreconnected_sdiff_finite (hS : IsClosedSurface S) {O F : Set S}
    (hO : IsOpen O) (hOc : IsPreconnected O) (hF : F.Finite) : IsPreconnected (O \ F) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction F, hF using Set.Finite.induction_on with
  | empty =>
    rw [sdiff_empty]
    exact hOc
  | @insert x F hxF hF ih =>
    have hG : IsOpen (O \ F) := hO.sdiff hF.isClosed
    have hEq : O \ insert x F = (O \ F) \ {x} := by
      ext y
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      tauto
    rw [hEq]
    by_cases hxG : x ∈ O \ F
    · obtain ⟨Z, hZ, hxZ, hZG, hZc, hZcl⟩ := exists_punctured_nbhd hS hG hxG
      obtain ⟨a, haZ⟩ : (Z \ {x}).Nonempty := by
        by_contra hcon
        rw [not_nonempty_iff_eq_empty] at hcon
        rw [hcon, closure_empty] at hZcl
        exact hZcl
      have hcl : IsClosed ((O \ F)ᶜ ∪ {x}) := hG.isClosed_compl.union isClosed_singleton
      refine isPreconnected_sdiff_of_local hG ih hcl ⟨x, hxG, rfl⟩ ⟨hZG haZ.1, haZ.2⟩ ?_
      rintro y _ ⟨t, ⟨-, ht⟩, htc⟩
      obtain rfl : t = x := ht
      obtain ⟨b, hbZ, hbC⟩ := mem_closure_iff.mp htc Z hZ hxZ
      have hbne : b ≠ t := (connectedComponentIn_subset _ _ hbC).2
      rw [connectedComponentIn_eq hbC]
      refine hZc.subset_connectedComponentIn ⟨hbZ, hbne⟩ ?_ haZ
      exact fun q hq => ⟨hZG hq.1, hq.2⟩
    · rw [sdiff_eq_left.mpr (disjoint_singleton_right.mpr hxG)]
      exact ih

omit [T2Space S] in
/-- Every edge of a drawing has at most 2 incident vertices. -/
theorem edgeSize_drawing_le_two {H : Drawing S} {e : Set S} (he : e ∈ H.E) :
    edgeSize H.toHypergraph e ≤ 2 := by
  have hends : H.toHypergraph.ends e = closure e ∩ H.V := by
    ext v
    exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨he, h.2, h.1⟩⟩
  unfold edgeSize
  rw [hends]
  rcases H.edge_cond e he with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
  · rw [hcap]
    exact (ncard_insert_le a {b}).trans (by simp)
  · rw [hcap, ncard_singleton]
    omega

/-- In the setting of (7.11), the radial atom `z'` corresponding to `z` lies in the restraint
union `restraintUnion K ins (2 * θ) c (2 * lam)` around any point `c ∈ z'`. -/
theorem correspondingAtom_subset_restraintUnion (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hE : H.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    {z z' : Set S} (hz' : IsCorrespondingAtom H K z z') {c : S} (hc : c ∈ z')
    (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam) :
    z' ⊆ restraintUnion K ins (2 * θ) c (2 * lam) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hT := hResp.2.1
  have hpreT : IsPretangle H.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hpreT hK.2.1.1 hd
  rcases hz'.2.2 with ⟨v, hv, rfl, rfl⟩ | ⟨hzE, hr, hsub⟩ | ⟨hr, w, ⟨hwK, hwr⟩, rfl⟩
  · have hvc : v = c := (mem_singleton_iff.mp hc).symm
    subst hvc
    have hcK : v ∈ K.V := hK.2.1.2.1 hv
    let W : GraphWalk K.toGraph v v := .nil hcK
    have hWlen : W.length < 2 * θ := by
      have := hT.one_le
      change 0 < 2 * θ
      omega
    have h85 := GM11.theorem_8_5_proof hS hsl W hWlen
    have hcW : v ∈ insWalk ins K W :=
      Or.inl ((walkDrawing K W).V_subset_U (by rw [walkDrawing_V]; exact W.start_mem_support))
    have hmem : insWalk ins K W ∈
        {X : Set S | IsRestraint K ins (2 * θ) X ∧ perimeterWalkLength K X ≤ 2 * lam ∧ v ∈ X} :=
      ⟨h85.1, h85.2.trans (Nat.zero_le _), hcW⟩
    exact singleton_subset_iff.mpr (mem_biUnion hmem hcW)
  · have h2lam : 2 ≤ lam := hz_lam hzE
    have h3θ : 3 ≤ θ := by omega
    have hzH : z ∈ H.toHypergraph.edgeSet := hzE
    have hsep := isSeparation_edgeHypergraph_deleteEdges hzH
    have hsize : edgeSize H.toHypergraph z ≤ 2 := edgeSize_drawing_le_two hzE
    have hord : separationOrder (edgeHypergraph H.toHypergraph z)
        (H.toHypergraph.deleteEdges {z}) < θ := by
      rw [separationOrder_edgeHypergraph_deleteEdges]
      omega
    have hmemT : (edgeHypergraph H.toHypergraph z, H.toHypergraph.deleteEdges {z}) ∈ T :=
      (GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1 hT.axiom2).mp
        hT z hzH (by omega)
    have h11 := (theorem_1_1_proof hS hResp hE hK hd hsep hord).mp hmemT z
      (by simp [edgeHypergraph])
    obtain ⟨C, hC, hCs, hClen, hCV, hzC⟩ := h11
    have hCeven := (circuit_length_eq_two_mul_ncard hK.2.1 hC hCs).1
    have hCV_le : (C.V ∩ H.V).ncard ≤ 2 := by
      have hsubV : C.V ∩ H.V ⊆ H.toHypergraph.ends z := by
        refine hCV.trans ?_
        intro x hx
        exact hx.1
      have hends_fin : (H.toHypergraph.ends z).Finite :=
        H.toHypergraph.vertexSet_finite.subset fun x hx => H.toHypergraph.vertex_mem_of_inc hx
      exact (ncard_le_ncard hsubV hends_fin).trans hsize
    have hC' : C.IsCircuit := hC
    obtain ⟨u₀, W₀, -, -, hV₀, -⟩ := hC'
    have hu₀ : u₀ ∈ C.V := hV₀ ▸ W₀.start_mem_support
    obtain ⟨W, hWC, hWlen⟩ := circuit_walk_at hC hCs hu₀
    have hWlt : W.length < 2 * θ := hWlen.trans_lt hClen
    have hzW : (z ∩ insWalk ins K W).Nonempty := by
      obtain ⟨p₀, hp₀⟩ := hzE.1
      refine ⟨p₀, hp₀, Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, ?_⟩, hzC hp₀⟩)⟩
      rw [hWC]
      exact Drawing.IsSubdrawing.refl C
    have hz'W : z' ⊆ insWalk ins K W :=
      (corresponding_atom_subset_iff hS hK hd hz' W hWlt).mpr hzW
    have h85 := GM11.theorem_8_5_proof hS hsl W hWlt
    have hper_le : perimeterWalkLength K (insWalk ins K W) ≤ 2 * lam := by
      calc perimeterWalkLength K (insWalk ins K W) ≤ W.length := h85.2
        _ = C.length := hWlen
        _ = 2 * (C.V ∩ H.V).ncard := hCeven
        _ ≤ 2 * lam := by omega
    have hmem : insWalk ins K W ∈
        {X : Set S | IsRestraint K ins (2 * θ) X ∧ perimeterWalkLength K X ≤ 2 * lam ∧ c ∈ X} :=
      ⟨h85.1, hper_le, hz'W hc⟩
    exact fun x hx => mem_biUnion hmem (hz'W hx)
  · have hwc : w = c := (mem_singleton_iff.mp hc).symm
    subst hwc
    let W : GraphWalk K.toGraph w w := .nil hwK
    have hWlen : W.length < 2 * θ := by
      have := hT.one_le
      change 0 < 2 * θ
      omega
    have h85 := GM11.theorem_8_5_proof hS hsl W hWlen
    have hcW : w ∈ insWalk ins K W :=
      Or.inl ((walkDrawing K W).V_subset_U (by rw [walkDrawing_V]; exact W.start_mem_support))
    have hmem : insWalk ins K W ∈
        {X : Set S | IsRestraint K ins (2 * θ) X ∧ perimeterWalkLength K X ≤ 2 * lam ∧ w ∈ X} :=
      ⟨h85.1, h85.2.trans (Nat.zero_le _), hcW⟩
    exact singleton_subset_iff.mpr (mem_biUnion hmem hcW)

/-- For an edge `e ∈ H.E` and its radial region `s ∈ K.R` (`e ⊆ s`), `e` has distance `> lam` from
`z` if and only if `s` lies in the complement of `restraintUnion K ins (2 * θ) c (2 * lam)`. -/
theorem edge_mem_span_iff (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hE : H.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {z z' : Set S} (hz : z ∈ H.A) (hz' : IsCorrespondingAtom H K z z') {c : S} (hc : c ∈ z')
    (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam)
    {e s : Set S} (he : e ∈ H.E) (hs : s ∈ K.R) (hes : e ⊆ s) :
    e ∈ (H.span ∅ {f ∈ H.E | lam < d z f}).E ↔
      s ⊆ (restraintUnion K ins (2 * θ) c (2 * lam))ᶜ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hT := hResp.2.1
  have hpreT : IsPretangle H.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hpreT hK.2.1.1 hd
  set Z := restraintUnion K ins (2 * θ) c (2 * lam)
  have hZn : IsGammaNice K Z := isGammaNice_restraintUnion c (2 * lam)
  have he_corr : IsCorrespondingAtom H K e s :=
    ⟨Or.inl (Or.inr he), Or.inr hs, Or.inr (Or.inl ⟨he, hs, hes⟩)⟩
  have hz'Z : z' ⊆ Z :=
    correspondingAtom_subset_restraintUnion hS hResp hE hK hd hz' hc hlam hz_lam
  rw [H.span_E]
  simp only [mem_inter_iff, mem_ofPred_eq, he, true_and, and_true]
  constructor
  · intro hgt y hys hyZ
    obtain ⟨X, ⟨hXr, hXlen, hcX⟩, hyX⟩ := mem_iUnion₂.mp hyZ
    obtain ⟨u, W, -, hWlen, hWlt, -, hWd⟩ := hXr.exists_walk hS
    have hinsW : insWalk ins K W = X := insWalk_eq hS hsl hXr hWd
    have hsX : s ⊆ insWalk ins K W := by
      rw [hinsW]
      exact nice_region hXr.isGammaNice hs ⟨y, hys, hyX⟩
    have hz'X : z' ⊆ insWalk ins K W := by
      have hzc : (z ∩ insWalk ins K W).Nonempty := by
        rw [← corresponding_atom_subset_iff hS hK hd hz' W hWlt]
        rcases hz'.2.2 with ⟨v, hv, rfl, rfl⟩ | ⟨hzE, hr, hsub⟩ | ⟨hr, w, ⟨hwK, hwr⟩, rfl⟩
        · have hvc : v = c := (mem_singleton_iff.mp hc).symm
          subst hvc
          exact singleton_subset_iff.mpr (hinsW.symm ▸ hcX)
        · exact nice_region hXr.isGammaNice hr ⟨c, hc, hcX⟩ |>.trans (by rw [hinsW])
        · have hwc : w = c := (mem_singleton_iff.mp hc).symm
          subst hwc
          exact singleton_subset_iff.mpr (hinsW.symm ▸ hcX)
      exact (corresponding_atom_subset_iff hS hK hd hz' W hWlt).mpr hzc
    obtain ⟨k, hk⟩ : ∃ k, W.length = 2 * k := ⟨_, closed_walk_length_eq_two_mul hK.2.1 W⟩
    have hd_le : tangleMetric H K ins θ z e ≤ k :=
      tangleMetric_le_of_walk hz' he_corr W hWlt hk hz'X hsX
    have hk_le : k ≤ lam := by omega
    rw [hd_eq z hz e (Or.inl (Or.inr he))] at hgt
    omega
  · intro hsZ
    by_contra hle
    push Not at hle
    rw [hd_eq z hz e (Or.inl (Or.inr he))] at hle
    obtain ⟨p₀, hp₀⟩ := region_nonempty hs
    apply hsZ hp₀
    by_cases hze : z = e
    · subst hze
      have hzeq : z' = s := (existsUnique_correspondingAtom_t1 hK hz).unique hz' he_corr
      exact hz'Z (hzeq.symm ▸ hp₀)
    · classical
      by_cases hex : ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
          IsCorrespondingAtom H K z x' ∧ IsCorrespondingAtom H K e y' ∧
          W.length < 2 * θ ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W
      · simp only [tangleMetric, hze, hex, ↓reduceIte] at hle
        set S_k := {k : ℕ | ∃ (u : S) (W : GraphWalk K.toGraph u u) (x' y' : Set S),
          IsCorrespondingAtom H K z x' ∧ IsCorrespondingAtom H K e y' ∧
          W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins K W ∧ y' ⊆ insWalk ins K W}
        have hle' : sInf S_k ≤ lam := hle
        obtain ⟨u, W, x', y', hx', hy', hWlt, hx'W, hy'W⟩ := hex
        obtain ⟨k₀, hk₀⟩ : ∃ k₀, W.length = 2 * k₀ := ⟨_, closed_walk_length_eq_two_mul hK.2.1 W⟩
        have hSk_ne : S_k.Nonempty := ⟨k₀, u, W, x', y', hx', hy', hWlt, hk₀, hx'W, hy'W⟩
        obtain ⟨u₁, W₁, x₁', y₁', hx₁', hy₁', hW₁lt, hW₁len, hx₁'W, hy₁'W⟩ := Nat.sInf_mem hSk_ne
        have hx₁_eq : x₁' = z' := (existsUnique_correspondingAtom_t1 hK hz).unique hx₁' hz'
        have hy₁_eq : y₁' = s :=
          (existsUnique_correspondingAtom_t1 hK (Or.inl (Or.inr he))).unique hy₁' he_corr
        subst hx₁_eq hy₁_eq
        have h85 := GM11.theorem_8_5_proof hS hsl W₁ hW₁lt
        have hper : perimeterWalkLength K (insWalk ins K W₁) ≤ 2 * lam := by
          calc perimeterWalkLength K (insWalk ins K W₁) ≤ W₁.length := h85.2
            _ = 2 * sInf S_k := hW₁len
            _ ≤ 2 * lam := by omega
        have hmem : insWalk ins K W₁ ∈
            {X : Set S | IsRestraint K ins (2 * θ) X ∧ perimeterWalkLength K X ≤ 2 * lam ∧ c ∈ X} :=
          ⟨h85.1, hper, hx₁'W hc⟩
        exact mem_biUnion hmem (hy₁'W hp₀)
      · simp only [tangleMetric, hze, hex, ↓reduceIte] at hle
        omega

/-- In the setting of (7.11), `restraintUnion K ins (2 * θ) c (2 * lam) ≠ univ` and
`(H.span ∅ {e ∈ H.E | lam < d z e}).E` is nonempty. -/
theorem restraintUnion_ne_univ_and_span_E_nonempty (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hE : H.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {z z' : Set S} (hz : z ∈ H.A) (hz' : IsCorrespondingAtom H K z z') {c : S} (hc : c ∈ z')
    (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam) :
    restraintUnion K ins (2 * θ) c (2 * lam) ≠ univ ∧
      (H.span ∅ {f ∈ H.E | lam < d z f}).E.Nonempty := by
  have : T2Space S := hS.2.1
  have hT := hResp.2.1
  have hpreT : IsPretangle H.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hpreT hK.2.1.1 hd
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨r₁, hr₁, hno₁⟩ := GM11.theorem_8_12_proof hS hsl c
  obtain ⟨e₁, he₁, he₁r₁⟩ := hrf.1 r₁ hr₁
  have hr₁_compl : r₁ ⊆ (restraintUnion K ins (2 * θ) c (2 * lam))ᶜ := by
    intro y hy hyZ
    obtain ⟨X, ⟨hXr, -, hcX⟩, hyX⟩ := mem_iUnion₂.mp hyZ
    exact hno₁ X hXr ⟨hcX, nice_region hXr.isGammaNice hr₁ ⟨y, hy, hyX⟩⟩
  obtain ⟨p₁, hp₁⟩ := region_nonempty hr₁
  refine ⟨fun hun => hr₁_compl hp₁ (hun ▸ mem_univ p₁), e₁, ?_⟩
  exact (edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he₁ hr₁ he₁r₁).mpr
    hr₁_compl

/-- In the setting of (7.11), the point set of `H.span ∅ {e ∈ H.E | lam < d z e}` is
preconnected. -/
theorem isPreconnected_span_U (hS : IsClosedSurface S) [ConnectedSpace S]
    {H K : Drawing S} {θ lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {ins : Drawing S → Set S}
    (hResp : IsRespectfulDrawingTangle H θ T) (hE : H.E.Nonempty)
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hd_eq : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y = tangleMetric H K ins θ x y)
    {z z' : Set S} (hz : z ∈ H.A) (hz' : IsCorrespondingAtom H K z z') {c : S} (hc : c ∈ z')
    (hlam : lam < θ) (hz_lam : z ∈ H.E → 2 ≤ lam) :
    IsPreconnected (H.span ∅ {f ∈ H.E | lam < d z f}).U := by
  classical
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hT := hResp.2.1
  have hpre : PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hpreT : IsPretangle H.toHypergraph θ T :=
    ⟨hT.one_le, hT.isSeparation, hT.order_lt, hT.axiom1, hT.axiom2⟩
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS hpreT hK.2.1.1 hd
  have hrf := GM11.regionFacts_of_radial hpre hS hK.2.2 hE
  set Z := restraintUnion K ins (2 * θ) c (2 * lam)
  set Γ' := H.span ∅ {f ∈ H.E | lam < d z f}
  have hz'Z : z' ⊆ Z :=
    correspondingAtom_subset_restraintUnion hS hResp hE hK hd hz' hc hlam hz_lam
  have hZne : Z.Nonempty := ⟨c, hz'Z hc⟩
  have hZc : IsClosed Z := isClosed_restraintUnion hS c (2 * lam)
  have hZn : IsGammaNice K Z := isGammaNice_restraintUnion c (2 * lam)
  have hZs : IsSimplyConnectedSet Z := GM11.theorem_8_10_proof hS hsl hZne
  obtain ⟨hZuniv, hΓ'E⟩ :=
    restraintUnion_ne_univ_and_span_E_nonempty hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam
  have hZcompl_conn : IsConnected Zᶜ := GM11.isConnected_compl hS hZc hZn hZs hZne hZuniv
  have hW_pre : IsPreconnected (Zᶜ \ K.V) :=
    isPreconnected_sdiff_finite hS hZc.isOpen_compl hZcompl_conn.isPreconnected K.finite_V
  -- Each point of `Γ'.U` lies in `closure e` for some `e ∈ Γ'.E`.
  have hU_eq : Γ'.U = ⋃ e ∈ Γ'.E, closure e := by
    apply subset_antisymm
    · rintro x (hxV | hxE)
      · rcases hxV with ⟨hx0, -⟩ | hxV
        · exact hx0.elim
        · obtain ⟨e, he, hxe, -⟩ := mem_iUnion₂.mp hxV
          exact mem_iUnion₂.mpr ⟨e, by rwa [H.span_E], hxe⟩
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
        exact mem_iUnion₂.mpr ⟨e, by rwa [H.span_E], hxe⟩
    · exact iUnion₂_subset fun e he => Γ'.closure_subset_U he
  -- Map each `e ∈ H.E` to its radial region in `K.R`.
  have hex_reg : ∀ e ∈ H.E, ∃ s ∈ K.R, e ⊆ s := fun e he => by
    obtain ⟨p₀, hp₀⟩ := he.1
    have hUU : H.U ∩ K.U = H.V := hK.2.1.1
    have hoff : ∀ y ∈ e, y ∉ K.U := fun y hy hyK => by
      have : y ∈ H.U ∩ K.U := ⟨(he.2.1 hy).1, hyK⟩
      rw [hUU] at this
      exact (he.2.1 hy).2 this
    refine ⟨connectedComponentIn (univ \ K.U) p₀, (mem_R_iff K).mpr ⟨p₀, hoff p₀ hp₀, rfl⟩, ?_⟩
    exact he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hp₀
      fun y hy => ⟨mem_univ y, hoff y hy⟩
  choose! reg hreg_mem hreg_sub using hex_reg
  have hΓ'E_sub : Γ'.E ⊆ H.E := by
    rw [H.span_E]
    exact inter_subset_right
  intro U₁ U₂ hU₁ hU₂ hcov hne₁ hne₂
  by_contra hdisj
  have hdisj' : ∀ x ∈ Γ'.U, x ∈ U₁ → x ∉ U₂ := fun x hx hx₁ hx₂ => hdisj ⟨x, hx, hx₁, hx₂⟩
  have hedge_side : ∀ e ∈ Γ'.E, closure e ⊆ U₁ ∨ closure e ⊆ U₂ := fun e he => by
    have heH := hΓ'E_sub he
    have hcl_pre : IsPreconnected (closure e) := heH.2.2.1.isConnected.isPreconnected.closure
    have hcl_sub : closure e ⊆ Γ'.U := Γ'.closure_subset_U he
    refine isPreconnected_iff_subset_of_disjoint.mp hcl_pre U₁ U₂ hU₁ hU₂ (hcl_sub.trans hcov) ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx₁, hx₂⟩
    exact hdisj' x (hcl_sub hx) hx₁ hx₂
  set E₁ := {e ∈ Γ'.E | closure e ⊆ U₁}
  set E₂ := {e ∈ Γ'.E | closure e ⊆ U₂}
  set C₁ := ⋃ e ∈ E₁, closure (reg e)
  set C₂ := ⋃ e ∈ E₂, closure (reg e)
  have hC₁ : IsClosed C₁ :=
    (Γ'.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  have hC₂ : IsClosed C₂ :=
    (Γ'.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
  have hs_sub : ∀ s ∈ K.R, s ⊆ Zᶜ → s ⊆ C₁ ∪ C₂ := fun s hs hsZ => by
    obtain ⟨e, he, hes⟩ := hrf.1 s hs
    have heΓ' : e ∈ Γ'.E :=
      (edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he hs hes).mpr hsZ
    obtain ⟨p₀, hp₀⟩ := he.1
    have hreg_eq : reg e = s :=
      region_eq_of_mem (hreg_mem e he) hs (hreg_sub e he hp₀) (hes hp₀)
    rw [← hreg_eq]
    rcases hedge_side e heΓ' with h₁ | h₂
    · exact subset_closure.trans (subset_biUnion_of_mem (u := fun x => closure (reg x))
        (show e ∈ E₁ from ⟨heΓ', h₁⟩) |>.trans subset_union_left)
    · exact subset_closure.trans (subset_biUnion_of_mem (u := fun x => closure (reg x))
        (show e ∈ E₂ from ⟨heΓ', h₂⟩) |>.trans subset_union_right)
  have hZcompl_sub : Zᶜ ⊆ C₁ ∪ C₂ := by
    intro y hyZ
    refine (hC₁.union hC₂).closure_subset (mem_closure_iff.mpr fun O hO hyO => ?_)
    obtain ⟨q, ⟨hqO, hqZ⟩, hqU⟩ :=
      exists_notMem_U (Γ := K) hS (hO.inter hZc.isOpen_compl) ⟨y, hyO, hyZ⟩
    obtain ⟨s, hs, hqs⟩ := exists_region_of_notMem hqU
    have hsZ : s ⊆ Zᶜ := fun x hx hxZ => hqZ (nice_region hZn hs ⟨x, hx, hxZ⟩ hqs)
    exact ⟨q, hqO, hs_sub s hs hsZ hqs⟩
  have hW_cov : Zᶜ \ K.V ⊆ C₁ ∪ C₂ := sdiff_subset.trans hZcompl_sub
  have hW_ne₁ : ((Zᶜ \ K.V) ∩ C₁).Nonempty := by
    obtain ⟨x₁, hx₁U, hx₁⟩ := hne₁
    rw [hU_eq] at hx₁U
    obtain ⟨e₁, he₁, hxe₁⟩ := mem_iUnion₂.mp hx₁U
    have he₁U₁ : closure e₁ ⊆ U₁ := (hedge_side e₁ he₁).resolve_right fun h₂ =>
      hdisj' x₁ (Γ'.closure_subset_U he₁ hxe₁) hx₁ (h₂ hxe₁)
    have he₁H := hΓ'E_sub he₁
    obtain ⟨p₁, hp₁⟩ := he₁H.1
    have hp₁s : p₁ ∈ reg e₁ := hreg_sub e₁ he₁H hp₁
    have hs₁Z : reg e₁ ⊆ Zᶜ :=
      (edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he₁H
        (hreg_mem e₁ he₁H) (hreg_sub e₁ he₁H)).mp he₁
    have hp₁V : p₁ ∉ K.V := fun hV =>
      region_subset (hreg_mem e₁ he₁H) hp₁s (K.V_subset_U hV)
    exact ⟨p₁, ⟨hs₁Z hp₁s, hp₁V⟩,
      mem_biUnion (show e₁ ∈ E₁ from ⟨he₁, he₁U₁⟩) (subset_closure hp₁s)⟩
  have hW_ne₂ : ((Zᶜ \ K.V) ∩ C₂).Nonempty := by
    obtain ⟨x₂, hx₂U, hx₂⟩ := hne₂
    rw [hU_eq] at hx₂U
    obtain ⟨e₂, he₂, hxe₂⟩ := mem_iUnion₂.mp hx₂U
    have he₂U₂ : closure e₂ ⊆ U₂ := (hedge_side e₂ he₂).resolve_left fun h₁ =>
      hdisj' x₂ (Γ'.closure_subset_U he₂ hxe₂) (h₁ hxe₂) hx₂
    have he₂H := hΓ'E_sub he₂
    obtain ⟨p₂, hp₂⟩ := he₂H.1
    have hp₂s : p₂ ∈ reg e₂ := hreg_sub e₂ he₂H hp₂
    have hs₂Z : reg e₂ ⊆ Zᶜ :=
      (edge_mem_span_iff hS hResp hE hK hd hd_eq hz hz' hc hlam hz_lam he₂H
        (hreg_mem e₂ he₂H) (hreg_sub e₂ he₂H)).mp he₂
    have hp₂V : p₂ ∉ K.V := fun hV =>
      region_subset (hreg_mem e₂ he₂H) hp₂s (K.V_subset_U hV)
    exact ⟨p₂, ⟨hs₂Z hp₂s, hp₂V⟩,
      mem_biUnion (show e₂ ∈ E₂ from ⟨he₂, he₂U₂⟩) (subset_closure hp₂s)⟩
  obtain ⟨y, ⟨hyZ, hyV⟩, hyC₁, hyC₂⟩ :=
    isPreconnected_closed_iff.mp hW_pre C₁ C₂ hC₁ hC₂ hW_cov hW_ne₁ hW_ne₂
  obtain ⟨e₁, ⟨he₁, he₁U₁⟩, hy₁⟩ := mem_iUnion₂.mp hyC₁
  obtain ⟨e₂, ⟨he₂, he₂U₂⟩, hy₂⟩ := mem_iUnion₂.mp hyC₂
  have he₁H := hΓ'E_sub he₁
  have he₂H := hΓ'E_sub he₂
  by_cases hyU : y ∈ K.U
  · obtain ⟨h, hh, hyh⟩ := K.exists_edge_of_mem hyU hyV
    have hh₁ : closure h ⊆ closure (reg e₁) :=
      isClosed_closure.closure_subset_iff.mpr
        (edge_subset_closure_of_incident hS hh (hreg_mem e₁ he₁H) ⟨y, hyh, hy₁⟩)
    have hh₂ : closure h ⊆ closure (reg e₂) :=
      isClosed_closure.closure_subset_iff.mpr
        (edge_subset_closure_of_incident hS hh (hreg_mem e₂ he₂H) ⟨y, hyh, hy₂⟩)
    obtain ⟨v, hv, -, -, w, -, -, hcap, -⟩ := spoke_ends hpre hS hh
    have hv_cl : v ∈ closure h := by
      have : v ∈ closure h ∩ K.V := by rw [hcap]; simp
      exact this.1
    have hv₁ : v ∈ closure e₁ :=
      hrf.2.2 (reg e₁) (hreg_mem e₁ he₁H) e₁ he₁H (hreg_sub e₁ he₁H) v hv (hh₁ hv_cl)
    have hv₂ : v ∈ closure e₂ :=
      hrf.2.2 (reg e₂) (hreg_mem e₂ he₂H) e₂ he₂H (hreg_sub e₂ he₂H) v hv (hh₂ hv_cl)
    exact hdisj' v (Γ'.closure_subset_U he₁ hv₁) (he₁U₁ hv₁) (he₂U₂ hv₂)
  · obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    obtain ⟨q₁, hq₁s, hq₁r⟩ := mem_closure_iff.mp hy₁ s (region_isOpen hs) hys
    obtain ⟨q₂, hq₂s, hq₂r⟩ := mem_closure_iff.mp hy₂ s (region_isOpen hs) hys
    have hs₁ : reg e₁ = s := region_eq_of_mem (hreg_mem e₁ he₁H) hs hq₁r hq₁s
    have hs₂ : reg e₂ = s := region_eq_of_mem (hreg_mem e₂ he₂H) hs hq₂r hq₂s
    have he₁₂ : e₁ = e₂ :=
      hrf.2.1 s hs e₁ he₁H e₂ he₂H (hs₁ ▸ hreg_sub e₁ he₁H) (hs₂ ▸ hreg_sub e₂ he₂H)
    obtain ⟨p₀, hp₀⟩ := he₁H.1
    exact hdisj' p₀ (Γ'.closure_subset_U he₁ (subset_closure hp₀))
      (he₁U₁ (subset_closure hp₀)) (he₂U₂ (subset_closure (he₁₂ ▸ hp₀)))

end GraphMinor.GM12
