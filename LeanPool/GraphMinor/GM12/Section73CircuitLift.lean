/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkLiftEdges
public import LeanPool.GraphMinor.GM12.Section73SplicedCircuit
import LeanPool.GraphMinor.GM12.Section73CircuitPath
import LeanPool.GraphMinor.GM12.Section73UnchangedCircuit
import LeanPool.GraphMinor.GM12.Section73DrawingImages
import LeanPool.GraphMinor.GM12.Section73RadialSpliceFibre
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# The old circuit inside the constructed lifted walk

For XII (7.3), Claim (1), page 262, remove the two new spokes
at the merged hub from the circuit. Lift the remaining path
unchanged and recover the two old region hubs. The replacement
edges recorded by the lifted walk contain the required two- or
four-edge splice. This constructs the old circuit inside that
walk, with the paper's length and deleted-vertex alternatives.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

open Classical in
private theorem spliced_lift_edges_map_into_circuit
    {S : Type*}
    [TopologicalSpace S]
    [T2Space S]
    {K : Drawing S}
    {v : S}
    (f : C(S, S))
    {C : Drawing S}
    (x : S)
    (y : S)
    (e : Set S)
    (e' : Set S)
    (Q : GraphWalk K.toGraph x y)
    (g : Set S)
    (p : S)
    (hfg : ⇑f '' g = e)
    (g' : Set S)
    (q : S)
    (hfg' : ⇑f '' g' = e')
    (k : Set S)
    (hk : k ∈ K.E)
    (hkl : K.toGraph.IsLink k v p)
    (k' : Set S)
    (hk' : k' ∈ K.E)
    (hkl' : K.toGraph.IsLink k' v q)
    (D : Drawing S)
    (hDE : D.E = if p = q then insert g (insert g' {e | e ∈ Q.edges}) else insert k (insert g
      (insert g' (insert k' {e | e ∈ Q.edges}))))
    (heC : e ∈ C.E)
    (heC' : e' ∈ C.E)
    (hQimg : ⇑f '' (walkDrawing K Q).U ⊆ C.U)
    (hStarImg : ∀ s ∈ K.E, v ∈ closure s → ⇑f '' s ⊆ C.U) :
    ∀ s ∈ D.E, ⇑f '' s ⊆ C.U := by
  intro s hs
  have hsCases : s = k ∨ s = g ∨ s = g' ∨ s = k' ∨ s ∈ Q.edges := by
    rw [hDE] at hs
    by_cases hpq : p = q
    · rw [ite_eq_left hpq] at hs
      rcases hs with rfl | rfl | hs
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
    · rw [ite_eq_right hpq] at hs
      exact hs
  rcases hsCases with hsEq | hsEq | hsEq | hsEq | hs
  · subst s
    exact hStarImg k hk (hkl.2.2.2.superset (Or.inl rfl)).1
  · subst s
    rw [hfg]; exact fun z hz => (heC.2.1 hz).1
  · subst s
    rw [hfg']; exact fun z hz => (heC'.2.1 hz).1
  · subst s
    exact hStarImg k' hk' (hkl'.2.2.2.superset (Or.inl rfl)).1
  · apply (image_mono (show s ⊆ (walkDrawing K Q).U from ?_)).trans hQimg
    have hsQ : s ∈ (walkDrawing K Q).E := by rw [walkDrawing_E]; exact hs
    exact fun z hz => (hsQ.2.1 hz).1

/-- Construct the old circuit in the hub case of XII (7.3),
Claim (1), page 262, inside the actual lifted walk. Its length
is the new circuit's length plus twice `ε`, with `ε` at most
one; when `ε = 1`, the old circuit contains the deleted vertex. -/
theorem exists_circuit_in_lifted_walk_through_hub
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJpre : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J)
    (hJtwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    {a : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph a a)
    (hpoints : (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r')
    (hedges : ∀ e ∈ W.edges, ∀ g ∈ spokeReplacementEdges K J v f e, g ∈ W'.edges)
    {C : Drawing S} (hC : C.IsCircuit) (hCW : C.IsSubdrawing (walkDrawing J W))
    (hvC : v ∈ C.V) :
    ∃ (D : Drawing S) (ε : ℕ), D.IsCircuit ∧ D.IsSubdrawing (walkDrawing K W') ∧
      ε ≤ 1 ∧ D.length = C.length + 2 * ε ∧ (ε = 1 → v ∈ D.V) ∧
      f '' D.U = C.U ∧
      ((D.U ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)).Subsingleton ∨
        ∃ p q, IsLineWithEnds
          (D.U ∩ ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) p q) := by
  classical
  let : CompactSpace S := hS.1
  have hCJ : C.IsSubdrawing J := hCW.trans (walkDrawing_isSubdrawing J W)
  have hV : J.V ⊆ K.V := by
    intro x hx
    rw [hJV, image_radial_vertices_eq hS hK hE hv hr' hvr' hfix hcollapse] at hx
    rcases hx with hx | hxv
    · exact hx.1
    · exact hxv ▸ hK.2.1.2.1 hv
  have hvJ : v ∈ J.V := hCJ.1 hvC
  have hretain : ∀ e x y, J.toGraph.IsLink e x y → x ≠ v → y ≠ v → e ∈ K.E := by
    intro e x y hel
    obtain ⟨_, _, _, _, hret⟩ := exists_edge_walk_lift hS hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV hJE hel
    exact hret
  have hloop : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y := by
    intro e x y hel hxy
    subst y
    have hb := bipartite_of_preRadial hJpre e x x hel
    by_cases hx : x ∈ (deleteVertices Γ {v}).V
    · exact (hb.mp hx) hx
    · exact hx (hb.mpr hx)
  obtain ⟨x, y, e, e', hel, hel', P, hP, hvP, hee, _, _, hCV, hCE, hClen⟩ :=
    exists_circuit_path_in_drawing hC hCJ hloop hvC
  obtain ⟨Q, hQS, hQE, hQout⟩ := exists_unchanged_path_lift hS ⟨hJtwo, hJpre⟩
    hr' hvr' hvJ hV hretain P hvP
  have hQsimple : Q.IsSimple := by change Q.support.Nodup; rw [hQS]; exact hP
  have hQlen : Q.length = P.length := congrArg List.length hQE
  obtain ⟨g, p, hg, hvg, hfg, hpr, hpK, hpn, _, hgl⟩ :=
    exists_old_spoke_at_contracted_vertex hS hK hv hr' f hfix hfibre hJV hJE hel
  obtain ⟨g', q, hg', hvg', hfg', hqr, hqK, hqn, _, hgl'⟩ :=
    exists_old_spoke_at_contracted_vertex hS hK hv hr' f hfix hfibre hJV hJE hel'.symm
  obtain ⟨k, hk, hkl⟩ := exists_spoke_to_hub_in_deleted_region hS hK hE hv hr' hvr' hpK hpn hpr
  obtain ⟨k', hk', hkl'⟩ := exists_spoke_to_hub_in_deleted_region hS hK hE hv hr' hvr' hqK hqn hqr
  have hpQ : p ∉ Q.support := fun hpQ => hQout p hpQ hpr
  have hqQ : q ∉ Q.support := fun hqQ => hQout q hqQ hqr
  have hvQ : v ∉ Q.support := fun hvQ => hQout v hvQ hvr'
  have hpv : p ≠ v := fun hpv => hpn (hpv ▸ hv)
  have hqv : q ≠ v := fun hqv => hqn (hqv ▸ hv)
  have hgg : g ≠ g' := by
    intro hgg
    exact hee (hfg.symm.trans ((congrArg (image f) hgg).trans hfg'))
  have heW : e ∈ W.edges := by
    have heC : e ∈ C.E := by rw [hCE]; exact Or.inl rfl
    have heD := hCW.2 heC
    rw [walkDrawing_E] at heD
    exact heD
  have heW' : e' ∈ W.edges := by
    have heC : e' ∈ C.E := by rw [hCE]; exact Or.inr (Or.inl rfl)
    have heD := hCW.2 heC
    rw [walkDrawing_E] at heD
    exact heD
  have hgN : g ∈ (walkDrawing K W').E := by
    rw [walkDrawing_E]
    exact hedges e heW g ⟨x, g, p, hel, hvg, hfg, hgl, Or.inl rfl⟩
  have hkN : k ∈ (walkDrawing K W').E := by
    rw [walkDrawing_E]
    exact hedges e heW k ⟨x, g, p, hel, hvg, hfg, hgl, Or.inr hkl⟩
  have hgN' : g' ∈ (walkDrawing K W').E := by
    rw [walkDrawing_E]
    exact hedges e' heW' g' ⟨y, g', q, hel'.symm, hvg', hfg', hgl', Or.inl rfl⟩
  have hkN' : k' ∈ (walkDrawing K W').E := by
    rw [walkDrawing_E]
    exact hedges e' heW' k' ⟨y, g', q, hel'.symm, hvg', hfg', hgl', Or.inr hkl'⟩
  have hPD : (walkDrawing J P).IsSubdrawing C := by
    constructor
    · rw [walkDrawing_V, hCV]
      exact fun z hz => Or.inr hz
    · rw [walkDrawing_E, hCE]
      exact fun d hd => Or.inr (Or.inr hd)
  have hQP : walkDrawing K Q = walkDrawing J P := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, walkDrawing_V, hQS]
    · rw [walkDrawing_E, walkDrawing_E, hQE]
  have hdis := subdrawing_disjoint_region_of_notMem_hub hS ⟨hJtwo, hJpre⟩ hr' hvr' hvJ
    (walkDrawing_isSubdrawing J P) (by rw [walkDrawing_V]; exact hvP)
  have hQU : (walkDrawing K Q).U ⊆ (walkDrawing K W').U := by
    rw [hQP]
    intro z hz
    have hzn : z ∉ r' := fun hzr => disjoint_left.mp hdis hz hzr
    have hzW : z ∈ (walkDrawing J W).U \ r' := ⟨hCW.U_subset (hPD.U_subset hz), hzn⟩
    rw [← hpoints] at hzW
    exact hzW.1
  have hQN := isSubdrawing_of_U_subset_common (walkDrawing_isSubdrawing K Q)
    (walkDrawing_isSubdrawing K W') hQU
  have hQedges : ∀ d ∈ Q.edges, d ∈ (walkDrawing K W').E := by
    intro d hd
    apply hQN.2
    rw [walkDrawing_E]
    exact hd
  obtain ⟨D, hD, hDN, hDlen, hDV, hDE⟩ := exists_spliced_circuit_in_subdrawing
    (walkDrawing_isSubdrawing K W') hkl hgl hgl'.symm hkl'.symm Q hQsimple
    hpQ hqQ hvQ hpv hqv hgg hkN hgN hgN' hkN' hQedges
  have hQfix : ∀ z ∈ (walkDrawing K Q).U, f z = z := by
    rw [hQP]
    exact fun z hz => hfix z (fun hzr => disjoint_left.mp hdis hz hzr)
  have hfp : f p = v := hcollapse p (Or.inr (mem_iUnion₂.mpr
    ⟨k, ⟨hk, (hkl.2.2.2.superset (Or.inl rfl)).1⟩,
      (hkl.2.2.2.superset (Or.inr rfl)).1⟩))
  have hfq : f q = v := hcollapse q (Or.inr (mem_iUnion₂.mpr
    ⟨k', ⟨hk', (hkl'.2.2.2.superset (Or.inl rfl)).1⟩,
      (hkl'.2.2.2.superset (Or.inr rfl)).1⟩))
  have hfv : f v = v := hcollapse v (Or.inl rfl)
  have hQV : ∀ z ∈ Q.support, z ∈ D.V := by
    intro z hz
    rw [hDV]
    exact Or.inl (Or.inl hz)
  have hQE_D : ∀ d ∈ Q.edges, d ∈ D.E := by
    intro d hd
    rw [hDE]
    split_ifs <;> simp only [mem_insert_iff, mem_ofPred_eq] <;> tauto
  have hgD : g ∈ D.E := by
    rw [hDE]
    split_ifs <;> simp only [mem_insert_iff, mem_ofPred_eq] <;> tauto
  have hgD' : g' ∈ D.E := by
    rw [hDE]
    split_ifs <;> simp only [mem_insert_iff, mem_ofPred_eq] <;> tauto
  have heC : e ∈ C.E := by rw [hCE]; exact Or.inl rfl
  have heC' : e' ∈ C.E := by rw [hCE]; exact Or.inr (Or.inl rfl)
  have hQV_C : ∀ z ∈ Q.support, z ∈ C.V := by
    intro z hz
    rw [hCV]
    exact Or.inr (hQS ▸ hz)
  have hQimg : f '' (walkDrawing K Q).U ⊆ C.U := by
    rintro z ⟨w, hw, rfl⟩
    rw [hQfix w hw]
    rw [hQP] at hw
    exact hPD.U_subset hw
  have hStarImg : ∀ s ∈ K.E, v ∈ closure s → f '' s ⊆ C.U := by
    intro s hs hvs z hz
    obtain ⟨w, hws, rfl⟩ := hz
    rw [hcollapse w (Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hs, hvs⟩, subset_closure hws⟩))]
    exact C.V_subset_U hvC
  have hVimage : f '' D.V ⊆ C.U := by
    rintro z ⟨w, hw, rfl⟩
    have hwCases : w ∈ Q.support ∨ w = p ∨ w = q ∨ w = v := by
      rw [hDV] at hw
      by_cases hpq : p = q
      · rw [ite_eq_left hpq] at hw
        simp only [mem_union, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff,
          mem_empty_iff_false, or_false] at hw
        tauto
      · rw [ite_eq_right hpq] at hw
        simp only [mem_union, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hw
        tauto
    rcases hwCases with hw | rfl | rfl | rfl
    · have hwDraw : w ∈ (walkDrawing K Q).V := by rw [walkDrawing_V]; exact hw
      rw [hQfix w ((walkDrawing K Q).V_subset_U hwDraw)]
      exact C.V_subset_U (hQV_C w hw)
    · rw [hfp]; exact C.V_subset_U hvC
    · rw [hfq]; exact C.V_subset_U hvC
    · rw [hfv]; exact C.V_subset_U hvC
  have hEimage : ∀ s ∈ D.E, f '' s ⊆ C.U := by
    exact spliced_lift_edges_map_into_circuit (S := S) (K := K) (v := v) f (C := C) x y e e' Q g p
      hfg g' q hfg' k hk hkl k' hk' hkl' D hDE heC heC' hQimg hStarImg
  have hVback : C.V ⊆ f '' D.U := by
    intro z hz
    rw [hCV] at hz
    rcases hz with rfl | hz
    · have hpD : p ∈ D.V := by rw [hDV]; exact Or.inl (Or.inr (Or.inl rfl))
      exact ⟨p, D.V_subset_U hpD, hfp⟩
    · have hzQ : z ∈ Q.support := hQS.symm ▸ hz
      have hzDraw : z ∈ (walkDrawing K Q).V := by rw [walkDrawing_V]; exact hzQ
      exact ⟨z, D.V_subset_U (hQV z hzQ),
        hQfix z ((walkDrawing K Q).V_subset_U hzDraw)⟩
  have hEback : ∀ s ∈ C.E, s ⊆ f '' D.U := by
    intro s hs z hz
    rw [hCE] at hs
    rcases hs with rfl | rfl | hs
    · obtain ⟨w, hw, hfw⟩ := (hfg.symm ▸ hz : z ∈ f '' g)
      exact ⟨w, (hgD.2.1 hw).1, hfw⟩
    · obtain ⟨w, hw, hfw⟩ := (hfg'.symm ▸ hz : z ∈ f '' g')
      exact ⟨w, (hgD'.2.1 hw).1, hfw⟩
    · have hsQ : s ∈ Q.edges := hQE.symm ▸ hs
      have hsD := hQE_D s hsQ
      have hsDraw : s ∈ (walkDrawing K Q).E := by rw [walkDrawing_E]; exact hsQ
      exact ⟨z, (hsD.2.1 hz).1, hQfix z ((hsDraw.2.1 hz).1)⟩
  have himage := drawing_image_eq_of_vertex_edge_images f hVimage hEimage hVback hEback
  have hDisQ : Disjoint (walkDrawing K Q).U r' := hQP.symm ▸ hdis
  have hshape := radial_spliced_circuit_fibre_shape hS ⟨hK.1, hK.2.1⟩ hv hr' hvr'
    hkl hgl hgl' hkl' hvg hvg' Q hDisQ hDV hDE
  refine ⟨D, if p = q then 0 else 1, hD, hDN, ?_, ?_, ?_, himage, hshape⟩
  · split_ifs <;> omega
  · rw [hDlen, hQlen, hClen]
    split_ifs <;> omega
  · intro hε
    have hpq : p ≠ q := by intro heq; simp only [heq, ite_true] at hε; omega
    rw [hDV, ite_eq_right hpq]
    exact Or.inr rfl

end GraphMinor.GM12
