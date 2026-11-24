/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section3Dual
public import LeanPool.GraphMinor.GM06.RegionCurve
import Mathlib.Analysis.Convex.PathConnected

/-!
# Graph Minors VI, Section 3: Induced Subdrawings and Chain Reductions for (3.6)

This file develops the subdrawing reduction machinery for the sufficiency proof of
Robertson and Seymour, *Graph Minors. VI. Disjoint paths across a disc*, (3.6) (page 122):
- `induceDrawing G V'`: the subdrawing of `G` induced by a subset of vertices `V' ⊆ G.V`,
  matching `G.toGraph.induce V'` and `G.toGraph.deleteVerts S`.
- `isConnected_compPointSet`: the point-set `compPointSet C` of a connected component `C` of
  `G.toGraph` is connected.
- `exists_region_of_same_component_compl` and `liftChain_of_subdrawing`: lifting `(x, y)`-chains
  from an induced subdrawing `G₁` to `G` via `disc_janiszewski_disjoint`.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric Graph GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Induced Subdrawings `induceDrawing` -/

/-- The subdrawing of `G` induced by a subset of vertices `V'`: its vertices are `V' ∩ G.V` and its
edges are the edges of `G` whose ends both lie in `V'`. -/
def induceDrawing [T1Space S] (G : Drawing S) (V' : Set S) : Drawing S :=
  G.span V' {e ∈ G.E | closure e ∩ G.V ⊆ V'}

theorem induceDrawing_V [T1Space S] (G : Drawing S) {V' : Set S} (hV' : V' ⊆ G.V) :
    (induceDrawing G V').V = V' := by
  rw [induceDrawing, Drawing.span_V, Drawing.spanV, inter_eq_left.mpr hV']
  refine subset_antisymm (union_subset subset_rfl ?_) subset_union_left
  rintro x hx
  obtain ⟨e, ⟨⟨_, hsub⟩, _⟩, hx_cap⟩ := mem_iUnion₂.mp hx
  exact hsub hx_cap

theorem induceDrawing_E [T1Space S] (G : Drawing S) (V' : Set S) :
    (induceDrawing G V').E = {e ∈ G.E | closure e ∩ G.V ⊆ V'} := by
  rw [induceDrawing, Drawing.span_E]
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

theorem induceDrawing_U [T1Space S] (G : Drawing S) {V' : Set S} (hV' : V' ⊆ G.V) :
    (induceDrawing G V').U = V' ∪ ⋃ e ∈ (induceDrawing G V').E, e := by
  have h1 : (induceDrawing G V').U =
      (induceDrawing G V').V ∪ ⋃ e ∈ {e ∈ G.E | closure e ∩ G.V ⊆ V'} ∩ G.E, closure e := rfl
  rw [h1, induceDrawing_V G hV', induceDrawing_E]
  ext x
  simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
  constructor
  · rintro (hxV' | ⟨e, ⟨⟨heG, hsub⟩, _⟩, hxcl⟩)
    · exact Or.inl hxV'
    · by_cases hxV : x ∈ G.V
      · exact Or.inl (hsub ⟨hxcl, hxV⟩)
      · right
        refine ⟨e, ⟨heG, hsub⟩, ?_⟩
        rw [← G.closure_diff_V heG]
        exact ⟨hxcl, hxV⟩
  · rintro (hxV' | ⟨e, ⟨heG, hsub⟩, hxe⟩)
    · exact Or.inl hxV'
    · exact Or.inr ⟨e, ⟨⟨heG, hsub⟩, heG⟩, subset_closure hxe⟩

theorem induceDrawing_U_inter_V [T1Space S] (G : Drawing S) {V' : Set S} (hV' : V' ⊆ G.V) :
    (induceDrawing G V').U ∩ G.V = V' := by
  rw [induceDrawing_U G hV']
  ext x
  simp only [mem_inter_iff, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hxV' | ⟨e, heE, hxe⟩, hxV⟩
    · exact hxV'
    · rw [induceDrawing_E] at heE
      have heG : e ∈ G.E := heE.1
      exact ((heG.2.1 hxe).2 hxV).elim
  · intro hxV'
    exact ⟨Or.inl hxV', hV' hxV'⟩

theorem induceDrawing_isSubdrawing [T1Space S] (G : Drawing S) {V' : Set S} (hV' : V' ⊆ G.V) :
    (induceDrawing G V').IsSubdrawing G := by
  refine ⟨?_, ?_⟩
  · rw [induceDrawing_V G hV']
    exact hV'
  · rw [induceDrawing_E]
    exact fun _ he => he.1

theorem induceDrawing_isProper [T1Space S] (G : Drawing S) (hProper : G.IsProper)
    {V' : Set S} (hV' : V' ⊆ G.V) :
    (induceDrawing G V').IsProper := by
  rintro x ⟨hxbd, hxU'⟩
  have hsub := (induceDrawing_isSubdrawing G hV').U_subset
  have hxV : x ∈ G.V := hProper ⟨hxbd, hsub hxU'⟩
  rw [induceDrawing_V G hV', ← induceDrawing_U_inter_V G hV']
  exact ⟨hxU', hxV⟩

theorem induceDrawing_toGraph_eq_induce [T1Space S] (G : Drawing S) {V' : Set S}
    (hV' : V' ⊆ G.V) :
    (induceDrawing G V').toGraph = G.toGraph.induce V' := by
  refine Graph.ext ?_ fun e x y => ?_
  · change (induceDrawing G V').V = V'
    exact induceDrawing_V G hV'
  · change (e ∈ (induceDrawing G V').E ∧ x ∈ (induceDrawing G V').V ∧
        y ∈ (induceDrawing G V').V ∧ closure e ∩ (induceDrawing G V').V = {x, y}) ↔
      (G.toGraph.induce V').IsLink e x y
    rw [induce_isLink, induceDrawing_V G hV', induceDrawing_E]
    constructor
    · rintro ⟨⟨heG, hsub⟩, hxV', hyV', hcap⟩
      have hcap_G : closure e ∩ G.V = {x, y} := by
        rw [← hcap]
        ext z
        simp only [mem_inter_iff]
        exact ⟨fun ⟨hzcl, hzV⟩ => ⟨hzcl, hsub ⟨hzcl, hzV⟩⟩,
          fun ⟨hzcl, hzV'⟩ => ⟨hzcl, hV' hzV'⟩⟩
      exact ⟨⟨heG, hV' hxV', hV' hyV', hcap_G⟩, hxV', hyV'⟩
    · rintro ⟨⟨heG, _, _, hcap_G⟩, hxV', hyV'⟩
      have hsub : closure e ∩ G.V ⊆ V' := by
        rw [hcap_G]
        rintro z (rfl | hzy)
        · exact hxV'
        · rw [mem_singleton_iff.mp hzy]
          exact hyV'
      have hcap : closure e ∩ V' = {x, y} := by
        rw [← hcap_G]
        ext z
        simp only [mem_inter_iff]
        exact ⟨fun ⟨hzcl, hzV'⟩ => ⟨hzcl, hV' hzV'⟩,
          fun ⟨hzcl, hzV⟩ => ⟨hzcl, hsub ⟨hzcl, hzV⟩⟩⟩
      exact ⟨⟨heG, hsub⟩, hxV', hyV', hcap⟩

theorem induceDrawing_toGraph_deleteVerts [T1Space S] (G : Drawing S) (X : Set S) :
    (induceDrawing G (G.V \ X)).toGraph = G.toGraph.deleteVerts X := by
  rw [induceDrawing_toGraph_eq_induce G sdiff_subset]
  refine Graph.ext ?_ fun e x y => ?_
  · rw [vertexSet_deleteVerts]
    rfl
  · rw [induce_isLink, deleteVerts_isLink]
    exact ⟨fun ⟨hl, hx, hy⟩ => ⟨hl, hx.2, hy.2⟩,
      fun ⟨hl, hx, hy⟩ => ⟨hl, ⟨hl.left_mem, hx⟩, ⟨hl.right_mem, hy⟩⟩⟩

theorem induceDrawing_toGraph_of_component [T1Space S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) :
    (induceDrawing G V(C)).toGraph = C := by
  obtain ⟨x, hx⟩ := hC.2.1.1
  rw [induceDrawing_toGraph_eq_induce G hC.1.vertexSet_mono]
  have heq := hC.eq_compOf_of_mem hx
  rw [heq]
  rfl

theorem induceDrawing_E_of_component [T2Space S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) :
    (induceDrawing G V(C)).E = E(C) := by
  rw [induceDrawing_E]
  ext e
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨heG, hsub⟩
    obtain ⟨γ, _, h0, _, _, _, _, hlink⟩ := exists_edge_param_isLink G heG
    have h0_cl : γ 0 ∈ closure e ∩ G.V := by
      rw [hlink.2.2.2]; exact mem_insert (γ 0) {γ 1}
    exact ((hC.isLink_iff_of_mem (hsub h0_cl)).mpr hlink).edge_mem
  · intro heC
    obtain ⟨u, v, hlinkC⟩ := C.exists_isLink_of_mem_edgeSet heC
    have hlinkG := hlinkC.mono hC.1
    refine ⟨hlinkG.1, ?_⟩
    rw [hlinkG.2.2.2]
    rintro z (rfl | hzv)
    · exact hlinkC.left_mem
    · rw [mem_singleton_iff.mp hzv]
      exact hlinkC.right_mem

theorem induceDrawing_U_of_component [T2Space S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) :
    (induceDrawing G V(C)).U = compPointSet C := by
  rw [induceDrawing_U G hC.1.vertexSet_mono, induceDrawing_E_of_component G hC, compPointSet]

/-! ## 2. Connectedness of `compPointSet` and Unions of Components -/

theorem isConnected_compPointSet [T2Space S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) :
    IsConnected (compPointSet C) := by
  obtain ⟨x₀, hx₀⟩ := hC.2.1.1
  have h_join : ∀ z ∈ compPointSet C,
      ∃ K ⊆ compPointSet C, IsConnected K ∧ x₀ ∈ K ∧ z ∈ K := by
    intro z hz
    rcases hz with hzV | hzE
    · obtain ⟨W⟩ := hC.2.1.2 x₀ hx₀ z hzV
      obtain ⟨K, _, hK_conn, hx₀K, hzK, hK_sub, _, _⟩ :=
        exists_compact_connected_of_walk G hC.1 W
      exact ⟨K, hK_sub, hK_conn, hx₀K, hzK⟩
    · simp only [mem_iUnion, exists_prop] at hzE
      rcases hzE with ⟨e, heC, hze⟩
      obtain ⟨u, v, hlinkC⟩ := C.exists_isLink_of_mem_edgeSet heC
      obtain ⟨W⟩ := hC.2.1.2 x₀ hx₀ u hlinkC.left_mem
      obtain ⟨KW, _, hKW_conn, hx₀W, huW, hKW_sub, _, _⟩ :=
        exists_compact_connected_of_walk G hC.1 W
      have hlinkG : G.toGraph.IsLink e u v := hlinkC.mono hC.1
      have hu_cl : u ∈ closure e := by
        have : u ∈ closure e ∩ G.V := by rw [hlinkG.2.2.2]; exact mem_insert u {v}
        exact this.1
      have hcl_sub : closure e ⊆ compPointSet C := by
        rw [compPointSet_eq_closure_union G hC]
        intro y hy
        exact Or.inr (mem_iUnion₂.mpr ⟨e, heC, hy⟩)
      refine ⟨KW ∪ closure e, union_subset hKW_sub hcl_sub,
        hKW_conn.union ⟨u, huW, hu_cl⟩ (isConnected_closure_edge G hlinkG.1),
        Or.inl hx₀W, Or.inr (subset_closure hze)⟩
  choose! K hK_sub hK_conn hx₀K hzK using h_join
  have h_eq : compPointSet C = ⋃₀ (K '' compPointSet C) := by
    ext z
    simp only [mem_sUnion, mem_image, exists_exists_and_eq_and]
    exact ⟨fun hz => ⟨z, hz, hzK z hz⟩, fun ⟨w, hw, hzw⟩ => hK_sub w hw hzw⟩
  refine ⟨⟨x₀, Or.inl hx₀⟩, ?_⟩
  rw [h_eq]
  refine isPreconnected_sUnion x₀ (K '' compPointSet C) ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hx₀K z hz
  · rintro _ ⟨z, hz, rfl⟩
    exact (hK_conn z hz).isPreconnected

/-- If `S_comp ⊆ graphComponents G.toGraph` is a family of components of `G` and
`V' = ⋃ C ∈ S_comp, V(C)`, then `(induceDrawing G V').U = ⋃ C ∈ S_comp, compPointSet C` and
`G.U \ (induceDrawing G V').U = ⋃ C ∈ graphComponents G.toGraph \ S_comp, compPointSet C`. -/
theorem induceDrawing_U_biUnion_components [T2Space S] (G : Drawing S)
    {S_comp : Set (Graph S (Set S))} (hS_comp : S_comp ⊆ graphComponents G.toGraph) :
    let V' := ⋃ C ∈ S_comp, V(C)
    (induceDrawing G V').U = (⋃ C ∈ S_comp, compPointSet C) ∧
      G.U \ (induceDrawing G V').U =
        (⋃ C ∈ graphComponents G.toGraph \ S_comp, compPointSet C) := by
  intro V'
  have hV' : V' ⊆ G.V := iUnion₂_subset fun C hC => (hS_comp hC).1.vertexSet_mono
  have hE_iff : ∀ e, e ∈ (induceDrawing G V').E ↔ ∃ C ∈ S_comp, e ∈ E(C) := by
    intro e
    rw [induceDrawing_E]
    constructor
    · rintro ⟨heG, hsub⟩
      obtain ⟨γ, _, h0, _, _, _, _, hlink⟩ := exists_edge_param_isLink G heG
      have h0_cl : γ 0 ∈ closure e ∩ G.V := by
        rw [hlink.2.2.2]; exact mem_insert (γ 0) {γ 1}
      have h0_V' : γ 0 ∈ V' := hsub h0_cl
      obtain ⟨C, hC_S, h0_C⟩ := mem_iUnion₂.mp h0_V'
      have hC := hS_comp hC_S
      exact ⟨C, hC_S, ((hC.isLink_iff_of_mem h0_C).mpr hlink).edge_mem⟩
    · rintro ⟨C, hC_S, heC⟩
      have hC := hS_comp hC_S
      obtain ⟨u, v, hlinkC⟩ := C.exists_isLink_of_mem_edgeSet heC
      have hlinkG := hlinkC.mono hC.1
      refine ⟨hlinkG.1, ?_⟩
      rw [hlinkG.2.2.2]
      rintro z (rfl | hzv)
      · exact mem_iUnion₂.mpr ⟨C, hC_S, hlinkC.left_mem⟩
      · rw [mem_singleton_iff.mp hzv]
        exact mem_iUnion₂.mpr ⟨C, hC_S, hlinkC.right_mem⟩
  have hU_eq : (induceDrawing G V').U = ⋃ C ∈ S_comp, compPointSet C := by
    rw [induceDrawing_U G hV']
    ext x
    simp only [V', compPointSet, mem_union, mem_iUnion, exists_prop, hE_iff]
    constructor
    · rintro (⟨C, hC_S, hxV⟩ | ⟨e, ⟨C, hC_S, heC⟩, hxe⟩)
      · exact ⟨C, hC_S, Or.inl hxV⟩
      · exact ⟨C, hC_S, Or.inr ⟨e, heC, hxe⟩⟩
    · rintro ⟨C, hC_S, hxV | ⟨e, heC, hxe⟩⟩
      · exact Or.inl ⟨C, hC_S, hxV⟩
      · exact Or.inr ⟨e, ⟨C, hC_S, heC⟩, hxe⟩
  refine ⟨hU_eq, ?_⟩
  rw [hU_eq, ← biUnion_compPointSet_eq_U G]
  ext x
  simp only [mem_sdiff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨C, hC, hxC⟩, hnot⟩
    refine ⟨C, ⟨hC, fun hC_S => hnot ⟨C, hC_S, hxC⟩⟩, hxC⟩
  · rintro ⟨C, ⟨hC, hnot_S⟩, hxC⟩
    refine ⟨⟨C, hC, hxC⟩, ?_⟩
    rintro ⟨C', hC'_S, hxC'⟩
    have hne : C ≠ C' := fun heq => hnot_S (heq ▸ hC'_S)
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G hC (hS_comp hC'_S) hne) hxC hxC'

/-! ## 3. Master Region-Lifting and Chain-Lifting Lemmas -/

/-- Entry into a region `r'` of `G₁` from a point `a ∈ closure r' \ K₂` where `K₂ = G.U \ G₁.U` is
closed: there exists a region `r ∈ G.R` with `r ⊆ r'`, `a ∈ closure r`, `(a ∈ r' → a ∈ r)`, and
`∃ p ∈ r, p ∈ connectedComponentIn (univ \ K₂) a`. -/
theorem exists_subregion_at_point (hS : IsClosedDiscSpace S) {G G₁ : Drawing S}
    (hProper₁ : G₁.IsProper) (hSub : G₁.IsSubdrawing G) (hK₂_closed : IsClosed (G.U \ G₁.U))
    {r' : Set S} (hr' : r' ∈ G₁.R) {a : S} (ha_cl : a ∈ closure r')
    (ha_not : a ∉ G.U \ G₁.U) :
    ∃ r ∈ G.R, r ⊆ r' ∧ a ∈ closure r ∧ (a ∈ r' → a ∈ r) ∧
      ∃ p ∈ r, p ∈ connectedComponentIn (univ \ (G.U \ G₁.U)) a := by
  let K₂ := G.U \ G₁.U
  have h_r'_diff : r' \ K₂ ⊆ univ \ G.U := by
    intro z hz
    exact ⟨mem_univ z, fun hzU => hz.2 ⟨hzU, region_subset hr' hz.1⟩⟩
  by_cases ha_in : a ∈ r'
  · have ha_not_G : a ∉ G.U := fun hzU => ha_not ⟨hzU, region_subset hr' ha_in⟩
    let r := connectedComponentIn (univ \ G.U) a
    have hrG : r ∈ G.R := ⟨a, ⟨mem_univ a, ha_not_G⟩, rfl⟩
    have ha_r : a ∈ r := mem_connectedComponentIn ⟨mem_univ a, ha_not_G⟩
    have hr_sub : r ⊆ r' := by
      rcases hr' with ⟨z₀, _, rfl⟩
      rw [connectedComponentIn_eq ha_in]
      exact connectedComponentIn_mono a (sdiff_subset_sdiff_right hSub.U_subset)
    exact ⟨r, hrG, hr_sub, subset_closure ha_r, fun _ => ha_r,
      a, ha_r, mem_connectedComponentIn ⟨mem_univ a, ha_not⟩⟩
  · obtain ⟨γ, hγ0, hγ_pos⟩ := exists_region_entry_path G₁ hS hProper₁ r' hr' a ha_cl
    have h0_open : (0 : unitInterval) ∈ γ ⁻¹' (univ \ K₂) := by
      change γ 0 ∈ univ \ K₂
      rw [hγ0]
      exact ⟨mem_univ a, ha_not⟩
    have h_open : IsOpen (γ ⁻¹' (univ \ K₂)) :=
      (isOpen_univ.sdiff hK₂_closed).preimage γ.continuous
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp h_open 0 h0_open
    let δ : ℝ := min (1 / 2) (ε / 2)
    have hδ_pos : 0 < δ := lt_min (by norm_num) (half_pos hε_pos)
    have hδ_le_one : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
    let t₀ : unitInterval := ⟨δ, le_of_lt hδ_pos, hδ_le_one⟩
    have ht₀_pos : (0 : unitInterval) < t₀ := hδ_pos
    have hIcc_sub : γ '' Icc 0 t₀ ⊆ univ \ K₂ := by
      rintro _ ⟨t, ht, rfl⟩
      apply hball
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      change |t.1 - 0| < ε
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact lt_of_le_of_lt ht.2 (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε_pos))
    have hIoc_sub : γ '' Ioc 0 t₀ ⊆ univ \ G.U := by
      rintro _ ⟨t, ht, rfl⟩
      exact h_r'_diff ⟨hγ_pos t ht.1, (hIcc_sub ⟨t, ⟨le_of_lt ht.1, ht.2⟩, rfl⟩).2⟩
    let p := γ t₀
    have hp_not_G : p ∉ G.U := (hIoc_sub ⟨t₀, ⟨ht₀_pos, le_rfl⟩, rfl⟩).2
    let r := connectedComponentIn (univ \ G.U) p
    have hrG : r ∈ G.R := ⟨p, ⟨mem_univ p, hp_not_G⟩, rfl⟩
    have hp_r : p ∈ r := mem_connectedComponentIn ⟨mem_univ p, hp_not_G⟩
    have hr_sub : r ⊆ r' := by
      rcases hr' with ⟨z₀, _, rfl⟩
      rw [connectedComponentIn_eq (hγ_pos t₀ ht₀_pos)]
      exact connectedComponentIn_mono p (sdiff_subset_sdiff_right hSub.U_subset)
    have hIoc_conn : IsPreconnected (γ '' Ioc 0 t₀) := by
      have h_real : IsPreconnected (Ioc (0 : ℝ) δ) := convex_Ioc 0 δ |>.isPreconnected
      let emb : ℝ → unitInterval := fun x => projIcc 0 1 zero_le_one x
      have hemb_eq : emb '' Ioc 0 δ = Ioc (0 : unitInterval) t₀ := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx_mem : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2.trans hδ_le_one⟩
          change projIcc 0 1 zero_le_one x ∈ Ioc (0 : unitInterval) t₀
          rw [projIcc_of_mem zero_le_one hx_mem]
          exact hx
        · intro ht
          exact ⟨t.1, ht, projIcc_val zero_le_one t⟩
      rw [← hemb_eq, ← image_comp]
      exact h_real.image _ (γ.continuous.comp continuous_projIcc).continuousOn
    have hIoc_in_r : γ '' Ioc 0 t₀ ⊆ r :=
      hIoc_conn.subset_connectedComponentIn ⟨t₀, ⟨ht₀_pos, le_rfl⟩, rfl⟩ hIoc_sub
    have ha_cl_r : a ∈ closure r := by
      have h0_cl : (0 : unitInterval) ∈ closure (Ioc 0 t₀) := by
        rw [Metric.mem_closure_iff]
        intro η hη
        let s : ℝ := min δ (η / 2)
        have hs_pos : 0 < s := lt_min hδ_pos (half_pos hη)
        have hs_le : s ≤ δ := min_le_left _ _
        have hs_mem : s ∈ unitInterval := ⟨le_of_lt hs_pos, hs_le.trans hδ_le_one⟩
        refine ⟨⟨s, hs_mem⟩, ⟨hs_pos, hs_le⟩, ?_⟩
        rw [dist_comm, Subtype.dist_eq, Real.dist_eq]
        change |s - 0| < η
        rw [sub_zero, abs_of_nonneg (le_of_lt hs_pos)]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hη)
      have ha_img : a ∈ closure (γ '' Ioc 0 t₀) := by
        rw [← hγ0]
        exact image_closure_subset_closure_image γ.continuous ⟨0, h0_cl, rfl⟩
      exact closure_mono hIoc_in_r ha_img
    have hIcc_conn : IsPreconnected (γ '' Icc 0 t₀) := by
      have h_real : IsPreconnected (Icc (0 : ℝ) δ) := convex_Icc 0 δ |>.isPreconnected
      let emb : ℝ → unitInterval := fun x => projIcc 0 1 zero_le_one x
      have hemb_eq : emb '' Icc 0 δ = Icc (0 : unitInterval) t₀ := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx_mem : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans hδ_le_one⟩
          change projIcc 0 1 zero_le_one x ∈ Icc (0 : unitInterval) t₀
          rw [projIcc_of_mem zero_le_one hx_mem]
          exact hx
        · intro ht
          exact ⟨t.1, ht, projIcc_val zero_le_one t⟩
      rw [← hemb_eq, ← image_comp]
      exact h_real.image _ (γ.continuous.comp continuous_projIcc).continuousOn
    have hp_comp : p ∈ connectedComponentIn (univ \ K₂) a := by
      refine hIcc_conn.subset_connectedComponentIn ?_ hIcc_sub ⟨t₀, ⟨t₀.2.1, le_rfl⟩, rfl⟩
      exact ⟨0, ⟨le_rfl, t₀.2.1⟩, hγ0⟩
    exact ⟨r, hrG, hr_sub, ha_cl_r, fun h => (ha_in h).elim, p, hp_r, hp_comp⟩

/-- **Master Region-Lifting Lemma**: if `G₁` is a subdrawing of `G` such that `K₂ := G.U \ G₁.U`
is closed, `r' ∈ G₁.R`, and `a, b ∈ closure r' \ K₂` lie in the same connected component of
`univ \ K₂`, then there exists a single region `r ∈ G.R` with `r ⊆ r'`, `a ∈ closure r`,
`b ∈ closure r`, `(a ∈ r' → a ∈ r)`, and `(b ∈ r' → b ∈ r)`. -/
theorem exists_region_of_same_component_compl (hS : IsClosedDiscSpace S) {G G₁ : Drawing S}
    (hProper₁ : G₁.IsProper) (hSub : G₁.IsSubdrawing G) (hK₂_closed : IsClosed (G.U \ G₁.U))
    {r' : Set S} (hr' : r' ∈ G₁.R) {a b : S}
    (ha_cl : a ∈ closure r') (hb_cl : b ∈ closure r')
    (ha_not : a ∉ G.U \ G₁.U) (hb_not : b ∉ G.U \ G₁.U)
    (h_same : b ∈ connectedComponentIn (univ \ (G.U \ G₁.U)) a) :
    ∃ r ∈ G.R, r ⊆ r' ∧ a ∈ closure r ∧ b ∈ closure r ∧
      (a ∈ r' → a ∈ r) ∧ (b ∈ r' → b ∈ r) := by
  let K₁ := G₁.U
  let K₂ := G.U \ G₁.U
  obtain ⟨r_a, hr_a, hr_a_sub, ha_cl_r, ha_in_r, p_a, hp_a_r, hp_a_comp⟩ :=
    exists_subregion_at_point hS hProper₁ hSub hK₂_closed hr' ha_cl ha_not
  obtain ⟨r_b, hr_b, hr_b_sub, hb_cl_r, hb_in_r, p_b, hp_b_r, hp_b_comp⟩ :=
    exists_subregion_at_point hS hProper₁ hSub hK₂_closed hr' hb_cl hb_not
  have hK_union : K₁ ∪ K₂ = G.U := union_sdiff_cancel hSub.U_subset
  have hK_disj : Disjoint K₁ K₂ := disjoint_sdiff_self_right
  have hp_a_not : p_a ∉ K₁ ∪ K₂ := by
    rw [hK_union]
    exact region_subset hr_a hp_a_r
  have hp_b_not : p_b ∉ K₁ ∪ K₂ := by
    rw [hK_union]
    exact region_subset hr_b hp_b_r
  have hp_ab₁ : p_b ∈ connectedComponentIn (univ \ K₁) p_a := by
    have hp_a_r' : p_a ∈ r' := hr_a_sub hp_a_r
    have hp_b_r' : p_b ∈ r' := hr_b_sub hp_b_r
    rcases hr' with ⟨z₀, _, h_r'_eq⟩
    have hp_a_c : p_a ∈ connectedComponentIn (univ \ G₁.U) z₀ := h_r'_eq ▸ hp_a_r'
    have hp_b_c : p_b ∈ connectedComponentIn (univ \ G₁.U) z₀ := h_r'_eq ▸ hp_b_r'
    change p_b ∈ connectedComponentIn (univ \ G₁.U) p_a
    rw [← connectedComponentIn_eq hp_a_c]
    exact hp_b_c
  have hp_ab₂ : p_b ∈ connectedComponentIn (univ \ K₂) p_a := by
    rw [← connectedComponentIn_eq hp_a_comp, connectedComponentIn_eq h_same]
    exact hp_b_comp
  have hp_ab := disc_janiszewski_disjoint hS G₁.isClosed_U hK₂_closed hK_disj
    hp_a_not hp_b_not hp_ab₁ hp_ab₂
  rw [hK_union] at hp_ab
  have hr_eq : r_a = r_b := by
    have h1 : r_a = connectedComponentIn (univ \ G.U) p_a := by
      rcases hr_a with ⟨z₀, _, rfl⟩
      exact connectedComponentIn_eq hp_a_r
    have h2 : r_b = connectedComponentIn (univ \ G.U) p_b := by
      rcases hr_b with ⟨z₀, _, rfl⟩
      exact connectedComponentIn_eq hp_b_r
    rw [h1, h2, connectedComponentIn_eq hp_ab]
  rw [← hr_eq] at hb_cl_r hb_in_r
  exact ⟨r_a, hr_a, hr_a_sub, ha_cl_r, hb_cl_r, ha_in_r, hb_in_r⟩

/-- A region `r ∈ Γ.R` of a proper drawing `Γ` on a closed disc space `S` with
`(Γ.V ∩ bd S).Nonempty` is peripheral if and only if `(r ∩ bd S).Nonempty`. -/
theorem isPeripheral_inr_iff_inter_bd_nonempty (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hProper : Γ.IsProper) (hV_ne : (Γ.V ∩ bd S).Nonempty) {r : Set S} (hr : r ∈ Γ.R) :
    ChainTerm.IsPeripheral Γ (.inr r) ↔ (r ∩ bd S).Nonempty := by
  simp only [ChainTerm.IsPeripheral]
  constructor
  · rintro ⟨_, seg, ⟨⟨z, hz, rfl⟩, _⟩, hseg_sub⟩
    exact ⟨z, hseg_sub (mem_connectedComponentIn hz), hz.1⟩
  · rintro ⟨z, hzr, hzbd⟩
    refine ⟨hr, ?_⟩
    have hz_not_U : z ∉ Γ.U := region_subset hr hzr
    have hz_diff : z ∈ bd S \ (Γ.V ∩ bd S) :=
      ⟨hzbd, fun h => hz_not_U (Γ.V_subset_U h.1)⟩
    have hseg : connectedComponentIn (bd S \ (Γ.V ∩ bd S)) z ∈ segmentsOf (bd S) (Γ.V ∩ bd S) :=
      connectedComponentIn_mem_segmentsOf hS.isOArc_bd
        (Γ.finite_V.subset inter_subset_left) inter_subset_right hV_ne hz_diff
    refine ⟨connectedComponentIn (bd S \ (Γ.V ∩ bd S)) z, hseg, ?_⟩
    have h_diff_sub : bd S \ (Γ.V ∩ bd S) ⊆ univ \ Γ.U := by
      rintro w ⟨hw_bd, hw_not⟩
      exact ⟨mem_univ w, fun hwU => hw_not ⟨hProper ⟨hw_bd, hwU⟩, hw_bd⟩⟩
    rcases hr with ⟨z₀, _, rfl⟩
    rw [connectedComponentIn_eq hzr]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hz_diff)
      ((connectedComponentIn_subset _ _).trans h_diff_sub)

/-- Monotonicity of `divisionCount` with respect to subset inclusion `Δ' ⊆ Δ`. -/
theorem divisionCount_le_of_subset {C : Set S} {Δ' Δ : Set (Set S)}
    (hΔ : IsDivision Δ) (hsub : Δ' ⊆ Δ) (x y : S) :
    divisionCount C Δ' x y ≤ divisionCount C Δ x y := by
  unfold divisionCount
  refine ncard_le_ncard (fun δ hδ => ⟨hsub hδ.1, hδ.2⟩) ?_
  exact hΔ.1.subset fun _ h => h.1

omit [TopologicalSpace S] in
private theorem decide_isVertex_match (t : ChainTerm S) (f : Set S → Set S) :
    decide (match t with | .inl v => .inl v | .inr r' => .inr (f r') : ChainTerm S).IsVertex =
      decide t.IsVertex := by
  cases t <;> rfl

private theorem chain_endpoints_in_region_closure
    {G₁ : Drawing S} {U₁ : Set S} {x y : S} {A : List (ChainTerm S)}
    (hChain : IsXYChain G₁ x y A) (hx_mem : x ∈ G₁.U ∪ U₁) (hy_mem : y ∈ G₁.U ∪ U₁) :
    let leftPt : Fin A.length → S := fun i =>
      match A[i.1]'i.2 with
      | .inl v => v
      | .inr _ =>
        if i.1 = 0 then x
        else
          match A[i.1 - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with
          | .inl v => v
          | .inr _ => x
    let rightPt : Fin A.length → S := fun i =>
      match A[i.1]'i.2 with
      | .inl v => v
      | .inr _ =>
        if hi1 : i.1 + 1 = A.length then y
        else
          match A[i.1 + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1) with
          | .inl v => v
          | .inr _ => y
    (∀ (i : Fin A.length) (r' : Set S),
      A[i.1]'i.2 = .inr r' → leftPt i ∈ closure r' ∧ leftPt i ∈ G₁.U ∪ U₁) ∧
    (∀ (i : Fin A.length) (r' : Set S),
      A[i.1]'i.2 = .inr r' → rightPt i ∈ closure r' ∧ rightPt i ∈ G₁.U ∪ U₁) := by
  intro leftPt rightPt
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G₁ A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
  have h_left_props : ∀ (i : Fin A.length) (r' : Set S),
      A[i.1]'i.2 = .inr r' → leftPt i ∈ closure r' ∧ leftPt i ∈ G₁.U ∪ U₁ := by
    intro i r' hir
    by_cases hi0 : i.1 = 0
    · have hhead : A.head hChain.ne_nil = A[i.1]'i.2 := by
        rw [List.head_eq_getElem_zero]; congr 1; omega
      have hmatch := hChain.head_matches
      rw [hhead, hir] at hmatch
      have hleft : leftPt i = x := by
        dsimp only [leftPt]; rw [hir]; simp only [hi0, ite_true]
      rw [hleft]
      exact ⟨subset_closure hmatch, hx_mem⟩
    · have hprev_lt : i.1 - 1 < A.length := Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2
      have hstep : (i.1 - 1) + 1 < A.length := by omega
      have hinc := h_chain_rel (i.1 - 1) hstep
      have h_idx_eq : A[(i.1 - 1) + 1]'hstep = A[i.1]'i.2 := by congr 1; omega
      rw [h_idx_eq, hir] at hinc
      rcases h_prev : A[i.1 - 1]'hprev_lt with v | r''
      · rw [h_prev] at hinc
        have hleft : leftPt i = v := by
          dsimp only [leftPt]; rw [hir]; simp only [hi0, ↓reduceIte, h_prev]
        rw [hleft]
        exact ⟨hinc.2.2, Or.inl (G₁.V_subset_U hinc.1)⟩
      · rw [h_prev] at hinc; exact False.elim hinc
  have h_right_props : ∀ (i : Fin A.length) (r' : Set S),
      A[i.1]'i.2 = .inr r' → rightPt i ∈ closure r' ∧ rightPt i ∈ G₁.U ∪ U₁ := by
    intro i r' hir
    by_cases hi1 : i.1 + 1 = A.length
    · have hlast : A.getLast hChain.ne_nil = A[i.1]'i.2 := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      have hmatch := hChain.last_matches
      rw [hlast, hir] at hmatch
      have hright : rightPt i = y := by
        dsimp only [rightPt]; rw [hir]; simp only [hi1, ↓reduceDIte]
      rw [hright]
      exact ⟨subset_closure hmatch, hy_mem⟩
    · have hnext_lt : i.1 + 1 < A.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1
      have hinc := h_chain_rel i.1 hnext_lt
      rw [hir] at hinc
      rcases h_next : A[i.1 + 1]'hnext_lt with v | r''
      · rw [h_next] at hinc
        have hright : rightPt i = v := by
          dsimp only [rightPt]; rw [hir]; simp only [hi1, ↓reduceDIte, h_next]
        rw [hright]
        exact ⟨hinc.2.2, Or.inl (G₁.V_subset_U hinc.1)⟩
      · rw [h_next] at hinc; exact False.elim hinc
  exact ⟨h_left_props, h_right_props⟩

omit [TopologicalSpace S] in
private theorem chainLength_eq_of_vertex_indicators {A B : List (ChainTerm S)}
    (hmap : A.map (fun t => decide t.IsVertex) = B.map (fun t => decide t.IsVertex)) :
    chainLength A = chainLength B := by
  unfold chainLength
  have h_count : ∀ L : List (ChainTerm S),
      (L.filter (fun t => decide t.IsVertex)).length =
        (L.map (fun t => decide t.IsVertex)).count true := by
    intro L
    induction L with
    | nil => rfl
    | cons hd tl ih =>
      by_cases h : decide hd.IsVertex
      · simp [List.filter, h, ih]
      · simp [List.filter, h, ih]
  rw [h_count, h_count, hmap]

private theorem chainEndpoint_mem_boundary {G G₁ : Drawing S} {U₁ : Set S}
    (hU₁ : U₁ ⊆ bd S \ G.U) {z : S} (hz : z ∈ U₁ ∪ (G₁.V ∩ bd S)) : z ∈ bd S :=
  hz.elim (fun hz' => (hU₁ hz').1) And.right

/-- **Master Chain-Lifting Theorem**: if `G₁` is a proper subdrawing of a proper drawing `G` on a
closed disc space `S` such that `K₂ := G.U \ G₁.U` is closed, `(G₁.V ∩ bd S).Nonempty`,
`U₁ ⊆ bd S \ G.U`, and `G₁.U ∪ U₁` lies in a single connected component of `univ \ K₂`, then every
`(x, y)`-chain `A` of `G₁` (for `x, y ∈ U₁ ∪ (G₁.V ∩ bd S)`) lifts to an `(x, y)`-chain `A_G` of
`G` with `chainLength A_G = chainLength A`. -/
theorem liftChain_of_subdrawing (hS : IsClosedDiscSpace S) {G G₁ : Drawing S}
    (hProper : G.IsProper) (hProper₁ : G₁.IsProper)
    (hSub : G₁.IsSubdrawing G) (hK₂_closed : IsClosed (G.U \ G₁.U))
    (hV₁_ne : (G₁.V ∩ bd S).Nonempty) {U₁ : Set S} (hU₁ : U₁ ⊆ bd S \ G.U)
    (h_same_comp : ∀ a ∈ G₁.U ∪ U₁, ∀ b ∈ G₁.U ∪ U₁,
      b ∈ connectedComponentIn (univ \ (G.U \ G₁.U)) a)
    {x y : S} (hx : x ∈ U₁ ∪ (G₁.V ∩ bd S)) (hy : y ∈ U₁ ∪ (G₁.V ∩ bd S))
    {A : List (ChainTerm S)} (hChain : IsXYChain G₁ x y A) :
    ∃ A_G : List (ChainTerm S), IsXYChain G x y A_G ∧ chainLength A_G = chainLength A := by
  have hm : 0 < A.length := List.length_pos_of_ne_nil hChain.ne_nil
  have hVG_ne : (G.V ∩ bd S).Nonempty :=
    hV₁_ne.mono (inter_subset_inter_left _ hSub.1)
  have hmem {z : S} (hz : z ∈ U₁ ∪ (G₁.V ∩ bd S)) : z ∈ G₁.U ∪ U₁ :=
    hz.elim Or.inr (fun h => Or.inl (G₁.V_subset_U h.1))
  have h_not_K₂ : ∀ z ∈ G₁.U ∪ U₁, z ∉ G.U \ G₁.U := by
    rintro z (hzG₁ | hzU₁) hzK₂
    · exact hzK₂.2 hzG₁
    · exact (hU₁ hzU₁).2 hzK₂.1
  let leftPt : Fin A.length → S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => v
    | .inr _ =>
      if i.1 = 0 then x
      else
        match A[i.1 - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.2) with
        | .inl v => v
        | .inr _ => x
  let rightPt : Fin A.length → S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => v
    | .inr _ =>
      if hi1 : i.1 + 1 = A.length then y
      else
        match A[i.1 + 1]'(Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.2) hi1) with
        | .inl v => v
        | .inr _ => y
  have h_chain_rel : ∀ (j : ℕ) (hj : j + 1 < A.length),
      ChainTerm.AreIncident G₁ A[j] A[j + 1] :=
    fun j hj => List.isChain_iff_getElem.mp hChain.isChain j hj
  obtain ⟨h_left_props, h_right_props⟩ := chain_endpoints_in_region_closure hChain (hmem hx)
    (hmem hy)
  have h_lift_reg : ∀ (i : Fin A.length) (r' : Set S), A[i.1]'i.2 = .inr r' →
      ∃ r ∈ G.R, r ⊆ r' ∧ leftPt i ∈ closure r ∧ rightPt i ∈ closure r ∧
        (leftPt i ∈ r' → leftPt i ∈ r) ∧ (rightPt i ∈ r' → rightPt i ∈ r) := by
    intro i r' hir
    have hr' : r' ∈ G₁.R := by
      have hv := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
      simpa [hir, ChainTerm.IsValid] using hv
    obtain ⟨hl_cl, hl_mem⟩ := h_left_props i r' hir
    obtain ⟨hr_cl, hr_mem⟩ := h_right_props i r' hir
    exact exists_region_of_same_component_compl hS hProper₁ hSub hK₂_closed hr'
      hl_cl hr_cl (h_not_K₂ _ hl_mem) (h_not_K₂ _ hr_mem)
      (h_same_comp _ hl_mem _ hr_mem)
  choose! r_lift hr_lift_R hr_lift_sub hr_lift_left_cl hr_lift_right_cl
    hr_lift_left_in hr_lift_right_in using h_lift_reg
  let termG : Fin A.length → ChainTerm S := fun i =>
    match A[i.1]'i.2 with
    | .inl v => .inl v
    | .inr r' => .inr (r_lift i r')
  let A_G : List (ChainTerm S) := List.ofFn termG
  have hlen_eq : A_G.length = A.length := List.length_ofFn
  have hne_nil : A_G ≠ [] := List.ne_nil_of_length_pos (hlen_eq.symm ▸ hm)
  have hget : ∀ (j : ℕ) (hj : j < A_G.length),
      A_G[j]'hj = termG ⟨j, hlen_eq ▸ hj⟩ := fun j hj => by simp [A_G]
  refine ⟨A_G, ⟨hne_nil, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    rw [hget j hj]
    have hv := hChain.valid (A[j]'(hlen_eq ▸ hj)) (List.getElem_mem _)
    change (termG ⟨j, hlen_eq ▸ hj⟩).IsValid G
    dsimp only [termG]
    split
    · rename_i v hv_eq
      rw [hv_eq] at hv
      exact hSub.1 hv
    · rename_i r hr_eq
      exact hr_lift_R _ r hr_eq
  · rw [List.isChain_iff_getElem]
    intro j hj
    have hj_lt : j < A_G.length := Nat.lt_of_succ_lt hj
    rw [hget j hj_lt, hget (j + 1) hj]
    have hjA : j + 1 < A.length := hlen_eq ▸ hj
    let i : Fin A.length := ⟨j, Nat.lt_of_succ_lt hjA⟩
    let i1 : Fin A.length := ⟨j + 1, hjA⟩
    have hinc := h_chain_rel j hjA
    change ChainTerm.AreIncident G (termG i) (termG i1)
    dsimp only [termG]
    rcases hir : A[i.1]'i.2 with v | r'
    · rw [hir] at hinc
      rcases hir1 : A[i1.1]'i1.2 with v' | r''
      · rw [hir1] at hinc; exact False.elim hinc
      · rw [hir1] at hinc
        have hleft : leftPt i1 = v := by
          dsimp only [leftPt, i1]; rw [hir1]; simp only [Nat.succ_ne_zero, ↓reduceIte]
          have h_idx : A[(j + 1) - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) hjA) = A[i.1]'i.2 := rfl
          rw [h_idx, hir]
        refine ⟨hSub.1 hinc.1, hr_lift_R i1 r'' hir1, ?_⟩
        rw [← hleft]
        exact hr_lift_left_cl i1 r'' hir1
    · rw [hir] at hinc
      rcases hir1 : A[i1.1]'i1.2 with v' | r''
      · rw [hir1] at hinc
        have hne_last : i.1 + 1 ≠ A.length := ne_of_lt hjA
        have hright : rightPt i = v' := by
          dsimp only [rightPt]; rw [hir]; simp only [hne_last, ↓reduceDIte]
          have h_idx : A[i.1 + 1]'hjA = A[i1.1]'i1.2 := rfl
          rw [h_idx, hir1]
        refine ⟨hSub.1 hinc.1, hr_lift_R i r' hir, ?_⟩
        rw [← hright]
        exact hr_lift_right_cl i r' hir
      · rw [hir1] at hinc; exact False.elim hinc
  · have hhead_G : A_G.head hne_nil = termG ⟨0, hm⟩ := by
      rw [List.head_eq_getElem_zero, hget]
    have hhead_A : A.head hChain.ne_nil = A[0]'hm := List.head_eq_getElem_zero _
    have hmatch := hChain.head_matches
    rw [hhead_A] at hmatch
    rw [hhead_G]
    dsimp only [termG]
    rcases hir0 : A[0]'hm with v | r'
    · rw [hir0] at hmatch; exact hmatch
    · rw [hir0] at hmatch
      change x ∈ r_lift ⟨0, hm⟩ r'
      have hleft : leftPt ⟨0, hm⟩ = x := by
        dsimp only [leftPt]; rw [hir0]; simp only [ite_true]
      rw [← hleft]
      exact hr_lift_left_in ⟨0, hm⟩ r' hir0 (hleft.symm ▸ hmatch)
  · let i_last : Fin A.length := ⟨A.length - 1, Nat.sub_lt hm zero_lt_one⟩
    have hlast_G : A_G.getLast hne_nil = termG i_last := by
      rw [List.getLast_eq_getElem, hget]
      congr 1; ext; dsimp [i_last]; omega
    have hlast_A : A.getLast hChain.ne_nil = A[i_last.1]'i_last.2 :=
      List.getLast_eq_getElem _
    have hmatch := hChain.last_matches
    rw [hlast_A] at hmatch
    rw [hlast_G]
    dsimp only [termG]
    rcases hir_last : A[i_last.1]'i_last.2 with v | r'
    · rw [hir_last] at hmatch; exact hmatch
    · rw [hir_last] at hmatch
      change y ∈ r_lift i_last r'
      have hi1 : i_last.1 + 1 = A.length := by dsimp [i_last]; omega
      have hright : rightPt i_last = y := by
        dsimp only [rightPt]; rw [hir_last]; simp only [hi1, ↓reduceDIte]
      rw [← hright]
      exact hr_lift_right_in i_last r' hir_last (hright.symm ▸ hmatch)
  · intro iG
    let i : Fin A.length := ⟨iG.1, hlen_eq ▸ iG.2⟩
    have hper_A := hChain.peripheral_iff i
    change (A_G[iG.1]'iG.2).IsPeripheral G ↔ (iG.1 = 0 ∨ iG.1 + 1 = A_G.length)
    rw [hget iG.1 iG.2]
    change (termG i).IsPeripheral G ↔ (i.1 = 0 ∨ i.1 + 1 = A_G.length)
    rw [hlen_eq]
    suffices h_iff : (termG i).IsPeripheral G ↔ (A[i.1]'i.2).IsPeripheral G₁ by
      exact h_iff.trans hper_A
    dsimp only [termG]
    rcases hir : A[i.1]'i.2 with v | r'
    · have hv : v ∈ G₁.V := by
        have hval := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
        simpa [hir, ChainTerm.IsValid] using hval
      simp only [ChainTerm.IsPeripheral]
      exact ⟨fun h => ⟨hv, h.2⟩, fun h => ⟨hSub.1 hv, h.2⟩⟩
    · have hr' : r' ∈ G₁.R := by
        have hval := hChain.valid (A[i.1]'i.2) (List.getElem_mem i.2)
        simpa [hir, ChainTerm.IsValid] using hval
      have hr : r_lift i r' ∈ G.R := hr_lift_R i r' hir
      have hr_sub : r_lift i r' ⊆ r' := hr_lift_sub i r' hir
      rw [isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr,
        isPeripheral_inr_iff_inter_bd_nonempty hS hProper₁ hV₁_ne hr']
      constructor
      · exact fun h => h.mono (inter_subset_inter_left _ hr_sub)
      · intro h_non
        have h_ends : i.1 = 0 ∨ i.1 + 1 = A.length := by
          rw [← hper_A]
          change (A[i.1]'i.2).IsPeripheral G₁
          rw [hir, isPeripheral_inr_iff_inter_bd_nonempty hS hProper₁ hV₁_ne hr']
          exact h_non
        rcases h_ends with hi0 | hi1
        · have hhead_A : A.head hChain.ne_nil = A[i.1]'i.2 := by
            rw [List.head_eq_getElem_zero]; congr 1; omega
          have hmatch := hChain.head_matches
          rw [hhead_A, hir] at hmatch
          change x ∈ r' at hmatch
          have hleft : leftPt i = x := by
            dsimp only [leftPt]; rw [hir]; simp only [hi0, ite_true]
          have hx_r : x ∈ r_lift i r' := by
            rw [← hleft]
            exact hr_lift_left_in i r' hir (hleft.symm ▸ hmatch)
          exact ⟨x, hx_r, chainEndpoint_mem_boundary hU₁ hx⟩
        · have hlast_A : A.getLast hChain.ne_nil = A[i.1]'i.2 := by
            rw [List.getLast_eq_getElem]; congr 1; omega
          have hmatch := hChain.last_matches
          rw [hlast_A, hir] at hmatch
          change y ∈ r' at hmatch
          have hright : rightPt i = y := by
            dsimp only [rightPt]; rw [hir]; simp only [hi1, ↓reduceDIte]
          have hy_r : y ∈ r_lift i r' := by
            rw [← hright]
            exact hr_lift_right_in i r' hir (hright.symm ▸ hmatch)
          exact ⟨y, hy_r, chainEndpoint_mem_boundary hU₁ hy⟩
  · have h_map : A_G.map (fun t => decide t.IsVertex) = A.map (fun t => decide t.IsVertex) := by
      refine List.ext_getElem (by simp [hlen_eq]) fun j hj₁ hj₂ => ?_
      simp only [List.getElem_map]
      have hjG : j < A_G.length := by simpa using hj₁
      rw [hget j hjG]
      let i : Fin A.length := ⟨j, hlen_eq ▸ hjG⟩
      exact decide_isVertex_match (A[i.1]'i.2) (r_lift i)
    exact chainLength_eq_of_vertex_indicators h_map

/-! ## 4. Restricting a Dual Point Set to a Subset `V' ⊆ V` -/

omit [TopologicalSpace S] in
theorem nextSegment_subset_of_subset {V' V : Set Circle} (hsub : V' ⊆ V) (v : Circle) :
    nextSegment V v ⊆ nextSegment V' v :=
  fun _ hz => ⟨hz.1, fun w hw => hz.2 w ⟨hsub hw.1, hw.2⟩⟩

omit [TopologicalSpace S] in
theorem range_circlePath_subset_insert_nextSegment {V : Set Circle} {v u : Circle}
    (hu : u ∈ nextSegment V v) :
    range (Circle.path v u) ⊆ insert v (nextSegment V v) := by
  have hvu : v ≠ u := hu.1.symm
  intro z hz
  rcases eq_or_ne z v with rfl | hzv
  · exact mem_insert z _
  · right
    rcases eq_or_ne z u with rfl | hzu
    · exact hu
    · have hz_compl : z ∈ ({v, u} : Set Circle)ᶜ := by simp [hzv, hzu]
      rw [compl_pair_eq_union_circleOpenArc hvu] at hz_compl
      have hz_not_uv : z ∉ circleOpenArc u v := by
        rw [← compl_range_circlePath hvu, mem_compl_iff, not_not]
        exact hz
      have hz_arc : z ∈ circleOpenArc v u := hz_compl.resolve_right hz_not_uv
      rw [mem_circleOpenArc_iff_angleDiff hvu] at hz_arc
      exact ⟨hzv, fun w hw => lt_trans hz_arc.2 (hu.2 w hw)⟩

omit [TopologicalSpace S] in
theorem exists_dualPointSet_subset_of_subset_univ {V V' U : Set Circle}
    (hV_fin : V.Finite) (hU : IsDualPointSet (univ : Set Circle) V U) (hV' : V' ⊆ V) :
    ∃ U' ⊆ U, IsDualPointSet (univ : Set Circle) V' U' ∧
      ∀ u' ∈ U', ∃ v' ∈ V', u' ∈ nextSegment V v' ∧
        ∃ K ⊆ insert v' (nextSegment V v'), IsConnected K ∧ v' ∈ K ∧ u' ∈ K := by
  let U' : Set Circle := ⋃ v' ∈ V', (U ∩ nextSegment V v')
  have hU'_sub : U' ⊆ U := iUnion₂_subset fun _ _ => inter_subset_left
  refine ⟨U', hU'_sub, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro hV'_emp
      simp [U', hV'_emp]
    · intro hV'_ne
      have hV_ne : V.Nonempty := hV'_ne.mono hV'
      have hU_compl : U ⊆ (univ : Set Circle) \ V := (hU.2 hV_ne).1
      have hU'_compl : U' ⊆ (univ : Set Circle) \ V' :=
        hU'_sub.trans (hU_compl.trans (sdiff_subset_sdiff subset_rfl hV'))
      refine ⟨hU'_compl, fun seg hseg => ?_⟩
      have hV'_fin : V'.Finite := hV_fin.subset hV'
      rw [mem_segmentsOf_univ_iff hV'_fin hV'_ne] at hseg
      obtain ⟨v', hv', rfl⟩ := hseg
      obtain ⟨u', hu'_eq⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV_fin hU (hV' hv')
      have hu'_mem : u' ∈ U ∩ nextSegment V v' := by
        rw [hu'_eq]; exact mem_singleton u'
      have h_inter_eq : U' ∩ nextSegment V' v' = {u'} := by
        apply Subset.antisymm
        · rintro z ⟨hzU', hz_seg'⟩
          obtain ⟨v'', hv'', hzU, hz_seg⟩ := mem_iUnion₂.mp hzU'
          have hz_seg'' : z ∈ nextSegment V' v'' :=
            nextSegment_subset_of_subset hV' v'' hz_seg
          have hz_compl : z ∈ V'ᶜ := nextSegment_subset_compl hz_seg'
          have h_uniq :=
            (exists_unique_nextSegment_of_mem_compl hV'_fin hV'_ne hz_compl).unique
              ⟨hv'', hz_seg''⟩ ⟨hv', hz_seg'⟩
          subst h_uniq
          have hz_in : z ∈ U ∩ nextSegment V v'' := ⟨hzU, hz_seg⟩
          rwa [hu'_eq] at hz_in
        · rw [singleton_subset_iff]
          exact ⟨mem_biUnion hv' hu'_mem, nextSegment_subset_of_subset hV' v' hu'_mem.2⟩
      rw [h_inter_eq, ncard_singleton]
  · intro u' hu'
    obtain ⟨v', hv', _, hu'_seg⟩ := mem_iUnion₂.mp hu'
    refine ⟨v', hv', hu'_seg, range (Circle.path v' u'),
      range_circlePath_subset_insert_nextSegment hu'_seg,
      isConnected_range (Circle.path v' u').continuous,
      ⟨0, (Circle.path v' u').source⟩, ⟨1, (Circle.path v' u').target⟩⟩

/-- For any finite subset `V ⊆ C` of an $O$-arc `C`, any dual point set `U` for `(C, V)`, and any
subset `V' ⊆ V`, there exists a subset `U' ⊆ U` that is a dual point set for `(C, V')` such that
each `u' ∈ U'` is joined to some `v' ∈ V'` inside `{v'} ∪ seg₀` for some segment
`seg₀ ∈ segmentsOf C V`. -/
theorem exists_dualPointSet_subset_of_subset {C V V' U : Set S}
    (hC : IsOArc C) (hV_sub : V ⊆ C) (hV_fin : V.Finite)
    (hU : IsDualPointSet C V U) (hV' : V' ⊆ V) :
    ∃ U' ⊆ U, IsDualPointSet C V' U' ∧
      ∀ u' ∈ U', ∃ v' ∈ V', ∃ seg₀ ∈ segmentsOf C V,
        u' ∈ seg₀ ∧ ∃ K ⊆ insert v' seg₀, IsConnected K ∧ v' ∈ K ∧ u' ∈ K := by
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  have hrange := range_oArcMap φ
  let V_c : Set Circle := oArcMap φ ⁻¹' V
  let V'_c : Set Circle := oArcMap φ ⁻¹' V'
  let U_c : Set Circle := oArcMap φ ⁻¹' U
  have hV_eq : oArcMap φ '' V_c = V :=
    image_preimage_eq_of_subset (hV_sub.trans hrange.symm.subset)
  have hV'_eq : oArcMap φ '' V'_c = V' :=
    image_preimage_eq_of_subset ((hV'.trans hV_sub).trans hrange.symm.subset)
  have hU_sub_C : U ⊆ C := (isDualPointSet_subset_diff hU).trans sdiff_subset
  have hU_eq : oArcMap φ '' U_c = U :=
    image_preimage_eq_of_subset (hU_sub_C.trans hrange.symm.subset)
  have hVc_fin : V_c.Finite := by
    refine Finite.of_finite_image ?_ hinj.injOn
    rwa [hV_eq]
  have hUc : IsDualPointSet (univ : Set Circle) V_c U_c := by
    rwa [← isDualPointSet_oArcMap_iff φ, hV_eq, hU_eq]
  have hV'c : V'_c ⊆ V_c := preimage_mono hV'
  obtain ⟨U'_c, hU'c_sub, hU'c_dual, hU'c_conn⟩ :=
    exists_dualPointSet_subset_of_subset_univ hVc_fin hUc hV'c
  refine ⟨oArcMap φ '' U'_c, ?_, ?_, ?_⟩
  · rw [← hU_eq]
    exact image_mono hU'c_sub
  · rw [← hV'_eq, isDualPointSet_oArcMap_iff φ]
    exact hU'c_dual
  · rintro _ ⟨u'_c, hu'_c, rfl⟩
    obtain ⟨v'_c, hv'_c, hu'_seg, K_c, hKc_sub, hKc_conn, hv'_Kc, hu'_Kc⟩ :=
      hU'c_conn u'_c hu'_c
    have hv'_V' : oArcMap φ v'_c ∈ V' := by
      rw [← hV'_eq]; exact mem_image_of_mem _ hv'_c
    have hseg_mem : oArcMap φ '' nextSegment V_c v'_c ∈ segmentsOf C V := by
      rw [← hV_eq, segmentsOf_oArcMap φ]
      exact mem_image_of_mem _ (nextSegment_mem_segmentsOf_univ hVc_fin (hV'c hv'_c))
    refine ⟨oArcMap φ v'_c, hv'_V', oArcMap φ '' nextSegment V_c v'_c, hseg_mem,
      mem_image_of_mem _ hu'_seg, oArcMap φ '' K_c, ?_,
      hKc_conn.image _ (isEmbedding_oArcMap φ).continuous.continuousOn,
      mem_image_of_mem _ hv'_Kc, mem_image_of_mem _ hu'_Kc⟩
    rw [← image_insert_eq]
    exact image_mono hKc_sub

/-! ## 5. Reductions for `(3.3)(ii)`, `(3.3)(iii)`, and `(3.3)(iv)` -/

theorem isConnected_of_isOArc {C : Set S} (hC : IsOArc C) : IsConnected C := by
  obtain ⟨φ⟩ := hC
  rw [← range_oArcMap φ]
  exact isConnected_range (isEmbedding_oArcMap φ).continuous

theorem isCompact_compPointSet [T2Space S] (G : Drawing S) {C : Graph S (Set S)}
    (hC : IsGraphComponent C G.toGraph) : IsCompact (compPointSet C) := by
  rw [compPointSet_eq_closure_union G hC]
  have hV_fin : V(C).Finite := G.finite_V.subset hC.1.vertexSet_mono
  have hE_fin : E(C).Finite := G.finite_edges.subset hC.1.edgeSet_mono
  exact hV_fin.isCompact.union (hE_fin.isCompact_biUnion fun e he =>
    isCompact_closure_edge G (hC.1.edgeSet_mono he))

/-- Monotonicity of `IsFeasible` with respect to subgraph inclusion `G₁ ≤ G₂`. -/
theorem IsFeasible.mono {α : Type u} {β : Type*} {G₁ G₂ : Graph α β} {Δ : Set (Set α)}
    (hle : G₁ ≤ G₂) (hF : IsFeasible G₁ Δ) : IsFeasible G₂ Δ := by
  rcases hF with ⟨H, hΔ, hΔ_sub, hHG₁, hFor, H_comp, hinj, hcomp, hcomps_eq⟩
  exact ⟨H, hΔ, hΔ_sub.trans hle.vertexSet_mono, hHG₁.trans hle, hFor,
    H_comp, hinj, hcomp, hcomps_eq⟩

/-- **Case (3.3)(ii) Reduction** (Graph Minors VI, page 122, Case 3):
If `(G.V ∩ bd S).Nonempty` and `G` has an internal component `C₀ ∈ graphComponents G.toGraph`
with `V(C₀) ∩ bd S = ∅`, then the subdrawing `G_bd` induced by the union of all components meeting
`bd S` satisfies `G_bd.V.ncard + G_bd.R.ncard < G.V.ncard + G.R.ncard`, `G_bd.V ∩ bd S = G.V ∩ bd
S`,
every chain of `G_bd` has non-negative redundancy, and `IsFeasible G_bd.toGraph Δ → IsFeasible
G.toGraph Δ`. -/
theorem exists_reduction_of_internal_component (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (hVG_ne : (G.V ∩ bd S).Nonempty)
    {C₀ : Graph S (Set S)} (hC₀ : C₀ ∈ graphComponents G.toGraph)
    (hC₀_disj : V(C₀) ∩ bd S = ∅)
    {Δ : Set (Set S)} {U : Set S}
    (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ x ∈ U ∪ (G.V ∩ bd S), ∀ y ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A) :
    ∃ G' : Drawing S, G'.IsProper ∧ G'.IsSubdrawing G ∧
      G'.V.ncard + G'.R.ncard < G.V.ncard + G.R.ncard ∧
      G'.V ∩ bd S = G.V ∩ bd S ∧
      (∀ x ∈ U ∪ (G'.V ∩ bd S), ∀ y ∈ U ∪ (G'.V ∩ bd S),
        ∀ A : List (ChainTerm S), IsXYChain G' x y A → 0 ≤ chainRedundancy G' Δ x y A) ∧
      (IsFeasible G'.toGraph Δ → IsFeasible G.toGraph Δ) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  let S_bd : Set (Graph S (Set S)) := {C ∈ graphComponents G.toGraph | (V(C) ∩ bd S).Nonempty}
  have hS_bd_sub : S_bd ⊆ graphComponents G.toGraph := fun _ h => h.1
  let V_bd : Set S := ⋃ C ∈ S_bd, V(C)
  have hV_bd_sub : V_bd ⊆ G.V := iUnion₂_subset fun C hC => hC.1.1.vertexSet_mono
  let G' : Drawing S := induceDrawing G V_bd
  have hProper' : G'.IsProper := induceDrawing_isProper G hProper hV_bd_sub
  have hSub' : G'.IsSubdrawing G := induceDrawing_isSubdrawing G hV_bd_sub
  have hG'_V : G'.V = V_bd := induceDrawing_V G hV_bd_sub
  have hV'_bd_eq : G'.V ∩ bd S = G.V ∩ bd S := by
    rw [hG'_V]
    apply Subset.antisymm (inter_subset_inter_left _ hV_bd_sub)
    rintro v ⟨hvV, hv_bd⟩
    refine ⟨mem_iUnion₂.mpr ⟨compOf G.toGraph v, ?_, self_mem_reachSet hvV⟩, hv_bd⟩
    exact ⟨isGraphComponent_compOf hvV, ⟨v, self_mem_reachSet hvV, hv_bd⟩⟩
  obtain ⟨v₀, hv₀C₀⟩ := hC₀.2.1.1
  have hv₀G : v₀ ∈ G.V := hC₀.1.vertexSet_mono hv₀C₀
  have hv₀_not : v₀ ∉ G'.V := by
    rw [hG'_V]
    intro hv₀_in
    obtain ⟨C, ⟨hC_comp, hC_ne⟩, hv₀C⟩ := mem_iUnion₂.mp hv₀_in
    have heq : C₀ = C := hC₀.eq_of_mem_mem hC_comp hv₀C₀ hv₀C
    rw [← heq, hC₀_disj] at hC_ne
    exact not_nonempty_empty hC_ne
  have hV_lt : G'.V.ncard < G.V.ncard :=
    ncard_lt_ncard ⟨hSub'.1, fun h => hv₀_not (h hv₀G)⟩ G.finite_V
  have hR_le : G'.R.ncard ≤ G.R.ncard :=
    disc_region_ncard_le_of_isSubdrawing hS hProper hSub'
  obtain ⟨hU'_eq, hK₂_eq⟩ := induceDrawing_U_biUnion_components G hS_bd_sub
  have hK₂_fin : (graphComponents G.toGraph \ S_bd).Finite :=
    (finite_graphComponents G).subset sdiff_subset
  have hK₂_closed : IsClosed (G.U \ G'.U) := by
    rw [hK₂_eq]
    exact hK₂_fin.isClosed_biUnion fun C hC => isClosed_compPointSet G hC.1
  have h_bd_disj_K₂ : Disjoint (bd S) (G.U \ G'.U) := by
    rw [hK₂_eq]
    refine disjoint_left.mpr fun x hx_bd hx_union => ?_
    obtain ⟨C, ⟨hC_comp, hC_not⟩, hxC⟩ := mem_iUnion₂.mp hx_union
    have hx_inter : x ∈ compPointSet C ∩ bd S := ⟨hxC, hx_bd⟩
    rw [compPointSet_inter_bd_eq G hProper hC_comp] at hx_inter
    exact hC_not ⟨hC_comp, ⟨x, hx_inter⟩⟩
  have h_U'_bd_conn : IsConnected (G'.U ∪ bd S) := by
    obtain ⟨b₀, _, hb₀_bd⟩ := hVG_ne
    have h_fam_conn : ∀ C ∈ S_bd, IsConnected (compPointSet C ∪ bd S) := by
      intro C hC
      refine IsConnected.union ?_ (isConnected_compPointSet G hC.1)
        (isConnected_of_isOArc hS.isOArc_bd)
      rw [compPointSet_inter_bd_eq G hProper hC.1]
      exact hC.2
    have h_union_eq : G'.U ∪ bd S =
        ⋃₀ (insert (bd S) ((fun C => compPointSet C ∪ bd S) '' S_bd)) := by
      change (induceDrawing G V_bd).U ∪ bd S = _
      rw [hU'_eq]
      ext x
      simp only [mem_union, mem_iUnion, exists_prop, sUnion_insert, mem_sUnion, mem_image,
        exists_exists_and_eq_and]
      constructor
      · rintro (⟨C, hC, hxC⟩ | hx_bd)
        · exact Or.inr ⟨C, hC, Or.inl hxC⟩
        · exact Or.inl hx_bd
      · rintro (hx_bd | ⟨C, hC, hxC | hx_bd⟩)
        · exact Or.inr hx_bd
        · exact Or.inl ⟨C, hC, hxC⟩
        · exact Or.inr hx_bd
    refine ⟨⟨b₀, Or.inr hb₀_bd⟩, ?_⟩
    rw [h_union_eq]
    refine isPreconnected_sUnion b₀ _ ?_ ?_
    · rintro _ (rfl | ⟨C, _, rfl⟩)
      · exact hb₀_bd
      · exact Or.inr hb₀_bd
    · rintro _ (rfl | ⟨C, hC, rfl⟩)
      · exact (isConnected_of_isOArc hS.isOArc_bd).isPreconnected
      · exact (h_fam_conn C hC).isPreconnected
  have h_U'_bd_sub : G'.U ∪ bd S ⊆ univ \ (G.U \ G'.U) := by
    rintro x (hxU' | hx_bd)
    · exact ⟨mem_univ x, fun h => h.2 hxU'⟩
    · exact ⟨mem_univ x, disjoint_left.mp h_bd_disj_K₂ hx_bd⟩
  have hU_sub : U ⊆ bd S \ G.U := by
    have h1 := isDualPointSet_subset_diff hU
    intro u hu
    obtain ⟨hu_bd, hu_not_V⟩ := h1 hu
    exact ⟨hu_bd, fun huU => hu_not_V ⟨hProper ⟨hu_bd, huU⟩, hu_bd⟩⟩
  have h_same_comp : ∀ a ∈ G'.U ∪ U, ∀ b ∈ G'.U ∪ U,
      b ∈ connectedComponentIn (univ \ (G.U \ G'.U)) a := by
    intro a ha b hb
    have ha' : a ∈ G'.U ∪ bd S := ha.imp_right fun h => (hU_sub h).1
    have hb' : b ∈ G'.U ∪ bd S := hb.imp_right fun h => (hU_sub h).1
    exact h_U'_bd_conn.isPreconnected.subset_connectedComponentIn ha' h_U'_bd_sub hb'
  have h_toGraph_le : G'.toGraph ≤ G.toGraph := by
    change (induceDrawing G V_bd).toGraph ≤ G.toGraph
    rw [induceDrawing_toGraph_eq_induce G hV_bd_sub]
    exact induce_le hV_bd_sub
  refine ⟨G', hProper', hSub', by omega, hV'_bd_eq, ?_, IsFeasible.mono h_toGraph_le⟩
  intro x hx y hy A hChain'
  have hxG : x ∈ U ∪ (G.V ∩ bd S) := by rwa [← hV'_bd_eq]
  have hyG : y ∈ U ∪ (G.V ∩ bd S) := by rwa [← hV'_bd_eq]
  obtain ⟨A_G, hChainG, hlen_eq⟩ := liftChain_of_subdrawing hS hProper hProper' hSub'
    hK₂_closed (hV'_bd_eq.symm ▸ hVG_ne) hU_sub h_same_comp hx hy hChain'
  have hredG := hRed x hxG y hyG A_G hChainG
  unfold chainRedundancy at hredG ⊢
  rw [← hlen_eq]
  exact hredG

/-- **Case (3.3)(iii) Exclusion** (Graph Minors VI, page 122, Case 4):
If `0 ≤ chainRedundancy G Δ x y A` holds for every chain `A` of `G`, then no member `δ ∈ Δ`
can intersect two distinct components `C₁ ≠ C₂` of `G.toGraph`. -/
theorem not_component_split_of_chainRedundancy_nonneg (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ x ∈ U ∪ (G.V ∩ bd S), ∀ y ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A)
    {δ₀ : Set S} (hδ₀ : δ₀ ∈ Δ)
    {C₁ C₂ : Graph S (Set S)} (hC₁ : C₁ ∈ graphComponents G.toGraph)
    (hC₂ : C₂ ∈ graphComponents G.toGraph) (hne : C₁ ≠ C₂)
    (h₁ : (δ₀ ∩ V(C₁)).Nonempty) (h₂ : (δ₀ ∩ V(C₂)).Nonempty) : False := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  obtain ⟨a, haδ₀, haC₁⟩ := h₁
  obtain ⟨b, hbδ₀, hbC₂⟩ := h₂
  have ha_bd : a ∈ G.V ∩ bd S := hΔ_sub ⟨δ₀, hδ₀, haδ₀⟩
  have hb_bd : b ∈ G.V ∩ bd S := hΔ_sub ⟨δ₀, hδ₀, hbδ₀⟩
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨a, ha_bd⟩
  let S_bd : Set (Graph S (Set S)) := {C ∈ graphComponents G.toGraph | (V(C) ∩ bd S).Nonempty}
  let Δ_G : Set (Set S) := (fun C => V(C) ∩ bd S) '' S_bd
  have hΔG_div : IsDivision Δ_G := by
    have hfin : S_bd.Finite := (finite_graphComponents G).subset fun _ h => h.1
    refine ⟨hfin.image _, ?_, ?_⟩
    · rintro _ ⟨C, hC, rfl⟩
      exact hC.2
    · rintro _ ⟨C, hC, rfl⟩ _ ⟨C', hC', rfl⟩ hne_set
      refine disjoint_left.mpr fun x hx hx' => hne_set ?_
      rw [hC.1.eq_of_mem_mem hC'.1 hx.1 hx'.1]
  have hΔG_union : divisionUnion Δ_G = G.V ∩ bd S := by
    ext x
    simp only [divisionUnion, Δ_G, mem_sUnion, mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨C, hC, hxC, hx_bd⟩
      exact ⟨hC.1.1.vertexSet_mono hxC, hx_bd⟩
    · rintro ⟨hxV, hx_bd⟩
      exact ⟨compOf G.toGraph x, ⟨isGraphComponent_compOf hxV, ⟨x, self_mem_reachSet hxV, hx_bd⟩⟩,
        self_mem_reachSet hxV, hx_bd⟩
  have hΔG_cf : IsCrossFree (bd S) Δ_G := by
    rintro ⟨_, ⟨C, hC, rfl⟩, _, ⟨C', hC', rfl⟩, hne_set, u₁, hu₁, u₃, hu₃, u₂, hu₂, u₄, hu₄, hcr⟩
    have hne_C : C ≠ C' := fun heq => hne_set (congrArg (fun K => V(K) ∩ bd S) heq)
    have h_inter := discCrossing_of_isClosedDiscSpace hS
      (A := compPointSet C) (B := compPointSet C')
      (isCompact_compPointSet G hC.1) (isCompact_compPointSet G hC'.1)
      (isConnected_compPointSet G hC.1) (isConnected_compPointSet G hC'.1)
      (Or.inl hu₁.1) (Or.inl hu₃.1)
      (Or.inl hu₂.1) (Or.inl hu₄.1) hcr
    obtain ⟨z, hzC, hzC'⟩ := h_inter
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G hC.1 hC'.1 hne_C) hzC hzC'
  have hU_ΔG : IsDualPointSet (bd S) (divisionUnion Δ_G) U := by
    rwa [hΔG_union]
  have h_dd := theorem_2_2_proof (bd S) U Δ_G hS.isOArc_bd hΔG_div
    (hΔG_union ▸ G.finite_V.inter_of_left _)
    (hΔG_union ▸ inter_subset_right) hU_ΔG hΔG_cf
  have h_not_equiv : ¬ dualEquivRel (bd S) (dualDivision (bd S) U Δ_G) a b := by
    intro h_equiv
    have ha_div : a ∈ divisionUnion Δ_G := by rw [hΔG_union]; exact ha_bd
    have hb_div : b ∈ divisionUnion Δ_G := by rw [hΔG_union]; exact hb_bd
    let δ_a : Set S := {v' ∈ divisionUnion Δ_G |
      dualEquivRel (bd S) (dualDivision (bd S) U Δ_G) a v'}
    have hδ_a_mem : δ_a ∈ doubleDualDivision (bd S) U Δ_G := ⟨a, ha_div, rfl⟩
    rw [h_dd] at hδ_a_mem
    obtain ⟨C, hC, hC_eq⟩ := hδ_a_mem
    dsimp only at hC_eq
    have ha_in : a ∈ V(C) ∩ bd S := by
      rw [hC_eq]; exact ⟨ha_div, dualEquivRel_refl _ _ a⟩
    have hb_in : b ∈ V(C) ∩ bd S := by
      rw [hC_eq]; exact ⟨hb_div, h_equiv⟩
    have hC₁_eq : C₁ = C := hC₁.eq_of_mem_mem hC.1 haC₁ ha_in.1
    have hC₂_eq : C₂ = C := hC₂.eq_of_mem_mem hC.1 hbC₂ hb_in.1
    exact hne (hC₁_eq.trans hC₂_eq.symm)
  unfold dualEquivRel at h_not_equiv
  push Not at h_not_equiv
  obtain ⟨δ_star, hδ_star, u₁, hu₁, u₂, hu₂, hcross_u_ab⟩ := h_not_equiv
  have hU_sub_diff : U ⊆ bd S \ divisionUnion Δ_G := isDualPointSet_subset_diff hU_ΔG
  have hδ_star_eq := dualDivision_mem_eq_of_mem hS.isOArc_bd
    (hΔG_union ▸ inter_subset_right) hU_sub_diff hδ_star hu₁
  have hu₁_U : u₁ ∈ U := by rw [hδ_star_eq] at hu₁; exact hu₁.1
  have hu₂_U : u₂ ∈ U := by rw [hδ_star_eq] at hu₂; exact hu₂.1
  have hu₁₂_rel : dualEquivRel (bd S) Δ_G u₁ u₂ := by rw [hδ_star_eq] at hu₂; exact hu₂.2
  have hU_sub_bd : U ⊆ bd S \ G.U := by
    rw [hΔG_union] at hU_sub_diff
    intro u hu
    obtain ⟨hu_bd, hu_not_V⟩ := hU_sub_diff hu
    exact ⟨hu_bd, fun huU => hu_not_V ⟨hProper ⟨hu_bd, huU⟩, hu_bd⟩⟩
  have h_no_comp_cross : ∀ C ∈ graphComponents G.toGraph,
      ∀ v₁ ∈ V(C) ∩ bd S, ∀ v₂ ∈ V(C) ∩ bd S, ¬ CrossesOn (bd S) v₁ v₂ u₁ u₂ := by
    intro C hC v₁ hv₁ v₂ hv₂ hcr
    have hC_bd : C ∈ S_bd := ⟨hC, ⟨v₁, hv₁⟩⟩
    exact hu₁₂_rel ⟨V(C) ∩ bd S, ⟨C, hC_bd, rfl⟩, v₁, hv₁, v₂, hv₂, hcr⟩
  have h_same_reg := same_region_of_no_component_crosses hS G hProper
    (hU_sub_bd hu₁_U).1 (hU_sub_bd hu₂_U).1
    (hU_sub_bd hu₁_U).2 (hU_sub_bd hu₂_U).2 h_no_comp_cross
  let r : Set S := connectedComponentIn (univ \ G.U) u₁
  have hr_R : r ∈ G.R := ⟨u₁, ⟨mem_univ u₁, (hU_sub_bd hu₁_U).2⟩, rfl⟩
  have hu₁_r : u₁ ∈ r := mem_connectedComponentIn ⟨mem_univ u₁, (hU_sub_bd hu₁_U).2⟩
  have hu₂_r : u₂ ∈ r := by
    change u₂ ∈ connectedComponentIn (univ \ G.U) u₁
    rw [h_same_reg]
    exact mem_connectedComponentIn ⟨mem_univ u₂, (hU_sub_bd hu₂_U).2⟩
  have hr_per : ChainTerm.IsPeripheral G (.inr r) := by
    rw [isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr_R]
    exact ⟨u₁, hu₁_r, (hU_sub_bd hu₁_U).1⟩
  have hChain_r : IsXYChain G u₁ u₂ [.inr r] := by
    refine ⟨List.cons_ne_nil _ _, ?_, List.isChain_singleton _, hu₁_r, hu₂_r, ?_⟩
    · intro t ht
      rw [List.mem_singleton.mp ht]
      exact hr_R
    · intro ⟨i, hi⟩
      have hi0 : i = 0 := Nat.lt_one_iff.mp hi
      subst hi0
      simpa using hr_per
  have hred := hRed u₁ (Or.inl hu₁_U) u₂ (Or.inl hu₂_U) [.inr r] hChain_r
  have hlen0 : chainLength ([.inr r] : List (ChainTerm S)) = 0 := by
    simp [chainLength, ChainTerm.IsVertex]
  have hcount_pos : 1 ≤ divisionCount (bd S) Δ u₁ u₂ := by
    unfold divisionCount
    have hδ₀_in : δ₀ ∈ {δ ∈ Δ | (δ ∩ {u₁, u₂}).Nonempty ∨
        ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (bd S) u v u₁ u₂} := by
      refine ⟨hδ₀, Or.inr ⟨a, haδ₀, b, hbδ₀, ?_⟩⟩
      exact hcross_u_ab.comm hS.isOArc_bd
    have h_fin : {δ ∈ Δ | (δ ∩ {u₁, u₂}).Nonempty ∨
        ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn (bd S) u v u₁ u₂}.Finite :=
      hΔ.1.subset fun _ h => h.1
    exact ncard_pos h_fin |>.mpr ⟨δ₀, hδ₀_in⟩
  unfold chainRedundancy at hred
  omega

/-- **Case (3.3)(iv) Component Reduction** (Graph Minors VI, page 122, Case 4):
For any component `C_i ∈ graphComponents G.toGraph` with `(V(C_i) ∩ bd S).Nonempty` and any
sub-division `Δ_i ⊆ Δ` with `divisionUnion Δ_i = V(C_i) ∩ bd S`, the induced drawing
`G_i = induceDrawing G V(C_i)` has a dual point set `U_i ⊆ U` for `(bd S, G_i.V ∩ bd S)` such
that every chain of `G_i` has non-negative redundancy with respect to `Δ_i`. -/
theorem exists_dualPointSet_and_chainRedundancy_of_component [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {C_i : Graph S (Set S)} (hC_i : C_i ∈ graphComponents G.toGraph)
    (hCi_bd : (V(C_i) ∩ bd S).Nonempty)
    {Δ Δ_i : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_i_sub : Δ_i ⊆ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ x ∈ U ∪ (G.V ∩ bd S), ∀ y ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G x y A → 0 ≤ chainRedundancy G Δ x y A) :
    let G_i := induceDrawing G V(C_i)
    ∃ U_i ⊆ U, IsDualPointSet (bd S) (G_i.V ∩ bd S) U_i ∧
      (∀ x ∈ U_i ∪ (G_i.V ∩ bd S), ∀ y ∈ U_i ∪ (G_i.V ∩ bd S),
        ∀ A : List (ChainTerm S), IsXYChain G_i x y A → 0 ≤ chainRedundancy G_i Δ_i x y A) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  let G_i := induceDrawing G V(C_i)
  change ∃ U_i ⊆ U, IsDualPointSet (bd S) (G_i.V ∩ bd S) U_i ∧
    (∀ x ∈ U_i ∪ (G_i.V ∩ bd S), ∀ y ∈ U_i ∪ (G_i.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G_i x y A → 0 ≤ chainRedundancy G_i Δ_i x y A)
  have hVi_sub : V(C_i) ⊆ G.V := hC_i.1.vertexSet_mono
  have hProper_i : G_i.IsProper := induceDrawing_isProper G hProper hVi_sub
  have hSub_i : G_i.IsSubdrawing G := induceDrawing_isSubdrawing G hVi_sub
  have hGi_V : G_i.V = V(C_i) := induceDrawing_V G hVi_sub
  have hGi_U : G_i.U = compPointSet C_i := induceDrawing_U_of_component G hC_i
  have hVi_bd_sub : G_i.V ∩ bd S ⊆ G.V ∩ bd S := inter_subset_inter_left _ hSub_i.1
  obtain ⟨U_i, hUi_sub, hUi_dual, hUi_conn⟩ := exists_dualPointSet_subset_of_subset
    hS.isOArc_bd inter_subset_right (G.finite_V.inter_of_left _) hU hVi_bd_sub
  have hS_i_sub : ({C_i} : Set (Graph S (Set S))) ⊆ graphComponents G.toGraph :=
    singleton_subset_iff.mpr hC_i
  obtain ⟨_, hK₂_eq⟩ := induceDrawing_U_biUnion_components G hS_i_sub
  have h_V_sUnion : (⋃ C ∈ ({C_i} : Set (Graph S (Set S))), V(C)) = V(C_i) := by simp
  have hK₂_eq' : G.U \ G_i.U = ⋃ C ∈ graphComponents G.toGraph \ {C_i}, compPointSet C := by
    change G.U \ (induceDrawing G V(C_i)).U = _
    rwa [← h_V_sUnion]
  have hK₂_fin : (graphComponents G.toGraph \ {C_i}).Finite :=
    (finite_graphComponents G).subset sdiff_subset
  have hK₂_closed : IsClosed (G.U \ G_i.U) := by
    rw [hK₂_eq']
    exact hK₂_fin.isClosed_biUnion fun C hC => isClosed_compPointSet G hC.1
  have hU_sub_bd : U ⊆ bd S \ G.U := by
    have h1 := isDualPointSet_subset_diff hU
    intro u hu
    obtain ⟨hu_bd, hu_not_V⟩ := h1 hu
    exact ⟨hu_bd, fun huU => hu_not_V ⟨hProper ⟨hu_bd, huU⟩, hu_bd⟩⟩
  have hUi_sub_bd : U_i ⊆ bd S \ G.U := hUi_sub.trans hU_sub_bd
  have hGi_bd_ne : (G_i.V ∩ bd S).Nonempty := hGi_V.symm ▸ hCi_bd
  obtain ⟨v₀, hv₀⟩ := hCi_bd
  have hv₀_Gi : v₀ ∈ G_i.U := G_i.V_subset_U (hGi_V.symm ▸ hv₀.1)
  have hGi_sub_compl : G_i.U ⊆ univ \ (G.U \ G_i.U) := fun z hz => ⟨mem_univ z, fun h => h.2 hz⟩
  have hGi_conn : IsConnected G_i.U := hGi_U ▸ isConnected_compPointSet G hC_i
  have h_in_cc_v₀ : ∀ z ∈ G_i.U ∪ U_i, z ∈ connectedComponentIn (univ \ (G.U \ G_i.U)) v₀ := by
    rintro z (hz_Gi | hz_Ui)
    · exact hGi_conn.isPreconnected.subset_connectedComponentIn hv₀_Gi hGi_sub_compl hz_Gi
    · obtain ⟨v', hv', seg₀, hseg₀, _, K, hK_sub, hK_conn, hv'_K, hz_K⟩ := hUi_conn z hz_Ui
      have hv'_Gi : v' ∈ G_i.U := G_i.V_subset_U hv'.1
      have hv'_cc : v' ∈ connectedComponentIn (univ \ (G.U \ G_i.U)) v₀ :=
        hGi_conn.isPreconnected.subset_connectedComponentIn hv₀_Gi hGi_sub_compl hv'_Gi
      have hseg_sub : seg₀ ⊆ bd S \ G.U := by
        rcases hseg₀.1 with ⟨w, hw, rfl⟩
        refine (connectedComponentIn_subset _ _).trans fun x hx =>
          ⟨hx.1, fun hxU => hx.2 ⟨hProper ⟨hx.1, hxU⟩, hx.1⟩⟩
      have hK_compl : K ⊆ univ \ (G.U \ G_i.U) := by
        refine hK_sub.trans ?_
        rintro x (rfl | hx_seg)
        · exact hGi_sub_compl hv'_Gi
        · exact ⟨mem_univ x, fun h => (hseg_sub hx_seg).2 h.1⟩
      rw [connectedComponentIn_eq hv'_cc]
      exact hK_conn.isPreconnected.subset_connectedComponentIn hv'_K hK_compl hz_K
  have h_same_comp : ∀ a ∈ G_i.U ∪ U_i, ∀ b ∈ G_i.U ∪ U_i,
      b ∈ connectedComponentIn (univ \ (G.U \ G_i.U)) a := by
    intro a ha b hb
    rw [← connectedComponentIn_eq (h_in_cc_v₀ a ha)]
    exact h_in_cc_v₀ b hb
  refine ⟨U_i, hUi_sub, hUi_dual, fun x hx y hy A hChain_i => ?_⟩
  have hxG : x ∈ U ∪ (G.V ∩ bd S) := hx.imp (fun h => hUi_sub h) (fun h => hVi_bd_sub h)
  have hyG : y ∈ U ∪ (G.V ∩ bd S) := hy.imp (fun h => hUi_sub h) (fun h => hVi_bd_sub h)
  obtain ⟨A_G, hChainG, hlen_eq⟩ := liftChain_of_subdrawing hS hProper hProper_i hSub_i
    hK₂_closed hGi_bd_ne hUi_sub_bd h_same_comp hx hy hChain_i
  have hredG := hRed x hxG y hyG A_G hChainG
  have hdiv_le : divisionCount (bd S) Δ_i x y ≤ divisionCount (bd S) Δ x y :=
    divisionCount_le_of_subset hΔ hΔ_i_sub x y
  unfold chainRedundancy at hredG ⊢
  omega

end GraphMinor.GM06
