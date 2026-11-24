/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.Section3Induce

/-!
# Graph Minors VI, Section 3: Singleton-Deletion Reduction for (3.6)

This file formalizes the singleton-deletion reduction (`(3.3)(i)`, Case 2 of the proof of `(3.6)`
on page 122 of Robertson and Seymour, *Graph Minors. VI. Disjoint paths across a disc*,
J. Combin. Theory Ser. B **41** (1986), 115–138):
if `{v} ∈ Δ`, deleting `v` from `G` and `{v}` from `Δ` produces a smaller proper drawing
`G' = induceDrawing G (G.V \ {v})` and division `Δ' = Δ \ {{v}}` preserving non-negative chain
redundancy.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Triangle Inequality and Singleton Removal for `divisionCount` -/

/-- Triangle inequality for `divisionCount` on an $O$-arc `C` when the middle point `y` is not in
`divisionUnion Δ`. -/
theorem divisionCount_le_add_of_not_mem {C : Set S} (hC : IsOArc C)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hV_sub : divisionUnion Δ ⊆ C)
    {x y z : S} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) (hy_not : y ∉ divisionUnion Δ) :
    divisionCount C Δ x z ≤ divisionCount C Δ x y + divisionCount C Δ y z := by
  let S_xz := {δ ∈ Δ | (δ ∩ {x, z}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v x z}
  let S_xy := {δ ∈ Δ | (δ ∩ {x, y}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v x y}
  let S_yz := {δ ∈ Δ | (δ ∩ {y, z}).Nonempty ∨ ∃ u ∈ δ, ∃ v ∈ δ, CrossesOn C u v y z}
  have h_sub : S_xz ⊆ S_xy ∪ S_yz := by
    rintro δ ⟨hδ, hcond⟩
    rcases hcond with ⟨w, hwδ, hwxz⟩ | ⟨u, huδ, v, hvδ, hcr⟩
    · rcases hwxz with rfl | hwz
      · exact Or.inl ⟨hδ, Or.inl ⟨w, hwδ, mem_insert w {y}⟩⟩
      · rw [mem_singleton_iff] at hwz
        subst hwz
        exact Or.inr ⟨hδ, Or.inl ⟨w, hwδ, mem_insert_of_mem y (mem_singleton w)⟩⟩
    · have hu_div : u ∈ divisionUnion Δ := ⟨δ, hδ, huδ⟩
      have hv_div : v ∈ divisionUnion Δ := ⟨δ, hδ, hvδ⟩
      have huy : u ≠ y := fun h => hy_not (h ▸ hu_div)
      have hvy : v ≠ y := fun h => hy_not (h ▸ hv_div)
      by_cases hcr_xy : CrossesOn C u v x y
      · exact Or.inl ⟨hδ, Or.inr ⟨u, huδ, v, hvδ, hcr_xy⟩⟩
      · have hcr_yz : CrossesOn C u v y z := by
          by_contra hcr_yz
          exact not_crossesOn_trans hC (hV_sub hu_div) (hV_sub hv_div)
            hx hy hz huy hvy hcr_xy hcr_yz hcr
        exact Or.inr ⟨hδ, Or.inr ⟨u, huδ, v, hvδ, hcr_yz⟩⟩
  have hxy_fin : S_xy.Finite := hΔ.1.subset fun _ h => h.1
  have hyz_fin : S_yz.Finite := hΔ.1.subset fun _ h => h.1
  unfold divisionCount
  exact (ncard_le_ncard h_sub (hxy_fin.union hyz_fin)).trans (ncard_union_le S_xy S_yz)

/-- If `divisionCount C Δ x y = 0` and `x, y, z ∈ C` with `y ∉ divisionUnion Δ`, then
`divisionCount C Δ x z ≤ divisionCount C Δ y z`. -/
theorem divisionCount_le_of_left_eq_zero {C : Set S} (hC : IsOArc C)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hV_sub : divisionUnion Δ ⊆ C)
    {x y z : S} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) (hy_not : y ∉ divisionUnion Δ)
    (h0 : divisionCount C Δ x y = 0) :
    divisionCount C Δ x z ≤ divisionCount C Δ y z := by
  have h := divisionCount_le_add_of_not_mem hC hΔ hV_sub hx hy hz hy_not
  omega

/-- If `divisionCount C Δ y z = 0` and `x, y, z ∈ C` with `y ∉ divisionUnion Δ`, then
`divisionCount C Δ x z ≤ divisionCount C Δ x y`. -/
theorem divisionCount_le_of_right_eq_zero {C : Set S} (hC : IsOArc C)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hV_sub : divisionUnion Δ ⊆ C)
    {x y z : S} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) (hy_not : y ∉ divisionUnion Δ)
    (h0 : divisionCount C Δ y z = 0) :
    divisionCount C Δ x z ≤ divisionCount C Δ x y := by
  have h := divisionCount_le_add_of_not_mem hC hΔ hV_sub hx hy hz hy_not
  omega

/-- Removing a singleton member `{v} ∈ Δ` decreases `divisionCount C Δ x v` by `1`. -/
theorem divisionCount_sdiff_singleton_right (C : Set S) {Δ : Set (Set S)} (hΔ : IsDivision Δ)
    {v : S} (hv : {v} ∈ Δ) (x : S) :
    divisionCount C Δ x v = divisionCount C (Δ \ {{v}}) x v + 1 := by
  let S_full := {δ ∈ Δ | (δ ∩ {x, v}).Nonempty ∨ ∃ a ∈ δ, ∃ b ∈ δ, CrossesOn C a b x v}
  let S_del := {δ ∈ Δ \ {{v}} | (δ ∩ {x, v}).Nonempty ∨ ∃ a ∈ δ, ∃ b ∈ δ, CrossesOn C a b x v}
  have h_eq : S_full = insert {v} S_del := by
    ext δ
    simp only [S_full, S_del, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro ⟨hδ, hcond⟩
      rcases eq_or_ne δ {v} with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hδ, hne⟩, hcond⟩
    · rintro (rfl | ⟨⟨hδ, _⟩, hcond⟩)
      · refine ⟨hv, Or.inl ⟨v, rfl, mem_insert_of_mem x (mem_singleton v)⟩⟩
      · exact ⟨hδ, hcond⟩
  have h_not_mem : {v} ∉ S_del := fun h => h.1.2 rfl
  have h_fin : S_del.Finite := hΔ.1.subset fun _ h => h.1.1
  unfold divisionCount
  change S_full.ncard = S_del.ncard + 1
  rw [h_eq, ncard_insert_of_notMem h_not_mem h_fin]

/-- Removing a singleton member `{v} ∈ Δ` decreases `divisionCount C Δ v y` by `1`. -/
theorem divisionCount_sdiff_singleton_left (C : Set S) {Δ : Set (Set S)} (hΔ : IsDivision Δ)
    {v : S} (hv : {v} ∈ Δ) (y : S) :
    divisionCount C Δ v y = divisionCount C (Δ \ {{v}}) v y + 1 := by
  let S_full := {δ ∈ Δ | (δ ∩ {v, y}).Nonempty ∨ ∃ a ∈ δ, ∃ b ∈ δ, CrossesOn C a b v y}
  let S_del := {δ ∈ Δ \ {{v}} | (δ ∩ {v, y}).Nonempty ∨ ∃ a ∈ δ, ∃ b ∈ δ, CrossesOn C a b v y}
  have h_eq : S_full = insert {v} S_del := by
    ext δ
    simp only [S_full, S_del, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro ⟨hδ, hcond⟩
      rcases eq_or_ne δ {v} with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hδ, hne⟩, hcond⟩
    · rintro (rfl | ⟨⟨hδ, _⟩, hcond⟩)
      · refine ⟨hv, Or.inl ⟨v, rfl, mem_insert v {y}⟩⟩
      · exact ⟨hδ, hcond⟩
  have h_not_mem : {v} ∉ S_del := fun h => h.1.2 rfl
  have h_fin : S_del.Finite := hΔ.1.subset fun _ h => h.1.1
  unfold divisionCount
  change S_full.ncard = S_del.ncard + 1
  rw [h_eq, ncard_insert_of_notMem h_not_mem h_fin]

/-! ## 2. Peripheral Regions, Dual Points, and Short Chains in `G` -/

/-- If a region `r ∈ G.R` of a proper drawing `G` on a closed disc space `S` (with
`(G.V ∩ bd S).Nonempty`) meets `bd S`, and `U` is a dual point set for `(bd S, G.V ∩ bd S)`, then
`r` contains a point of `U`. -/
theorem exists_mem_U_of_region_inter_bd_nonempty (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (hVG_ne : (G.V ∩ bd S).Nonempty)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    {r : Set S} (hr : r ∈ G.R) (hr_bd : (r ∩ bd S).Nonempty) :
    ∃ u ∈ U, u ∈ r := by
  have hr_per : ChainTerm.IsPeripheral G (.inr r) :=
    (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr).mpr hr_bd
  obtain ⟨_, seg, hseg, hseg_sub⟩ := hr_per
  have h_card : (U ∩ seg).ncard = 1 := (hU.2 hVG_ne).2 seg hseg
  obtain ⟨u, hu_eq⟩ := ncard_eq_one.mp h_card
  have hu_mem : u ∈ U ∩ seg := by rw [hu_eq]; exact mem_singleton u
  exact ⟨u, hu_mem.1, hseg_sub hu_mem.2⟩

/-- If `x, y ∈ U ∪ (G.V ∩ bd S)` both lie in a peripheral region `r ∈ G.R`, then `[.inr r]` is an
`(x, y)`-chain of `G` of length `0`, so non-negative chain redundancy implies
`divisionCount (bd S) Δ x y = 0`. -/
theorem divisionCount_eq_zero_of_mem_region (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (hVG_ne : (G.V ∩ bd S).Nonempty)
    {Δ : Set (Set S)} {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {r : Set S} (hr : r ∈ G.R) {x y : S}
    (hx : x ∈ U ∪ (G.V ∩ bd S)) (hy : y ∈ U ∪ (G.V ∩ bd S))
    (hxr : x ∈ r) (hyr : y ∈ r) :
    divisionCount (bd S) Δ x y = 0 := by
  have hx_bd : x ∈ bd S := by
    rcases hx with hxU | hxV
    · exact (isDualPointSet_subset_diff hU hxU).1
    · exact hxV.2
  have hr_per : ChainTerm.IsPeripheral G (.inr r) := by
    rw [isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr]
    exact ⟨x, hxr, hx_bd⟩
  have hChain : IsXYChain G x y [.inr r] := by
    refine ⟨List.cons_ne_nil _ _, ?_, List.isChain_singleton _, hxr, hyr, ?_⟩
    · intro t ht
      rw [List.mem_singleton.mp ht]
      exact hr
    · intro ⟨i, hi⟩
      have hi0 : i = 0 := Nat.lt_one_iff.mp hi
      subst hi0
      simpa using hr_per
  have hred := hRed x hx y hy [.inr r] hChain
  have hlen : chainLength ([.inr r] : List (ChainTerm S)) = 0 := by
    simp [chainLength, ChainTerm.IsVertex]
  unfold chainRedundancy at hred
  omega

/-- If `{v} ∈ Δ`, `r ∈ G.R`, `u ∈ U ∪ (G.V ∩ bd S)`, `u ∈ r`, and `v ∈ closure r`, then
`[.inr r, .inl v]` is a `(u, v)`-chain of `G` and `[.inl v, .inr r]` is a `(v, u)`-chain of `G`,
both of length `1`, so `divisionCount (bd S) (Δ \ {{v}}) u v = 0` and
`divisionCount (bd S) (Δ \ {{v}}) v u = 0`. -/
theorem divisionCount_sdiff_eq_zero_of_region_incident_v (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {r : Set S} (hr : r ∈ G.R) {u : S} (hu : u ∈ U ∪ (G.V ∩ bd S))
    (hur : u ∈ r) (hvr : v ∈ closure r) :
    divisionCount (bd S) (Δ \ {{v}}) u v = 0 ∧
      divisionCount (bd S) (Δ \ {{v}}) v u = 0 := by
  have hv_bd : v ∈ G.V ∩ bd S := hΔ_sub ⟨{v}, hv, rfl⟩
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v, hv_bd⟩
  have hu_bd : u ∈ bd S := by
    rcases hu with huU | huV
    · exact (isDualPointSet_subset_diff hU huU).1
    · exact huV.2
  have hr_per : ChainTerm.IsPeripheral G (.inr r) := by
    rw [isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr]
    exact ⟨u, hur, hu_bd⟩
  have hv_per : ChainTerm.IsPeripheral G (.inl v) := hv_bd
  have hChain1 : IsXYChain G u v [.inr r, .inl v] := by
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, hur, rfl, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hr
      · rw [List.mem_singleton.mp ht']
        exact hv_bd.1
    · rw [List.isChain_cons_cons]
      exact ⟨⟨hv_bd.1, hr, hvr⟩, List.isChain_singleton _⟩
    · intro ⟨i, hi⟩
      have hi_cases : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases hi_cases with rfl | rfl
      · simpa using hr_per
      · simpa using hv_per
  have hChain2 : IsXYChain G v u [.inl v, .inr r] := by
    refine ⟨List.cons_ne_nil _ _, ?_, ?_, rfl, hur, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hv_bd.1
      · rw [List.mem_singleton.mp ht']
        exact hr
    · rw [List.isChain_cons_cons]
      exact ⟨⟨hv_bd.1, hr, hvr⟩, List.isChain_singleton _⟩
    · intro ⟨i, hi⟩
      have hi_cases : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases hi_cases with rfl | rfl
      · simpa using hv_per
      · simpa using hr_per
  have hlen1 : chainLength ([.inr r, .inl v] : List (ChainTerm S)) = 1 := rfl
  have hlen2 : chainLength ([.inl v, .inr r] : List (ChainTerm S)) = 1 := rfl
  have hred1 := hRed u hu v (Or.inr hv_bd) [.inr r, .inl v] hChain1
  have hred2 := hRed v (Or.inr hv_bd) u hu [.inl v, .inr r] hChain2
  have hdiv1 := divisionCount_sdiff_singleton_right (bd S) hΔ hv u
  have hdiv2 := divisionCount_sdiff_singleton_left (bd S) hΔ hv u
  unfold chainRedundancy at hred1 hred2
  omega

/-! ## 3. Subregions of `G` Inside a Region `r'` of `G'` -/

/-- For any subdrawing `G' ⊆ G` of a proper drawing `G` on a closed disc space `S`, any region
`r' ∈ G'.R`, and any point `a ∈ closure r'` (with `a ∉ G.U` if `a ∈ r'`), there exists a region
`r ∈ G.R` such that `r ⊆ r'`, `a ∈ closure r`, and `(a ∈ r' → a ∈ r)`. -/
theorem exists_subregion_closure_of_mem_closure (hS : IsClosedDiscSpace S)
    {G G' : Drawing S} (hProper : G.IsProper) (hSub : G'.IsSubdrawing G)
    {r' : Set S} (hr' : r' ∈ G'.R) {a : S} (ha : a ∈ closure r')
    (ha_not_U : a ∈ r' → a ∉ G.U) :
    ∃ r ∈ G.R, r ⊆ r' ∧ a ∈ closure r ∧ (a ∈ r' → a ∈ r) := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  by_cases ha_in : a ∈ r'
  · have haU : a ∉ G.U := ha_not_U ha_in
    obtain ⟨r, hr, har⟩ := exists_region_of_notMem haU
    have hr_sub : r ⊆ r' := subset_region hr' (region_isPreconnected hr)
      (disjoint_left.mpr fun y hy h => region_subset hr hy (hSub.U_subset h)) har ha_in
    exact ⟨r, hr, hr_sub, subset_closure har, fun _ => har⟩
  · let S_sub : Set (Set S) := {r ∈ G.R | r ⊆ r'}
    have hS_fin : S_sub.Finite := (disc_finite_R hS G hProper).subset fun _ h => h.1
    have hr'_sub_cl : r' ⊆ closure (⋃ r ∈ S_sub, r) := by
      intro x hxr'
      rw [mem_closure_iff]
      intro O hO hxO
      obtain ⟨y, ⟨hyO, hyr'⟩, hyU⟩ :=
        disc_exists_notMem_U hS hProper (hO.inter (region_isOpen hr')) ⟨x, hxO, hxr'⟩
      obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
      have hr_sub : r ⊆ r' := subset_region hr' (region_isPreconnected hr)
        (disjoint_left.mpr fun z hz h => region_subset hr hz (hSub.U_subset h)) hyr hyr'
      exact ⟨y, hyO, mem_iUnion₂.mpr ⟨r, ⟨hr, hr_sub⟩, hyr⟩⟩
    have hcl_sub : closure r' ⊆ ⋃ r ∈ S_sub, closure r := by
      rw [← hS_fin.closure_biUnion]
      exact closure_minimal hr'_sub_cl isClosed_closure
    obtain ⟨r, ⟨hr, hr_sub⟩, ha_cl⟩ := mem_iUnion₂.mp (hcl_sub ha)
    exact ⟨r, hr, hr_sub, ha_cl, fun h => (ha_in h).elim⟩

/-- If `G' = induceDrawing G (G.V \ {v})` for a proper drawing `G` on a closed disc space `S`,
`r' ∈ G'.R`, and `r₁, r₂ ∈ G.R` satisfy `r₁ ⊆ r'` and `r₂ ⊆ r'`, then either `r₁ = r₂` or
`v ∈ closure r₁ ∧ v ∈ closure r₂`. -/
theorem subregion_eq_or_mem_closure_of_delete_vertex [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (v : S)
    {r' r₁ r₂ : Set S} (hr' : r' ∈ (induceDrawing G (G.V \ {v})).R)
    (hr₁ : r₁ ∈ G.R) (hr₂ : r₂ ∈ G.R) (hs₁ : r₁ ⊆ r') (hs₂ : r₂ ⊆ r') :
    r₁ = r₂ ∨ (v ∈ closure r₁ ∧ v ∈ closure r₂) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  rcases eq_or_ne r₁ r₂ with rfl | hne
  · exact Or.inl rfl
  · right
    have hSub : (induceDrawing G (G.V \ {v})).IsSubdrawing G :=
      induceDrawing_isSubdrawing G sdiff_subset
    have h_aux : ∀ {c d : Set S}, c ∈ G.R → d ∈ G.R → c ⊆ r' → d ⊆ r' → c ≠ d →
        v ∈ closure c := by
      intro c d hc hd hcs hds hcd
      obtain ⟨e, heG, he_not, a, b, ha_mem, _, _, _, hia, _⟩ :=
        disc_theorem_5_1 hS hProper hSub (Z := {c}) hr' hc (mem_singleton c) hd
          (fun h => hcd (mem_singleton_iff.mp h).symm) hcs hds
      rw [mem_singleton_iff] at ha_mem
      subst ha_mem
      have he_cl : e ⊆ closure a :=
        disc_edge_subset_closure_of_incident hS hProper hia.1 hia.2.1 hia.2.2
      have hcl_sub : closure e ⊆ closure a := closure_minimal he_cl isClosed_closure
      rw [induceDrawing_E] at he_not
      have h_not_sub : ¬ (closure e ∩ G.V ⊆ G.V \ {v}) := fun h => he_not ⟨heG, h⟩
      obtain ⟨z, ⟨hz_cl, hzV⟩, hz_not⟩ := not_subset.mp h_not_sub
      have hzv : z = v := by
        by_contra hzv
        exact hz_not ⟨hzV, hzv⟩
      subst hzv
      exact hcl_sub hz_cl
    exact ⟨h_aux hr₁ hr₂ hs₁ hs₂ hne, h_aux hr₂ hr₁ hs₂ hs₁ hne.symm⟩

/-! ## 4. Chain Redundancy Under Singleton Deletion -/

/-- If `a ∈ r₁` and `b ∈ r₂` for two subregions `r₁, r₂ ∈ G.R` of the same region `r'` of
`induceDrawing G (G.V \ {v})`, then `divisionCount (bd S) (Δ \ {{v}}) a b = 0`. -/
private lemma divisionCount_sdiff_eq_zero_of_subregions [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {r' r₁ r₂ : Set S} (hr' : r' ∈ (induceDrawing G (G.V \ {v})).R)
    (hr₁ : r₁ ∈ G.R) (hr₂ : r₂ ∈ G.R) (hr₁_sub : r₁ ⊆ r') (hr₂_sub : r₂ ⊆ r')
    {a b : S} (ha : a ∈ U ∪ (G.V ∩ bd S)) (hb : b ∈ U ∪ (G.V ∩ bd S))
    (har₁ : a ∈ r₁) (hbr₂ : b ∈ r₂) :
    divisionCount (bd S) (Δ \ {{v}}) a b = 0 := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v, hΔ_sub ⟨{v}, hv, rfl⟩⟩
  have hU_sub_bd : U ⊆ bd S \ G.U := by
    have h1 := isDualPointSet_subset_diff hU
    intro u hu
    exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
  rcases subregion_eq_or_mem_closure_of_delete_vertex hS hProper v hr'
      hr₁ hr₂ hr₁_sub hr₂_sub with rfl | ⟨hva, hvb⟩
  · have h0 := divisionCount_eq_zero_of_mem_region hS hProper hVG_ne hU hRed
      hr₁ ha hb har₁ hbr₂
    have hle := divisionCount_le_of_subset (C := bd S) hΔ (sdiff_subset : Δ \ {{v}} ⊆ Δ) a b
    omega
  · have h1 := (divisionCount_sdiff_eq_zero_of_region_incident_v hS hProper hΔ hΔ_sub
      hv hU hRed hr₁ ha har₁ hva).1
    have h2 := (divisionCount_sdiff_eq_zero_of_region_incident_v hS hProper hΔ hΔ_sub
      hv hU hRed hr₂ hb hbr₂ hvb).2
    have hΔ'_div : IsDivision (Δ \ {{v}}) :=
      ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
    have hΔ'_sub_bd : divisionUnion (Δ \ {{v}}) ⊆ bd S :=
      (sUnion_mono sdiff_subset).trans (hΔ_sub.trans inter_subset_right)
    have hv_not_Δ' : v ∉ divisionUnion (Δ \ {{v}}) := by
      rintro ⟨δ, ⟨hδ, hne⟩, hvδ⟩
      exact (hΔ.2.2 hδ hv hne).ne_of_mem hvδ rfl rfl
    have ha_bd : a ∈ bd S := ha.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
    have hb_bd : b ∈ bd S := hb.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
    have hv_bd : v ∈ bd S := (hΔ_sub ⟨{v}, hv, rfl⟩).2
    have htri := divisionCount_le_add_of_not_mem hS.isOArc_bd hΔ'_div hΔ'_sub_bd
      ha_bd hv_bd hb_bd hv_not_Δ'
    omega

/-- Case `A'.length = 1` of singleton deletion: if `A'` is a 1-term `(x, y)`-chain of
`G' = induceDrawing G (G.V \ {v})`, then `0 ≤ chainRedundancy G' (Δ \ {{v}}) x y A'`. -/
theorem chainRedundancy_nonneg_of_length_one [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x y : S} (hx : x ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    (hy : y ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (hlen1 : A'.length = 1) :
    0 ≤ chainRedundancy (induceDrawing G (G.V \ {v})) (Δ \ {{v}}) x y A' := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  let G' := induceDrawing G (G.V \ {v})
  let Δ' := Δ \ {{v}}
  have hSub : G'.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hxG : x ∈ U ∪ (G.V ∩ bd S) :=
    hx.imp (fun h => hU'_sub h) (fun h => ⟨hSub.1 h.1, h.2⟩)
  have hyG : y ∈ U ∪ (G.V ∩ bd S) :=
    hy.imp (fun h => hU'_sub h) (fun h => ⟨hSub.1 h.1, h.2⟩)
  obtain ⟨t₀, rfl⟩ := List.length_eq_one_iff.mp hlen1
  have ht₀_val := hChain.valid t₀ (List.mem_singleton_self t₀)
  have hhead : ([t₀] : List (ChainTerm S)).head hChain.ne_nil = t₀ := rfl
  have hlast : ([t₀] : List (ChainTerm S)).getLast hChain.ne_nil = t₀ := rfl
  have hmatch_x := hChain.head_matches
  have hmatch_y := hChain.last_matches
  rw [hhead] at hmatch_x
  rw [hlast] at hmatch_y
  rcases t₀ with w | r'
  · change w ∈ G'.V at ht₀_val
    change w = x at hmatch_x
    change w = y at hmatch_y
    subst hmatch_x hmatch_y
    have hw_per : ChainTerm.IsPeripheral G (.inl w) := by
      have hper' := (hChain.peripheral_iff ⟨0, Nat.zero_lt_one⟩).mpr (Or.inl rfl)
      exact ⟨hSub.1 hper'.1, hper'.2⟩
    have hChainG : IsXYChain G w w [.inl w] := by
      refine ⟨List.cons_ne_nil _ _, ?_, List.isChain_singleton _, rfl, rfl, ?_⟩
      · intro t ht; rw [List.mem_singleton.mp ht]; exact hSub.1 ht₀_val
      · intro ⟨i, hi⟩
        have hi0 : i = 0 := Nat.lt_one_iff.mp hi
        subst hi0
        simpa using hw_per
    have hredG := hRed w hxG w hxG [.inl w] hChainG
    have hdiv_le := divisionCount_le_of_subset (C := bd S) hΔ (sdiff_subset : Δ' ⊆ Δ) w w
    unfold chainRedundancy at hredG ⊢
    omega
  · change r' ∈ G'.R at ht₀_val
    change x ∈ r' at hmatch_x
    change y ∈ r' at hmatch_y
    have hU_sub_bd : U ⊆ bd S \ G.U := by
      have h1 := isDualPointSet_subset_diff hU
      intro u hu
      exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
    have hx_not_U : x ∉ G.U := by
      rcases hx with hxU' | hxV'
      · exact (hU_sub_bd (hU'_sub hxU')).2
      · exact fun _ => region_subset ht₀_val hmatch_x (G'.V_subset_U hxV'.1)
    have hy_not_U : y ∉ G.U := by
      rcases hy with hyU' | hyV'
      · exact (hU_sub_bd (hU'_sub hyU')).2
      · exact fun _ => region_subset ht₀_val hmatch_y (G'.V_subset_U hyV'.1)
    obtain ⟨r_x, hr_x, hr_x_sub, _, hxr_x_in⟩ :=
      exists_subregion_closure_of_mem_closure hS hProper hSub ht₀_val
        (subset_closure hmatch_x) (fun _ => hx_not_U)
    obtain ⟨r_y, hr_y, hr_y_sub, _, hyr_y_in⟩ :=
      exists_subregion_closure_of_mem_closure hS hProper hSub ht₀_val
        (subset_closure hmatch_y) (fun _ => hy_not_U)
    have hxr_x : x ∈ r_x := hxr_x_in hmatch_x
    have hyr_y : y ∈ r_y := hyr_y_in hmatch_y
    have hdiv0 := divisionCount_sdiff_eq_zero_of_subregions hS hProper hΔ hΔ_sub hv hU hRed
      ht₀_val hr_x hr_y hr_x_sub hr_y_sub hxG hyG hxr_x hyr_y
    have hlen0 : chainLength ([.inr r'] : List (ChainTerm S)) = 0 := rfl
    unfold chainRedundancy
    omega

/-- Criterion for `IsXYChain` in terms of index-wise properties when `2 ≤ L.length`. -/
private lemma isXYChain_of_getElem (G : Drawing S) (a b : S) (L : List (ChainTerm S))
    (hlen : 2 ≤ L.length)
    (hvalid : ∀ i : Fin L.length, ChainTerm.IsValid G L[i])
    (hadj : ∀ (i : ℕ) (hi : i + 1 < L.length),
      ChainTerm.AreIncident G (L[i]'(Nat.lt_of_succ_lt hi)) (L[i + 1]'hi))
    (hhead : ChainTerm.MatchesEnd a (L[0]'(by omega)))
    (hlast : ChainTerm.MatchesEnd b (L[L.length - 1]'(by omega)))
    (hper_zero : ChainTerm.IsPeripheral G (L[0]'(by omega)))
    (hper_last : ChainTerm.IsPeripheral G (L[L.length - 1]'(by omega)))
    (hper_mid : ∀ (i : ℕ) (hi : i < L.length), 0 < i → i + 1 < L.length →
      ¬ ChainTerm.IsPeripheral G (L[i]'hi)) :
    IsXYChain G a b L := by
  have hne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine ⟨hne, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    exact hvalid ⟨i, hi⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    exact hadj i hi
  · rw [List.head_eq_getElem_zero]
    exact hhead
  · rw [List.getLast_eq_getElem]
    exact hlast
  · intro ⟨i, hi⟩
    change ChainTerm.IsPeripheral G (L[i]'hi) ↔ i = 0 ∨ i + 1 = L.length
    constructor
    · intro hper
      by_contra hnot
      have h1 : i ≠ 0 := fun h0 => hnot (Or.inl h0)
      have h2 : i + 1 ≠ L.length := fun hl => hnot (Or.inr hl)
      exact hper_mid i hi (Nat.pos_of_ne_zero h1) (by omega) hper
    · rintro (rfl | hl)
      · exact hper_zero
      · have hi_eq : i = L.length - 1 := by omega
        subst hi_eq
        exact hper_last

omit [TopologicalSpace S] in
private lemma chainLength_append (L₁ L₂ : List (ChainTerm S)) :
    chainLength (L₁ ++ L₂) = chainLength L₁ + chainLength L₂ := by
  simp [chainLength, List.filter_append]

omit [TopologicalSpace S] in
private lemma chainLength_cons (t : ChainTerm S) (L : List (ChainTerm S)) :
    chainLength (t :: L) = (if t.IsVertex then 1 else 0) + chainLength L := by
  by_cases h : t.IsVertex <;> simp [chainLength, h, Nat.add_comm]

omit [TopologicalSpace S] in
private lemma chainLength_eq_of_isVertex_eq {L₁ L₂ : List (ChainTerm S)}
    (hlen : L₁.length = L₂.length)
    (hisV : ∀ (i : ℕ) (hi : i < L₁.length),
      ChainTerm.IsVertex (L₁[i]'hi) ↔ ChainTerm.IsVertex (L₂[i]'(hlen ▸ hi))) :
    chainLength L₁ = chainLength L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a L₁ ih =>
    cases L₂ with
    | nil => simp at hlen
    | cons b L₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have h0 : a.IsVertex ↔ b.IsVertex := hisV 0 (Nat.zero_lt_succ _)
      have hite : (if a.IsVertex then 1 else 0) = (if b.IsVertex then 1 else 0) := by
        by_cases ha : a.IsVertex
        · have hb : b.IsVertex := h0.mp ha
          simp [ha, hb]
        · have hb : ¬ b.IsVertex := fun hb => ha (h0.mpr hb)
          simp [ha, hb]
      have htail : chainLength L₁ = chainLength L₂ :=
        ih hlen (fun i hi => hisV (i + 1) (Nat.succ_lt_succ hi))
      rw [chainLength_cons, chainLength_cons, hite, htail]

omit [TopologicalSpace S] in
private lemma chainLength_drop_antitone (L : List (ChainTerm S)) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    chainLength (L.drop k₂) ≤ chainLength (L.drop k₁) := by
  have hd : (L.drop k₁).take (k₂ - k₁) ++ L.drop k₂ = L.drop k₁ := by
    have h1 := List.take_append_drop (k₂ - k₁) (L.drop k₁)
    rwa [List.drop_drop, Nat.add_sub_of_le h] at h1
  have hc := congrArg chainLength hd
  rw [chainLength_append] at hc
  omega

omit [TopologicalSpace S] in
private lemma chainLength_take_add_drop_le (A : List (ChainTerm S))
    {j₁ j₂ : ℕ} (hj₁ : j₁ < A.length) (hle : j₁ ≤ j₂)
    (hnotV : ¬ ChainTerm.IsVertex (A[j₁]'hj₁)) :
    chainLength (A.take (j₁ + 1)) + chainLength (A.drop j₂) ≤ chainLength A := by
  have hsplit : chainLength (A.take (j₁ + 1)) + chainLength (A.drop (j₁ + 1)) = chainLength A := by
    rw [← chainLength_append, List.take_append_drop]
  have hcons : A.drop j₁ = A[j₁] :: A.drop (j₁ + 1) := List.drop_eq_getElem_cons hj₁
  have hite0 : (if (A[j₁]'hj₁).IsVertex then 1 else 0) = 0 := by
    simp [hnotV]
  have hdrop_eq : chainLength (A.drop j₁) = chainLength (A.drop (j₁ + 1)) := by
    rw [hcons, chainLength_cons, hite0, zero_add]
  have hmono := chainLength_drop_antitone A hle
  omega

/-- Raw left-anchored lift of `A'[i]` to a chain term of `G`. -/
private lemma exists_left_raw_term [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (v : S)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hVG_ne : (G.V ∩ bd S).Nonempty)
    {x y : S} (hx : x ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (i : Fin A'.length) :
    ∃ t : ChainTerm S,
      t.IsValid G ∧
      (t.IsVertex ↔ (A'[i]).IsVertex) ∧
      (∀ w, A'[i] = .inl w ↔ t = .inl w) ∧
      (∀ r', A'[i] = .inr r' → ∃ r ∈ G.R, t = .inr r ∧ r ⊆ r') ∧
      (i.1 = 0 → t.MatchesEnd x ∧ t.IsPeripheral G) ∧
      (∀ (h0 : 0 < i.1) (w : S),
        A'[i.1 - 1]'(by omega) = .inl w → ChainTerm.AreIncident G (.inl w) t) := by
  let G' := induceDrawing G (G.V \ {v})
  have hSub : G'.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hval' : (A'[i]).IsValid G' := hChain.valid A'[i] (List.getElem_mem _)
  rcases hAi : A'[i] with w | r'
  · rw [hAi] at hval'
    change w ∈ G'.V at hval'
    refine ⟨.inl w, hSub.1 hval', Iff.rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro hi0
      have hhead : A'.head hChain.ne_nil = A'[i] := by
        rw [List.head_eq_getElem_zero]
        congr 1
        exact hi0.symm
      have hm := hChain.head_matches
      rw [hhead, hAi] at hm
      have hper' := (hChain.peripheral_iff i).mpr (Or.inl hi0)
      rw [hAi] at hper'
      exact ⟨hm, hSub.1 hper'.1, hper'.2⟩
    · intro h0 w' hw'
      have hadj' := List.isChain_iff_getElem.mp hChain.isChain (i.1 - 1) (by omega)
      have hidx : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel h0
      change ChainTerm.AreIncident G' (A'[i.1 - 1]'(by omega)) (A'[i.1 - 1 + 1]'(by omega)) at hadj'
      simp only [hidx] at hadj'
      have hAi' : A'[i.1] = .inl w := hAi
      rw [hw', hAi'] at hadj'
      exact False.elim hadj'
  · rw [hAi] at hval'
    change r' ∈ G'.R at hval'
    by_cases hi0 : i.1 = 0
    · have hhead : A'.head hChain.ne_nil = A'[i] := by
        rw [List.head_eq_getElem_zero]
        congr 1
        exact hi0.symm
      have hmx : x ∈ r' := by
        have hm := hChain.head_matches
        rw [hhead, hAi] at hm
        exact hm
      have hU_sub_bd : U ⊆ bd S \ G.U := by
        have h1 := isDualPointSet_subset_diff hU
        intro u hu
        exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
      have hx_not_U : x ∉ G.U := by
        rcases hx with hxU' | hxV'
        · exact (hU_sub_bd (hU'_sub hxU')).2
        · exact fun _ => region_subset hval' hmx (G'.V_subset_U hxV'.1)
      have hx_bd : x ∈ bd S := by
        rcases hx with hxU' | hxV'
        · exact (hU_sub_bd (hU'_sub hxU')).1
        · exact hxV'.2
      obtain ⟨r, hr, hr_sub, _, hxr_in⟩ :=
        exists_subregion_closure_of_mem_closure hS hProper hSub hval'
          (subset_closure hmx) (fun _ => hx_not_U)
      have hxr : x ∈ r := hxr_in hmx
      have hper_r : ChainTerm.IsPeripheral G (.inr r) :=
        (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr).mpr ⟨x, hxr, hx_bd⟩
      refine ⟨.inr r, hr, Iff.rfl, ?_, ?_, fun _ => ⟨hxr, hper_r⟩, fun h0 => by omega⟩
      · intro w; constructor <;> intro h <;> cases h
      · intro r'' hr''
        cases hr''
        exact ⟨r, hr, rfl, hr_sub⟩
    · have h0 : 0 < i.1 := Nat.pos_of_ne_zero hi0
      have hadj' := List.isChain_iff_getElem.mp hChain.isChain (i.1 - 1) (by omega)
      have hidx : i.1 - 1 + 1 = i.1 := Nat.sub_add_cancel h0
      change ChainTerm.AreIncident G' (A'[i.1 - 1]'(by omega)) (A'[i.1 - 1 + 1]'(by omega)) at hadj'
      simp only [hidx] at hadj'
      have hAi' : A'[i.1] = .inr r' := hAi
      rw [hAi'] at hadj'
      rcases hprev : A'[i.1 - 1]'(by omega) with w₀ | r₀
      · rw [hprev] at hadj'
        rcases hadj' with ⟨hw₀_V', _, hw₀_cl⟩
        have hw₀_not_r' : w₀ ∉ r' := fun h => region_subset hval' h (G'.V_subset_U hw₀_V')
        obtain ⟨r, hr, hr_sub, hw₀_clr, _⟩ :=
          exists_subregion_closure_of_mem_closure hS hProper hSub hval'
            hw₀_cl (fun h => absurd h hw₀_not_r')
        refine ⟨.inr r, hr, Iff.rfl, ?_, ?_, fun h => absurd h hi0, ?_⟩
        · intro w; constructor <;> intro h <;> cases h
        · intro r'' hr''
          cases hr''
          exact ⟨r, hr, rfl, hr_sub⟩
        · intro _ w hw
          rw [hprev] at hw
          cases hw
          exact ⟨hSub.1 hw₀_V', hr, hw₀_clr⟩
      · rw [hprev] at hadj'
        exact False.elim hadj'

/-- Raw right-anchored lift of `A'[i]` to a chain term of `G`. -/
private lemma exists_right_raw_term [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (v : S)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hVG_ne : (G.V ∩ bd S).Nonempty)
    {x y : S} (hy : y ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (i : Fin A'.length) :
    ∃ t : ChainTerm S,
      t.IsValid G ∧
      (t.IsVertex ↔ (A'[i]).IsVertex) ∧
      (∀ w, A'[i] = .inl w ↔ t = .inl w) ∧
      (∀ r', A'[i] = .inr r' → ∃ r ∈ G.R, t = .inr r ∧ r ⊆ r') ∧
      (i.1 + 1 = A'.length → t.MatchesEnd y ∧ t.IsPeripheral G) ∧
      (∀ (h1 : i.1 + 1 < A'.length) (w : S),
        A'[i.1 + 1]'h1 = .inl w → ChainTerm.AreIncident G t (.inl w)) := by
  let G' := induceDrawing G (G.V \ {v})
  have hSub : G'.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hval' : (A'[i]).IsValid G' := hChain.valid A'[i] (List.getElem_mem _)
  rcases hAi : A'[i] with w | r'
  · rw [hAi] at hval'
    change w ∈ G'.V at hval'
    refine ⟨.inl w, hSub.1 hval', Iff.rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro hilast
      have hlast : A'.getLast hChain.ne_nil = A'[i] := by
        rw [List.getLast_eq_getElem]
        congr 1
        omega
      have hm := hChain.last_matches
      rw [hlast, hAi] at hm
      have hper' := (hChain.peripheral_iff i).mpr (Or.inr hilast)
      rw [hAi] at hper'
      exact ⟨hm, hSub.1 hper'.1, hper'.2⟩
    · intro h1 w' hw'
      have hadj' := List.isChain_iff_getElem.mp hChain.isChain i.1 h1
      change ChainTerm.AreIncident G' (A'[i]) (A'[i.1 + 1]'h1) at hadj'
      rw [hAi, hw'] at hadj'
      exact False.elim hadj'
  · rw [hAi] at hval'
    change r' ∈ G'.R at hval'
    by_cases hilast : i.1 + 1 = A'.length
    · have hlast : A'.getLast hChain.ne_nil = A'[i] := by
        rw [List.getLast_eq_getElem]
        congr 1
        omega
      have hmy : y ∈ r' := by
        have hm := hChain.last_matches
        rw [hlast, hAi] at hm
        exact hm
      have hU_sub_bd : U ⊆ bd S \ G.U := by
        have h1 := isDualPointSet_subset_diff hU
        intro u hu
        exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
      have hy_not_U : y ∉ G.U := by
        rcases hy with hyU' | hyV'
        · exact (hU_sub_bd (hU'_sub hyU')).2
        · exact fun _ => region_subset hval' hmy (G'.V_subset_U hyV'.1)
      have hy_bd : y ∈ bd S := by
        rcases hy with hyU' | hyV'
        · exact (hU_sub_bd (hU'_sub hyU')).1
        · exact hyV'.2
      obtain ⟨r, hr, hr_sub, _, hyr_in⟩ :=
        exists_subregion_closure_of_mem_closure hS hProper hSub hval'
          (subset_closure hmy) (fun _ => hy_not_U)
      have hyr : y ∈ r := hyr_in hmy
      have hper_r : ChainTerm.IsPeripheral G (.inr r) :=
        (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr).mpr ⟨y, hyr, hy_bd⟩
      refine ⟨.inr r, hr, Iff.rfl, ?_, ?_, fun _ => ⟨hyr, hper_r⟩, fun h1 => by omega⟩
      · intro w; constructor <;> intro h <;> cases h
      · intro r'' hr''
        cases hr''
        exact ⟨r, hr, rfl, hr_sub⟩
    · have h1 : i.1 + 1 < A'.length := by omega
      have hadj' := List.isChain_iff_getElem.mp hChain.isChain i.1 h1
      change ChainTerm.AreIncident G' (A'[i]) (A'[i.1 + 1]'h1) at hadj'
      rw [hAi] at hadj'
      rcases hnext : A'[i.1 + 1]'h1 with w₀ | r₀
      · rw [hnext] at hadj'
        rcases hadj' with ⟨hw₀_V', _, hw₀_cl⟩
        have hw₀_not_r' : w₀ ∉ r' := fun h => region_subset hval' h (G'.V_subset_U hw₀_V')
        obtain ⟨r, hr, hr_sub, hw₀_clr, _⟩ :=
          exists_subregion_closure_of_mem_closure hS hProper hSub hval'
            hw₀_cl (fun h => absurd h hw₀_not_r')
        refine ⟨.inr r, hr, Iff.rfl, ?_, ?_, fun h => absurd h hilast, ?_⟩
        · intro w; constructor <;> intro h <;> cases h
        · intro r'' hr''
          cases hr''
          exact ⟨r, hr, rfl, hr_sub⟩
        · intro _ w hw
          rw [hnext] at hw
          cases hw
          exact ⟨hSub.1 hw₀_V', hr, hw₀_clr⟩
      · rw [hnext] at hadj'
        exact False.elim hadj'

/-- Any lift `t` of an internal term `A'[i]` (`0 < i` and `i + 1 < A'.length`) is non-peripheral
in `G`. -/
private lemma not_isPeripheral_of_sub_internal [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) (v : S) (hVG_ne : (G.V ∩ bd S).Nonempty)
    (hVG'_ne : ((induceDrawing G (G.V \ {v})).V ∩ bd S).Nonempty)
    {x y : S} {A' : List (ChainTerm S)}
    (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (i : Fin A'.length) (h0 : 0 < i.1) (h1 : i.1 + 1 < A'.length)
    {t : ChainTerm S}
    (hinl : ∀ w, A'[i] = .inl w ↔ t = .inl w)
    (hinr : ∀ r', A'[i] = .inr r' → ∃ r ∈ G.R, t = .inr r ∧ r ⊆ r') :
    ¬ t.IsPeripheral G := by
  let G' := induceDrawing G (G.V \ {v})
  have hProper' : G'.IsProper := induceDrawing_isProper G hProper sdiff_subset
  have hnot_per' : ¬ (A'[i]).IsPeripheral G' := by
    rw [hChain.peripheral_iff i]
    omega
  have hval' : (A'[i]).IsValid G' := hChain.valid A'[i] (List.getElem_mem _)
  rcases hAi : A'[i] with w | r'
  · have ht : t = .inl w := (hinl w).mp hAi
    rw [ht]
    rw [hAi] at hnot_per' hval'
    intro hper
    exact hnot_per' ⟨hval', hper.2⟩
  · obtain ⟨r, hr, rfl, hr_sub⟩ := hinr r' hAi
    rw [hAi] at hnot_per' hval'
    change r' ∈ G'.R at hval'
    intro hper
    obtain ⟨z, hzr, hz_bd⟩ :=
      (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr).mp hper
    exact hnot_per' ((isPeripheral_inr_iff_inter_bd_nonempty hS hProper' hVG'_ne hval').mpr
      ⟨z, hr_sub hzr, hz_bd⟩)

/-- If two lifts `t₁, t₂` of `A'[i]` differ, then `A'[i]` is not a vertex and both `t₁` and `t₂`
are incident to `.inl v` in `G`. -/
private lemma incident_v_of_sub_ne [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper) {v : S} (hv_V : v ∈ G.V)
    {x y : S} {A' : List (ChainTerm S)}
    (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (i : Fin A'.length) {t₁ t₂ : ChainTerm S}
    (hinl₁ : ∀ w, A'[i] = .inl w ↔ t₁ = .inl w)
    (hinr₁ : ∀ r', A'[i] = .inr r' → ∃ r ∈ G.R, t₁ = .inr r ∧ r ⊆ r')
    (hinl₂ : ∀ w, A'[i] = .inl w ↔ t₂ = .inl w)
    (hinr₂ : ∀ r', A'[i] = .inr r' → ∃ r ∈ G.R, t₂ = .inr r ∧ r ⊆ r')
    (hne : t₁ ≠ t₂) :
    ¬ (A'[i]).IsVertex ∧ ChainTerm.AreIncident G t₁ (.inl v) ∧
      ChainTerm.AreIncident G (.inl v) t₂ := by
  have hval' : (A'[i]).IsValid (induceDrawing G (G.V \ {v})) :=
    hChain.valid A'[i] (List.getElem_mem _)
  rcases hAi : A'[i] with w | r'
  · exfalso
    exact hne (((hinl₁ w).mp hAi).trans ((hinl₂ w).mp hAi).symm)
  · rw [hAi] at hval'
    obtain ⟨r₁, hr₁, rfl, hr₁_sub⟩ := hinr₁ r' hAi
    obtain ⟨r₂, hr₂, rfl, hr₂_sub⟩ := hinr₂ r' hAi
    have hr_ne : r₁ ≠ r₂ := fun h => hne (congrArg Sum.inr h)
    rcases subregion_eq_or_mem_closure_of_delete_vertex hS hProper v hval'
        hr₁ hr₂ hr₁_sub hr₂_sub with heq | ⟨hv₁, hv₂⟩
    · exact absurd heq hr_ne
    · exact ⟨not_false, ⟨hv_V, hr₁, hv₁⟩, ⟨hv_V, hr₂, hv₂⟩⟩

/-- Left endpoint adjustment at `i = 0` when `2 ≤ A'.length`. -/
private lemma exists_left_endpoint_adjustment [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x y : S} (hxG : x ∈ U ∪ (G.V ∩ bd S)) (hyG : y ∈ U ∪ (G.V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (hlen2 : 2 ≤ A'.length)
    {t_L₀ t_R₀ : ChainTerm S}
    (hinl_L : ∀ w, A'[0]'(by omega) = .inl w ↔ t_L₀ = .inl w)
    (hinr_L : ∀ r', A'[0]'(by omega) = .inr r' → ∃ r ∈ G.R, t_L₀ = .inr r ∧ r ⊆ r')
    (h0_L : t_L₀.MatchesEnd x ∧ t_L₀.IsPeripheral G)
    (hinl_R : ∀ w, A'[0]'(by omega) = .inl w ↔ t_R₀ = .inl w)
    (hinr_R : ∀ r', A'[0]'(by omega) = .inr r' → ∃ r ∈ G.R, t_R₀ = .inr r ∧ r ⊆ r') :
    ∃ (x_eff : S) (t_L₀' : ChainTerm S),
      x_eff ∈ U ∪ (G.V ∩ bd S) ∧
      divisionCount (bd S) (Δ \ {{v}}) x y ≤ divisionCount (bd S) (Δ \ {{v}}) x_eff y ∧
      (t_L₀' = t_L₀ ∨ t_L₀' = t_R₀) ∧
      t_L₀'.MatchesEnd x_eff ∧ t_L₀'.IsPeripheral G ∧
      (t_L₀' ≠ t_R₀ → ¬ t_R₀.IsPeripheral G) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v, hΔ_sub ⟨{v}, hv, rfl⟩⟩
  by_cases hcase : t_R₀.IsPeripheral G ∧ t_L₀ ≠ t_R₀
  · rcases hcase with ⟨hper_R, hne⟩
    have hval' : (A'[0]'(by omega)).IsValid (induceDrawing G (G.V \ {v})) :=
      hChain.valid (A'[0]'(by omega)) (List.getElem_mem _)
    rcases hA0 : A'[0]'(by omega) with w | r'
    · exfalso
      exact hne (((hinl_L w).mp hA0).trans ((hinl_R w).mp hA0).symm)
    · rw [hA0] at hval'
      obtain ⟨r₁, hr₁, ht_L₀, hr₁_sub⟩ := hinr_L r' hA0
      obtain ⟨r₂, hr₂, ht_R₀, hr₂_sub⟩ := hinr_R r' hA0
      have hxr₁ : x ∈ r₁ := by
        have hm := h0_L.1
        rw [ht_L₀] at hm
        exact hm
      have hper_r₂ : ChainTerm.IsPeripheral G (.inr r₂) := ht_R₀ ▸ hper_R
      have hr₂_bd : (r₂ ∩ bd S).Nonempty :=
        (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr₂).mp hper_r₂
      obtain ⟨x₀, hx₀U, hx₀r₂⟩ :=
        exists_mem_U_of_region_inter_bd_nonempty hS hProper hVG_ne hU hr₂ hr₂_bd
      have hx₀G : x₀ ∈ U ∪ (G.V ∩ bd S) := Or.inl hx₀U
      have hdiv0 := divisionCount_sdiff_eq_zero_of_subregions hS hProper hΔ hΔ_sub hv hU hRed
        hval' hr₁ hr₂ hr₁_sub hr₂_sub hxG hx₀G hxr₁ hx₀r₂
      have hU_sub_bd : U ⊆ bd S \ G.U := by
        have h1 := isDualPointSet_subset_diff hU
        intro u hu
        exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
      have hx_bd : x ∈ bd S := hxG.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
      have hx₀_bd : x₀ ∈ bd S := (hU_sub_bd hx₀U).1
      have hy_bd : y ∈ bd S := hyG.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
      have hx₀_not : x₀ ∉ divisionUnion (Δ \ {{v}}) := fun h =>
        (hU_sub_bd hx₀U).2 (G.V_subset_U (hΔ_sub ((sUnion_mono sdiff_subset) h)).1)
      have hΔ'_div : IsDivision (Δ \ {{v}}) :=
        ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
      have hΔ'_sub_bd : divisionUnion (Δ \ {{v}}) ⊆ bd S :=
        (sUnion_mono sdiff_subset).trans (hΔ_sub.trans inter_subset_right)
      have hle := divisionCount_le_of_left_eq_zero hS.isOArc_bd hΔ'_div hΔ'_sub_bd
        hx_bd hx₀_bd hy_bd hx₀_not hdiv0
      have hm₀ : t_R₀.MatchesEnd x₀ := by
        rw [ht_R₀]
        exact hx₀r₂
      exact ⟨x₀, t_R₀, hx₀G, hle, Or.inr rfl, hm₀, hper_R, fun h => absurd rfl h⟩
  · refine ⟨x, t_L₀, hxG, le_rfl, Or.inl rfl, h0_L.1, h0_L.2, ?_⟩
    intro hne hper_R
    exact hcase ⟨hper_R, hne⟩

/-- Right endpoint adjustment at `i = A'.length - 1` when `2 ≤ A'.length`. -/
private lemma exists_right_endpoint_adjustment [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x_eff y : S} (hx_effG : x_eff ∈ U ∪ (G.V ∩ bd S)) (hyG : y ∈ U ∪ (G.V ∩ bd S))
    {x : S} {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (hlen2 : 2 ≤ A'.length)
    {t_Ll t_Rl : ChainTerm S}
    (hinl_L : ∀ w, A'[A'.length - 1]'(by omega) = .inl w ↔ t_Ll = .inl w)
    (hinr_L : ∀ r', A'[A'.length - 1]'(by omega) = .inr r' → ∃ r ∈ G.R, t_Ll = .inr r ∧ r ⊆ r')
    (hinl_R : ∀ w, A'[A'.length - 1]'(by omega) = .inl w ↔ t_Rl = .inl w)
    (hinr_R : ∀ r', A'[A'.length - 1]'(by omega) = .inr r' → ∃ r ∈ G.R, t_Rl = .inr r ∧ r ⊆ r')
    (hl_R : t_Rl.MatchesEnd y ∧ t_Rl.IsPeripheral G) :
    ∃ (y_eff : S) (t_Rl' : ChainTerm S),
      y_eff ∈ U ∪ (G.V ∩ bd S) ∧
      divisionCount (bd S) (Δ \ {{v}}) x_eff y ≤ divisionCount (bd S) (Δ \ {{v}}) x_eff y_eff ∧
      (t_Rl' = t_Rl ∨ t_Rl' = t_Ll) ∧
      t_Rl'.MatchesEnd y_eff ∧ t_Rl'.IsPeripheral G ∧
      (t_Ll ≠ t_Rl' → ¬ t_Ll.IsPeripheral G) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v, hΔ_sub ⟨{v}, hv, rfl⟩⟩
  by_cases hcase : t_Ll.IsPeripheral G ∧ t_Ll ≠ t_Rl
  · rcases hcase with ⟨hper_L, hne⟩
    have hval' : (A'[A'.length - 1]'(by omega)).IsValid (induceDrawing G (G.V \ {v})) :=
      hChain.valid (A'[A'.length - 1]'(by omega)) (List.getElem_mem _)
    rcases hAl : A'[A'.length - 1]'(by omega) with w | r'
    · exfalso
      exact hne (((hinl_L w).mp hAl).trans ((hinl_R w).mp hAl).symm)
    · rw [hAl] at hval'
      obtain ⟨r₁, hr₁, ht_Ll, hr₁_sub⟩ := hinr_L r' hAl
      obtain ⟨r₂, hr₂, ht_Rl, hr₂_sub⟩ := hinr_R r' hAl
      have hyr₂ : y ∈ r₂ := by
        have hm := hl_R.1
        rw [ht_Rl] at hm
        exact hm
      have hper_r₁ : ChainTerm.IsPeripheral G (.inr r₁) := ht_Ll ▸ hper_L
      have hr₁_bd : (r₁ ∩ bd S).Nonempty :=
        (isPeripheral_inr_iff_inter_bd_nonempty hS hProper hVG_ne hr₁).mp hper_r₁
      obtain ⟨y₀, hy₀U, hy₀r₁⟩ :=
        exists_mem_U_of_region_inter_bd_nonempty hS hProper hVG_ne hU hr₁ hr₁_bd
      have hy₀G : y₀ ∈ U ∪ (G.V ∩ bd S) := Or.inl hy₀U
      have hdiv0 := divisionCount_sdiff_eq_zero_of_subregions hS hProper hΔ hΔ_sub hv hU hRed
        hval' hr₁ hr₂ hr₁_sub hr₂_sub hy₀G hyG hy₀r₁ hyr₂
      have hU_sub_bd : U ⊆ bd S \ G.U := by
        have h1 := isDualPointSet_subset_diff hU
        intro u hu
        exact ⟨(h1 hu).1, fun huU => (h1 hu).2 ⟨hProper ⟨(h1 hu).1, huU⟩, (h1 hu).1⟩⟩
      have hx_eff_bd : x_eff ∈ bd S := hx_effG.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
      have hy₀_bd : y₀ ∈ bd S := (hU_sub_bd hy₀U).1
      have hy_bd : y ∈ bd S := hyG.elim (fun h => (hU_sub_bd h).1) (fun h => h.2)
      have hy₀_not : y₀ ∉ divisionUnion (Δ \ {{v}}) := fun h =>
        (hU_sub_bd hy₀U).2 (G.V_subset_U (hΔ_sub ((sUnion_mono sdiff_subset) h)).1)
      have hΔ'_div : IsDivision (Δ \ {{v}}) :=
        ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
      have hΔ'_sub_bd : divisionUnion (Δ \ {{v}}) ⊆ bd S :=
        (sUnion_mono sdiff_subset).trans (hΔ_sub.trans inter_subset_right)
      have hle := divisionCount_le_of_right_eq_zero hS.isOArc_bd hΔ'_div hΔ'_sub_bd
        hx_eff_bd hy₀_bd hy_bd hy₀_not hdiv0
      have hm₀ : t_Ll.MatchesEnd y₀ := by
        rw [ht_Ll]
        exact hy₀r₁
      exact ⟨y₀, t_Ll, hy₀G, hle, Or.inr rfl, hm₀, hper_L, fun h => absurd rfl h⟩
  · refine ⟨y, t_Rl, hyG, le_rfl, Or.inl rfl, hl_R.1, hl_R.2, ?_⟩
    intro hne hper_L
    exact hcase ⟨hper_L, hne⟩

/-- Combined per-index chain lift data for `2 ≤ A'.length`. -/
private lemma exists_chain_lift_data [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hVG'_ne : ((induceDrawing G (G.V \ {v})).V ∩ bd S).Nonempty)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x y : S} (hx : x ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    (hy : y ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (hlen2 : 2 ≤ A'.length) :
    ∃ (x_eff y_eff : S) (t_L t_R : Fin A'.length → ChainTerm S),
      x_eff ∈ U ∪ (G.V ∩ bd S) ∧
      y_eff ∈ U ∪ (G.V ∩ bd S) ∧
      divisionCount (bd S) (Δ \ {{v}}) x y ≤ divisionCount (bd S) (Δ \ {{v}}) x_eff y_eff ∧
      (∀ i : Fin A'.length, (t_L i).IsValid G ∧ (t_R i).IsValid G) ∧
      (∀ i : Fin A'.length,
        ((t_L i).IsVertex ↔ (A'[i]).IsVertex) ∧ ((t_R i).IsVertex ↔ (A'[i]).IsVertex)) ∧
      (t_L ⟨0, by omega⟩).MatchesEnd x_eff ∧ (t_L ⟨0, by omega⟩).IsPeripheral G ∧
      (t_R ⟨A'.length - 1, by omega⟩).MatchesEnd y_eff ∧
      (t_R ⟨A'.length - 1, by omega⟩).IsPeripheral G ∧
      (∀ (i : ℕ) (hi : i + 1 < A'.length),
        ChainTerm.AreIncident G (t_R ⟨i, Nat.lt_of_succ_lt hi⟩) (t_L ⟨i + 1, hi⟩)) ∧
      (∀ i : Fin A'.length, 0 < i.1 → (i.1 + 1 < A'.length ∨ t_L i ≠ t_R i) →
        ¬ (t_L i).IsPeripheral G) ∧
      (∀ i : Fin A'.length, i.1 + 1 < A'.length → (0 < i.1 ∨ t_L i ≠ t_R i) →
        ¬ (t_R i).IsPeripheral G) ∧
      (∀ i : Fin A'.length, t_L i ≠ t_R i →
        ¬ (A'[i]).IsVertex ∧ ChainTerm.AreIncident G (t_L i) (.inl v) ∧
          ChainTerm.AreIncident G (.inl v) (t_R i)) := by
  let G' := induceDrawing G (G.V \ {v})
  have hSub : G'.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hv_bd : v ∈ G.V ∩ bd S := hΔ_sub ⟨{v}, hv, rfl⟩
  have hVG_ne : (G.V ∩ bd S).Nonempty := ⟨v, hv_bd⟩
  have hxG : x ∈ U ∪ (G.V ∩ bd S) :=
    hx.imp (fun h => hU'_sub h) (fun h => ⟨hSub.1 h.1, h.2⟩)
  have hyG : y ∈ U ∪ (G.V ∩ bd S) :=
    hy.imp (fun h => hU'_sub h) (fun h => ⟨hSub.1 h.1, h.2⟩)
  choose t_L_raw hL_val hL_isV hL_inl hL_inr hL_0 hL_inc using
    exists_left_raw_term hS hProper v hU hU'_sub hVG_ne hx hChain
  choose t_R_raw hR_val hR_isV hR_inl hR_inr hR_last hR_inc using
    exists_right_raw_term hS hProper v hU hU'_sub hVG_ne hy hChain
  let i₀ : Fin A'.length := ⟨0, by omega⟩
  let il : Fin A'.length := ⟨A'.length - 1, by omega⟩
  have hil_add : il.1 + 1 = A'.length := Nat.sub_add_cancel (by omega)
  obtain ⟨x_eff, t_L₀', hx_effG, hdiv_x, hL₀_eq, hm_x, hper_x, hnot_per_R₀⟩ :=
    exists_left_endpoint_adjustment hS hProper hΔ hΔ_sub hv hU hRed hxG hyG hChain hlen2
      (hL_inl i₀) (hL_inr i₀) (hL_0 i₀ rfl) (hR_inl i₀) (hR_inr i₀)
  obtain ⟨y_eff, t_Rl', hy_effG, hdiv_y, hRl_eq, hm_y, hper_y, hnot_per_Ll⟩ :=
    exists_right_endpoint_adjustment hS hProper hΔ hΔ_sub hv hU hRed hx_effG hyG hChain hlen2
      (hL_inl il) (hL_inr il) (hR_inl il) (hR_inr il) (hR_last il hil_add)
  let t_L : Fin A'.length → ChainTerm S := fun i => if i = i₀ then t_L₀' else t_L_raw i
  let t_R : Fin A'.length → ChainTerm S := fun i => if i = il then t_Rl' else t_R_raw i
  have ht_L_cases : ∀ i, t_L i = t_L_raw i ∨ t_L i = t_R_raw i := by
    intro i
    dsimp [t_L]
    split_ifs with h
    · subst h; exact hL₀_eq
    · exact Or.inl rfl
  have ht_R_cases : ∀ i, t_R i = t_R_raw i ∨ t_R i = t_L_raw i := by
    intro i
    dsimp [t_R]
    split_ifs with h
    · subst h; exact hRl_eq
    · exact Or.inl rfl
  have ht_L_inl : ∀ i w, A'[i] = .inl w ↔ t_L i = .inl w := by
    intro i w
    rcases ht_L_cases i with h | h <;> rw [h]
    · exact hL_inl i w
    · exact hR_inl i w
  have ht_R_inl : ∀ i w, A'[i] = .inl w ↔ t_R i = .inl w := by
    intro i w
    rcases ht_R_cases i with h | h <;> rw [h]
    · exact hR_inl i w
    · exact hL_inl i w
  have ht_L_inr : ∀ i r', A'[i] = .inr r' → ∃ r ∈ G.R, t_L i = .inr r ∧ r ⊆ r' := by
    intro i r' hr'
    rcases ht_L_cases i with h | h <;> rw [h]
    · exact hL_inr i r' hr'
    · exact hR_inr i r' hr'
  have ht_R_inr : ∀ i r', A'[i] = .inr r' → ∃ r ∈ G.R, t_R i = .inr r ∧ r ⊆ r' := by
    intro i r' hr'
    rcases ht_R_cases i with h | h <;> rw [h]
    · exact hR_inr i r' hr'
    · exact hL_inr i r' hr'
  refine ⟨x_eff, y_eff, t_L, t_R, hx_effG, hy_effG, hdiv_x.trans hdiv_y, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · rcases ht_L_cases i with h | h <;> rw [h]
      · exact hL_val i
      · exact hR_val i
    · rcases ht_R_cases i with h | h <;> rw [h]
      · exact hR_val i
      · exact hL_val i
  · intro i
    constructor
    · rcases ht_L_cases i with h | h <;> rw [h]
      · exact hL_isV i
      · exact hR_isV i
    · rcases ht_R_cases i with h | h <;> rw [h]
      · exact hR_isV i
      · exact hL_isV i
  · simp [t_L, i₀, hm_x]
  · simp [t_L, i₀, hper_x]
  · simp [t_R, il, hm_y]
  · simp [t_R, il, hper_y]
  · intro i hi
    have hne_il : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin A'.length) ≠ il := by
      intro h
      have := congrArg Fin.val h
      dsimp [il] at this
      omega
    have hne_i₀ : (⟨i + 1, hi⟩ : Fin A'.length) ≠ i₀ := by
      intro h
      have := congrArg Fin.val h
      dsimp [i₀] at this
      omega
    have hR_eq : t_R ⟨i, Nat.lt_of_succ_lt hi⟩ = t_R_raw ⟨i, Nat.lt_of_succ_lt hi⟩ := by
      simp [t_R, hne_il]
    have hL_eq : t_L ⟨i + 1, hi⟩ = t_L_raw ⟨i + 1, hi⟩ := by
      simp [t_L, hne_i₀]
    rw [hR_eq, hL_eq]
    have hadj' := List.isChain_iff_getElem.mp hChain.isChain i hi
    rcases hAi : A'[i]'(Nat.lt_of_succ_lt hi) with w | r'
    · have hR_w : t_R_raw ⟨i, Nat.lt_of_succ_lt hi⟩ = .inl w :=
        (hR_inl ⟨i, Nat.lt_of_succ_lt hi⟩ w).mp hAi
      rw [hR_w]
      exact hL_inc ⟨i + 1, hi⟩ (Nat.zero_lt_succ i) w hAi
    · rcases hAi1 : A'[i + 1]'hi with w₁ | r₁'
      · have hL_w₁ : t_L_raw ⟨i + 1, hi⟩ = .inl w₁ :=
          (hL_inl ⟨i + 1, hi⟩ w₁).mp hAi1
        rw [hL_w₁]
        exact hR_inc ⟨i, Nat.lt_of_succ_lt hi⟩ hi w₁ hAi1
      · rw [hAi, hAi1] at hadj'
        exact False.elim hadj'
  · intro i h0 hcond
    have hne_i₀ : i ≠ i₀ := by
      intro h
      have := congrArg Fin.val h
      dsimp [i₀] at this
      omega
    have hL_eq : t_L i = t_L_raw i := by simp [t_L, hne_i₀]
    rcases hcond with h1 | hne
    · exact not_isPeripheral_of_sub_internal hS hProper v hVG_ne hVG'_ne hChain i h0 h1
        (ht_L_inl i) (ht_L_inr i)
    · by_cases h1 : i.1 + 1 < A'.length
      · exact not_isPeripheral_of_sub_internal hS hProper v hVG_ne hVG'_ne hChain i h0 h1
          (ht_L_inl i) (ht_L_inr i)
      · have hil_eq : i = il := Fin.ext (by dsimp [il]; omega)
        subst hil_eq
        rw [hL_eq] at hne ⊢
        have hR_il : t_R il = t_Rl' := by simp [t_R]
        rw [hR_il] at hne
        exact hnot_per_Ll hne
  · intro i h1 hcond
    have hne_il : i ≠ il := by
      intro h
      have := congrArg Fin.val h
      dsimp [il] at this
      omega
    have hR_eq : t_R i = t_R_raw i := by simp [t_R, hne_il]
    rcases hcond with h0 | hne
    · exact not_isPeripheral_of_sub_internal hS hProper v hVG_ne hVG'_ne hChain i h0 h1
        (ht_R_inl i) (ht_R_inr i)
    · by_cases h0 : 0 < i.1
      · exact not_isPeripheral_of_sub_internal hS hProper v hVG_ne hVG'_ne hChain i h0 h1
          (ht_R_inl i) (ht_R_inr i)
      · have hi₀_eq : i = i₀ := Fin.ext (by dsimp [i₀]; omega)
        subst hi₀_eq
        rw [hR_eq] at hne ⊢
        have hL_i₀ : t_L i₀ = t_L₀' := by simp [t_L]
        rw [hL_i₀] at hne
        exact hnot_per_R₀ hne
  · intro i hne
    exact incident_v_of_sub_ne hS hProper hv_bd.1 hChain i
      (ht_L_inl i) (ht_L_inr i) (ht_R_inl i) (ht_R_inr i) hne

omit [TopologicalSpace S] in
private theorem first_last_chain_mismatch {n : ℕ} {t_L t_R : Fin n → ChainTerm S}
    (h_ex_ne : ∃ i, t_L i ≠ t_R i) :
    ∃ j₁ j₂ : Fin n, t_L j₁ ≠ t_R j₁ ∧ t_L j₂ ≠ t_R j₂ ∧ j₁.1 ≤ j₂.1 ∧
      (∀ i : Fin n, i.1 < j₁.1 → t_L i = t_R i) ∧
      (∀ i : Fin n, j₂.1 < i.1 → t_L i = t_R i) := by
  classical
  let S_mis : Finset (Fin n) := Finset.univ.filter (fun i => t_L i ≠ t_R i)
  have hS_ne : S_mis.Nonempty := by
    obtain ⟨i, hi⟩ := h_ex_ne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j₁ : Fin n := S_mis.min' hS_ne
  let j₂ : Fin n := S_mis.max' hS_ne
  have hj₁_ne : t_L j₁ ≠ t_R j₁ := (Finset.mem_filter.mp (Finset.min'_mem S_mis hS_ne)).2
  have hj₂_ne : t_L j₂ ≠ t_R j₂ := (Finset.mem_filter.mp (Finset.max'_mem S_mis hS_ne)).2
  have hj_le : j₁.1 ≤ j₂.1 := Finset.min'_le S_mis j₂ (Finset.max'_mem S_mis hS_ne)
  have hj₁_min : ∀ i : Fin n, i.1 < j₁.1 → t_L i = t_R i := by
    intro i hi
    by_contra hne
    have hmem : i ∈ S_mis := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    have hle : j₁.1 ≤ i.1 := Finset.min'_le S_mis i hmem
    omega
  have hj₂_max : ∀ i : Fin n, j₂.1 < i.1 → t_L i = t_R i := by
    intro i hi
    by_contra hne
    have hmem : i ∈ S_mis := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    have hle : i.1 ≤ j₂.1 := Finset.le_max' S_mis i hmem
    omega
  exact ⟨j₁, j₂, hj₁_ne, hj₂_ne, hj_le, hj₁_min, hj₂_max⟩

private theorem divisionCount_sdiff_singleton_le_add
    (hS : IsClosedDiscSpace S) {G : Drawing S} {Δ : Set (Set S)} {U : Set S}
    (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) {v x y : S} (hv : {v} ∈ Δ)
    (hv_bd : v ∈ bd S) (hx : x ∈ U ∪ (G.V ∩ bd S)) (hy : y ∈ U ∪ (G.V ∩ bd S)) :
    divisionCount (bd S) (Δ \ {{v}}) x y ≤
      divisionCount (bd S) (Δ \ {{v}}) x v + divisionCount (bd S) (Δ \ {{v}}) v y := by
  have hx_bd : x ∈ bd S := hx.elim (fun h => (isDualPointSet_subset_diff hU h).1) And.right
  have hy_bd : y ∈ bd S := hy.elim (fun h => (isDualPointSet_subset_diff hU h).1) And.right
  have hΔ'_div : IsDivision (Δ \ {{v}}) :=
    ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
  have hΔ'_sub_bd : divisionUnion (Δ \ {{v}}) ⊆ bd S :=
    (sUnion_mono sdiff_subset).trans (hΔ_sub.trans inter_subset_right)
  have hv_not_Δ' : v ∉ divisionUnion (Δ \ {{v}}) := by
    rintro ⟨δ, ⟨hδ, hne⟩, hvδ⟩
    exact (hΔ.2.2 hδ hv hne).ne_of_mem hvδ rfl rfl
  exact divisionCount_le_add_of_not_mem hS.isOArc_bd hΔ'_div hΔ'_sub_bd
    hx_bd hv_bd hy_bd hv_not_Δ'

/-- Case `2 ≤ A'.length` of singleton deletion: if `A'` is an `(x, y)`-chain of
`G' = induceDrawing G (G.V \ {v})` with `2 ≤ A'.length`, then
`0 ≤ chainRedundancy G' (Δ \ {{v}}) x y A'`. -/
theorem chainRedundancy_nonneg_of_length_ge_two [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hVG'_ne : ((induceDrawing G (G.V \ {v})).V ∩ bd S).Nonempty)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x y : S} (hx : x ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    (hy : y ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A')
    (hlen2 : 2 ≤ A'.length) :
    0 ≤ chainRedundancy (induceDrawing G (G.V \ {v})) (Δ \ {{v}}) x y A' := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hv_bd : v ∈ G.V ∩ bd S := hΔ_sub ⟨{v}, hv, rfl⟩
  obtain ⟨x_eff, y_eff, t_L, t_R, hx_effG, hy_effG, hdiv_xy, hval, hisV,
      hm_x, hper_x, hm_y, hper_y, hadj, hnot_per_L, hnot_per_R, hmis⟩ :=
    exists_chain_lift_data hS hProper hΔ hΔ_sub hv hU hU'_sub hVG'_ne hRed hx hy hChain hlen2
  by_cases h_all_eq : ∀ i : Fin A'.length, t_L i = t_R i
  · let L := List.ofFn t_L
    have hL_len : L.length = A'.length := List.length_ofFn
    have hChainL : IsXYChain G x_eff y_eff L := by
      refine isXYChain_of_getElem G x_eff y_eff L (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro ⟨i, hi⟩
        change ChainTerm.IsValid G (L[i]'hi)
        simp only [L, List.getElem_ofFn]
        exact (hval ⟨i, hL_len ▸ hi⟩).1
      · intro i hi
        simp only [L, List.getElem_ofFn]
        have hi' : i + 1 < A'.length := hL_len ▸ hi
        rw [h_all_eq ⟨i, Nat.lt_of_succ_lt hi'⟩]
        exact hadj i hi'
      · simp only [L, List.getElem_ofFn]; exact hm_x
      · simp only [L, List.getElem_ofFn, hL_len]
        rw [h_all_eq ⟨A'.length - 1, by omega⟩]
        exact hm_y
      · simp only [L, List.getElem_ofFn]; exact hper_x
      · simp only [L, List.getElem_ofFn, hL_len]
        rw [h_all_eq ⟨A'.length - 1, by omega⟩]
        exact hper_y
      · intro i hi h0 h1
        simp only [L, List.getElem_ofFn]
        exact hnot_per_L ⟨i, hL_len ▸ hi⟩ h0 (Or.inl (by dsimp; omega))
    have hlen_eq : chainLength L = chainLength A' := by
      refine chainLength_eq_of_isVertex_eq hL_len fun i hi => ?_
      simp only [L, List.getElem_ofFn]
      exact (hisV ⟨i, hL_len ▸ hi⟩).1
    have hredL := hRed x_eff hx_effG y_eff hy_effG L hChainL
    have hdiv_sub := divisionCount_le_of_subset (C := bd S) hΔ
      (sdiff_subset : Δ \ {{v}} ⊆ Δ) x_eff y_eff
    unfold chainRedundancy at hredL ⊢
    omega
  · have h_ex_ne : ∃ i : Fin A'.length, t_L i ≠ t_R i := by
      by_contra h
      exact h_all_eq fun i => not_not.mp fun hi => h ⟨i, hi⟩
    obtain ⟨j₁, j₂, hj₁_ne, hj₂_ne, hj_le, hj₁_min, hj₂_max⟩ :=
      first_last_chain_mismatch h_ex_ne
    have hj₁_lt : j₁.1 < A'.length := j₁.2
    have hj₂_lt : j₂.1 < A'.length := j₂.2
    let L_list := List.ofFn t_L
    let R_list := List.ofFn t_R
    let P := L_list.take (j₁.1 + 1) ++ [.inl v]
    let Q := (.inl v) :: R_list.drop j₂.1
    have hL_take_len : (L_list.take (j₁.1 + 1)).length = j₁.1 + 1 := by
      simp [L_list]
    have hP_len : P.length = j₁.1 + 2 := by
      simp [P, hL_take_len]
    have hP_get_lt : ∀ (k : ℕ) (hk : k < j₁.1 + 1),
        P[k]'(by omega) = t_L ⟨k, by omega⟩ := by
      intro k hk
      have hk' : k < (L_list.take (j₁.1 + 1)).length := by omega
      rw [List.getElem_append_left hk', List.getElem_take, List.getElem_ofFn]
    have hP_get_last : P[j₁.1 + 1]'(by omega) = .inl v := by
      have hk' : (L_list.take (j₁.1 + 1)).length ≤ j₁.1 + 1 := by omega
      rw [List.getElem_append_right hk']
      simp [hL_take_len]
    have hR_drop_len : (R_list.drop j₂.1).length = A'.length - j₂.1 := by
      simp [R_list]
    have hQ_len : Q.length = A'.length - j₂.1 + 1 := by
      simp [Q, hR_drop_len]
    have hQ_get_zero : Q[0]'(by omega) = .inl v := rfl
    have hQ_get_succ : ∀ (k : ℕ) (hk0 : 0 < k) (hk : k < Q.length),
        Q[k]'hk = t_R ⟨j₂.1 + (k - 1), by omega⟩ := by
      intro k hk0 hk
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0) with ⟨m, rfl⟩
      simp [Q, R_list]
    have hChainP : IsXYChain G x_eff v P := by
      refine isXYChain_of_getElem G x_eff v P (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro ⟨k, hk⟩
        by_cases hk_lt : k < j₁.1 + 1
        · change ChainTerm.IsValid G (P[k]'hk)
          rw [hP_get_lt k hk_lt]
          exact (hval ⟨k, by omega⟩).1
        · have hk_eq : k = j₁.1 + 1 := by omega
          subst hk_eq
          change ChainTerm.IsValid G (P[j₁.1 + 1]'hk)
          rw [hP_get_last]
          exact hv_bd.1
      · intro k hk
        by_cases hk_lt : k < j₁.1
        · rw [hP_get_lt k (by omega), hP_get_lt (k + 1) (by omega)]
          have heq := hj₁_min ⟨k, by omega⟩ hk_lt
          rw [heq]
          exact hadj k (by omega)
        · have hk_eq : k = j₁.1 := by omega
          subst hk_eq
          rw [hP_get_lt j₁.1 (by omega), hP_get_last]
          exact (hmis j₁ hj₁_ne).2.1
      · rw [hP_get_lt 0 (by omega)]; exact hm_x
      · have hlast_idx : P.length - 1 = j₁.1 + 1 := by omega
        simp only [hlast_idx, hP_get_last]
        rfl
      · rw [hP_get_lt 0 (by omega)]; exact hper_x
      · have hlast_idx : P.length - 1 = j₁.1 + 1 := by omega
        simp only [hlast_idx, hP_get_last]
        exact hv_bd
      · intro k hk hk0 hk1
        have hk_lt : k < j₁.1 + 1 := by omega
        rw [hP_get_lt k hk_lt]
        by_cases hk_eq : k = j₁.1
        · subst hk_eq
          exact hnot_per_L j₁ hk0 (Or.inr hj₁_ne)
        · exact hnot_per_L ⟨k, by omega⟩ hk0 (Or.inl (by dsimp; omega))
    have hChainQ : IsXYChain G v y_eff Q := by
      refine isXYChain_of_getElem G v y_eff Q (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro ⟨k, hk⟩
        by_cases hk0 : k = 0
        · subst hk0
          change ChainTerm.IsValid G (Q[0]'hk)
          rw [hQ_get_zero]
          exact hv_bd.1
        · change ChainTerm.IsValid G (Q[k]'hk)
          rw [hQ_get_succ k (Nat.pos_of_ne_zero hk0) hk]
          exact (hval ⟨j₂.1 + (k - 1), by omega⟩).2
      · intro k hk
        by_cases hk0 : k = 0
        · subst hk0
          rw [hQ_get_zero, hQ_get_succ 1 Nat.zero_lt_one hk]
          simpa using (hmis j₂ hj₂_ne).2.2
        · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
          rw [hQ_get_succ k hk_pos (Nat.lt_of_succ_lt hk),
            hQ_get_succ (k + 1) (Nat.zero_lt_succ k) hk]
          have hidx_next : j₂.1 + (k + 1 - 1) = j₂.1 + (k - 1) + 1 := by omega
          have hgt : j₂.1 < j₂.1 + (k - 1) + 1 := by omega
          have heq := hj₂_max ⟨j₂.1 + (k - 1) + 1, by omega⟩ hgt
          have hfin_eq : (⟨j₂.1 + (k + 1 - 1), by omega⟩ : Fin A'.length) =
              ⟨j₂.1 + (k - 1) + 1, by omega⟩ := Fin.ext hidx_next
          rw [hfin_eq, ← heq]
          exact hadj (j₂.1 + (k - 1)) (by omega)
      · rw [hQ_get_zero]; rfl
      · rw [hQ_get_succ (Q.length - 1) (by omega) (by omega)]
        have hfin_eq : (⟨j₂.1 + (Q.length - 1 - 1), by omega⟩ : Fin A'.length) =
            ⟨A'.length - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hfin_eq]
        exact hm_y
      · rw [hQ_get_zero]; exact hv_bd
      · rw [hQ_get_succ (Q.length - 1) (by omega) (by omega)]
        have hfin_eq : (⟨j₂.1 + (Q.length - 1 - 1), by omega⟩ : Fin A'.length) =
            ⟨A'.length - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hfin_eq]
        exact hper_y
      · intro k hk hk0 hk1
        rw [hQ_get_succ k hk0 hk]
        by_cases hk1_eq : k = 1
        · subst hk1_eq
          have hfin_eq : (⟨j₂.1 + (1 - 1), by omega⟩ : Fin A'.length) = j₂ :=
            Fin.ext (by dsimp)
          rw [hfin_eq]
          exact hnot_per_R j₂ (by omega) (Or.inr hj₂_ne)
        · exact hnot_per_R ⟨j₂.1 + (k - 1), by omega⟩ (by dsimp; omega) (Or.inl (by dsimp; omega))
    have hP_chainLen : chainLength P = chainLength (A'.take (j₁.1 + 1)) + 1 := by
      have h1 : chainLength P = chainLength (L_list.take (j₁.1 + 1)) + 1 := by
        rw [chainLength_append]
        rfl
      have h2 : chainLength (L_list.take (j₁.1 + 1)) = chainLength (A'.take (j₁.1 + 1)) := by
        have hlen_eq : (L_list.take (j₁.1 + 1)).length = (A'.take (j₁.1 + 1)).length := by
          simp [L_list]
        refine chainLength_eq_of_isVertex_eq hlen_eq fun k hk => ?_
        rw [List.getElem_take, List.getElem_take, List.getElem_ofFn]
        exact (hisV ⟨k, by omega⟩).1
      omega
    have hQ_chainLen : chainLength Q = 1 + chainLength (A'.drop j₂.1) := by
      have h1 : chainLength Q = 1 + chainLength (R_list.drop j₂.1) := by
        rw [chainLength_cons]
        rfl
      have h2 : chainLength (R_list.drop j₂.1) = chainLength (A'.drop j₂.1) := by
        have hlen_eq : (R_list.drop j₂.1).length = (A'.drop j₂.1).length := by
          simp [R_list]
        refine chainLength_eq_of_isVertex_eq hlen_eq fun k hk => ?_
        rw [List.getElem_drop, List.getElem_drop, List.getElem_ofFn]
        exact (hisV ⟨j₂.1 + k, by omega⟩).2
      omega
    have hsum_le : chainLength P + chainLength Q ≤ chainLength A' + 2 := by
      have htake_drop := chainLength_take_add_drop_le A' j₁.2 hj_le (hmis j₁ hj₁_ne).1
      omega
    have hredP := hRed x_eff hx_effG v (Or.inr hv_bd) P hChainP
    have hredQ := hRed v (Or.inr hv_bd) y_eff hy_effG Q hChainQ
    have htri := divisionCount_sdiff_singleton_le_add hS hΔ hΔ_sub hU hv hv_bd.2 hx_effG hy_effG
    have hsdiff_L := divisionCount_sdiff_singleton_right (bd S) hΔ hv x_eff
    have hsdiff_R := divisionCount_sdiff_singleton_left (bd S) hΔ hv y_eff
    unfold chainRedundancy at hredP hredQ ⊢
    omega

/-- Combined chain redundancy preservation under deleting a singleton `{v} ∈ Δ`:
every `(x, y)`-chain `A'` of `G' = induceDrawing G (G.V \ {v})` has
`0 ≤ chainRedundancy G' (Δ \ {{v}}) x y A'`. -/
theorem chainRedundancy_nonneg_of_delete_singleton [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U U' : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U) (hU'_sub : U' ⊆ U)
    (hU'_dual : IsDualPointSet (bd S) ((induceDrawing G (G.V \ {v})).V ∩ bd S) U')
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A)
    {x y : S} (hx : x ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    (hy : y ∈ U' ∪ ((induceDrawing G (G.V \ {v})).V ∩ bd S))
    {A' : List (ChainTerm S)} (hChain : IsXYChain (induceDrawing G (G.V \ {v})) x y A') :
    0 ≤ chainRedundancy (induceDrawing G (G.V \ {v})) (Δ \ {{v}}) x y A' := by
  have hVG'_ne : ((induceDrawing G (G.V \ {v})).V ∩ bd S).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hU'_emp : U' = ∅ := hU'_dual.1 hemp
    rw [hU'_emp, hemp, union_empty] at hx
    exact hx
  have hpos : 0 < A'.length := List.length_pos_of_ne_nil hChain.ne_nil
  by_cases hlen1 : A'.length = 1
  · exact chainRedundancy_nonneg_of_length_one hS hProper hΔ hΔ_sub hv hU hU'_sub hRed
      hx hy hChain hlen1
  · exact chainRedundancy_nonneg_of_length_ge_two hS hProper hΔ hΔ_sub hv hU hU'_sub hVG'_ne hRed
      hx hy hChain (by omega)

/-- **Case (3.3)(i) Singleton Reduction** (Graph Minors VI, page 122, Case 1):
If `{v} ∈ Δ`, then `G' = induceDrawing G (G.V \ {v})` and `Δ' = Δ \ {{v}}` satisfy:
- `G'.IsProper` and `G'.V.ncard + G'.R.ncard < G.V.ncard + G.R.ncard`
- `IsDivision Δ'` and `divisionUnion Δ' = G'.V ∩ bd S` (when `divisionUnion Δ = G.V ∩ bd S`)
- there exists a dual point set `U' ⊆ U` for `(bd S, G'.V ∩ bd S)` such that every chain of `G'`
  has non-negative redundancy with respect to `Δ'`
- `IsFeasible G'.toGraph Δ' → IsFeasible G.toGraph Δ`. -/
theorem exists_reduction_of_singleton_mem [T1Space S] (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hΔ_eq : divisionUnion Δ = G.V ∩ bd S)
    {v : S} (hv : {v} ∈ Δ)
    {U : Set S} (hU : IsDualPointSet (bd S) (G.V ∩ bd S) U)
    (hRed : ∀ a ∈ U ∪ (G.V ∩ bd S), ∀ b ∈ U ∪ (G.V ∩ bd S),
      ∀ A : List (ChainTerm S), IsXYChain G a b A → 0 ≤ chainRedundancy G Δ a b A) :
    let G' := induceDrawing G (G.V \ {v})
    let Δ' := Δ \ {{v}}
    G'.IsProper ∧ G'.IsSubdrawing G ∧
    G'.V.ncard + G'.R.ncard < G.V.ncard + G.R.ncard ∧
    IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
    (∃ U' ⊆ U, IsDualPointSet (bd S) (G'.V ∩ bd S) U' ∧
      ∀ x ∈ U' ∪ (G'.V ∩ bd S), ∀ y ∈ U' ∪ (G'.V ∩ bd S),
        ∀ A' : List (ChainTerm S), IsXYChain G' x y A' → 0 ≤ chainRedundancy G' Δ' x y A') ∧
    (IsFeasible G'.toGraph Δ' → IsFeasible G.toGraph Δ) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  let G' := induceDrawing G (G.V \ {v})
  let Δ' := Δ \ {{v}}
  change G'.IsProper ∧ G'.IsSubdrawing G ∧
    G'.V.ncard + G'.R.ncard < G.V.ncard + G.R.ncard ∧
    IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
    (∃ U' ⊆ U, IsDualPointSet (bd S) (G'.V ∩ bd S) U' ∧
      ∀ x ∈ U' ∪ (G'.V ∩ bd S), ∀ y ∈ U' ∪ (G'.V ∩ bd S),
        ∀ A' : List (ChainTerm S), IsXYChain G' x y A' → 0 ≤ chainRedundancy G' Δ' x y A') ∧
    (IsFeasible G'.toGraph Δ' → IsFeasible G.toGraph Δ)
  have hProper' : G'.IsProper := induceDrawing_isProper G hProper sdiff_subset
  have hSub' : G'.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hG'_V : G'.V = G.V \ {v} := induceDrawing_V G sdiff_subset
  have hΔ_sub : divisionUnion Δ ⊆ G.V ∩ bd S := hΔ_eq.subset
  have hv_bd : v ∈ G.V ∩ bd S := hΔ_sub ⟨{v}, hv, rfl⟩
  have hV_lt : G'.V.ncard < G.V.ncard := by
    rw [hG'_V]
    exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h hv_bd.1).2 rfl⟩ G.finite_V
  have hR_le : G'.R.ncard ≤ G.R.ncard :=
    disc_region_ncard_le_of_isSubdrawing hS hProper hSub'
  have hΔ'_div : IsDivision Δ' :=
    ⟨hΔ.1.subset sdiff_subset, fun δ hδ => hΔ.2.1 δ hδ.1, hΔ.2.2.subset sdiff_subset⟩
  have hΔ'_eq : divisionUnion Δ' = G'.V ∩ bd S := by
    rw [hG'_V]
    ext x
    simp only [divisionUnion, mem_sUnion, mem_inter_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨δ, ⟨hδ, hne⟩, hxδ⟩
      have hx_bd : x ∈ G.V ∩ bd S := hΔ_sub ⟨δ, hδ, hxδ⟩
      refine ⟨⟨hx_bd.1, ?_⟩, hx_bd.2⟩
      rintro rfl
      exact (hΔ.2.2 hδ hv hne).ne_of_mem hxδ rfl rfl
    · rintro ⟨⟨hxV, hxv⟩, hx_bd⟩
      have hx_union : x ∈ divisionUnion Δ := hΔ_eq.symm ▸ ⟨hxV, hx_bd⟩
      obtain ⟨δ, hδ, hxδ⟩ := hx_union
      refine ⟨δ, ⟨hδ, ?_⟩, hxδ⟩
      rintro rfl
      exact hxv hxδ
  have hV'_bd_sub : G'.V ∩ bd S ⊆ G.V ∩ bd S := inter_subset_inter_left _ hSub'.1
  obtain ⟨U', hU'_sub, hU'_dual, _⟩ := exists_dualPointSet_subset_of_subset
    hS.isOArc_bd inter_subset_right (G.finite_V.inter_of_left _) hU hV'_bd_sub
  refine ⟨hProper', hSub', by omega, hΔ'_div, hΔ'_eq,
    ⟨U', hU'_sub, hU'_dual, fun x hx y hy A' hChain =>
      chainRedundancy_nonneg_of_delete_singleton hS hProper hΔ hΔ_sub hv hU hU'_sub hU'_dual hRed
        hx hy hChain⟩, ?_⟩
  intro hFeas'
  have htoGraph : G'.toGraph = G.toGraph.deleteVerts {v} :=
    induceDrawing_toGraph_deleteVerts G {v}
  rw [htoGraph] at hFeas'
  exact (theorem_3_3_i G.toGraph Δ v hΔ (hΔ_sub.trans inter_subset_left) hv).mpr hFeas'

end GraphMinor.GM06
