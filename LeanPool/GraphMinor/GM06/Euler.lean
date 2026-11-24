/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.EdgeChart
public import LeanPool.GraphMinor.GM06.Section3Main

/-!
# Region Counting and Dual Region Separation on a Closed Disc Space

This file proves the region-counting inequalities for proper drawings on a closed disc space `S`
(`IsClosedDiscSpace S`) and deduces that for any connected proper drawing `G` on `S` and any
drawing `G_dual` satisfying the remaining properties of `IsDiscDualDrawing G G_dual`, distinct
vertices `v₁ ≠ v₂ ∈ G.V` lie in distinct regions of `G_dual`.
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric unitInterval Complex GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-! ## 1. Region Deletion Identities -/

/-- For an edge `e ∈ Γ.E` of a proper drawing `Γ` on a closed disc space `S`, `e` lies in a single
region `r₀'` of `Γ.deleteEdge e`, and every region `r' ≠ r₀'` of `Γ.deleteEdge e` is a region of
`Γ` whose closure is disjoint from `e`. -/
theorem region_of_deleteEdge_sdiff (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (_hprop : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e) :
    let r₀' := connectedComponentIn (univ \ (Γ.deleteEdge e).U) p
    r₀' ∈ (Γ.deleteEdge e).R ∧ e ⊆ r₀' ∧
    ∀ r' ∈ (Γ.deleteEdge e).R, r' ≠ r₀' → r' ∈ Γ.R ∧ Disjoint e (closure r') := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  dsimp only
  set Γ' := Γ.deleteEdge e
  set r₀' := connectedComponentIn (univ \ Γ'.U) p
  have hUe : Γ'.U = Γ.U \ e := deleteEdge_U Γ he
  have hp_compl : p ∈ univ \ Γ'.U := by
    rw [hUe]
    exact ⟨mem_univ p, fun h => h.2 hp⟩
  have hr₀' : r₀' ∈ Γ'.R := ⟨p, hp_compl, rfl⟩
  have he_conn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have he_sub_compl : e ⊆ univ \ Γ'.U := by
    rw [hUe]
    exact fun x hx => ⟨mem_univ x, fun h => h.2 hx⟩
  have he_r₀' : e ⊆ r₀' :=
    he_conn.subset_connectedComponentIn hp he_sub_compl
  refine ⟨hr₀', he_r₀', fun r' hr' hne => ?_⟩
  have hdisj_r₀' : Disjoint r' r₀' := by
    refine disjoint_left.mpr fun x hxr' hxr₀' => hne ?_
    exact region_eq_of_mem hr' hr₀' hxr' hxr₀'
  have hdisj_e : Disjoint r' e := hdisj_r₀'.mono_right he_r₀'
  have hdisj_cl : Disjoint e (closure r') := by
    refine disjoint_left.mpr fun x hxe hxcl => ?_
    obtain ⟨y, hyr₀', hyr'⟩ :=
      mem_closure_iff.mp hxcl r₀' (region_isOpen hr₀') (he_r₀' hxe)
    exact disjoint_left.mp hdisj_r₀' hyr' hyr₀'
  have hr'_sub : r' ⊆ univ \ Γ.U := by
    intro x hx
    have hx' : x ∉ Γ'.U := region_subset hr' hx
    rw [hUe] at hx'
    exact ⟨mem_univ x, fun hxU => hx' ⟨hxU, disjoint_left.mp hdisj_e hx⟩⟩
  obtain ⟨x₀, hx₀⟩ := region_nonempty hr'
  have hr'_mem : r' ∈ Γ.R := by
    refine (mem_R_iff Γ).mpr ⟨x₀, (hr'_sub hx₀).2, subset_antisymm ?_ ?_⟩
    · exact (region_isPreconnected hr').subset_connectedComponentIn hx₀ hr'_sub
    · have hsub := deleteEdge_isSubdrawing Γ e
      have h_sub_r' : connectedComponentIn (univ \ Γ.U) x₀ ⊆
          connectedComponentIn (univ \ Γ'.U) x₀ :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn (hr'_sub hx₀))
          (fun y hy => ⟨mem_univ y, fun hyU' =>
            (connectedComponentIn_subset _ _ hy).2 (hsub.U_subset hyU')⟩)
      obtain ⟨z, -, rfl⟩ := (mem_R_iff Γ').mp hr'
      rwa [connectedComponentIn_eq hx₀]
  exact ⟨hr'_mem, hdisj_cl⟩

/-- For any edge `e ∈ Γ.E` of a proper drawing `Γ` on a closed disc space `S`, there is a region
`r₀' ∈ (Γ.deleteEdge e).R` containing `e` and two regions `r₁, r₂ ∈ Γ.R` with `e ⊆ closure r₁` and
`e ⊆ closure r₂` such that `(Γ.deleteEdge e).R \ {r₀'} = Γ.R \ {r₁, r₂}`, and every region
`r ∈ Γ.R` with `e ⊆ closure r` equals `r₁` or `r₂`. -/
theorem exists_deleteEdge_R_sdiff_eq (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) :
    ∃ r₀' ∈ (Γ.deleteEdge e).R, ∃ r₁ ∈ Γ.R, ∃ r₂ ∈ Γ.R,
      e ⊆ r₀' ∧ e ⊆ closure r₁ ∧ e ⊆ closure r₂ ∧
      (∀ r ∈ Γ.R, e ⊆ closure r → r = r₁ ∨ r = r₂) ∧
      (Γ.deleteEdge e).R \ {r₀'} = Γ.R \ {r₁, r₂} := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨hr₀', he_r₀', hother⟩ := region_of_deleteEdge_sdiff hS hprop he hp
  set Γ' := Γ.deleteEdge e
  set r₀' := connectedComponentIn (univ \ Γ'.U) p
  obtain ⟨W, A₁, A₂, hW, hpW, -, hsub, c₁, c₂, d₁, d₂, cl₁, cl₂⟩ :=
    disc_exists_edge_sides hS Γ hprop he hp
  have hA₁_ne : A₁.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have := cl₁ ⟨hp, hpW⟩
    rw [hcon, closure_empty] at this
    exact this
  have hA₂_ne : A₂.Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have := cl₂ ⟨hp, hpW⟩
    rw [hcon, closure_empty] at this
    exact this
  obtain ⟨x₁, hx₁⟩ := hA₁_ne
  obtain ⟨x₂, hx₂⟩ := hA₂_ne
  obtain ⟨r₁, hr₁, hxr₁⟩ := exists_region_of_notMem (disjoint_left.mp d₁ hx₁)
  obtain ⟨r₂, hr₂, hxr₂⟩ := exists_region_of_notMem (disjoint_left.mp d₂ hx₂)
  have hA₁_r₁ : A₁ ⊆ r₁ := subset_region hr₁ c₁ d₁ hx₁ hxr₁
  have hA₂_r₂ : A₂ ⊆ r₂ := subset_region hr₂ c₂ d₂ hx₂ hxr₂
  have hi₁ : e ⊆ closure r₁ :=
    disc_edge_subset_closure_of_incident hS hprop he hr₁
      ⟨p, hp, closure_mono hA₁_r₁ (cl₁ ⟨hp, hpW⟩)⟩
  have hi₂ : e ⊆ closure r₂ :=
    disc_edge_subset_closure_of_incident hS hprop he hr₂
      ⟨p, hp, closure_mono hA₂_r₂ (cl₂ ⟨hp, hpW⟩)⟩
  have hall_inc : ∀ r ∈ Γ.R, e ⊆ closure r → r = r₁ ∨ r = r₂ := by
    intro r hr hi
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp (hi hp) W hW hpW
    rcases hsub ⟨hxW, region_subset hr hxr⟩ with hx | hx
    · exact Or.inl (region_eq_of_mem hr hr₁ hxr (hA₁_r₁ hx))
    · exact Or.inr (region_eq_of_mem hr hr₂ hxr (hA₂_r₂ hx))
  refine ⟨r₀', hr₀', r₁, hr₁, r₂, hr₂, he_r₀', hi₁, hi₂, hall_inc, ?_⟩
  ext r
  simp only [mem_sdiff, mem_singleton_iff, mem_insert_iff, not_or]
  constructor
  · rintro ⟨hr', hne⟩
    obtain ⟨hr, hdisj⟩ := hother r hr' hne
    refine ⟨hr, ?_, ?_⟩
    · rintro rfl
      exact disjoint_left.mp hdisj hp (hi₁ hp)
    · rintro rfl
      exact disjoint_left.mp hdisj hp (hi₂ hp)
  · rintro ⟨hr, hne₁, hne₂⟩
    rcases disc_edge_incident_or_disjoint hS hprop he hr with hinc | hdisj
    · rcases hall_inc r hr hinc with rfl | rfl
      · exact (hne₁ rfl).elim
      · exact (hne₂ rfl).elim
    · refine ⟨region_deleteEdge_of_not_incident he hr hdisj, ?_⟩
      rintro rfl
      exact region_subset hr (he_r₀' hp) (he.2.1 hp).1

/-- Deleting an edge reduces the number of regions by at most `1`:
`Γ.R.ncard ≤ (Γ.deleteEdge e).R.ncard + 1`. -/
theorem deleteEdge_R_ncard_le (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) :
    Γ.R.ncard ≤ (Γ.deleteEdge e).R.ncard + 1 := by
  obtain ⟨r₀', hr₀', r₁, hr₁, r₂, hr₂, -, -, -, -, hdiff⟩ :=
    exists_deleteEdge_R_sdiff_eq hS hprop he
  have hfin : Γ.R.Finite := disc_finite_R hS Γ hprop
  have hfin' : (Γ.deleteEdge e).R.Finite :=
    disc_finite_R hS (Γ.deleteEdge e) (deleteEdge_isProper hprop e)
  have h₁ : ((Γ.deleteEdge e).R \ {r₀'}).ncard + 1 = (Γ.deleteEdge e).R.ncard :=
    ncard_sdiff_singleton_add_one hr₀' hfin'
  have hsub : Γ.R ⊆ insert r₁ (insert r₂ (Γ.R \ {r₁, r₂})) := by
    intro r hr
    by_cases h1 : r = r₁
    · exact Or.inl h1
    · by_cases h2 : r = r₂
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨hr, fun h => h.elim h1 h2⟩)
  have h₂ : Γ.R.ncard ≤ (insert r₁ (insert r₂ (Γ.R \ {r₁, r₂}))).ncard :=
    ncard_le_ncard hsub (((hfin.subset sdiff_subset).insert r₂).insert r₁)
  have h₃ : (insert r₁ (insert r₂ (Γ.R \ {r₁, r₂}))).ncard ≤
      (insert r₂ (Γ.R \ {r₁, r₂})).ncard + 1 := ncard_insert_le _ _
  have h₄ : (insert r₂ (Γ.R \ {r₁, r₂})).ncard ≤ (Γ.R \ {r₁, r₂}).ncard + 1 :=
    ncard_insert_le _ _
  have h₅ : (Γ.R \ {r₁, r₂}).ncard = ((Γ.deleteEdge e).R \ {r₀'}).ncard :=
    congrArg Set.ncard hdiff.symm
  omega

/-- If an edge `e ∈ Γ.E` is incident with two distinct regions `ra ≠ rb ∈ Γ.R`, then
`Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1`. -/
theorem deleteEdge_R_ncard_eq_add_one_of_two_regions (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) {e ra rb : Set S} (he : e ∈ Γ.E)
    (hra : ra ∈ Γ.R) (hrb : rb ∈ Γ.R) (hne : ra ≠ rb)
    (hia : e ⊆ closure ra) (hib : e ⊆ closure rb) :
    Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1 := by
  obtain ⟨r₀', hr₀', r₁, hr₁, r₂, hr₂, -, _, _, hall, hdiff⟩ :=
    exists_deleteEdge_R_sdiff_eq hS hprop he
  have hfin : Γ.R.Finite := disc_finite_R hS Γ hprop
  have hfin' : (Γ.deleteEdge e).R.Finite :=
    disc_finite_R hS (Γ.deleteEdge e) (deleteEdge_isProper hprop e)
  have h₁ : ((Γ.deleteEdge e).R \ {r₀'}).ncard + 1 = (Γ.deleteEdge e).R.ncard :=
    ncard_sdiff_singleton_add_one hr₀' hfin'
  have hr₁₂_ne : r₁ ≠ r₂ := by
    intro heq
    subst heq
    have ha1 : ra = r₁ := (hall ra hra hia).elim id id
    have hb1 : rb = r₁ := (hall rb hrb hib).elim id id
    exact hne (ha1.trans hb1.symm)
  have h₂ : (Γ.R \ {r₁, r₂}).ncard + 2 = Γ.R.ncard := by
    have h_eq : Γ.R \ {r₁, r₂} = (Γ.R \ {r₂}) \ {r₁} := by
      ext r
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
      tauto
    have hr₁_mem : r₁ ∈ Γ.R \ {r₂} := ⟨hr₁, hr₁₂_ne⟩
    have ha := ncard_sdiff_singleton_add_one hr₁_mem (hfin.subset sdiff_subset)
    have hb := ncard_sdiff_singleton_add_one hr₂ hfin
    rw [h_eq]
    omega
  rw [hdiff] at h₁
  omega

/-! ## 2. Preconnectivity of `O \ bd S` and Region Separation by Redundant Edges -/

omit [T2Space S] in
/-- For any open preconnected set `O ⊆ S` in a closed disc space `S`, `O \ bd S` is
preconnected. -/
theorem isPreconnected_sdiff_bd_of_isOpen (hS : IsClosedDiscSpace S) {O : Set S}
    (hO : IsOpen O) (hOc : IsPreconnected O) : IsPreconnected (O \ bd S) := by
  intro U V hU hV hcov ⟨a, haO, haU⟩ ⟨b, hbO, hbV⟩
  by_contra hdisj
  rw [not_nonempty_iff_eq_empty] at hdisj
  have hlocal : ∀ x ∈ O, ∃ Z : Set S, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ O ∧ IsPreconnected (Z \ bd S) := by
    intro x hx
    obtain ⟨φ⟩ := hS
    have hbd_img := image_bd_homeomorph φ
    rw [bd_closedUnitDisc] at hbd_img
    let c : ClosedUnitDisc := φ.symm x
    have hc_in : c ∈ φ ⁻¹' O := by
      change φ c ∈ O
      rw [φ.apply_symm_apply]
      exact hx
    have hP_open : IsOpen (φ ⁻¹' O) := hO.preimage φ.continuous
    rw [isOpen_induced_iff] at hP_open
    obtain ⟨W, hW_open, hW_eq⟩ := hP_open
    have hcW : c.1 ∈ W := by
      have : c ∈ Subtype.val ⁻¹' W := by rwa [hW_eq]
      exact this
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW_open c.1 hcW
    let B : Set ClosedUnitDisc := Subtype.val ⁻¹' Metric.ball c.1 δ
    have hB_open : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
    let U_open : Set EuclideanPlane := Metric.ball c.1 δ ∩ OpenUnitDisc
    have hU_sub : U_open ⊆ ClosedUnitDisc :=
      fun y hy => Metric.ball_subset_closedBall hy.2
    let B_int : Set ClosedUnitDisc := Subtype.val ⁻¹' U_open
    have hB_int_conn : IsPreconnected B_int := by
      refine (IsInducing.subtypeVal :
        IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane)).isPreconnected_image.mp ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hU_sub]
      exact ((convex_ball _ _).inter convex_openUnitDisc).isPreconnected
    have hZ_diff : (φ '' B) \ bd S = φ '' B_int := by
      ext q
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hq_bd⟩
        refine ⟨y, ⟨hy, ?_⟩, rfl⟩
        have hle : ‖y.1‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
        have hne : ‖y.1‖ ≠ 1 := by
          intro h1
          apply hq_bd
          rw [← hbd_img]
          exact ⟨y, by simpa [UnitCircle] using h1, rfl⟩
        simpa [OpenUnitDisc] using lt_of_le_of_ne hle hne
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        refine ⟨⟨y, hy1, rfl⟩, ?_⟩
        rw [← hbd_img]
        rintro ⟨z, hz, hφz⟩
        have hzy : z = y := φ.injective hφz
        subst hzy
        have h1 : ‖z.1‖ < 1 := by simpa [OpenUnitDisc] using hy2
        have h2 : ‖z.1‖ = 1 := by simpa [UnitCircle] using hz
        linarith
    refine ⟨φ '' B, φ.isOpenMap _ hB_open, ⟨c, Metric.mem_ball_self hδ, φ.apply_symm_apply x⟩,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyW : y.1 ∈ W := hball hy
      have hyP : y ∈ φ ⁻¹' O := by rw [← hW_eq]; exact hyW
      exact hyP
    · rw [hZ_diff]
      exact hB_int_conn.image _ φ.continuous.continuousOn
  let U' : Set S := {x ∈ O | ∃ Z, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ O ∧ Z \ bd S ⊆ U}
  let V' : Set S := {x ∈ O | ∃ Z, IsOpen Z ∧ x ∈ Z ∧ Z ⊆ O ∧ Z \ bd S ⊆ V}
  have hU'_open : IsOpen U' := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨_, Z, hZ, hxZ, hZO, hZU⟩
    filter_upwards [hZ.mem_nhds hxZ] with y hy
    exact ⟨hZO hy, Z, hZ, hy, hZO, hZU⟩
  have hV'_open : IsOpen V' := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨_, Z, hZ, hxZ, hZO, hZV⟩
    filter_upwards [hZ.mem_nhds hxZ] with y hy
    exact ⟨hZO hy, Z, hZ, hy, hZO, hZV⟩
  have hO_cov : O ⊆ U' ∪ V' := by
    intro x hx
    obtain ⟨Z, hZ, hxZ, hZO, hZ_conn⟩ := hlocal x hx
    have hZ_sub : Z \ bd S ⊆ U ∪ V := fun y hy => hcov ⟨hZO hy.1, hy.2⟩
    by_cases hZU : Z \ bd S ⊆ U
    · exact Or.inl ⟨hx, Z, hZ, hxZ, hZO, hZU⟩
    · refine Or.inr ⟨hx, Z, hZ, hxZ, hZO, fun y hy => ?_⟩
      rcases hZ_sub hy with hyU | hyV
      · obtain ⟨z, hzZ, hzU⟩ := not_subset.mp hZU
        have hzV : z ∈ V := (hZ_sub hzZ).resolve_left hzU
        obtain ⟨w, hwZ, hwUV⟩ := hZ_conn U V hU hV hZ_sub ⟨y, hy, hyU⟩ ⟨z, hzZ, hzV⟩
        have hw_in : w ∈ (O \ bd S) ∩ (U ∩ V) := ⟨⟨hZO hwZ.1, hwZ.2⟩, hwUV⟩
        rw [hdisj] at hw_in
        exact hw_in.elim
      · exact hyV
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  have ha_U' : a ∈ O ∩ U' := by
    refine ⟨haO.1, haO.1, (O \ bd S) ∩ U, (hO.sdiff hbd_cl).inter hU, ⟨haO, haU⟩,
      fun y hy => hy.1.1, fun y hy => hy.1.2⟩
  have hb_V' : b ∈ O ∩ V' := by
    refine ⟨hbO.1, hbO.1, (O \ bd S) ∩ V, (hO.sdiff hbd_cl).inter hV, ⟨hbO, hbV⟩,
      fun y hy => hy.1.1, fun y hy => hy.1.2⟩
  obtain ⟨x, hxO, ⟨_, Z₁, hZ₁, hxZ₁, hZ₁O, hZ₁U⟩, ⟨_, Z₂, hZ₂, hxZ₂, _, hZ₂V⟩⟩ :=
    hOc U' V' hU'_open hV'_open hO_cov ⟨a, ha_U'⟩ ⟨b, hb_V'⟩
  obtain ⟨y, ⟨hy1, hy2⟩, hy_bd⟩ :=
    open_sdiff_bd_nonempty hS (hZ₁.inter hZ₂) ⟨x, hxZ₁, hxZ₂⟩
  have hy_in : y ∈ (O \ bd S) ∩ (U ∩ V) :=
    ⟨⟨hZ₁O hy1, hy_bd⟩, hZ₁U ⟨hy1, hy_bd⟩, hZ₂V ⟨hy2, hy_bd⟩⟩
  rw [hdisj] at hy_in
  exact hy_in

omit [T2Space S] in
/-- Any two points `a, b ∈ r \ bd S` of a region `r ∈ Γ.R` lie in the same connected component of
`(univ \ bd S) \ Γ.U`. -/
theorem mem_connectedComponentIn_sdiff_bd_of_region (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    {r : Set S} (hr : r ∈ Γ.R) {a b : S} (ha : a ∈ r \ bd S) (hb : b ∈ r \ bd S) :
    b ∈ connectedComponentIn ((univ \ bd S) \ Γ.U) a := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have hconn : IsPreconnected (r \ bd S) :=
    isPreconnected_sdiff_bd_of_isOpen hS (region_isOpen hr) (region_isPreconnected hr)
  refine hconn.subset_connectedComponentIn ha ?_ hb
  intro x hx
  exact ⟨⟨mem_univ x, hx.2⟩, region_subset hr hx.1⟩

/-- In the closed unit disc of `ℂ`, if `φ : ℂ → ℂ` is continuous and injective on
`closedBall (0 : ℂ) 1` and `K_out ⊆ ℂ` is a compact preconnected set disjoint from
`φ '' ball (0 : ℂ) 1` containing `φ (-1)` and `φ 1`, then `φ (Complex.I / 2)` and `φ (-Complex.I /
2)` do not lie
in the same connected component of `(φ '' {z ∈ closedBall 0 1 | z.im = 0} ∪ K_out)ᶜ`. -/
theorem not_mem_connectedComponentIn_of_chart_loop {φ : ℂ → ℂ} {K_out : Set ℂ}
    (hφc : ContinuousOn φ (closedBall (0 : ℂ) 1)) (hφi : InjOn φ (closedBall (0 : ℂ) 1))
    (hK_comp : IsCompact K_out) (hK_pre : IsPreconnected K_out)
    (hK_disj : Disjoint K_out (φ '' ball (0 : ℂ) 1))
    (hm1 : φ (-1) ∈ K_out) (hp1 : φ 1 ∈ K_out) :
    let K_in := φ '' {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0}
    φ (-Complex.I / 2) ∉ connectedComponentIn (K_in ∪ K_out)ᶜ (φ (Complex.I / 2)) := by
  intro K_in hab
  let p_pos : ℂ := φ (Complex.I / 2)
  let p_neg : ℂ := φ (-Complex.I / 2)
  have hI2_ball : (Complex.I / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_I, RCLike.norm_ofNat]
    norm_num
  have hmI2_ball : (-Complex.I / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_neg, norm_I, RCLike.norm_ofNat]
    norm_num
  have hI2_cb : (Complex.I / 2 : ℂ) ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hI2_ball
  have hmI2_cb : (-Complex.I / 2 : ℂ) ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hmI2_ball
  have h1_cb : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hm1_cb : (-1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hp_not_Kin : p_pos ∉ K_in := by
    rintro ⟨z, ⟨hz, hzim⟩, hz_eq⟩
    have := hφi hz hI2_cb hz_eq
    subst this
    simp at hzim
  have hm_not_Kin : p_neg ∉ K_in := by
    rintro ⟨z, ⟨hz, hzim⟩, hz_eq⟩
    have := hφi hz hmI2_cb hz_eq
    subst this
    simp at hzim
  have hp_not_Kout : p_pos ∉ K_out :=
    fun h => disjoint_left.mp hK_disj h ⟨Complex.I / 2, hI2_ball, rfl⟩
  have hm_not_Kout : p_neg ∉ K_out :=
    fun h => disjoint_left.mp hK_disj h ⟨-Complex.I / 2, hmI2_ball, rfl⟩
  have hKin_comp : IsCompact K_in := by
    have hcl : IsClosed {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} :=
      isClosed_closedBall.inter (isClosed_eq Complex.continuous_im continuous_const)
    exact ( (isCompact_closedBall (0 : ℂ) 1).inter_right
      (isClosed_eq Complex.continuous_im continuous_const) ).image_of_continuousOn
      (hφc.mono fun _ h => h.1)
  have hlog₁ : HasLogOn (K_in ∪ K_out) (fun z => (z - p_neg) / (z - p_pos)) :=
    hasLogOn_div_of_same_component (hKin_comp.union hK_comp).isClosed
      (fun h => h.elim hp_not_Kin hp_not_Kout) hab
  let R₀ : Set ℂ := {z : ℂ | z ∈ sphere (0 : ℂ) 1 ∧ 0 ≤ z.im}
  let R_pos : Set ℂ := φ '' R₀
  have hR₀_sub : R₀ ⊆ closedBall (0 : ℂ) 1 := fun z hz => sphere_subset_closedBall hz.1
  have hR₀_comp : IsCompact R₀ :=
    (isCompact_sphere (0 : ℂ) 1).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hR_comp : IsCompact R_pos := hR₀_comp.image_of_continuousOn (hφc.mono hR₀_sub)
  have hR_disj : Disjoint R_pos (φ '' ball (0 : ℂ) 1) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have heq := hφi (hR₀_sub hz) (ball_subset_closedBall hw) hwz.symm
    subst heq
    have h1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz.1
    have h2 : ‖z‖ < 1 := mem_ball_zero_iff.mp hw
    linarith
  have hp_not_R : p_pos ∉ R_pos :=
    fun h => disjoint_left.mp hR_disj h ⟨Complex.I / 2, hI2_ball, rfl⟩
  have hm_not_R : p_neg ∉ R_pos :=
    fun h => disjoint_left.mp hR_disj h ⟨-Complex.I / 2, hmI2_ball, rfl⟩
  have hab_R : p_neg ∈ connectedComponentIn (K_out ∪ R_pos)ᶜ p_pos := by
    let seg : Set ℂ := segment ℝ (Complex.I / 2 : ℂ) (-Complex.I / 2)
    have hseg_ball : seg ⊆ ball (0 : ℂ) 1 :=
      (convex_ball (0 : ℂ) 1).segment_subset hI2_ball hmI2_ball
    have hseg_pre : IsPreconnected (φ '' seg) :=
      (convex_segment (Complex.I / 2 : ℂ) (-Complex.I / 2)).isPreconnected.image φ
        (hφc.mono (hseg_ball.trans ball_subset_closedBall))
    have hseg_sub : φ '' seg ⊆ (K_out ∪ R_pos)ᶜ := by
      rintro _ ⟨z, hz, rfl⟩
      rintro (hK | hR)
      · exact disjoint_left.mp hK_disj hK ⟨z, hseg_ball hz, rfl⟩
      · exact disjoint_left.mp hR_disj hR ⟨z, hseg_ball hz, rfl⟩
    exact hseg_pre.subset_connectedComponentIn
      ⟨Complex.I / 2, left_mem_segment ℝ _ _, rfl⟩ hseg_sub ⟨-Complex.I / 2, right_mem_segment ℝ _
        _, rfl⟩
  have hlog₂ : HasLogOn (K_out ∪ R_pos) (fun z => (z - p_neg) / (z - p_pos)) :=
    hasLogOn_div_of_same_component (hK_comp.union hR_comp).isClosed
      (fun h => h.elim hp_not_Kout hp_not_R) hab_R
  obtain ⟨g₁, hg₁c, hg₁⟩ := hlog₁
  obtain ⟨g₂, hg₂c, hg₂⟩ := hlog₂
  dsimp only at hg₁ hg₂
  have hnz : ∀ x ∈ K_out, (x - p_neg) / (x - p_pos) ≠ 0 := by
    intro x hx
    rw [hg₂ x (Or.inl hx)]
    exact exp_ne_zero _
  have hexp : ∀ x ∈ K_out, exp (g₁ x - g₂ x) = 1 := by
    intro x hx
    rw [exp_sub, ← hg₁ x (Or.inr hx), ← hg₂ x (Or.inl hx)]
    exact div_self (hnz x hx)
  have hconstant : ∀ x ∈ K_out, g₁ x - g₂ x = g₁ (φ (-1)) - g₂ (φ (-1)) := fun x hx =>
    eq_of_exp_eq_one hK_pre
      ((hg₁c.mono subset_union_right).sub (hg₂c.mono subset_union_left)) hexp hx hm1
  set c := g₁ (φ (-1)) - g₂ (φ (-1))
  have hc_exp : exp c = 1 := hexp (φ (-1)) hm1
  have hKin_R_inter : K_in ∩ R_pos ⊆ K_out := by
    rintro _ ⟨⟨z, ⟨hz, hzim⟩, rfl⟩, ⟨w, ⟨hw, _⟩, hwz⟩⟩
    have heq := hφi hz (sphere_subset_closedBall hw) hwz.symm
    subst heq
    have hnorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    have hre_sq : z.re ^ 2 = 1 := by
      have hsq := Complex.sq_norm z
      rw [hnorm, one_pow, Complex.normSq_apply, hzim] at hsq
      linarith
    rcases sq_eq_one_iff.mp hre_sq with hre | hre
    · have hz1 : z = 1 := Complex.ext (by simpa using hre) (by simpa using hzim)
      rw [hz1]
      exact hp1
    · have hzm1 : z = -1 := Complex.ext (by simpa using hre) (by simpa using hzim)
      rw [hzm1]
      exact hm1
  have hlogF : HasLogOn (K_in ∪ R_pos) (fun z => (z - p_neg) / (z - p_pos)) := by
    refine hasLogOn_union (gA := g₁) (gB := fun z => g₂ z + c)
      hKin_comp.isClosed hR_comp.isClosed
      (hg₁c.mono subset_union_left) ((hg₂c.mono subset_union_right).add continuousOn_const)
      (fun z hz => hg₁ z (Or.inl hz))
      (fun z hz => by rw [exp_add, hc_exp, mul_one]; exact hg₂ z (Or.inr hz))
      fun z hz => ?_
    have := hconstant z (hKin_R_inter hz)
    dsimp [c]
    linear_combination this
  let U₀ : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < z.im}
  have hU₀_open : IsOpen U₀ :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hU₀_sub : U₀ ⊆ closedBall (0 : ℂ) 1 := fun z hz => ball_subset_closedBall hz.1
  let U : Set ℂ := φ '' U₀
  have hU_open : IsOpen U :=
    isOpen_image_of_injOn hU₀_open (hφc.mono hU₀_sub) (hφi.mono hU₀_sub)
  let D₀ : Set ℂ := {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ 0 ≤ z.im}
  have hD₀_comp : IsCompact D₀ :=
    (isCompact_closedBall (0 : ℂ) 1).inter_right (isClosed_le continuous_const
      Complex.continuous_im)
  have hD_comp : IsCompact (φ '' D₀) :=
    hD₀_comp.image_of_continuousOn (hφc.mono fun _ h => h.1)
  have hU_bdd : Bornology.IsBounded U :=
    hD_comp.isBounded.subset (image_mono fun z hz => ⟨ball_subset_closedBall hz.1, hz.2.le⟩)
  have hp_in_U : p_pos ∈ U := ⟨Complex.I / 2, ⟨hI2_ball, by simp⟩, rfl⟩
  have hcl_U_sub : closure U ⊆ φ '' D₀ :=
    hD_comp.isClosed.closure_subset_iff.mpr
      (image_mono fun z hz => ⟨ball_subset_closedBall hz.1, hz.2.le⟩)
  have hm_not_clU : p_neg ∉ closure U := by
    intro hcl
    obtain ⟨z, hz, hzeq⟩ := hcl_U_sub hcl
    have heq := hφi hz.1 hmI2_cb hzeq
    subst heq
    have : (0 : ℝ) ≤ (-Complex.I / 2 : ℂ).im := hz.2
    simp at this
    linarith
  have hfront_sub : frontier U ⊆ K_in ∪ R_pos := by
    rw [hU_open.frontier_eq]
    rintro w ⟨hw_cl, hw_not_U⟩
    obtain ⟨z, ⟨hz_cb, hz_im⟩, rfl⟩ := hcl_U_sub hw_cl
    rcases eq_or_lt_of_le hz_im with hzim0 | hzim_pos
    · exact Or.inl ⟨z, ⟨hz_cb, hzim0.symm⟩, rfl⟩
    · have hznorm : ‖z‖ = 1 := by
        have hle : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz_cb
        refine le_antisymm hle (not_lt.mp fun hlt => hw_not_U ?_)
        exact ⟨z, ⟨mem_ball_zero_iff.mpr hlt, hzim_pos⟩, rfl⟩
      exact Or.inr ⟨z, ⟨mem_sphere_zero_iff_norm.mpr hznorm, hz_im⟩, rfl⟩
  have hlog_inv : HasLogOn (frontier U) (fun z => (z - p_pos) ^ (1 : ℤ) / (z - p_neg)) := by
    refine ((hlogF.mono hfront_sub).inv).congr fun z _ => ?_
    simp [inv_div]
  have hne_clU : ∀ z ∈ closure U, z - p_neg ≠ 0 :=
    fun z hz h => hm_not_clU (sub_eq_zero.mp h ▸ hz)
  exact one_ne_zero (eq_zero_of_hasLogOn_frontier hU_open hU_bdd hp_in_U
    (continuousOn_id.sub continuousOn_const) hne_clU hlog_inv)

omit [T2Space S] in
private theorem edge_meets_closure_of_radial_component {Γ : Drawing S}
    {e : Set S} {G : ℂ → S} (hGc : ContinuousOn G (closedBall 0 1)) (hmid_e : G 0 ∈ e)
    (hG_off_real : ∀ z ∈ closedBall (0 : ℂ) 1, z.im ≠ 0 → G z ∉ Γ.U) :
    ∀ w ∈ ball (0 : ℂ) 1, w.im ≠ 0 →
      (e ∩ closure (connectedComponentIn (univ \ Γ.U) (G w))).Nonempty := by
  intro w hw hwim
  have hw_cb : w ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hw
  refine ⟨G 0, hmid_e, ?_⟩
  rw [mem_closure_iff_nhds]
  intro V hV
  have h0_cb : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hpre : G ⁻¹' V ∈ 𝓝[closedBall (0 : ℂ) 1] 0 := hGc.continuousWithinAt h0_cb hV
  rw [mem_nhdsWithin_iff] at hpre
  obtain ⟨δ, hδ_pos, hδ⟩ := hpre
  let t : ℝ := min (1 / 2) (δ / 2)
  have ht_pos : 0 < t := lt_min (by norm_num) (half_pos hδ_pos)
  have ht_le1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htw_cb : (t : ℂ) * w ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
    have h1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw_cb
    nlinarith
  have htw_ball : (t : ℂ) * w ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
    have h1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have h2 : t ≤ δ / 2 := min_le_right _ _
    nlinarith
  have hGtw_V : G ((t : ℂ) * w) ∈ V := hδ ⟨htw_ball, htw_cb⟩
  have hseg_sub : (fun s : ℝ => G ((s : ℂ) * w)) '' Icc t 1 ⊆ univ \ Γ.U := by
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le ht_pos hs1
    have hsw_cb : (s : ℂ) * w ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      have h1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw_cb
      nlinarith
    have hsw_im : ((s : ℂ) * w).im ≠ 0 := by
      simp [hs_pos.ne', hwim]
    exact ⟨mem_univ _, hG_off_real _ hsw_cb hsw_im⟩
  have hseg_cont : ContinuousOn (fun s : ℝ => G ((s : ℂ) * w)) (Icc t 1) := by
    refine hGc.comp ((Complex.continuous_ofReal.mul continuous_const).continuousOn) ?_
    intro s ⟨hs1, hs2⟩
    have hs_pos : 0 < s := lt_of_lt_of_le ht_pos hs1
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
    have h1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw_cb
    nlinarith
  have hseg_pre : IsPreconnected ((fun s : ℝ => G ((s : ℂ) * w)) '' Icc t 1) :=
    isPreconnected_Icc.image _ hseg_cont
  have hw_in : G w ∈ (fun s : ℝ => G ((s : ℂ) * w)) '' Icc t 1 :=
    ⟨1, ⟨ht_le1, le_rfl⟩, by simp⟩
  have htw_in : G ((t : ℂ) * w) ∈ (fun s : ℝ => G ((s : ℂ) * w)) '' Icc t 1 :=
    ⟨t, ⟨le_rfl, ht_le1⟩, rfl⟩
  exact ⟨G ((t : ℂ) * w), hGtw_V, hseg_pre.subset_connectedComponentIn hw_in hseg_sub htw_in⟩

/-- If `e ∈ Γ.E` has ends `u, v ∈ Γ.V` and there is a compact preconnected set
`C₀ ⊆ (Γ.deleteEdge e).U ∪ bd S` containing `u` and `v`, then deleting `e` decreases the number of
regions by `1`: `Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1`. -/
theorem deleteEdge_R_ncard_eq_add_one_of_ends_connected (hS : IsClosedDiscSpace S)
    {Γ : Drawing S} (hΓ : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) {u v : S}
    (hlink : Γ.toGraph.IsLink e u v) {C₀ : Set S}
    (hC₀_comp : IsCompact C₀) (hC₀_pre : IsPreconnected C₀)
    (hC₀_sub : C₀ ⊆ (Γ.deleteEdge e).U ∪ bd S) (hu : u ∈ C₀) (hv : v ∈ C₀) :
    Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1 := by
  obtain ⟨γ, hγc, hγ0, hγ1, hγi, hγ_open, hγ_cl, hlink_γ⟩ := exists_edge_param_isLink Γ he
  have hpair : ({γ 0, γ 1} : Set S) = {u, v} := hlink_γ.2.2.2.symm.trans hlink.2.2.2
  have hγ0_C₀ : γ 0 ∈ C₀ := by
    have : γ 0 ∈ ({u, v} : Set S) := hpair ▸ mem_insert (γ 0) {γ 1}
    rcases this with rfl | rfl <;> assumption
  have hγ1_C₀ : γ 1 ∈ C₀ := by
    have : γ 1 ∈ ({u, v} : Set S) := hpair ▸ mem_insert_of_mem (γ 0) rfl
    rcases this with rfl | rfl <;> assumption
  let t₀ : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : I) 1 :=
    ⟨Subtype.mk_lt_mk.mpr (by norm_num), Subtype.mk_lt_mk.mpr (by norm_num)⟩
  obtain ⟨G, a, b, hGc, hGi, ha, hab, hb1, hb, hG0, hG_sub, hG_inter, _, hG_arc, hG_ends⟩ :=
    disc_exists_edge_chart hS Γ hΓ he hγc hγ0 hγ1 hγi hγ_open ht₀ ht₀.1 ht₀.2
      isOpen_univ (mem_univ _)
  let C_left : Set S := γ '' Icc 0 a
  let C_right : Set S := γ '' Icc b 1
  have hC_left_comp : IsCompact C_left := isCompact_Icc.image hγc
  have hC_right_comp : IsCompact C_right := isCompact_Icc.image hγc
  have hC_left_pre : IsPreconnected C_left := isPreconnected_Icc.image γ hγc.continuousOn
  have hC_right_pre : IsPreconnected C_right := isPreconnected_Icc.image γ hγc.continuousOn
  have hu_left : γ 0 ∈ C_left := ⟨0, ⟨le_rfl, unitInterval.nonneg a⟩, rfl⟩
  have hv_right : γ 1 ∈ C_right := ⟨1, ⟨unitInterval.le_one b, le_rfl⟩, rfl⟩
  have hγa_left : γ a ∈ C_left := ⟨a, ⟨unitInterval.nonneg a, le_rfl⟩, rfl⟩
  have hγb_right : γ b ∈ C_right := ⟨b, ⟨le_rfl, unitInterval.le_one b⟩, rfl⟩
  let C_loop : Set S := (C_left ∪ C₀) ∪ C_right
  have hCloop_comp : IsCompact C_loop := (hC_left_comp.union hC₀_comp).union hC_right_comp
  have hCloop_pre : IsPreconnected C_loop :=
    (hC_left_pre.union (γ 0) hu_left hγ0_C₀ hC₀_pre).union (γ 1)
      (Or.inr hγ1_C₀) hv_right hC_right_pre
  have hcl_sub_U : closure e ⊆ Γ.U :=
    Γ.isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset)
  have hCloop_sub : C_loop ⊆ Γ.U ∪ bd S := by
    have hleft_sub : C_left ⊆ Γ.U ∪ bd S :=
      (image_subset_range γ _).trans (hγ_cl.symm.subset.trans (hcl_sub_U.trans subset_union_left))
    have hright_sub : C_right ⊆ Γ.U ∪ bd S :=
      (image_subset_range γ _).trans (hγ_cl.symm.subset.trans (hcl_sub_U.trans subset_union_left))
    have hC₀_sub' : C₀ ⊆ Γ.U ∪ bd S :=
      hC₀_sub.trans (union_subset_union_left _ (deleteEdge_isSubdrawing Γ e).U_subset)
    exact union_subset (union_subset hleft_sub hC₀_sub') hright_sub
  have hm1_in : G (-1) ∈ C_loop := by
    rcases hG_ends with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact Or.inl (Or.inl hγa_left)
    · rw [h1]; exact Or.inr hγb_right
  have hp1_in : G 1 ∈ C_loop := by
    rcases hG_ends with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact Or.inr hγb_right
    · rw [h2]; exact Or.inl (Or.inl hγa_left)
  have hdisj_e_delU : Disjoint e (Γ.deleteEdge e).U := by
    rw [deleteEdge_U Γ he]
    exact disjoint_sdiff_self_right
  have hCloop_disj : Disjoint C_loop (G '' ball (0 : ℂ) 1) := by
    refine disjoint_left.mpr ?_
    rintro x hx ⟨z, hz_ball, rfl⟩
    have hz_cb : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz_ball
    have hGz_not_bd : G z ∉ bd S := (hG_sub ⟨z, hz_cb, rfl⟩).2
    have hGz_U : G z ∈ Γ.U := (hCloop_sub hx).resolve_right hGz_not_bd
    have hzim : z.im = 0 := (hG_inter z hz_cb).mp hGz_U
    have hGz_ab : G z ∈ γ '' Icc a b := hG_arc ▸ ⟨z, ⟨hz_cb, hzim⟩, rfl⟩
    obtain ⟨t₂, ht₂, hgt₂⟩ := hGz_ab
    have ht₂_ioo : t₂ ∈ Ioo (0 : I) 1 := ⟨ha.trans_le ht₂.1, ht₂.2.trans_lt hb⟩
    have hGz_e : G z ∈ e := hγ_open ▸ ⟨t₂, ht₂_ioo, hgt₂⟩
    have hGz_not_C₀ : G z ∉ C₀ := fun h => by
      rcases hC₀_sub h with hdel | hbd
      · exact disjoint_left.mp hdisj_e_delU hGz_e hdel
      · exact hGz_not_bd hbd
    have hGz_ends : G z ∈ C_left ∪ C_right := by
      rcases hx with (hx_left | hx_C₀) | hx_right
      · exact Or.inl hx_left
      · exact (hGz_not_C₀ hx_C₀).elim
      · exact Or.inr hx_right
    have hGz_a_or_b : G z = γ a ∨ G z = γ b := by
      rcases hGz_ends with ⟨t₁, ht₁, hgt₁⟩ | ⟨t₁, ht₁, hgt₁⟩
      · have ht₁_ne0 : t₁ ≠ 0 := fun h0 => (he.2.1 hGz_e).2 (hgt₁ ▸ h0 ▸ hγ0)
        have ht₁_ioo : t₁ ∈ Ioo (0 : I) 1 :=
          ⟨unitInterval.pos_iff_ne_zero.mpr ht₁_ne0, ht₁.2.trans_lt (hab.trans ht₀.2)⟩
        have heq := hγi ht₁_ioo ht₂_ioo (hgt₁.trans hgt₂.symm)
        have : t₁ = a := le_antisymm ht₁.2 (heq ▸ ht₂.1)
        exact Or.inl (hgt₁.symm.trans (congrArg γ this))
      · have ht₁_ne1 : t₁ ≠ 1 := fun h1 => (he.2.1 hGz_e).2 (hgt₁ ▸ h1 ▸ hγ1)
        have ht₁_ioo : t₁ ∈ Ioo (0 : I) 1 :=
          ⟨(ht₀.1.trans hb1).trans_le ht₁.1, unitInterval.lt_one_iff_ne_one.mpr ht₁_ne1⟩
        have heq := hγi ht₁_ioo ht₂_ioo (hgt₁.trans hgt₂.symm)
        have : t₁ = b := le_antisymm (heq ▸ ht₂.2) ht₁.1
        exact Or.inr (hgt₁.symm.trans (congrArg γ this))
    have hGz_pm1 : G z = G (-1) ∨ G z = G 1 := by
      rcases hG_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hGz_a_or_b with h | h
      · exact Or.inl (h.trans h1.symm)
      · exact Or.inr (h.trans h2.symm)
      · exact Or.inr (h.trans h2.symm)
      · exact Or.inl (h.trans h1.symm)
    have h1_cb : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    have hm1_cb : (-1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    rcases hGz_pm1 with h | h
    · have := hGi hz_cb hm1_cb h
      subst this
      simp at hz_ball
    · have := hGi hz_cb h1_cb h
      subst this
      simp at hz_ball
  obtain ⟨h, g, hhc, hhi, hh_univ, _, _, _, _, _⟩ := exists_disc_complex_chart hS
  let φ : ℂ → ℂ := h ∘ G
  have hφc : ContinuousOn φ (closedBall (0 : ℂ) 1) := hhc.comp_continuousOn hGc
  have hφi : InjOn φ (closedBall (0 : ℂ) 1) :=
    fun z₁ hz₁ z₂ hz₂ heq => hGi hz₁ hz₂ (hhi heq)
  let K_out : Set ℂ := h '' C_loop
  have hK_comp : IsCompact K_out := hCloop_comp.image hhc
  have hK_pre : IsPreconnected K_out := hCloop_pre.image h hhc.continuousOn
  have hK_disj : Disjoint K_out (φ '' ball (0 : ℂ) 1) := by
    rw [image_comp]
    exact Disjoint.image hCloop_disj hhi.injOn (subset_univ _) (subset_univ _)
  have hm1_K : φ (-1) ∈ K_out := ⟨G (-1), hm1_in, rfl⟩
  have hp1_K : φ 1 ∈ K_out := ⟨G 1, hp1_in, rfl⟩
  have hnot_same :=
    not_mem_connectedComponentIn_of_chart_loop hφc hφi hK_comp hK_pre hK_disj hm1_K hp1_K
  have hI2_ball : (Complex.I / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_I, RCLike.norm_ofNat]
    norm_num
  have hmI2_ball : (-Complex.I / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, norm_neg, norm_I, RCLike.norm_ofNat]
    norm_num
  have hG_off_real : ∀ z ∈ closedBall (0 : ℂ) 1, z.im ≠ 0 → G z ∈ (univ \ bd S) \ Γ.U := by
    intro z hz hzim
    exact ⟨hG_sub ⟨z, hz, rfl⟩, fun hxU => hzim ((hG_inter z hz).mp hxU)⟩
  let x_pos : S := G (Complex.I / 2)
  let x_neg : S := G (-Complex.I / 2)
  have hx_pos : x_pos ∈ (univ \ bd S) \ Γ.U :=
    hG_off_real (Complex.I / 2) (ball_subset_closedBall hI2_ball) (by simp)
  have hx_neg : x_neg ∈ (univ \ bd S) \ Γ.U :=
    hG_off_real (-Complex.I / 2) (ball_subset_closedBall hmI2_ball) (by simp)
  let r_pos : Set S := connectedComponentIn (univ \ Γ.U) x_pos
  let r_neg : Set S := connectedComponentIn (univ \ Γ.U) x_neg
  have hr_pos_R : r_pos ∈ Γ.R := ⟨x_pos, ⟨mem_univ _, hx_pos.2⟩, rfl⟩
  have hr_neg_R : r_neg ∈ Γ.R := ⟨x_neg, ⟨mem_univ _, hx_neg.2⟩, rfl⟩
  have hmid_e : γ t₀ ∈ e := hγ_open ▸ ⟨t₀, ht₀, rfl⟩
  have hinc_of_im_ne_zero := edge_meets_closure_of_radial_component hGc (hG0 ▸ hmid_e)
    (fun z hz him => (hG_off_real z hz him).2)
  have hinc_pos : e ⊆ closure r_pos :=
    disc_edge_subset_closure_of_incident hS hΓ he hr_pos_R
      (hinc_of_im_ne_zero (Complex.I / 2) hI2_ball (by simp))
  have hinc_neg : e ⊆ closure r_neg :=
    disc_edge_subset_closure_of_incident hS hΓ he hr_neg_R
      (hinc_of_im_ne_zero (-Complex.I / 2) hmI2_ball (by simp))
  have hr_ne : r_pos ≠ r_neg := by
    intro heq
    have hx_pos_r : x_pos ∈ r_pos \ bd S :=
      ⟨mem_connectedComponentIn ⟨mem_univ _, hx_pos.2⟩, hx_pos.1.2⟩
    have hx_neg_r : x_neg ∈ r_pos \ bd S := by
      rw [heq]
      exact ⟨mem_connectedComponentIn ⟨mem_univ _, hx_neg.2⟩, hx_neg.1.2⟩
    have hsame_S : x_neg ∈ connectedComponentIn ((univ \ bd S) \ Γ.U) x_pos :=
      mem_connectedComponentIn_sdiff_bd_of_region hS hr_pos_R hx_pos_r hx_neg_r
    let Comp := connectedComponentIn ((univ \ bd S) \ Γ.U) x_pos
    have hComp_pre : IsPreconnected (h '' Comp) :=
      isPreconnected_connectedComponentIn.image h hhc.continuousOn
    have hComp_sub : h '' Comp ⊆
        (φ '' {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0} ∪ K_out)ᶜ := by
      rintro _ ⟨y, hyComp, rfl⟩
      have hy : y ∈ (univ \ bd S) \ Γ.U := connectedComponentIn_subset _ _ hyComp
      rintro (⟨z, hz, hzy⟩ | ⟨w, hw, hwy⟩)
      · have hGz_y : G z = y := hhi hzy
        have hGz_U : G z ∈ Γ.U := (hG_inter z hz.1).mpr hz.2
        rw [hGz_y] at hGz_U
        exact hy.2 hGz_U
      · have hw_y : w = y := hhi hwy
        subst hw_y
        rcases hCloop_sub hw with hwU | hw_bd
        · exact hy.2 hwU
        · exact hy.1.2 hw_bd
    have hφ_pos_in : φ (Complex.I / 2) ∈ h '' Comp :=
      ⟨x_pos, mem_connectedComponentIn hx_pos, rfl⟩
    have hφ_neg_in : φ (-Complex.I / 2) ∈ h '' Comp :=
      ⟨x_neg, hsame_S, rfl⟩
    exact hnot_same (hComp_pre.subset_connectedComponentIn hφ_pos_in hComp_sub hφ_neg_in)
  exact deleteEdge_R_ncard_eq_add_one_of_two_regions hS hΓ he hr_pos_R hr_neg_R hr_ne hinc_pos
    hinc_neg

/-- An edge `e ∈ Γ.E` with ends `u, v ∈ Γ.V` is redundant in `Γ` if `u` and `v` are joined by a walk
in `(Γ.deleteEdge e).toGraph`, or both `u` and `v` are joined by walks to `Γ.V ∩ bd S` in
`(Γ.deleteEdge e).toGraph`. In either case, `Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1`. -/
theorem deleteEdge_R_ncard_eq_add_one_of_redundant (hS : IsClosedDiscSpace S)
    {Γ : Drawing S} (hΓ : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E) {u v : S}
    (hlink : Γ.toGraph.IsLink e u v)
    (hred : Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∨
      ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
       (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂)))) :
    Γ.R.ncard = (Γ.deleteEdge e).R.ncard + 1 := by
  have : CompactSpace S := compactSpace_of_isClosedDiscSpace hS
  rcases hred with ⟨⟨W⟩⟩ | ⟨⟨b₁, hb₁, ⟨W₁⟩⟩, ⟨b₂, hb₂, ⟨W₂⟩⟩⟩
  · obtain ⟨K, hK_comp, hK_conn, huK, hvK, _, hK_U, _⟩ :=
      exists_compact_connected_of_walk (Γ.deleteEdge e) le_rfl W
    exact deleteEdge_R_ncard_eq_add_one_of_ends_connected hS hΓ he hlink
      hK_comp hK_conn.isPreconnected (hK_U.trans subset_union_left) huK hvK
  · obtain ⟨K₁, hK₁_comp, hK₁_conn, huK₁, hb₁K₁, _, hK₁_U, _⟩ :=
      exists_compact_connected_of_walk (Γ.deleteEdge e) le_rfl W₁
    obtain ⟨K₂, hK₂_comp, hK₂_conn, hvK₂, hb₂K₂, _, hK₂_U, _⟩ :=
      exists_compact_connected_of_walk (Γ.deleteEdge e) le_rfl W₂
    have hbd_comp : IsCompact (bd S) := (isClosed_bd_of_isClosedDiscSpace hS).isCompact
    obtain ⟨φ_bd⟩ := hS.isOArc_bd
    have hbd_pre : IsPreconnected (bd S) := by
      rw [← range_oArcMap φ_bd, ← image_univ]
      exact isPreconnected_univ.image _ (isEmbedding_oArcMap φ_bd).continuous.continuousOn
    let C₀ : Set S := (K₁ ∪ bd S) ∪ K₂
    have hC₀_comp : IsCompact C₀ := (hK₁_comp.union hbd_comp).union hK₂_comp
    have hC₀_pre : IsPreconnected C₀ :=
      (hK₁_conn.isPreconnected.union b₁ hb₁K₁ hb₁.2 hbd_pre).union b₂
        (Or.inr hb₂.2) hb₂K₂ hK₂_conn.isPreconnected
    have hC₀_sub : C₀ ⊆ (Γ.deleteEdge e).U ∪ bd S :=
      union_subset (union_subset (hK₁_U.trans subset_union_left) subset_union_right)
        (hK₂_U.trans subset_union_left)
    exact deleteEdge_R_ncard_eq_add_one_of_ends_connected hS hΓ he hlink
      hC₀_comp hC₀_pre hC₀_sub (Or.inl (Or.inl huK₁)) (Or.inr hvK₂)

/-! ## 3. Deleting an Internal Leaf -/

/-- If `w ∈ Γ.V \ bd S` has a unique incident edge `e ∈ Γ.E` with ends `w ≠ u`, then
`Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})` has `Γ'.V = Γ.V \ {w}`, `Γ'.E = Γ.E \ {e}`,
`Γ'.U ∪ closure e = Γ.U`, `closure e ∩ Γ'.U ⊆ {u}`, `closure e ∩ bd S ⊆ {u}`, and
`Γ'.IsProper`. -/
theorem deleteLeaf_props {Γ : Drawing S} (hΓ : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E)
    {w u : S} (hlink : Γ.toGraph.IsLink e w u) (hw_ne : w ≠ u) (hw_bd : w ∉ bd S)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → w ∉ closure f) :
    let Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
    Γ'.V = Γ.V \ {w} ∧ Γ'.E = Γ.E \ {e} ∧ Γ'.IsSubdrawing Γ ∧ Γ'.IsProper ∧
    IsLine (closure e) ∧ Γ'.U ∪ closure e = Γ.U ∧
    closure e ∩ Γ'.U ⊆ {u} ∧ closure e ∩ bd S ⊆ {u} := by
  intro Γ'
  have hE' : Γ'.E = Γ.E \ {e} := by
    rw [Γ.span_E, inter_eq_left.mpr sdiff_subset]
  have hV' : Γ'.V = Γ.V \ {w} := by
    rw [Γ.span_V]
    unfold Drawing.spanV
    rw [inter_eq_left.mpr sdiff_subset, inter_eq_left.mpr sdiff_subset]
    refine Subset.antisymm (union_subset le_rfl ?_) subset_union_left
    rintro x hx
    obtain ⟨f, ⟨hfE, hfe⟩, hxf, hxV⟩ := mem_iUnion₂.mp hx
    exact ⟨hxV, fun hxw => hleaf f hfE hfe (hxw ▸ hxf)⟩
  have hsub : Γ'.IsSubdrawing Γ :=
    ⟨Γ.spanV_subset _ _, by rw [hE']; exact sdiff_subset⟩
  have hprop' : Γ'.IsProper := fun x hx => by
    have hxV : x ∈ Γ.V := hΓ ⟨hx.1, hsub.U_subset hx.2⟩
    rw [hV']
    exact ⟨hxV, fun hxw => hw_bd (hxw ▸ hx.1)⟩
  have hcl_e : closure e = e ∪ {w, u} := closure_edge_eq_union_ends Γ hlink hw_ne
  have hline : IsLine (closure e) := by
    rcases Γ.edge_cond e he with ⟨u', v', _, _, f, _, _⟩ | ⟨u', hcap', _⟩
    · exact ⟨f⟩
    · exfalso
      have hpair : ({w, u} : Set S) = {u'} := hlink.2.2.2.symm.trans hcap'
      have hw_u' : w = u' := mem_singleton_iff.mp (hpair ▸ mem_insert w {u})
      have hu_u' : u = u' := mem_singleton_iff.mp (hpair ▸ mem_insert_of_mem w rfl)
      exact hw_ne (hw_u'.trans hu_u'.symm)
  have hU_union : Γ'.U ∪ closure e = Γ.U := by
    refine Subset.antisymm (union_subset hsub.U_subset (Γ.closure_subset_U he)) ?_
    intro x hxU
    by_cases hxe : x ∈ closure e
    · exact Or.inr hxe
    · left
      rw [Γ'.U_eq, hV', hE']
      rw [Γ.U_eq] at hxU
      rcases hxU with hxV | hx_edges
      · refine Or.inl ⟨hxV, fun hxw => hxe ?_⟩
        rw [hcl_e, hxw]
        exact Or.inr (mem_insert w {u})
      · obtain ⟨f, hfE, hxf⟩ := mem_iUnion₂.mp hx_edges
        have hfe : f ≠ e := fun h => hxe (h ▸ hxf)
        exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hfE, hfe⟩, hxf⟩)
  have hinter_U : closure e ∩ Γ'.U ⊆ {u} := by
    rintro x ⟨hxcl, hxU'⟩
    rw [hcl_e] at hxcl
    rw [Γ'.U_eq, hV', hE'] at hxU'
    rcases hxcl with hxe | (rfl | hxu)
    · exfalso
      rcases hxU' with ⟨hxV, _⟩ | hx_edges
      · exact (he.2.1 hxe).2 hxV
      · obtain ⟨f, ⟨hfE, hfe⟩, hxf⟩ := mem_iUnion₂.mp hx_edges
        have hxf_open : x ∈ f := by
          rw [← Γ.closure_diff_V hfE]
          exact ⟨hxf, (he.2.1 hxe).2⟩
        exact hfe (Γ.edge_eq_of_mem hfE he hxf_open hxe)
    · exfalso
      rcases hxU' with ⟨_, hnw⟩ | hx_edges
      · exact hnw rfl
      · obtain ⟨f, ⟨hfE, hfe⟩, hwf⟩ := mem_iUnion₂.mp hx_edges
        exact hleaf f hfE hfe hwf
    · exact hxu
  have hinter_bd : closure e ∩ bd S ⊆ {u} := by
    rintro x ⟨hxcl, hxbd⟩
    rw [hcl_e] at hxcl
    rcases hxcl with hxe | (rfl | hxu)
    · exact ((he.2.1 hxe).2 (hΓ ⟨hxbd, (he.2.1 hxe).1⟩)).elim
    · exact (hw_bd hxbd).elim
    · exact hxu
  exact ⟨hV', hE', hsub, hprop', hline, hU_union, hinter_U, hinter_bd⟩

/-- Deleting an internal leaf `w ∈ Γ.V \ bd S` and its unique incident edge `e ∈ Γ.E` preserves the
number of regions: `Γ.R.ncard = (Γ.span (Γ.V \ {w}) (Γ.E \ {e})).R.ncard`. -/
theorem deleteLeaf_R_ncard_eq (hS : IsClosedDiscSpace S) {Γ : Drawing S} (hΓ : Γ.IsProper)
    {e : Set S} (he : e ∈ Γ.E) {w u : S} (hlink : Γ.toGraph.IsLink e w u)
    (hw_ne : w ≠ u) (hw_bd : w ∉ bd S) (hleaf : ∀ f ∈ Γ.E, f ≠ e → w ∉ closure f) :
    Γ.R.ncard = (Γ.span (Γ.V \ {w}) (Γ.E \ {e})).R.ncard := by
  classical
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  set Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
  obtain ⟨_, _, hsub, hprop', hline, hU_union, hinter_U, hinter_bd⟩ :=
    deleteLeaf_props hΓ he hlink hw_ne hw_bd hleaf
  refine le_antisymm ?_ (disc_region_ncard_le_of_isSubdrawing hS hΓ hsub)
  have hfin' : Γ'.R.Finite := disc_finite_R hS Γ' hprop'
  let φ : Set S → Set S := fun r =>
    if hr : r ∈ Γ.R then
      connectedComponentIn (univ \ Γ'.U) (Classical.choose (region_nonempty hr))
    else ∅
  have hφ_eq : ∀ {r : Set S} (hr : r ∈ Γ.R),
      φ r = connectedComponentIn (univ \ Γ'.U) (Classical.choose (region_nonempty hr)) :=
    fun hr => dite_eq_left_of_eq_true (eq_true hr)
  have hφ_maps : MapsTo φ Γ.R Γ'.R := by
    intro r hr
    rw [hφ_eq hr]
    have hx := Classical.choose_spec (region_nonempty hr)
    have hxU : Classical.choose (region_nonempty hr) ∉ Γ'.U :=
      fun h => region_subset hr hx (hsub.U_subset h)
    exact ⟨_, ⟨mem_univ _, hxU⟩, rfl⟩
  have hφ_inj : InjOn φ Γ.R := by
    intro r₁ hr₁ r₂ hr₂ heq
    rw [hφ_eq hr₁, hφ_eq hr₂] at heq
    set x₁ := Classical.choose (region_nonempty hr₁)
    set x₂ := Classical.choose (region_nonempty hr₂)
    have hx₁ : x₁ ∈ r₁ := Classical.choose_spec (region_nonempty hr₁)
    have hx₂ : x₂ ∈ r₂ := Classical.choose_spec (region_nonempty hr₂)
    let r' := connectedComponentIn (univ \ Γ'.U) x₁
    have hr'_R : r' ∈ Γ'.R := by
      have hx₁U : x₁ ∉ Γ'.U := fun h => region_subset hr₁ hx₁ (hsub.U_subset h)
      exact ⟨x₁, ⟨mem_univ _, hx₁U⟩, rfl⟩
    have hr₁_sub : r₁ ⊆ r' :=
      (region_isPreconnected hr₁).subset_connectedComponentIn hx₁
        fun y hy => ⟨mem_univ _, fun hyU => region_subset hr₁ hy (hsub.U_subset hyU)⟩
    have hr₂_sub : r₂ ⊆ r' := by
      change r₂ ⊆ connectedComponentIn (univ \ Γ'.U) x₁
      rw [heq]
      exact (region_isPreconnected hr₂).subset_connectedComponentIn hx₂
        fun y hy => ⟨mem_univ _, fun hyU => region_subset hr₂ hy (hsub.U_subset hyU)⟩
    obtain ⟨a, ha₁, habd⟩ := open_sdiff_bd_nonempty hS (region_isOpen hr₁) ⟨x₁, hx₁⟩
    obtain ⟨b, hb₂, hbbd⟩ := open_sdiff_bd_nonempty hS (region_isOpen hr₂) ⟨x₂, hx₂⟩
    have ha_r' : a ∈ r' \ bd S := ⟨hr₁_sub ha₁, habd⟩
    have hb_r' : b ∈ r' \ bd S := ⟨hr₂_sub hb₂, hbbd⟩
    have hab' : b ∈ connectedComponentIn ((univ \ bd S) \ Γ'.U) a :=
      mem_connectedComponentIn_sdiff_bd_of_region hS hr'_R ha_r' hb_r'
    have ha_compl : a ∈ (univ \ bd S) \ (Γ'.U ∪ closure e) := by
      rw [hU_union]
      exact ⟨⟨mem_univ _, habd⟩, region_subset hr₁ ha₁⟩
    have hb_compl : b ∈ (univ \ bd S) \ (Γ'.U ∪ closure e) := by
      rw [hU_union]
      exact ⟨⟨mem_univ _, hbbd⟩, region_subset hr₂ hb₂⟩
    have hab : b ∈ connectedComponentIn ((univ \ bd S) \ (Γ'.U ∪ closure e)) a :=
      disc_sdiff_arc_connectedComponentIn hS Γ'.isClosed_U hline hinter_U hinter_bd
        ha_compl hb_compl hab'
    rw [hU_union] at hab
    have hb_r₁ : b ∈ r₁ := by
      have hr₁_eq : r₁ = connectedComponentIn (univ \ Γ.U) a :=
        region_eq_of_mem hr₁ ⟨a, ⟨mem_univ _, region_subset hr₁ ha₁⟩, rfl⟩ ha₁
          (mem_connectedComponentIn ⟨mem_univ _, region_subset hr₁ ha₁⟩)
      rw [hr₁_eq]
      exact connectedComponentIn_mono a (sdiff_subset_sdiff sdiff_subset subset_rfl) hab
    exact region_eq_of_mem hr₁ hr₂ hb_r₁ hb₂
  exact ncard_le_ncard_of_injOn φ hφ_maps hφ_inj hfin'

theorem deleteEdge_V (Γ : Drawing S) (e : Set S) : (Γ.deleteEdge e).V = Γ.V := by
  refine Subset.antisymm (deleteEdge_isSubdrawing Γ e).1 ?_
  intro x hx
  exact Or.inl ⟨hx, hx⟩

/-- If `Γ.E.Nonempty` and no edge `e ∈ Γ.E` is redundant, then `Γ` has an internal leaf
`w ∈ Γ.V \ bd S` with a unique incident edge `e ∈ Γ.E`. -/
theorem exists_internal_leaf_of_no_redundant_edge {Γ : Drawing S} (hE : Γ.E.Nonempty)
    (hno : ∀ e ∈ Γ.E, ∀ u v, Γ.toGraph.IsLink e u v →
      ¬ Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∧
      ¬ ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
         (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂)))) :
    ∃ e ∈ Γ.E, ∃ w u : S, w ≠ u ∧ w ∈ Γ.V \ bd S ∧ Γ.toGraph.IsLink e w u ∧
      ∀ f ∈ Γ.E, f ≠ e → w ∉ closure f := by
  classical
  have hne_ends : ∀ f ∈ Γ.E, ∀ u v, Γ.toGraph.IsLink f u v → u ≠ v := by
    intro f hf u v hl heq
    subst heq
    have hu' : u ∈ (Γ.deleteEdge f).V := by rw [deleteEdge_V]; exact hl.left_mem
    exact (hno f hf u u hl).1 ⟨.nil hu'⟩
  have hlink : ∀ f ∈ Γ.E, ∀ x ∈ Γ.V, x ∈ closure f → ∃ y, x ≠ y ∧ Γ.toGraph.IsLink f x y := by
    intro f hf x hxV hxf
    obtain ⟨γ, _, h0, h1, _, _, _, hl⟩ := exists_edge_param_isLink Γ hf
    have hne := hne_ends f hf (γ 0) (γ 1) hl
    have hx : x ∈ closure f ∩ Γ.V := ⟨hxf, hxV⟩
    rw [hl.2.2.2] at hx
    rcases hx with rfl | hx
    · exact ⟨γ 1, hne, hl⟩
    · rw [mem_singleton_iff.mp hx]
      exact ⟨γ 0, hne.symm, hl.symm⟩
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨γ₀, _, _, _, _, _, _, hlink₀_raw⟩ := exists_edge_param_isLink Γ he₀
  have hnot_both := (hno e₀ he₀ (γ₀ 0) (γ₀ 1) hlink₀_raw).2
  have hex_end : ∃ x₁ x₀ : S, Γ.toGraph.IsLink e₀ x₁ x₀ ∧
      ∀ b ∈ Γ.V ∩ bd S, ¬ Nonempty (GraphWalk (Γ.deleteEdge e₀).toGraph x₁ b) := by
    by_cases h1 : ∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e₀).toGraph (γ₀ 0) b₁)
    · refine ⟨γ₀ 1, γ₀ 0, hlink₀_raw.symm, fun b hb h2 => hnot_both ⟨h1, b, hb, h2⟩⟩
    · refine ⟨γ₀ 0, γ₀ 1, hlink₀_raw, fun b hb h2 => h1 ⟨b, hb, h2⟩⟩
  obtain ⟨x₁, x₀, hlink₀, hx₁_no_bd⟩ := hex_end
  have hx₁_ne_x₀ : x₁ ≠ x₀ := hne_ends e₀ he₀ x₁ x₀ hlink₀
  set Γ₀ := Γ.deleteEdge e₀
  have hsub₀ : Γ₀.IsSubdrawing Γ := deleteEdge_isSubdrawing Γ e₀
  have hV₀ : Γ₀.V = Γ.V := deleteEdge_V Γ e₀
  have hE₀ : Γ₀.E = Γ.E \ {e₀} := deleteEdge_E Γ e₀
  let P : ℕ → Prop := fun n =>
    ∃ (a : S) (W : GraphWalk Γ₀.toGraph a x₁), W.IsSimple ∧ W.length = n
  have hbound : ∀ n, P n → n ≤ Γ₀.finite_V.toFinset.card := by
    rintro n ⟨a, W, hW, rfl⟩
    have hsub : W.support.toFinset ⊆ Γ₀.finite_V.toFinset := by
      intro x hx
      simp only [List.mem_toFinset] at hx
      have : x ∈ Γ₀.V := W.mem_vertexSet_of_mem_support hx
      simpa using this
    have h₁ := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hW, length_support] at h₁
    omega
  have hx₁_V₀ : x₁ ∈ Γ₀.V := by rw [hV₀]; exact hlink₀.left_mem
  have hP0 : P 0 := ⟨x₁, .nil hx₁_V₀, List.nodup_singleton x₁, rfl⟩
  let N := Nat.findGreatest P Γ₀.finite_V.toFinset.card
  have hmax : ∀ n, P n → n ≤ N := fun n hn => Nat.le_findGreatest (hbound n hn) hn
  have hN : P N := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨a, W, hW, hlen⟩ := hN
  have ha_V : a ∈ Γ.V := by
    rw [← hV₀]
    exact W.mem_vertexSet_of_mem_support W.start_mem_support
  have ha_not_bd : a ∉ bd S := fun habd =>
    hx₁_no_bd a ⟨ha_V, habd⟩ ⟨W.reverse⟩
  cases W with
  | nil _ =>
    simp only [GraphWalk.length_nil] at hlen
    refine ⟨e₀, he₀, x₁, x₀, hx₁_ne_x₀, ⟨ha_V, ha_not_bd⟩, hlink₀, fun f hf hfe hxf => ?_⟩
    obtain ⟨y, hxy, hl_f⟩ := hlink f hf x₁ ha_V hxf
    have hf₀ : f ∈ Γ₀.E := by rw [hE₀]; exact ⟨hf, hfe⟩
    have hl_f₀ : Γ₀.toGraph.IsLink f x₁ y := (hsub₀.isLink_iff hf₀).mpr hl_f
    have hP1 : P 1 := by
      refine ⟨y, .cons hl_f₀.symm (.nil hl_f₀.left_mem), ?_, rfl⟩
      exact List.nodup_cons.mpr ⟨by simpa using hxy.symm, List.nodup_singleton _⟩
    have := hmax 1 hP1
    omega
  | @cons _ u _ e h r =>
    have he_Γ : e ∈ Γ.E := hsub₀.2 h.1
    have hl_e : Γ.toGraph.IsLink e a u := (hsub₀.isLink_iff h.1).mp h
    have hau : a ≠ u := hne_ends e he_Γ a u hl_e
    have hnd := List.nodup_cons.mp hW
    refine ⟨e, he_Γ, a, u, hau, ⟨ha_V, ha_not_bd⟩, hl_e, fun f hf hfe haf => ?_⟩
    by_cases hfe₀ : f = e₀
    · subst f
      have ha_pair : a ∈ ({x₁, x₀} : Set S) := hlink₀.2.2.2 ▸ ⟨haf, ha_V⟩
      rcases ha_pair with rfl | ha_x₀
      · exact hnd.1 r.end_mem_support
      · rw [mem_singleton_iff.mp ha_x₀] at h
        exact (hno e₀ he₀ x₁ x₀ hlink₀).1 ⟨(GraphWalk.cons h r).reverse⟩
    · obtain ⟨y, hay, hl_f⟩ := hlink f hf a ha_V haf
      have hf₀ : f ∈ Γ₀.E := by rw [hE₀]; exact ⟨hf, hfe₀⟩
      have hl_f₀ : Γ₀.toGraph.IsLink f a y := (hsub₀.isLink_iff hf₀).mpr hl_f
      by_cases hy : y ∈ (GraphWalk.cons h r).support
      · obtain ⟨W₁, W₂, hsplit⟩ := (GraphWalk.cons h r).exists_append_of_mem hy
        have hfW₁ : f ∉ W₁.edges := by
          intro hfW₁
          have h₁ : f ∈ (GraphWalk.cons h r).edges := by
            rw [hsplit, GraphWalk.edges_append]
            exact List.mem_append_left _ hfW₁
          rcases List.mem_cons.mp h₁ with h₂ | h₂
          · exact hfe h₂
          · exact hnd.1 (r.left_mem_support_of_mem_edges h₂ hl_f₀)
        obtain ⟨W₁', hsupp₁, hed₁⟩ := hsub₀.exists_walk_up W₁
        obtain ⟨W₁'', -, -⟩ := (deleteEdge_isSubdrawing Γ f).exists_walk_down W₁'
          (fun x hx => by
            rw [deleteEdge_V]
            exact W₁'.mem_vertexSet_of_mem_support hx)
          (fun g hg => by
            rw [deleteEdge_E]
            refine ⟨mem_E_of_mem_edges W₁' hg, ?_⟩
            intro hgf
            exact hfW₁ (mem_singleton_iff.mp hgf ▸ hed₁ ▸ hg))
        exact (hno f hf a y hl_f).1 ⟨W₁''⟩
      · have hPN1 : P (N + 1) :=
          ⟨y, .cons hl_f₀.symm (.cons h r), List.nodup_cons.mpr ⟨hy, hW⟩, by
            simp only [GraphWalk.length_cons] at hlen ⊢
            omega⟩
        have := hmax (N + 1) hPN1
        omega

/-! ## 4. Region-Counting Bounds (Euler's Formula on a Disc) -/

omit [T2Space S] in
/-- If `Γ` is a proper drawing on `S` with `Γ.E = ∅`, then `Γ.R.ncard = 1`. -/
theorem R_ncard_eq_one_of_E_empty (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hΓ : Γ.IsProper) (hE : Γ.E = ∅) : Γ.R.ncard = 1 := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ_disc⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ_disc.surjective.connectedSpace
    φ_disc.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ_disc⟩
  obtain ⟨p, -, hp⟩ :=
    disc_exists_notMem_U hS hΓ isOpen_univ ⟨φ_disc ⟨0, by simp [ClosedUnitDisc]⟩, mem_univ _⟩
  have hr₀ : connectedComponentIn (univ \ Γ.U) p ∈ Γ.R := ⟨p, ⟨mem_univ p, hp⟩, rfl⟩
  have hU : Γ.U = Γ.V := by
    rw [Γ.U_eq, hE]
    simp
  have hc : IsPreconnected (univ \ Γ.U) := by
    rw [hU]
    exact disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ Γ.finite_V
  have hsub : Γ.R.Subsingleton := fun r₁ h₁ r₂ h₂ => by
    obtain ⟨x, hx⟩ := region_nonempty h₁
    obtain ⟨y, hy⟩ := region_nonempty h₂
    refine region_eq_of_mem h₁ h₂ (subset_region h₁ hc ?_ ⟨mem_univ _, region_subset h₁ hx⟩ hx
      ⟨mem_univ _, region_subset h₂ hy⟩) hy
    exact disjoint_left.mpr fun q hq => hq.2
  have hR_eq : Γ.R = {connectedComponentIn (univ \ Γ.U) p} :=
    Subset.antisymm (fun r hr => mem_singleton_iff.mpr (hsub hr hr₀))
      (singleton_subset_iff.mpr hr₀)
  rw [hR_eq, ncard_singleton]

/-- Lower bound on `Γ.V.ncard + Γ.R.ncard` for any proper drawing `Γ` on a closed disc space `S`. -/
theorem euler_lower_bound (hS : IsClosedDiscSpace S) {Γ : Drawing S} (hΓ : Γ.IsProper) :
    Γ.E.ncard + (Γ.V ∩ bd S).ncard + 1 ≤ Γ.V.ncard + Γ.R.ncard ∧
    (Γ.V.Nonempty → Γ.E.ncard + 2 ≤ Γ.V.ncard + Γ.R.ncard) := by
  classical
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    rcases Γ.E.eq_empty_or_nonempty with hE_emp | hE_ne
    · have hE0 : Γ.E.ncard = 0 := by rw [hE_emp, ncard_empty]
      have hR1 : Γ.R.ncard = 1 := R_ncard_eq_one_of_E_empty hS hΓ hE_emp
      have hVbd : (Γ.V ∩ bd S).ncard ≤ Γ.V.ncard :=
        ncard_le_ncard inter_subset_left Γ.finite_V
      refine ⟨by omega, fun hV => ?_⟩
      have hV1 : 1 ≤ Γ.V.ncard := (ncard_pos Γ.finite_V).mpr hV
      omega
    · by_cases hred : ∃ e ∈ Γ.E, ∃ u v, Γ.toGraph.IsLink e u v ∧
        (Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∨
         ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
          (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))))
      · obtain ⟨e, he, u, v, hlink, hred_e⟩ := hred
        let Γ' := Γ.deleteEdge e
        have hΓ' : Γ'.IsProper := deleteEdge_isProper hΓ e
        have hV' : Γ'.V = Γ.V := deleteEdge_V Γ e
        have hE' : Γ'.E = Γ.E \ {e} := deleteEdge_E Γ e
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hlt : Γ'.E.ncard < n := by omega
        have hR_eq : Γ.R.ncard = Γ'.R.ncard + 1 :=
          deleteEdge_R_ncard_eq_add_one_of_redundant hS hΓ he hlink hred_e
        obtain ⟨ih1, ih2⟩ := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' rfl
        rw [hV'] at ih1 ih2
        refine ⟨by omega, fun hV => ?_⟩
        have := ih2 hV
        omega
      · have hno : ∀ e ∈ Γ.E, ∀ u v, Γ.toGraph.IsLink e u v →
            ¬ Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∧
            ¬ ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
               (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))) := by
          intro e he u v hl
          exact ⟨fun h1 => hred ⟨e, he, u, v, hl, Or.inl h1⟩,
            fun h2 => hred ⟨e, he, u, v, hl, Or.inr h2⟩⟩
        obtain ⟨e, he, w, u, hw_ne, ⟨hw_V, hw_bd⟩, hlink, hleaf⟩ :=
          exists_internal_leaf_of_no_redundant_edge hE_ne hno
        let Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
        obtain ⟨hV', hE', _, hΓ', _, _, _, _⟩ :=
          deleteLeaf_props hΓ he hlink hw_ne hw_bd hleaf
        have hV_card : Γ'.V.ncard + 1 = Γ.V.ncard := by
          rw [hV']
          exact ncard_sdiff_singleton_add_one hw_V Γ.finite_V
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hVbd_eq : Γ'.V ∩ bd S = Γ.V ∩ bd S := by
          rw [hV']
          ext x
          simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
          exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun hxw => hw_bd (hxw ▸ h.2)⟩, h.2⟩⟩
        have hR_eq : Γ.R.ncard = Γ'.R.ncard :=
          deleteLeaf_R_ncard_eq hS hΓ he hlink hw_ne hw_bd hleaf
        have hlt : Γ'.E.ncard < n := by omega
        obtain ⟨ih1, ih2⟩ := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' rfl
        have hu_V' : u ∈ Γ'.V := by
          rw [hV']
          exact ⟨hlink.right_mem, hw_ne.symm⟩
        have ih2' := ih2 ⟨u, hu_V'⟩
        rw [hVbd_eq] at ih1
        omega

/-- Retracting a walk along a leaf edge `e` from `w` to `u` produces a walk in
`Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})`. -/
theorem deleteLeaf_walk {Γ : Drawing S} (hΓ : Γ.IsProper) {e : Set S} (he : e ∈ Γ.E)
    {w u : S} (hlink : Γ.toGraph.IsLink e w u) (hw_ne : w ≠ u) (hw_bd : w ∉ bd S)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → w ∉ closure f) {x y : S}
    (hx : x ∈ Γ.V \ {w}) (hy : y ∈ Γ.V \ {w})
    (W : GraphWalk Γ.toGraph x y) :
    Nonempty (GraphWalk (Γ.span (Γ.V \ {w}) (Γ.E \ {e})).toGraph x y) := by
  classical
  let Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
  obtain ⟨hV', hE', hsub, _, _, _, _, _⟩ :=
    deleteLeaf_props hΓ he hlink hw_ne hw_bd hleaf
  let proj : S → S := fun z => if z = w then u else z
  have hu_V' : u ∈ Γ'.V := by rw [hV']; exact ⟨hlink.right_mem, hw_ne.symm⟩
  have hproj_mem : ∀ z ∈ Γ.V, proj z ∈ Γ'.V := by
    intro z hz
    dsimp [proj]
    split_ifs with hzw
    · exact hu_V'
    · rw [hV']; exact ⟨hz, hzw⟩
  have hwalk : ∀ {a b : S}, GraphWalk Γ.toGraph a b →
      Nonempty (GraphWalk Γ'.toGraph (proj a) (proj b)) := by
    intro a b W₀
    induction W₀ with
    | @nil z hz =>
      exact ⟨.nil (hproj_mem z hz)⟩
    | @cons a z b f hl rest ih =>
      obtain ⟨W_rest⟩ := ih
      by_cases hfe : f = e
      · subst f
        have hpair : ({a, z} : Set S) = {w, u} := hl.2.2.2.symm.trans hlink.2.2.2
        have ha_wu : a = w ∨ a = u := by
          have : a ∈ ({w, u} : Set S) := hpair ▸ mem_insert a {z}
          simpa using this
        have hz_wu : z = w ∨ z = u := by
          have : z ∈ ({w, u} : Set S) := hpair ▸ mem_insert_of_mem a rfl
          simpa using this
        have hpa : proj a = u := by rcases ha_wu with rfl | rfl <;> simp [proj]
        have hpz : proj z = u := by rcases hz_wu with rfl | rfl <;> simp [proj]
        rw [hpa, ← hpz]
        exact ⟨W_rest⟩
      · have haw : a ≠ w := fun h => hleaf f hl.1 hfe (h ▸ (hl.2.2.2 ▸ mem_insert a {z}).1)
        have hzw : z ≠ w := fun h =>
          hleaf f hl.1 hfe (h ▸ (hl.2.2.2 ▸ mem_insert_of_mem a (mem_singleton z)).1)
        have hpa : proj a = a := by simp [proj, haw]
        have hpz : proj z = z := by simp [proj, hzw]
        have hf' : f ∈ Γ'.E := by rw [hE']; exact ⟨hl.1, hfe⟩
        have hl' : Γ'.toGraph.IsLink f a z := (hsub.isLink_iff hf').mpr hl
        rw [hpa]
        rw [hpz] at W_rest
        exact ⟨.cons hl' W_rest⟩
  have hpx : proj x = x := by simp [proj, mem_singleton_iff.not.mp hx.2]
  have hpy : proj y = y := by simp [proj, mem_singleton_iff.not.mp hy.2]
  obtain ⟨W'⟩ := hwalk W
  rw [hpx, hpy] at W'
  exact ⟨W'⟩

/-- Deleting a redundant edge `e` whose ends `u, v` are joined by a walk in `(Γ.deleteEdge
e).toGraph`
preserves connectivity of any walk in `Γ.toGraph`. -/
theorem deleteEdge_walk_of_ends_reachable {Γ : Drawing S} {e : Set S} {u v : S}
    (hlink : Γ.toGraph.IsLink e u v)
    (huv : Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v))
    {x y : S} (W : GraphWalk Γ.toGraph x y) :
    Nonempty (GraphWalk (Γ.deleteEdge e).toGraph x y) := by
  obtain ⟨P⟩ := huv
  let Γ' := Γ.deleteEdge e
  have hsub : Γ'.IsSubdrawing Γ := deleteEdge_isSubdrawing Γ e
  have hV' : Γ'.V = Γ.V := deleteEdge_V Γ e
  have hE' : Γ'.E = Γ.E \ {e} := deleteEdge_E Γ e
  induction W with
  | @nil z hz =>
    have hz' : z ∈ Γ'.toGraph.vertexSet := by change z ∈ Γ'.V; rw [hV']; exact hz
    exact ⟨.nil hz'⟩
  | @cons a z b f hl rest ih =>
    obtain ⟨W_rest⟩ := ih
    by_cases hfe : f = e
    · subst f
      have hpair : ({a, z} : Set S) = {u, v} := hl.2.2.2.symm.trans hlink.2.2.2
      have ha_uv : a = u ∨ a = v := by
        have : a ∈ ({u, v} : Set S) := hpair ▸ mem_insert a {z}
        simpa using this
      have hz_uv : z = u ∨ z = v := by
        have : z ∈ ({u, v} : Set S) := hpair ▸ mem_insert_of_mem a rfl
        simpa using this
      rcases ha_uv with rfl | rfl <;> rcases hz_uv with rfl | rfl
      · exact ⟨W_rest⟩
      · exact ⟨P.append W_rest⟩
      · exact ⟨P.reverse.append W_rest⟩
      · exact ⟨W_rest⟩
    · have hf' : f ∈ Γ'.E := by rw [hE']; exact ⟨hl.1, hfe⟩
      have hl' : Γ'.toGraph.IsLink f a z := (hsub.isLink_iff hf').mpr hl
      exact ⟨.cons hl' W_rest⟩

/-- Upper bound on `Γ.V.ncard + Γ.R.ncard` when `Γ` is connected and `Γ.V ∩ bd S = ∅`. -/
theorem euler_upper_bound_of_bd_empty (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hΓ : Γ.IsProper) (hConn : IsGraphConnected Γ.toGraph) (hbd : Γ.V ∩ bd S = ∅) :
    Γ.V.ncard + Γ.R.ncard ≤ Γ.E.ncard + 2 := by
  classical
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    rcases Γ.E.eq_empty_or_nonempty with hE_emp | hE_ne
    · have hE0 : Γ.E.ncard = 0 := by rw [hE_emp, ncard_empty]
      have hR1 : Γ.R.ncard = 1 := R_ncard_eq_one_of_E_empty hS hΓ hE_emp
      obtain ⟨v₀, hv₀⟩ := hConn.1
      have hV_sub : Γ.V ⊆ {v₀} := by
        intro v hv
        obtain ⟨W⟩ := hConn.2 v hv v₀ hv₀
        cases W with
        | nil _ => rfl
        | cons hl _ =>
          have he : _ ∈ Γ.E := hl.1
          rw [hE_emp] at he
          exact he.elim
      have hV1 : Γ.V.ncard ≤ 1 := (ncard_le_ncard hV_sub (finite_singleton v₀)).trans
        (by rw [ncard_singleton])
      omega
    · by_cases hred : ∃ e ∈ Γ.E, ∃ u v, Γ.toGraph.IsLink e u v ∧
        (Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∨
         ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
          (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))))
      · obtain ⟨e, he, u, v, hlink, hred_e⟩ := hred
        have huv : Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) := by
          rcases hred_e with h1 | ⟨⟨b₁, hb₁, _⟩, _⟩
          · exact h1
          · rw [hbd] at hb₁; exact hb₁.elim
        let Γ' := Γ.deleteEdge e
        have hΓ' : Γ'.IsProper := deleteEdge_isProper hΓ e
        have hV' : Γ'.V = Γ.V := deleteEdge_V Γ e
        have hE' : Γ'.E = Γ.E \ {e} := deleteEdge_E Γ e
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hConn' : IsGraphConnected Γ'.toGraph := by
          refine ⟨by change Γ'.V.Nonempty; rw [hV']; exact hConn.1, fun x hx y hy => ?_⟩
          rw [show Γ'.toGraph.vertexSet = Γ.V from hV'] at hx hy
          obtain ⟨W⟩ := hConn.2 x hx y hy
          exact deleteEdge_walk_of_ends_reachable hlink huv W
        have hbd' : Γ'.V ∩ bd S = ∅ := by rw [hV']; exact hbd
        have hR_le : Γ.R.ncard ≤ Γ'.R.ncard + 1 := deleteEdge_R_ncard_le hS hΓ he
        have hlt : Γ'.E.ncard < n := by omega
        have ih' := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' hConn' hbd' rfl
        rw [hV'] at ih'
        omega
      · have hno : ∀ e ∈ Γ.E, ∀ u v, Γ.toGraph.IsLink e u v →
            ¬ Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∧
            ¬ ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
               (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))) := by
          intro e he u v hl
          exact ⟨fun h1 => hred ⟨e, he, u, v, hl, Or.inl h1⟩,
            fun h2 => hred ⟨e, he, u, v, hl, Or.inr h2⟩⟩
        obtain ⟨e, he, w, u, hw_ne, ⟨hw_V, hw_bd⟩, hlink, hleaf⟩ :=
          exists_internal_leaf_of_no_redundant_edge hE_ne hno
        let Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
        obtain ⟨hV', hE', _, hΓ', _, _, _, _⟩ :=
          deleteLeaf_props hΓ he hlink hw_ne hw_bd hleaf
        have hV_card : Γ'.V.ncard + 1 = Γ.V.ncard := by
          rw [hV']
          exact ncard_sdiff_singleton_add_one hw_V Γ.finite_V
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hu_V' : u ∈ Γ'.V := by rw [hV']; exact ⟨hlink.right_mem, hw_ne.symm⟩
        have hConn' : IsGraphConnected Γ'.toGraph := by
          refine ⟨⟨u, hu_V'⟩, fun x hx y hy => ?_⟩
          change x ∈ Γ'.V at hx
          change y ∈ Γ'.V at hy
          rw [hV'] at hx hy
          obtain ⟨W⟩ := hConn.2 x hx.1 y hy.1
          exact deleteLeaf_walk hΓ he hlink hw_ne hw_bd hleaf hx hy W
        have hbd' : Γ'.V ∩ bd S = ∅ :=
          subset_empty_iff.mp ((inter_subset_inter_left _ (hV' ▸ sdiff_subset)).trans
            (subset_empty_iff.mpr hbd))
        have hR_eq : Γ.R.ncard = Γ'.R.ncard :=
          deleteLeaf_R_ncard_eq hS hΓ he hlink hw_ne hw_bd hleaf
        have hlt : Γ'.E.ncard < n := by omega
        have ih' := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' hConn' hbd' rfl
        omega

/-- Upper bound on `Γ.V.ncard + Γ.R.ncard` when every vertex of `Γ` can reach `Γ.V ∩ bd S`. -/
theorem euler_upper_bound_of_reach_bd (hS : IsClosedDiscSpace S) {Γ : Drawing S}
    (hΓ : Γ.IsProper)
    (hreach : ∀ v ∈ Γ.V, ∃ b ∈ Γ.V ∩ bd S, Nonempty (GraphWalk Γ.toGraph v b)) :
    Γ.V.ncard + Γ.R.ncard ≤ Γ.E.ncard + (Γ.V ∩ bd S).ncard + 1 := by
  classical
  induction hn : Γ.E.ncard using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    rcases Γ.E.eq_empty_or_nonempty with hE_emp | hE_ne
    · have hE0 : Γ.E.ncard = 0 := by rw [hE_emp, ncard_empty]
      have hR1 : Γ.R.ncard = 1 := R_ncard_eq_one_of_E_empty hS hΓ hE_emp
      have hV_sub : Γ.V ⊆ Γ.V ∩ bd S := by
        intro v hv
        obtain ⟨b, hb, ⟨W⟩⟩ := hreach v hv
        cases W with
        | nil _ => exact hb
        | cons hl _ =>
          have he : _ ∈ Γ.E := hl.1
          rw [hE_emp] at he
          exact he.elim
      have hV_le : Γ.V.ncard ≤ (Γ.V ∩ bd S).ncard :=
        ncard_le_ncard hV_sub (Γ.finite_V.subset inter_subset_left)
      omega
    · by_cases hred : ∃ e ∈ Γ.E, ∃ u v, Γ.toGraph.IsLink e u v ∧
        (Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∨
         ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
          (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))))
      · obtain ⟨e, he, u, v, hlink, hred_e⟩ := hred
        let Γ' := Γ.deleteEdge e
        have hsub : Γ'.IsSubdrawing Γ := deleteEdge_isSubdrawing Γ e
        have hΓ' : Γ'.IsProper := deleteEdge_isProper hΓ e
        have hV' : Γ'.V = Γ.V := deleteEdge_V Γ e
        have hE' : Γ'.E = Γ.E \ {e} := deleteEdge_E Γ e
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hreach' : ∀ x ∈ Γ'.V, ∃ b ∈ Γ'.V ∩ bd S, Nonempty (GraphWalk Γ'.toGraph x b) := by
          rw [hV']
          rcases hred_e with huv | ⟨hu_bd, hv_bd⟩
          · intro x hx
            obtain ⟨b, hb, ⟨W⟩⟩ := hreach x hx
            exact ⟨b, hb, deleteEdge_walk_of_ends_reachable hlink huv W⟩
          · have hwalk_bd : ∀ {a c : S}, GraphWalk Γ.toGraph a c →
                (∃ b ∈ Γ.V ∩ bd S, Nonempty (GraphWalk Γ'.toGraph c b)) →
                ∃ b ∈ Γ.V ∩ bd S, Nonempty (GraphWalk Γ'.toGraph a b) := by
              intro a c W₀ hc
              induction W₀ with
              | nil _ => exact hc
              | @cons a z c f hl rest ih_w =>
                have hz := ih_w hc
                by_cases hfe : f = e
                · subst f
                  have hpair : ({a, z} : Set S) = {u, v} := hl.2.2.2.symm.trans hlink.2.2.2
                  have ha_uv : a = u ∨ a = v := by
                    have : a ∈ ({u, v} : Set S) := hpair ▸ mem_insert a {z}
                    simpa using this
                  rcases ha_uv with rfl | rfl
                  · exact hu_bd
                  · exact hv_bd
                · obtain ⟨b, hb, ⟨W_zb⟩⟩ := hz
                  have hf' : f ∈ Γ'.E := by rw [hE']; exact ⟨hl.1, hfe⟩
                  have hl' : Γ'.toGraph.IsLink f a z := (hsub.isLink_iff hf').mpr hl
                  exact ⟨b, hb, ⟨.cons hl' W_zb⟩⟩
            intro x hx
            obtain ⟨b, hb, ⟨W⟩⟩ := hreach x hx
            have hb_V' : b ∈ Γ'.toGraph.vertexSet := by change b ∈ Γ'.V; rw [hV']; exact hb.1
            exact hwalk_bd W ⟨b, hb, ⟨.nil hb_V'⟩⟩
        have hR_le : Γ.R.ncard ≤ Γ'.R.ncard + 1 := deleteEdge_R_ncard_le hS hΓ he
        have hlt : Γ'.E.ncard < n := by omega
        have ih' := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' hreach' rfl
        rw [hV'] at ih'
        omega
      · have hno : ∀ e ∈ Γ.E, ∀ u v, Γ.toGraph.IsLink e u v →
            ¬ Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u v) ∧
            ¬ ((∃ b₁ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph u b₁)) ∧
               (∃ b₂ ∈ Γ.V ∩ bd S, Nonempty (GraphWalk (Γ.deleteEdge e).toGraph v b₂))) := by
          intro e he u v hl
          exact ⟨fun h1 => hred ⟨e, he, u, v, hl, Or.inl h1⟩,
            fun h2 => hred ⟨e, he, u, v, hl, Or.inr h2⟩⟩
        obtain ⟨e, he, w, u, hw_ne, ⟨hw_V, hw_bd⟩, hlink, hleaf⟩ :=
          exists_internal_leaf_of_no_redundant_edge hE_ne hno
        let Γ' := Γ.span (Γ.V \ {w}) (Γ.E \ {e})
        obtain ⟨hV', hE', _, hΓ', _, _, _, _⟩ :=
          deleteLeaf_props hΓ he hlink hw_ne hw_bd hleaf
        have hV_card : Γ'.V.ncard + 1 = Γ.V.ncard := by
          rw [hV']
          exact ncard_sdiff_singleton_add_one hw_V Γ.finite_V
        have hE_card : Γ'.E.ncard + 1 = Γ.E.ncard := by
          rw [hE']
          exact ncard_sdiff_singleton_add_one he Γ.finite_edges
        have hVbd_eq : Γ'.V ∩ bd S = Γ.V ∩ bd S := by
          rw [hV']
          ext x
          simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
          exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun hxw => hw_bd (hxw ▸ h.2)⟩, h.2⟩⟩
        have hreach' : ∀ x ∈ Γ'.V, ∃ b ∈ Γ'.V ∩ bd S, Nonempty (GraphWalk Γ'.toGraph x b) := by
          intro x hx
          rw [hV'] at hx
          obtain ⟨b, hb, ⟨W⟩⟩ := hreach x hx.1
          have hb' : b ∈ Γ'.V ∩ bd S := by rwa [hVbd_eq]
          have hb_diff : b ∈ Γ.V \ {w} := by rw [← hV']; exact hb'.1
          exact ⟨b, hb', deleteLeaf_walk hΓ he hlink hw_ne hw_bd hleaf hx hb_diff W⟩
        have hR_eq : Γ.R.ncard = Γ'.R.ncard :=
          deleteLeaf_R_ncard_eq hS hΓ he hlink hw_ne hw_bd hleaf
        have hlt : Γ'.E.ncard < n := by omega
        have ih' := ih Γ'.E.ncard hlt (Γ := Γ') hΓ' hreach' rfl
        rw [hVbd_eq] at ih'
        omega

/-! ## 5. Dual Region Separation of Primal Vertices -/

omit [T2Space S] in
/-- On any `O`-arc `C`, if `U` is a dual point set for `(C, V)` with `V ⊆ C` finite, then
`U.ncard = V.ncard`. -/
theorem ncard_eq_of_isDualPointSet {C V U : Set S} (hC : IsOArc C) (hV_sub : V ⊆ C)
    (hV_fin : V.Finite) (hU : IsDualPointSet C V U) : U.ncard = V.ncard := by
  classical
  have hle_univ : ∀ {V₀ U₀ : Set Circle}, V₀.Finite →
      IsDualPointSet (univ : Set Circle) V₀ U₀ → V₀.ncard ≤ U₀.ncard := by
    intro V₀ U₀ hV₀ hU₀
    have hU₀_fin : U₀.Finite := finite_of_isDualPointSet_univ hV₀ hU₀
    rcases V₀.eq_empty_or_nonempty with rfl | hne
    · rw [ncard_empty]
      exact Nat.zero_le _
    · have hex : ∀ v : Circle, ∃ u : Circle, v ∈ V₀ → U₀ ∩ nextSegment V₀ v = {u} := by
        intro v
        by_cases hv : v ∈ V₀
        · obtain ⟨u, hu⟩ := exists_unique_mem_nextSegment_of_isDualPointSet hV₀ hU₀ hv
          exact ⟨u, fun _ => hu⟩
        · exact ⟨v, fun h => (hv h).elim⟩
      choose f hf using hex
      have hf_maps : MapsTo f V₀ U₀ := by
        intro v hv
        have : f v ∈ U₀ ∩ nextSegment V₀ v := by rw [hf v hv]; exact mem_singleton _
        exact this.1
      have hf_inj : InjOn f V₀ := by
        intro v₁ hv₁ v₂ hv₂ heq
        have h1 : f v₁ ∈ U₀ ∩ nextSegment V₀ v₁ := by rw [hf v₁ hv₁]; exact mem_singleton _
        have h2 : f v₁ ∈ U₀ ∩ nextSegment V₀ v₂ := by rw [heq, hf v₂ hv₂]; exact mem_singleton _
        have hu_compl : f v₁ ∈ V₀ᶜ := ((hU₀.2 hne).1 h1.1).2
        obtain ⟨v, _, huniq⟩ := exists_unique_nextSegment_of_mem_compl hV₀ hne hu_compl
        exact (huniq v₁ ⟨hv₁, h1.2⟩).trans (huniq v₂ ⟨hv₂, h2.2⟩).symm
      exact ncard_le_ncard_of_injOn f hf_maps hf_inj hU₀_fin
  have hU_sub : U ⊆ C := (isDualPointSet_subset_diff hU).trans sdiff_subset
  obtain ⟨φ⟩ := hC
  have hinj := injective_oArcMap φ
  let V₀ := oArcMap φ ⁻¹' V
  let U₀ := oArcMap φ ⁻¹' U
  have hV_eq : oArcMap φ '' V₀ = V :=
    image_preimage_eq_of_subset (hV_sub.trans (range_oArcMap φ).symm.subset)
  have hU_eq : oArcMap φ '' U₀ = U :=
    image_preimage_eq_of_subset (hU_sub.trans (range_oArcMap φ).symm.subset)
  have hV₀_fin : V₀.Finite := Finite.of_finite_image (by rwa [hV_eq]) hinj.injOn
  have hU₀ : IsDualPointSet (univ : Set Circle) V₀ U₀ := by
    rwa [← isDualPointSet_oArcMap_iff φ, hV_eq, hU_eq]
  have hU₀_fin : U₀.Finite := finite_of_isDualPointSet_univ hV₀_fin hU₀
  have hU₀_symm : IsDualPointSet (univ : Set Circle) U₀ V₀ :=
    isDualPointSet_univ_symm hV₀_fin hU₀
  have hcard_eq : U₀.ncard = V₀.ncard :=
    le_antisymm (hle_univ hU₀_fin hU₀_symm) (hle_univ hV₀_fin hU₀)
  rw [← hU_eq, ← hV_eq, hinj.injOn.ncard_image, hinj.injOn.ncard_image, hcard_eq]

/-- If `G` is a connected proper drawing on a closed disc space `S` and `G_dual` satisfies all
conditions of `IsDiscDualDrawing G G_dual` except possibly vertex-region injectivity on `G.V`, then
distinct vertices `v₁ ≠ v₂ ∈ G.V` lie in distinct regions of `G_dual`. -/
theorem dual_region_injective_on_V (hS : IsClosedDiscSpace S) {G G_dual : Drawing S}
    (hG : G.IsProper) (hConn : IsGraphConnected G.toGraph)
    (hDual_prop : G_dual.IsProper)
    (hDual_V_unique : ∀ r ∈ G.R, ∃! w, w ∈ r ∧ w ∈ G_dual.V)
    (hDual_V_in_R : ∀ w ∈ G_dual.V, ∃ r ∈ G.R, w ∈ r)
    (hDual_bd : IsDualPointSet (bd S) (G.V ∩ bd S) (G_dual.V ∩ bd S))
    (edgeEquiv : G.E ≃ G_dual.E)
    (hedge : ∀ e : G.E,
      ((edgeEquiv e).1 ∩ G.U = (edgeEquiv e).1 ∩ e.1) ∧
      (e.1 ∩ G_dual.U = e.1 ∩ (edgeEquiv e).1) ∧
      ((edgeEquiv e).1 ∩ e.1).ncard = 1 ∧
      (∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident (edgeEquiv e).1 r' → (r' ∩ e.1).Nonempty)) :
    ∀ v₁ ∈ G.V, ∀ v₂ ∈ G.V,
      connectedComponentIn (univ \ G_dual.U) v₁ = connectedComponentIn (univ \ G_dual.U) v₂ →
        v₁ = v₂ := by
  classical
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  obtain ⟨φ_disc⟩ := hS
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected ⟨0, by simp⟩)
  have : PreconnectedSpace S := (φ_disc.surjective.connectedSpace
    φ_disc.continuous).toPreconnectedSpace
  have hS : IsClosedDiscSpace S := ⟨φ_disc⟩
  have hdisj_V_U : Disjoint G.V G_dual.U := by
    refine disjoint_left.mpr fun v hv hvU => ?_
    by_cases hvVd : v ∈ G_dual.V
    · obtain ⟨r, hr, hvr⟩ := hDual_V_in_R v hvVd
      exact region_subset hr hvr (G.V_subset_U hv)
    · obtain ⟨e', he', hve'⟩ := G_dual.exists_edge_of_mem hvU hvVd
      let e := edgeEquiv.symm ⟨e', he'⟩
      have he_eq : (edgeEquiv e).1 = e' :=
        congrArg Subtype.val (edgeEquiv.apply_symm_apply ⟨e', he'⟩)
      have hmem : v ∈ (edgeEquiv e).1 ∩ G.U := ⟨he_eq ▸ hve', G.V_subset_U hv⟩
      rw [(hedge e).1] at hmem
      exact (e.2.2.1 hmem.2).2 hv
  let compV : S → Set S := fun v => connectedComponentIn (univ \ G_dual.U) v
  have hcompV_mem : ∀ {v : S}, v ∈ G.V → compV v ∈ G_dual.R ∧ v ∈ compV v := by
    intro v hv
    have hv_compl : v ∈ univ \ G_dual.U := ⟨mem_univ v, disjoint_left.mp hdisj_V_U hv⟩
    exact ⟨⟨v, hv_compl, rfl⟩, mem_connectedComponentIn hv_compl⟩
  have hsurj_R : G_dual.R ⊆ compV '' G.V := by
    intro r_dual hr_dual
    by_cases hex : ∃ e' ∈ G_dual.E, G_dual.EdgeRegionIncident e' r_dual
    · obtain ⟨e', he', hinc⟩ := hex
      let e := edgeEquiv.symm ⟨e', he'⟩
      have he_eq : (edgeEquiv e).1 = e' :=
        congrArg Subtype.val (edgeEquiv.apply_symm_apply ⟨e', he'⟩)
      obtain ⟨_, he2, he3, he4⟩ := hedge e
      rw [he_eq] at he2 he3 he4
      obtain ⟨γ, hγ, h0, h1, hinj, himg, _, _⟩ := exists_edge_param_isLink G e.2
      obtain ⟨p, hp_eq⟩ := ncard_eq_one.mp he3
      have hp_mem : p ∈ e' ∩ e.1 := by rw [hp_eq]; exact mem_singleton p
      have hp_e' : p ∈ e' := hp_mem.1
      have hp_e : p ∈ e.1 := hp_mem.2
      have he_GdU : e.1 ∩ G_dual.U = {p} := by rw [he2, inter_comm, hp_eq]
      rw [← himg] at hp_e
      obtain ⟨t₀, ht₀, rfl⟩ := hp_e
      have hIco_sub : γ '' Ico 0 t₀ ⊆ univ \ G_dual.U := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨mem_univ _, fun htU => ?_⟩
        by_cases ht0 : t = 0
        · subst ht0; exact disjoint_left.mp hdisj_V_U h0 htU
        · have ht_Ioo : t ∈ Ioo (0 : unitInterval) 1 :=
            ⟨unitInterval.pos_iff_ne_zero.mpr ht0, ht.2.trans ht₀.2⟩
          have hmem : γ t ∈ e.1 ∩ G_dual.U := ⟨himg ▸ mem_image_of_mem γ ht_Ioo, htU⟩
          rw [he_GdU, mem_singleton_iff] at hmem
          exact ht.2.ne (hinj ht_Ioo ht₀ hmem)
      have hIco_comp : γ '' Ico 0 t₀ ⊆ compV (γ 0) :=
        (isPreconnected_Ico.image γ hγ.continuousOn).subset_connectedComponentIn
          ⟨0, left_mem_Ico.mpr ht₀.1, rfl⟩ hIco_sub
      have hIoc_sub : γ '' Ioc t₀ 1 ⊆ univ \ G_dual.U := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨mem_univ _, fun htU => ?_⟩
        by_cases ht1 : t = 1
        · subst ht1; exact disjoint_left.mp hdisj_V_U h1 htU
        · have ht_Ioo : t ∈ Ioo (0 : unitInterval) 1 :=
            ⟨ht₀.1.trans ht.1, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
          have hmem : γ t ∈ e.1 ∩ G_dual.U := ⟨himg ▸ mem_image_of_mem γ ht_Ioo, htU⟩
          rw [he_GdU, mem_singleton_iff] at hmem
          exact ht.1.ne' (hinj ht_Ioo ht₀ hmem)
      have hIoc_comp : γ '' Ioc t₀ 1 ⊆ compV (γ 1) :=
        (isPreconnected_Ioc.image γ hγ.continuousOn).subset_connectedComponentIn
          ⟨1, right_mem_Ioc.mpr ht₀.2, rfl⟩ hIoc_sub
      obtain ⟨x, hx_r', hx_e⟩ := he4 r_dual hr_dual hinc
      have hxU : x ∉ G_dual.U := region_subset hr_dual hx_r'
      rw [← himg] at hx_e
      obtain ⟨t, ht, rfl⟩ := hx_e
      have hne : t ≠ t₀ := fun h => hxU (h ▸ (he'.2.1 hp_e').1)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hxu := hIco_comp ⟨t, ⟨unitInterval.nonneg t, hlt⟩, rfl⟩
        exact ⟨γ 0, h0, (region_eq_of_mem hr_dual (hcompV_mem h0).1 hx_r' hxu).symm⟩
      · have hxv := hIoc_comp ⟨t, ⟨hgt, unitInterval.le_one t⟩, rfl⟩
        exact ⟨γ 1, h1, (region_eq_of_mem hr_dual (hcompV_mem h1).1 hx_r' hxv).symm⟩
    · have hfront : closure r_dual \ r_dual ⊆ G_dual.U := by
        rintro y ⟨hy_cl, hy_not_r⟩
        by_contra hyU
        obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem hyU
        obtain ⟨w, hwr', hwr⟩ := mem_closure_iff.mp hy_cl r' (region_isOpen hr') hyr'
        exact hy_not_r (region_eq_of_mem hr' hr_dual hwr' hwr ▸ hyr')
      have hAll_conn : IsPreconnected (univ \ G_dual.V) :=
        disc_isPreconnected_sdiff_finite hS isOpen_univ isPreconnected_univ G_dual.finite_V
      obtain ⟨x₀, hx₀⟩ := region_nonempty hr_dual
      have hx₀_in : x₀ ∈ (univ \ G_dual.V) ∩ r_dual :=
        ⟨⟨mem_univ x₀, fun hxV => region_subset hr_dual hx₀ (G_dual.V_subset_U hxV)⟩, hx₀⟩
      have hsub_all : univ \ G_dual.V ⊆ r_dual := by
        intro x hx
        by_contra hxr
        by_cases hxcl : x ∈ closure r_dual
        · have hxU : x ∈ G_dual.U := hfront ⟨hxcl, hxr⟩
          obtain ⟨e', he', hxe'⟩ := G_dual.exists_edge_of_mem hxU hx.2
          exact hex ⟨e', he', he', hr_dual, x, hxe', hxcl⟩
        · obtain ⟨w, -, hwr, hwcl⟩ :=
            hAll_conn r_dual (closure r_dual)ᶜ (region_isOpen hr_dual) isClosed_closure.isOpen_compl
              (fun y hy => by
                by_cases hyr : y ∈ r_dual
                · exact Or.inl hyr
                · exact Or.inr fun hycl => by
                    have hyU : y ∈ G_dual.U := hfront ⟨hycl, hyr⟩
                    obtain ⟨e', he', hye'⟩ := G_dual.exists_edge_of_mem hyU hy.2
                    exact hex ⟨e', he', he', hr_dual, y, hye', hycl⟩)
              ⟨x₀, hx₀_in⟩ ⟨x, hx, hxcl⟩
          exact hwcl (subset_closure hwr)
      obtain ⟨v₀, hv₀⟩ := hConn.1
      have hv₀_r : v₀ ∈ r_dual :=
        hsub_all ⟨mem_univ v₀, fun hvVd => disjoint_left.mp hdisj_V_U hv₀ (G_dual.V_subset_U hvVd)⟩
      exact ⟨v₀, hv₀,
        (region_eq_of_mem hr_dual (hcompV_mem hv₀).1 hv₀_r (hcompV_mem hv₀).2).symm⟩
  have himg_eq : compV '' G.V = G_dual.R := by
    refine Subset.antisymm ?_ hsurj_R
    rintro _ ⟨v, hv, rfl⟩
    exact (hcompV_mem hv).1
  let ρ : S → Set S := fun w => connectedComponentIn (univ \ G.U) w
  have hρ_inj : InjOn ρ G_dual.V := by
    intro w₁ hw₁ w₂ hw₂ heq
    obtain ⟨r₁, hr₁, hw₁r⟩ := hDual_V_in_R w₁ hw₁
    obtain ⟨r₂, hr₂, hw₂r⟩ := hDual_V_in_R w₂ hw₂
    have hρ1 : ρ w₁ = r₁ :=
      region_eq_of_mem ⟨w₁, ⟨mem_univ _, region_subset hr₁ hw₁r⟩, rfl⟩ hr₁
        (mem_connectedComponentIn ⟨mem_univ _, region_subset hr₁ hw₁r⟩) hw₁r
    have hρ2 : ρ w₂ = r₂ :=
      region_eq_of_mem ⟨w₂, ⟨mem_univ _, region_subset hr₂ hw₂r⟩, rfl⟩ hr₂
        (mem_connectedComponentIn ⟨mem_univ _, region_subset hr₂ hw₂r⟩) hw₂r
    have hr_eq : r₁ = r₂ := hρ1.symm.trans (heq.trans hρ2)
    subst hr_eq
    obtain ⟨w, _, hw_uniq⟩ := hDual_V_unique r₁ hr₁
    exact (hw_uniq w₁ ⟨hw₁r, hw₁⟩).trans (hw_uniq w₂ ⟨hw₂r, hw₂⟩).symm
  have hρ_img : ρ '' G_dual.V = G.R := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨r', hr', hwr'⟩ := hDual_V_in_R w hw
      have hρw : ρ w = r' :=
        region_eq_of_mem ⟨w, ⟨mem_univ _, region_subset hr' hwr'⟩, rfl⟩ hr'
          (mem_connectedComponentIn ⟨mem_univ _, region_subset hr' hwr'⟩) hwr'
      exact hρw ▸ hr'
    · intro hr
      obtain ⟨w, ⟨hwr, hwV⟩, _⟩ := hDual_V_unique r hr
      refine ⟨w, hwV, ?_⟩
      exact region_eq_of_mem ⟨w, ⟨mem_univ _, region_subset hr hwr⟩, rfl⟩ hr
        (mem_connectedComponentIn ⟨mem_univ _, region_subset hr hwr⟩) hwr
  have hV_dual_card : G_dual.V.ncard = G.R.ncard := by
    rw [← hρ_img, hρ_inj.ncard_image]
  have hE_dual_card : G_dual.E.ncard = G.E.ncard := by
    have henc : G.E.encard = G_dual.E.encard := encard_congr edgeEquiv
    exact (congrArg ENat.toNat henc).symm
  have hbd_card : (G_dual.V ∩ bd S).ncard = (G.V ∩ bd S).ncard :=
    ncard_eq_of_isDualPointSet hS.isOArc_bd inter_subset_right
      (G.finite_V.subset inter_subset_left) hDual_bd
  obtain ⟨p₀, -, hp₀⟩ :=
    disc_exists_notMem_U hS hG isOpen_univ ⟨φ_disc ⟨0, by simp [ClosedUnitDisc]⟩, mem_univ _⟩
  have hr₀ : connectedComponentIn (univ \ G.U) p₀ ∈ G.R := ⟨p₀, ⟨mem_univ p₀, hp₀⟩, rfl⟩
  obtain ⟨w₀, ⟨_, hw₀_V⟩, _⟩ := hDual_V_unique _ hr₀
  have hDual_V_ne : G_dual.V.Nonempty := ⟨w₀, hw₀_V⟩
  have hV_le_R : G.V.ncard ≤ G_dual.R.ncard := by
    rcases (G.V ∩ bd S).eq_empty_or_nonempty with hbd_emp | ⟨b₀, hb₀⟩
    · have hup := euler_upper_bound_of_bd_empty hS hG hConn hbd_emp
      have hlow := (euler_lower_bound hS hDual_prop).2 hDual_V_ne
      omega
    · have hreach : ∀ v ∈ G.V, ∃ b ∈ G.V ∩ bd S, Nonempty (GraphWalk G.toGraph v b) :=
        fun v hv => ⟨b₀, hb₀, hConn.2 v hv b₀ hb₀.1⟩
      have hup := euler_upper_bound_of_reach_bd hS hG hreach
      have hlow := (euler_lower_bound hS hDual_prop).1
      omega
  have hR_le_V : G_dual.R.ncard ≤ G.V.ncard := by
    rw [← himg_eq]
    exact ncard_image_le G.finite_V
  have hcard_eq : (compV '' G.V).ncard = G.V.ncard := by
    rw [himg_eq]
    omega
  have hinj : InjOn compV G.V := injOn_of_ncard_image_eq hcard_eq G.finite_V
  exact fun v₁ hv₁ v₂ hv₂ heq => hinj hv₁ hv₂ heq

end GraphMinor.GM06
