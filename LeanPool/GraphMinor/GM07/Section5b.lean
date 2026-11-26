/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section5a
public import LeanPool.GraphMinor.GM07.Section11b
public import LeanPool.GraphMinor.GM07.Section11d
public import LeanPool.GraphMinor.GM07.AlphaExists
public import LeanPool.GraphMinor.Surface.PushOff
public import LeanPool.GraphMinor.Surface.SurfacePull
public import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM19.Section6a
import LeanPool.GraphMinor.GM07.Section2Base

/-!
# Graph Minors VII, Section 5 (Part B): (5.5)–(5.7)

This file formalizes (5.5), (5.6), and (5.7) of Robertson and Seymour,
*Graph Minors. VII. Disjoint Paths on a Surface*, J. Combin. Theory Ser. B **45** (1988), 212–254:
- `isSolid_closure_sUnion_regions`: the closure of the union of a collection of regions of a proper
  drawing `G` in a surface `S` is solid (`IsSolid`).
- `theorem_5_5`: (5.5) (page 231, proof on page 254).
- `theorem_5_6`: (5.6) (page 232).
- `theorem_5_7`: (5.7) (page 232).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Filter unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## 1. Closed Nice Sets from Unions of Regions and Solidarity -/

/-- On a closed surface `T`, the closure of the union of any collection `ℛ ⊆ Γ.R` of regions of a
drawing `Γ` is `Γ`-nice (`IsGammaNice Γ (closure (⋃₀ ℛ))`). -/
theorem isGammaNice_closure_sUnion_regions (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) :
    IsGammaNice Γ (closure (⋃₀ ℛ)) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set Z := closure (⋃₀ ℛ)
  refine isGammaNice_of_sat fun a ha hne => ?_
  rcases ha with (⟨v, _, rfl⟩ | he) | hr
  · obtain ⟨x, rfl : x = v, hxZ⟩ := hne
    exact singleton_subset_iff.mpr hxZ
  · obtain ⟨y, hye, hyZ⟩ := hne
    obtain ⟨W, A₁, A₂, hW, hyW, -, hcov, c₁, c₂, d₁, d₂, h₁, h₂⟩ :=
      exists_edge_sides hS Γ he hye
    obtain ⟨w, hwW, hwR⟩ := mem_closure_iff.mp hyZ W hW hyW
    obtain ⟨r₀, hr₀ℛ, hwr₀⟩ := mem_sUnion.mp hwR
    have hr₀ : r₀ ∈ Γ.R := hℛ hr₀ℛ
    have hwU : w ∉ Γ.U := region_subset hr₀ hwr₀
    have hinc : (a ∩ closure r₀).Nonempty := by
      rcases hcov ⟨hwW, hwU⟩ with hA₁ | hA₂
      · exact ⟨y, hye, closure_mono (subset_region hr₀ c₁ d₁ hA₁ hwr₀) (h₁ ⟨hye, hyW⟩)⟩
      · exact ⟨y, hye, closure_mono (subset_region hr₀ c₂ d₂ hA₂ hwr₀) (h₂ ⟨hye, hyW⟩)⟩
    have he_sub : a ⊆ closure r₀ :=
      edge_subset_closure_of_incident hS he hr₀ hinc
    exact he_sub.trans (closure_mono (subset_sUnion_of_mem hr₀ℛ))
  · obtain ⟨y, hyr, hyZ⟩ := hne
    obtain ⟨w, hwr, hwR⟩ := mem_closure_iff.mp hyZ a (region_isOpen hr) hyr
    obtain ⟨r₀, hr₀ℛ, hwr₀⟩ := mem_sUnion.mp hwR
    have hr₀ : r₀ ∈ Γ.R := hℛ hr₀ℛ
    have h_eq : a = r₀ := region_eq_of_mem hr hr₀ hwr hwr₀
    subst h_eq
    exact (subset_sUnion_of_mem hr₀ℛ).trans subset_closure

/-- Adding boundary cuff drawings to a proper drawing `G` in `S` yields a drawing `G_bd : Drawing S`
with `G_bd.U = G.U ∪ bd S` and `G_bd.V ⊆ G.V ∪ bd S` such that `G.V ⊆ G_bd.V`. -/
theorem exists_drawing_union_bd (hS : IsSurface S) (G : Drawing S) (hG : G.IsProper) :
    ∃ G_bd : Drawing S, G_bd.U = G.U ∪ bd S ∧ G.V ⊆ G_bd.V ∧ G_bd.V ⊆ G.V ∪ bd S := by
  classical
  have : T2Space S := hS.2.1
  have hcuffs := cuff_statement.{u} S hS
  have hfin_cuffs : (cuffs S).Finite := hcuffs.2.1
  have key : ∀ L : Finset (Set S), (∀ C ∈ L, C ∈ cuffs S) →
      ∃ D : Drawing S, D.U = G.U ∪ ⋃ C ∈ L, C ∧ G.V ⊆ D.V ∧ D.V ⊆ G.V ∪ ⋃ C ∈ L, C := by
    intro L
    induction L using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨G, by simp, Subset.rfl, by simp⟩
    | insert C L hCL ih =>
      intro hL
      obtain ⟨D₀, hD₀U, hGV_D₀, hD₀V⟩ := ih fun C' hC' => hL C' (Finset.mem_insert_of_mem hC')
      have hC_cuff : C ∈ cuffs S := hL C (Finset.mem_insert_self C L)
      have hC_oarc : IsOArc C := hcuffs.2.2 C hC_cuff
      obtain ⟨c₀, hc₀⟩ := isOArc_nonempty hC_oarc
      let A : Set S := insert c₀ (G.V ∩ C)
      have hA_fin : A.Finite := (G.finite_V.inter_of_left C).insert c₀
      have hA_ne : A.Nonempty := insert_nonempty c₀ (G.V ∩ C)
      have hA_sub : A ⊆ C := insert_subset hc₀ inter_subset_right
      obtain ⟨D_C, hDC_U, hDC_V⟩ := exists_drawing_on_oArc hC_oarc hA_fin hA_ne hA_sub
      have hmeet : D₀.U ∩ D_C.U ⊆ D₀.V ∩ D_C.V := by
        rw [hD₀U, hDC_U, hDC_V]
        rintro x ⟨hxG | hxL, hxC⟩
        · have hxbd : x ∈ bd S := cuff_subset_bd hC_cuff hxC
          have hxV : x ∈ G.V := hG ⟨hxbd, hxG⟩
          exact ⟨hGV_D₀ hxV, mem_insert_of_mem c₀ ⟨hxV, hxC⟩⟩
        · obtain ⟨C', hC'L, hxC'⟩ := mem_iUnion₂.mp hxL
          have hC'_cuff : C' ∈ cuffs S := hL C' (Finset.mem_insert_of_mem hC'L)
          have hCC' : C' = C := by
            obtain ⟨y, hy, rfl⟩ := hC'_cuff
            obtain ⟨z, hz, rfl⟩ := hC_cuff
            have h1 := connectedComponentIn_eq hxC'
            have h2 := connectedComponentIn_eq hxC
            exact h1.trans h2.symm
          exact False.elim (hCL (hCC' ▸ hC'L))
      refine ⟨D₀.glue D_C hmeet, ?_, ?_, ?_⟩
      · change D₀.U ∪ D_C.U = _
        rw [hD₀U, hDC_U]
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro ((h | ⟨C', hC', hx⟩) | hx)
          · exact Or.inl h
          · exact Or.inr ⟨C', Or.inr hC', hx⟩
          · exact Or.inr ⟨C, Or.inl rfl, hx⟩
        · rintro (h | ⟨C', rfl | hC', hx⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr hx
          · exact Or.inl (Or.inr ⟨C', hC', hx⟩)
      · exact hGV_D₀.trans subset_union_left
      · change D₀.V ∪ D_C.V ⊆ _
        rw [hDC_V]
        rintro x (hxD₀ | rfl | ⟨hxV, hxC⟩)
        · rcases hD₀V hxD₀ with hxV | hxL
          · exact Or.inl hxV
          · obtain ⟨C', hC'L, hxC'⟩ := mem_iUnion₂.mp hxL
            exact Or.inr (mem_iUnion₂.mpr ⟨C', Finset.mem_insert_of_mem hC'L, hxC'⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨C, Finset.mem_insert_self C L, hc₀⟩)
        · exact Or.inl hxV
  obtain ⟨D, hDU, hGV, hDV⟩ := key hfin_cuffs.toFinset fun C hC => hfin_cuffs.mem_toFinset.mp hC
  have h_cuffs_eq_bd : (⋃ C ∈ hfin_cuffs.toFinset, C) = bd S := by
    ext x
    simp only [mem_iUnion, Finite.mem_toFinset]
    constructor
    · rintro ⟨C, hC, hxC⟩
      exact cuff_subset_bd hC hxC
    · intro hx
      exact ⟨connectedComponentIn (bd S) x, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩
  rw [h_cuffs_eq_bd] at hDU hDV
  exact ⟨D, hDU, hGV, hDV⟩

/-- Pullback of `IsSolid` along a closed embedding `j : S → T`. -/
theorem isSolid_of_isClosedEmbedding [T2Space S] {T : Type u} [TopologicalSpace T]
    {j : S → T} (hj : IsClosedEmbedding j) {Z : Set S} (hZ : IsSolid (j '' Z)) :
    IsSolid Z :=
  isSolid_of_isClosedEmbedding_aux hj hZ

/-- Embed a surface `S` with a proper drawing `G` into a closed surface `T` with a drawing
`Γ : Drawing T` such that for any `ℛ ⊆ G.R` and `Z = closure (⋃₀ ℛ)`, `j '' Z = closure (⋃₀ ℛ_T)`
for a subset `ℛ_T ⊆ Γ.R`. -/
theorem exists_capped_drawing [ConnectedSpace S] (hS : IsSurface S) (G : Drawing S)
    (hG : G.IsProper) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (j : S → T) (K : Set T) (Γ : Drawing T),
      IsClosedSurface T ∧ ConnectedSpace T ∧ IsClosedEmbedding j ∧ IsClosed K ∧
      range j ∪ K = univ ∧ range j ∩ K = j '' bd S ∧
      Γ.U = j '' (G.U ∪ bd S) ∧ j '' G.V ⊆ Γ.V ∧ Γ.V ⊆ j '' (G.V ∪ bd S) ∧
      ∀ ℛ : Set (Set S), ℛ ⊆ G.R →
        ∃ ℛ_T : Set (Set T), ℛ_T ⊆ Γ.R ∧ j '' closure (⋃₀ ℛ) = closure (⋃₀ ℛ_T) ∧
          ⋃₀ ℛ_T = j '' (⋃₀ ℛ \ bd S) := by
  obtain ⟨T, topT, j, K, hT, hj, hK, hunion, hinter, hconnT⟩ := exists_capAll S hS
  have hT_conn : ConnectedSpace T := hconnT inferInstance
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space T := hT.2.1
  obtain ⟨G_bd, hGbd_U, hGV_Gbd, hGbd_V⟩ := exists_drawing_union_bd hS G hG
  obtain ⟨Γ, hΓ_U, hΓ_V, -, -⟩ :=
    exists_transport G_bd hj.continuous hj.injective.injOn
  rw [hGbd_U] at hΓ_U
  refine ⟨T, topT, j, K, Γ, hT, hT_conn, hj, hK, hunion, hinter, hΓ_U,
    (image_mono hGV_Gbd).trans (le_of_eq hΓ_V.symm),
    (le_of_eq hΓ_V).trans (image_mono hGbd_V), ?_⟩
  intro ℛ hℛ
  have h_open_S_int : IsOpen (j '' (bd S)ᶜ) := by
    have heq : j '' (bd S)ᶜ = Kᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩ hyK
        have : j x ∈ range j ∩ K := ⟨⟨x, rfl⟩, hyK⟩
        rw [hinter] at this
        obtain ⟨x', hx', hjx⟩ := this
        exact hx (hj.injective hjx ▸ hx')
      · intro hyK
        have : y ∈ range j ∪ K := hunion.symm ▸ mem_univ y
        rcases this with ⟨x, rfl⟩ | hyK'
        · refine ⟨x, fun hxbd => hyK ?_, rfl⟩
          have : j x ∈ range j ∩ K := hinter ▸ ⟨x, hxbd, rfl⟩
          exact this.2
        · exact False.elim (hyK hyK')
    rw [heq]
    exact hK.isOpen_compl
  set ℛ_T : Set (Set T) := {R' ∈ Γ.R | R' ⊆ j '' (⋃₀ ℛ \ bd S)}
  have h_sUnion_eq : ⋃₀ ℛ_T = j '' (⋃₀ ℛ \ bd S) := by
    apply Subset.antisymm
    · exact sUnion_subset fun R' hR' => hR'.2
    · rintro _ ⟨x, ⟨hxℛ, hxbd⟩, rfl⟩
      obtain ⟨r, hrℛ, hxr⟩ := mem_sUnion.mp hxℛ
      have hr : r ∈ G.R := hℛ hrℛ
      have hjx_notU : j x ∉ Γ.U := by
        rw [hΓ_U]
        rintro ⟨x', hx'U | hx'bd, hjx⟩
        · have hxx' : x = x' := hj.injective hjx.symm
          exact region_subset hr hxr (hxx' ▸ hx'U)
        · have hxx' : x = x' := hj.injective hjx.symm
          exact hxbd (hxx' ▸ hx'bd)
      obtain ⟨R', hR'Γ, hjxR'⟩ := exists_region_of_notMem hjx_notU
      refine mem_sUnion.mpr ⟨R', ⟨hR'Γ, ?_⟩, hjxR'⟩
      have h_sub_range : R' ⊆ j '' (univ \ (G.U ∪ bd S)) := by
        intro y hy
        have hy_notU : y ∉ Γ.U := region_subset hR'Γ hy
        have hy_notK : y ∉ K := by
          have h_disj : Disjoint R' K := by
            by_contra hnot
            obtain ⟨z, hzR', hzK⟩ := not_disjoint_iff.mp hnot
            have hR'_pre : IsPreconnected R' := region_isPreconnected hR'Γ
            have h1 : R' ⊆ j '' (bd S)ᶜ ∪ (range j)ᶜ := by
              intro w hw
              by_cases hw_range : w ∈ range j
              · obtain ⟨x_w, hw_eq⟩ := hw_range
                left
                refine ⟨x_w, fun hx_bd => region_subset hR'Γ hw ?_, hw_eq⟩
                rw [hΓ_U]
                exact ⟨x_w, Or.inr hx_bd, hw_eq⟩
              · exact Or.inr hw_range
            have h_open1 : IsOpen (j '' (bd S)ᶜ) := h_open_S_int
            have h_open2 : IsOpen (range j)ᶜ := hj.isClosed_range.isOpen_compl
            have h_disj12 : Disjoint (j '' (bd S)ᶜ) (range j)ᶜ :=
              disjoint_left.mpr fun w ⟨x_w, _, hw_eq⟩ hw_c => hw_c ⟨x_w, hw_eq⟩
            have h_sub1 := hR'_pre.subset_left_of_subset_union h_open1 h_open2 h_disj12 h1
              ⟨j x, hjxR', ⟨x, hxbd, rfl⟩⟩
            obtain ⟨x_z, hx_z_bd, hxz_eq⟩ := h_sub1 hzR'
            have : j x_z ∈ range j ∩ K := ⟨⟨x_z, rfl⟩, hxz_eq.symm ▸ hzK⟩
            rw [hinter] at this
            obtain ⟨x', hx'bd, hjx'⟩ := this
            exact hx_z_bd (hj.injective hjx' ▸ hx'bd)
          exact disjoint_left.mp h_disj hy
        have hy_range : y ∈ range j := by
          have : y ∈ range j ∪ K := hunion.symm ▸ mem_univ y
          exact this.resolve_right hy_notK
        obtain ⟨x_y, rfl⟩ := hy_range
        refine ⟨x_y, ⟨mem_univ _, fun h_in => hy_notU ?_⟩, rfl⟩
        rw [hΓ_U]
        exact ⟨x_y, h_in, rfl⟩
      intro y hyR'
      obtain ⟨x_y, ⟨_, hx_y_not⟩, rfl⟩ := h_sub_range hyR'
      have hx_y_bd : x_y ∉ bd S := fun h => hx_y_not (Or.inr h)
      have h_pre : IsPreconnected (j ⁻¹' R') := by
        let h_homeo := hj.toHomeomorph
        have h_eq : j ⁻¹' R' = h_homeo.symm '' (Subtype.val ⁻¹' R' : Set (range j)) := by
          ext w
          constructor
          · intro hw
            exact ⟨⟨j w, ⟨w, rfl⟩⟩, hw, by simp [h_homeo]⟩
          · rintro ⟨⟨_, ⟨w', rfl⟩⟩, hw', rfl⟩
            simpa [h_homeo] using hw'
        have h_sub_eq : (Subtype.val ⁻¹' R' : Set (range j)) =
            (fun z : R' => (⟨z.1, let ⟨w, _, hw⟩ := h_sub_range z.2; ⟨w, hw⟩⟩ : range j)) ''
              univ := by
          ext ⟨z, hz_range⟩
          constructor
          · intro hzR'
            exact ⟨⟨z, hzR'⟩, mem_univ _, rfl⟩
          · rintro ⟨⟨z', hz'R'⟩, _, h_eq'⟩
            obtain rfl : z' = z := congrArg Subtype.val h_eq'
            exact hz'R'
        rw [h_eq, h_sub_eq, ← image_comp]
        have : PreconnectedSpace R' := isPreconnected_iff_preconnectedSpace.mp
          (region_isPreconnected hR'Γ)
        refine isPreconnected_univ.image _ ?_
        exact (h_homeo.symm.continuous.comp
          (Continuous.subtype_mk continuous_subtype_val _)).continuousOn
      have h_sub_compl : j ⁻¹' R' ⊆ G.Uᶜ := fun w hw hwU =>
        region_subset hR'Γ hw (by rw [hΓ_U]; exact ⟨w, Or.inl hwU, rfl⟩)
      have hx_y_r : x_y ∈ r :=
        subset_region hr h_pre (disjoint_left.mpr h_sub_compl) hjxR' hxr hyR'
      exact ⟨x_y, ⟨mem_sUnion.mpr ⟨r, hrℛ, hx_y_r⟩, hx_y_bd⟩, rfl⟩
  refine ⟨ℛ_T, fun R' hR' => hR'.1, ?_, h_sUnion_eq⟩
  rw [h_sUnion_eq, hj.closure_image_eq (⋃₀ ℛ \ bd S)]
  congr 1
  have : LocallyConnectedSpace S := hS.locallyConnected
  apply Subset.antisymm
  · refine closure_minimal (fun x hx => ?_) isClosed_closure
    obtain ⟨r, hrℛ, hxr⟩ := mem_sUnion.mp hx
    have hr_open : IsOpen r := region_isOpen (hℛ hrℛ)
    rw [mem_closure_iff]
    intro V hV hxV
    have hx_cl : x ∈ closure (bd S)ᶜ := mem_closure_compl_bd (hS.2.2 x)
    obtain ⟨w, ⟨hwV, hwr⟩, hw_not_bd⟩ := mem_closure_iff.mp hx_cl (V ∩ r)
      (hV.inter hr_open) ⟨hxV, hxr⟩
    exact ⟨w, hwV, mem_sUnion.mpr ⟨r, hrℛ, hwr⟩, hw_not_bd⟩
  · exact closure_mono sdiff_subset

/-- If `G` is a proper drawing in a connected surface `S` and `ℛ ⊆ G.R` is a set of regions of `G`,
then `closure (⋃₀ ℛ)` is solid (`IsSolid (closure (⋃₀ ℛ))`). -/
theorem isSolid_closure_sUnion_regions [ConnectedSpace S] (hS : IsSurface S) (G : Drawing S)
    (hG : G.IsProper) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ G.R) :
    IsSolid (closure (⋃₀ ℛ)) := by
  obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, -, -, -, -, -, -, hℛ_map⟩ :=
    exists_capped_drawing hS G hG
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  obtain ⟨ℛ_T, hℛ_T, h_cl_eq, -⟩ := hℛ_map ℛ hℛ
  have hZn : IsGammaNice Γ (closure (⋃₀ ℛ_T)) :=
    isGammaNice_closure_sUnion_regions hT Γ hℛ_T
  have hSolid_T : IsSolid (j '' closure (⋃₀ ℛ)) := by
    rw [h_cl_eq]
    exact isSolid_of_nice hT isClosed_closure hZn
  exact isSolid_of_isClosedEmbedding hj hSolid_T

/-! ## 2. Proof of (5.5) (pages 231, 254) -/

/-- An open set `O` is *good in `closure (⋃₀ ℛ)`* for a drawing `Γ` if `O ∩ closure (⋃₀ ℛ)` is
contained in a simply connected subset `K ⊆ closure (⋃₀ ℛ)` and any two points
`x, y ∈ O ∩ ⋃₀ ℛ` are joined in `closure (⋃₀ ℛ)` by a path `p` in `K` and a homotopic path `q`
in `(Γ.U \ Γ.V)ᶜ`. -/
def GoodOpenIn (Γ : Drawing S) (ℛ : Set (Set S)) (O : Set S) : Prop :=
  let Z := closure (⋃₀ ℛ)
  IsOpen O ∧ ∃ K : Set S, IsSimplyConnectedSet K ∧ K ⊆ Z ∧ O ∩ Z ⊆ K ∧
    ∀ x (hx : x ∈ O ∩ ⋃₀ ℛ) y (hy : y ∈ O ∩ ⋃₀ ℛ),
      ∃ (p q : Path (⟨x, subset_closure hx.2⟩ : Z) ⟨y, subset_closure hy.2⟩),
        (∀ u, (p u).1 ∈ K) ∧ (∀ u, (q u).1 ∈ (Γ.U \ Γ.V)ᶜ) ∧ p.Homotopic q

theorem goodOpenIn_of_joinedIn (Γ : Drawing S) (ℛ : Set (Set S)) {O K : Set S}
    (hO : IsOpen O) (hK : IsSimplyConnectedSet K) (hKZ : K ⊆ closure (⋃₀ ℛ))
    (hOK : O ∩ closure (⋃₀ ℛ) ⊆ K)
    (hjoin : ∀ x ∈ O ∩ ⋃₀ ℛ, ∀ y ∈ O ∩ ⋃₀ ℛ, JoinedIn (K ∩ (Γ.U \ Γ.V)ᶜ) x y) :
    GoodOpenIn Γ ℛ O := by
  refine ⟨hO, K, hK, hKZ, hOK, fun x hx y hy => ?_⟩
  obtain ⟨p₀, hp₀⟩ := hjoin x hx y hy
  let p : Path (⟨x, subset_closure hx.2⟩ : closure (⋃₀ ℛ)) ⟨y, subset_closure hy.2⟩ :=
    pathCod p₀ (subset_closure hx.2) (subset_closure hy.2) fun u => hKZ (hp₀ u).1
  exact ⟨p, p, fun u => (hp₀ u).1, fun u => (hp₀ u).2, Path.Homotopic.refl p⟩

theorem sub_path_trans_mem {Z A : Set S} {a b c : Z} {p : Path a b} {q : Path b c}
    (hp : ∀ u, (p u).1 ∈ A) (hq : ∀ u, (q u).1 ∈ A) (u : I) : ((p.trans q) u).1 ∈ A := by
  have : (p.trans q) u ∈ range p ∪ range q := Path.trans_range p q ▸ mem_range_self u
  rcases this with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hv ▸ hp v
  · exact hv ▸ hq v

theorem sub_path_symm_mem {Z A : Set S} {a b : Z} {p : Path a b}
    (hp : ∀ u, (p u).1 ∈ A) (u : I) : (p.symm u).1 ∈ A := by
  rw [Path.symm_apply]
  exact hp _

/-- Case 1: Every point `z ∈ closure (⋃₀ ℛ) \ Γ.U` has a `GoodOpenIn` neighborhood. -/
theorem exists_goodOpenIn_of_notMem_U (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) {z : S}
    (hzZ : z ∈ closure (⋃₀ ℛ)) (hzU : z ∉ Γ.U) :
    ∃ O : Set S, z ∈ O ∧ GoodOpenIn Γ ℛ O := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hZn : IsGammaNice Γ (closure (⋃₀ ℛ)) := isGammaNice_closure_sUnion_regions hS Γ hℛ
  obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
  have hrZ : r ⊆ closure (⋃₀ ℛ) := nice_region hZn hr ⟨z, hzr, hzZ⟩
  obtain ⟨D, D', hD, hD', hzD', hD'D, hDr, -⟩ :=
    exists_closedDisc_nbhd hS (region_isOpen hr) hzr
  refine ⟨D', hzD', goodOpenIn_of_joinedIn Γ ℛ hD' hD.isSimplyConnectedSet
    (hDr.trans hrZ) (inter_subset_left.trans hD'D) fun x hx y hy => ?_⟩
  refine (hD.isPathConnected.joinedIn x (hD'D hx.1) y (hD'D hy.1)).mono fun w hw => ?_
  exact ⟨hw, fun h => region_subset hr (hDr hw) h.1⟩

/-- Case 2a: A polar chart at `z ∈ Γ.V ∩ closure (⋃₀ ℛ)` gives a `GoodOpenIn` neighborhood. -/
theorem exists_goodOpenIn_of_isPolar (hS : IsClosedSurface S)
    {Γ : Drawing S} {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) {z : S}
    (hzV : z ∈ Γ.V) (hzZ : z ∈ closure (⋃₀ ℛ)) {Φ : C(ClosedUnitDisc, S)}
    (hp : IsPolar Γ z Φ) :
    ∃ O : Set S, z ∈ O ∧ GoodOpenIn Γ ℛ O := by
  have : T2Space S := hS.2.1
  have hZn : IsGammaNice Γ (closure (⋃₀ ℛ)) := isGammaNice_closure_sUnion_regions hS Γ hℛ
  set Z := closure (⋃₀ ℛ)
  let T₀ : Set ClosedUnitDisc := Φ ⁻¹' Z
  have hT₀_star : ∀ x ∈ T₀, ∀ c : I, discScale c x ∈ T₀ :=
    fun x hx c => hp.star isClosed_closure hZn hx c
  have hcT₀ : polarCentre ∈ T₀ := by
    change Φ polarCentre ∈ Z
    rw [hp.centre]
    exact hzZ
  have hK_sc : IsSimplyConnectedSet (Φ '' T₀) :=
    isSimplyConnected_star hp.inj hT₀_star ⟨polarCentre, hcT₀⟩
  have hKZ : Φ '' T₀ ⊆ Z := by rintro _ ⟨x, hx, rfl⟩; exact hx
  have hOK : interior (range Φ) ∩ Z ⊆ Φ '' T₀ := by
    rintro y ⟨hy_int, hyZ⟩
    obtain ⟨x, rfl⟩ := interior_subset hy_int
    exact ⟨x, hyZ, rfl⟩
  refine ⟨interior (range Φ), hp.nhd,
    goodOpenIn_of_joinedIn Γ ℛ isOpen_interior hK_sc hKZ hOK fun x hx y hy => ?_⟩
  have hray_join : ∀ w ∈ interior (range Φ) ∩ ⋃₀ ℛ,
      JoinedIn (Φ '' T₀ ∩ (Γ.U \ Γ.V)ᶜ) z w := by
    intro w ⟨hw_int, hwℛ⟩
    obtain ⟨r₀, hr₀ℛ, hwr₀⟩ := mem_sUnion.mp hwℛ
    have hwU : w ∉ Γ.U := region_subset (hℛ hr₀ℛ) hwr₀
    obtain ⟨u, rfl⟩ := interior_subset hw_int
    have huT₀ : u ∈ T₀ := subset_closure hwℛ
    have huc : u ≠ polarCentre := by
      rintro rfl
      exact hwU (hp.centre.symm ▸ Γ.V_subset_U hzV)
    have hcont : Continuous fun t : I => Φ (discScale t u) :=
      (Φ.continuous.comp continuous_discScale).comp (Continuous.prodMk continuous_id
        continuous_const)
    refine ⟨⟨⟨fun t => Φ (discScale t u), hcont⟩, by simp [discScale_zero, hp.centre],
      by simp [discScale_one]⟩, fun t => ⟨⟨discScale t u, hT₀_star u huT₀ t, rfl⟩, ?_⟩⟩
    change Φ (discScale t u) ∈ (Γ.U \ Γ.V)ᶜ
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | h0
    · have ht0 : t = 0 := Subtype.ext h0.symm
      rw [ht0, discScale_zero, hp.centre]
      exact fun h => h.2 hzV
    · obtain ⟨a, ha, h1, h2⟩ := hp.ray u huc t h0
      intro hU_diff
      rcases ha with (⟨v, hv, rfl⟩ | he) | hr
      · exact hwU (h1.symm ▸ Γ.V_subset_U hv)
      · exact hwU (he.2.1 h1).1
      · exact region_subset hr h2 hU_diff.1
  exact (hray_join x hx).symm.trans (hray_join y hy)

/-- Case 2: Every vertex `z ∈ Γ.V ∩ closure (⋃₀ ℛ)` has a `GoodOpenIn` neighborhood. -/
theorem exists_goodOpenIn_of_mem_V [ConnectedSpace S] (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) {z : S}
    (hzV : z ∈ Γ.V) (hzZ : z ∈ closure (⋃₀ ℛ)) :
    ∃ O : Set S, z ∈ O ∧ GoodOpenIn Γ ℛ O := by
  classical
  have : T2Space S := hS.2.1
  have : Nonempty S := ⟨z⟩
  have : LocallyPathConnectedSpace S := IsClosedSurface.locallyPathConnectedSpace hS
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ z)
  · obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_sectors hS hγ hzV h2
    exact exists_goodOpenIn_of_isPolar hS hℛ hzV hzZ hΦ
  · have hfinℛ : ℛ.Finite := (finite_R hS Γ).subset hℛ
    have hz_biUnion : z ∈ ⋃ r ∈ ℛ, closure r := by
      have h_eq : closure (⋃₀ ℛ) = ⋃ r ∈ ℛ, closure r := by
        rw [sUnion_eq_biUnion, hfinℛ.closure_biUnion]
      rwa [← h_eq]
    obtain ⟨r₀, hr₀ℛ, hzr₀⟩ := mem_iUnion₂.mp hz_biUnion
    have hr₀ : r₀ ∈ Γ.R := hℛ hr₀ℛ
    obtain ⟨W_r, hW_r, hzW_r, hW_r_sub⟩ := exists_nbhd_of_few hS hγ hzV h2 hr₀ hzr₀
    have hW_r_Z : W_r ⊆ closure (⋃₀ ℛ) :=
      hW_r_sub.trans (closure_mono (subset_sUnion_of_mem hr₀ℛ))
    have hfinH : Finite (halfEdges Γ γ z) := (finite_halfEdges Γ γ z).to_subtype
    have hss : Subsingleton (halfEdges Γ γ z) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    rcases isEmpty_or_nonempty (halfEdges Γ γ z) with h0 | ⟨⟨⟨e, b⟩, he, hb⟩⟩
    · have hno : ∀ g ∈ Γ.E, z ∉ closure g := by
        intro g hg hzg
        obtain ⟨b, hb⟩ := exists_end_eq hγ hg hzV hzg
        exact h0.false ⟨(g, b), hg, hb⟩
      let T : Set S := (Γ.V \ {z}) ∪ ⋃ g ∈ Γ.E, closure g
      have hT : IsClosed T := (Γ.finite_V.subset sdiff_subset).isClosed.union
        (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
      have hzT : z ∉ T := by
        rintro (h | h)
        · exact h.2 rfl
        · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
          exact hno g hg hzg
      obtain ⟨D, D', hD, hD', hzD', hD'D, hDT, -⟩ :=
        exists_closedDisc_nbhd hS (hW_r.inter hT.isOpen_compl) ⟨hzW_r, hzT⟩
      have hDZ : D ⊆ closure (⋃₀ ℛ) := fun w hw => hW_r_Z (hDT hw).1
      refine ⟨D', hzD', goodOpenIn_of_joinedIn Γ ℛ hD' hD.isSimplyConnectedSet hDZ
        (inter_subset_left.trans hD'D) fun x hx y hy => ?_⟩
      refine (hD.isPathConnected.joinedIn x (hD'D hx.1) y (hD'D hy.1)).mono fun w hw => ⟨hw, ?_⟩
      rintro ⟨hwU, hwV⟩
      obtain ⟨g, hg, hwg⟩ := Γ.exists_edge_of_mem hwU hwV
      exact (hDT hw).2 (Or.inr (mem_iUnion₂.mpr ⟨g, hg, subset_closure hwg⟩))
    · have hleaf : ∀ f ∈ Γ.E, f ≠ e → z ∉ closure f := by
        intro f hf hfe hzf
        obtain ⟨b', hb'⟩ := exists_end_eq hγ hf hzV hzf
        have := congrArg (fun k : halfEdges Γ γ z => k.1.1)
          (hss.elim ⟨(f, b'), hf, hb'⟩ ⟨(e, b), he, hb⟩)
        exact hfe this
      have hzcl : z ∈ closure e := by
        have := end_mem_closure hγ he b
        rwa [hb] at this
      have hnot_loop : ∃ u : S, u ≠ z ∧ closure e ∩ Γ.V = {u, z} ∧ IsLineWithEnds (closure e) u z
        := by
        rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hl⟩ | ⟨u, hu, -⟩
        · have hz_uv : z = u ∨ z = v := by
            have : z ∈ closure e ∩ Γ.V := ⟨hzcl, hzV⟩
            rwa [hcap, mem_insert_iff, mem_singleton_iff] at this
          rcases hz_uv with rfl | rfl
          · exact ⟨v, huv.symm, by rw [pair_comm]; exact hcap, hl.symm⟩
          · exact ⟨u, huv, hcap, hl⟩
        · exfalso
          have hend : ∀ c, γ e (endOf c) = z := by
            intro c
            have h₁ : γ e (endOf c) ∈ closure e ∩ Γ.V := by
              refine ⟨end_mem_closure hγ he c, ?_⟩
              cases c
              · exact hγ.zero e he
              · exact hγ.one e he
            have h₂ : z ∈ closure e ∩ Γ.V := ⟨hzcl, hzV⟩
            rw [hu] at h₁ h₂
            exact h₁.trans h₂.symm
          have := congrArg (fun k : halfEdges Γ γ z => k.1.2)
            (hss.elim ⟨(e, true), he, hend true⟩ ⟨(e, false), he, hend false⟩)
          simp at this
      obtain ⟨u, huz, hcap, hL⟩ := hnot_loop
      obtain ⟨D, D', hD, hD', hzD', hD'D, hDW_r, -⟩ :=
        exists_closedDisc_nbhd hS hW_r hzW_r
      have hDZ : D ⊆ closure (⋃₀ ℛ) := hDW_r.trans hW_r_Z
      obtain ⟨Z_leaf, hZ_leaf, hzZ_leaf, hZ_conn⟩ :=
        exists_leaf_nbhd hS Γ he huz hcap hL hleaf hD' hzD'
      refine ⟨Z_leaf ∩ D', ⟨hzZ_leaf, hzD'⟩,
        goodOpenIn_of_joinedIn Γ ℛ (hZ_leaf.inter hD') hD.isSimplyConnectedSet hDZ
          ((inter_subset_left.trans inter_subset_right).trans hD'D)
          fun x hx y hy => ?_⟩
      have hxU : x ∉ Γ.U := by
        obtain ⟨r, hrℛ, hxr⟩ := mem_sUnion.mp hx.2
        exact region_subset (hℛ hrℛ) hxr
      have hyU : y ∉ Γ.U := by
        obtain ⟨r, hrℛ, hyr⟩ := mem_sUnion.mp hy.2
        exact region_subset (hℛ hrℛ) hyr
      obtain ⟨A, hA_conn, hA_disj, hxA, hyA, hAD'⟩ :=
        hZ_conn x hx.1.1 hxU y hy.1.1 hyU
      have hAU : A ⊆ D' \ Γ.U := fun w hw => ⟨hAD' hw, disjoint_left.mp hA_disj hw⟩
      have hj := joinedIn_of_isOpen_of_isPreconnected (hD'.sdiff Γ.isClosed_U) hA_conn hAU hxA hyA
      exact hj.mono fun w ⟨hwD', hwU⟩ => ⟨hD'D hwD', fun h => hwU h.1⟩

/-- In an edge chart `c : IsEdgeChart Γ γ t₀ M a b` at `γ t₀ ∈ e ∩ closure (⋃₀ ℛ)`, the intersection
`c.disc ∩ closure (⋃₀ ℛ)` is simply connected (`IsSimplyConnectedSet`). -/
theorem IsEdgeChart.isSimplyConnectedSet_inter_closure_regions
    (hS : IsClosedSurface S) {Γ : Drawing S} {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R)
    {e : Set S} (he : e ∈ Γ.E) {γ : I → S} (hγ : Continuous γ) (hγe : γ '' Ioo 0 1 = e)
    {t₀ a b : I} (ht₀ : t₀ ∈ Ioo (0 : I) 1) {M : ℂ → S}
    (c : IsEdgeChart Γ γ t₀ M a b) (hzZ : γ t₀ ∈ closure (⋃₀ ℛ)) :
    IsSimplyConnectedSet (c.disc ∩ closure (⋃₀ ℛ)) := by
  have : T2Space S := hS.2.1
  have hZn : IsGammaNice Γ (closure (⋃₀ ℛ)) := isGammaNice_closure_sUnion_regions hS Γ hℛ
  have heZ : e ⊆ closure (⋃₀ ℛ) :=
    nice_edge hZn he ⟨γ t₀, hγe ▸ mem_image_of_mem γ ht₀, hzZ⟩
  have hcl_eZ : closure e ⊆ closure (⋃₀ ℛ) := closure_minimal heZ isClosed_closure
  set Z := closure (⋃₀ ℛ)
  let B := Metric.closedBall (0 : ℂ) 1
  let c₀ : B := ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let scale : I → B → B := fun s w =>
    ⟨(s : ℝ) • w.1, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (unitInterval.nonneg s)]
      have hw1 : ‖w.1‖ ≤ 1 := by
        have h := w.2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      nlinarith [unitInterval.nonneg s, unitInterval.le_one s, norm_nonneg w.1]⟩
  have hscale_cont : Continuous fun p : I × B => scale p.1 p.2 := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp
      continuous_snd)
  have hscale_zero : ∀ w : B, scale 0 w = c₀ := fun w => Subtype.ext (by simp [scale, c₀])
  have hscale_one : ∀ w : B, scale 1 w = w := fun w => Subtype.ext (by simp [scale])
  let Φ : C(B, S) :=
    ⟨fun w => M w.1, c.cont.comp_continuous continuous_subtype_val fun w => w.2⟩
  have hΦ_inj : Function.Injective Φ := fun u v h => Subtype.ext (c.inj u.2 v.2 h)
  let T₀ : Set B := Φ ⁻¹' Z
  have hcT₀ : c₀ ∈ T₀ := by
    change M 0 ∈ Z
    rw [c.zero]
    exact hzZ
  have hT₀_star : ∀ w ∈ T₀, ∀ s : I, scale s w ∈ T₀ := by
    intro w hwZ s
    rcases eq_or_lt_of_le (unitInterval.nonneg s) with h0 | hs_pos
    · have hs0 : s = 0 := Subtype.ext h0.symm
      rw [hs0, hscale_zero]
      exact hcT₀
    · have hs_pos' : (0 : ℝ) < (s : ℝ) := hs_pos
      rcases IsEdgeChart.cases_of_closedBall w.2 with hwL | hw0 | hwU
      · have hsw_L : (scale s w).1 ∈ IsEdgeChart.lower := by
          refine ⟨(scale s w).2, ?_⟩
          change ((s : ℝ) • w.1).im < 0
          rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
             zero_mul, add_zero]
          exact mul_neg_of_pos_of_neg hs_pos' hwL.2
        obtain ⟨r, hr, hwr⟩ := exists_region_of_notMem
          (disjoint_left.mp c.lower_disjoint ⟨w.1, hwL, rfl⟩)
        have hrZ : r ⊆ Z := nice_region hZn hr ⟨M w.1, hwr, hwZ⟩
        have hL_r : M '' IsEdgeChart.lower ⊆ r :=
          subset_region hr c.lower_conn c.lower_disjoint ⟨w.1, hwL, rfl⟩ hwr
        exact hrZ (hL_r ⟨(scale s w).1, hsw_L, rfl⟩)
      · have hsw_0 : (scale s w).1 ∈ {z : ℂ | z ∈ Metric.closedBall 0 1 ∧ z.im = 0} := by
          refine ⟨(scale s w).2, ?_⟩
          change ((s : ℝ) • w.1).im = 0
          rw [Complex.real_smul, Complex.mul_im, hw0, Complex.ofReal_im, mul_zero, zero_mul,
            add_zero]
        have hM_mem : M (scale s w).1 ∈ γ '' Icc a b := by
          rw [← c.closed_eq]
          exact ⟨(scale s w).1, hsw_0, rfl⟩
        obtain ⟨t, _, hMt⟩ := hM_mem
        have ht_cl : γ t ∈ closure e := by
          have ht_Ioo : t ∈ closure (Ioo (0 : I) 1) := by
            rw [closure_Ioo (zero_ne_one' I)]
            exact ⟨t.2.1, t.2.2⟩
          have := image_closure_subset_closure_image hγ ⟨t, ht_Ioo, rfl⟩
          rwa [hγe] at this
        change M (scale s w).1 ∈ Z
        rw [← hMt]
        exact hcl_eZ ht_cl
      · have hsw_U : (scale s w).1 ∈ IsEdgeChart.upper := by
          refine ⟨(scale s w).2, ?_⟩
          change 0 < ((s : ℝ) • w.1).im
          rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, add_zero]
          exact mul_pos hs_pos' hwU.2
        obtain ⟨r, hr, hwr⟩ := exists_region_of_notMem
          (disjoint_left.mp c.upper_disjoint ⟨w.1, hwU, rfl⟩)
        have hrZ : r ⊆ Z := nice_region hZn hr ⟨M w.1, hwr, hwZ⟩
        have hU_r : M '' IsEdgeChart.upper ⊆ r :=
          subset_region hr c.upper_conn c.upper_disjoint ⟨w.1, hwU, rfl⟩ hwr
        exact hrZ (hU_r ⟨(scale s w).1, hsw_U, rfl⟩)
  have h_eq : c.disc ∩ Z = Φ '' T₀ := by
    ext y
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hyZ⟩
      exact ⟨⟨w, hw⟩, hyZ, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwZ, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, hwZ⟩
  rw [h_eq]
  have hcont : Continuous fun p : I × B => Φ (scale p.1 p.2) :=
    Φ.continuous.comp hscale_cont
  refine ⟨⟨Φ c₀, ⟨c₀, hcT₀, rfl⟩, ?_⟩, fun φ hφ => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hp : Continuous fun t : I => Φ (scale t x) :=
      hcont.comp (Continuous.prodMk continuous_id continuous_const)
    refine ⟨⟨⟨fun t => Φ (scale t x), hp⟩, by simp [hscale_zero], by simp [hscale_one]⟩,
      fun t => ?_⟩
    exact ⟨_, hT₀_star x hx t, rfl⟩
  · have : CompactSpace B := isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall
      (0 : ℂ) 1)
    have hemb : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hΦ_inj).isEmbedding
    have hex : ∀ z, ∃ x ∈ T₀, Φ x = φ z := fun z => hφ (mem_range_self z)
    choose ψ hψT hψ using hex
    have hψc : Continuous ψ := hemb.continuous_iff.mpr (by
      have : (Φ ∘ ψ) = φ := funext hψ
      rw [this]
      exact φ.continuous)
    refine ⟨Φ c₀, ⟨c₀, hcT₀, rfl⟩, ⟨⟨fun p => Φ (scale (σ p.2) (ψ p.1)), ?_⟩, ?_, ?_, ?_⟩⟩
    · exact hcont.comp (Continuous.prodMk (by fun_prop) (by fun_prop))
    · intro p
      exact ⟨_, hT₀_star _ (hψT _) _, rfl⟩
    · intro z
      change Φ (scale (σ 0) (ψ z)) = φ z
      rw [unitInterval.symm_zero, hscale_one, hψ]
    · intro z
      change Φ (scale (σ 1) (ψ z)) = Φ c₀
      rw [unitInterval.symm_one, hscale_zero]

private theorem good_open_times_closed
    {S : Type u}
    [TopologicalSpace S]
    (hS : IsClosedSurface S)
    (Γ : Drawing S)
    {ℛ : Set (Set S)}
    (hℛ : ℛ ⊆ Γ.R)
    {e : Set S}
    (he : e ∈ Γ.E)
    [this : T2Space S]
    (hman : ∀ (x : S), IsManifoldPoint x)
    (γ : ↑I → S)
    (hγ : Continuous γ)
    (hγ0 : γ 0 ∈ Γ.V)
    (hγ1 : γ 1 ∈ Γ.V)
    (hinj : InjOn γ (Ioo 0 1))
    (hγe : γ '' Ioo 0 1 = e)
    (hγ_mem_Z : ∀ (t : ↑I), γ t ∈ closure (⋃₀ ℛ))
    (h0T : 0 ∈ ({t | ∃ O, γ t ∈ O ∧ GoodOpenIn Γ ℛ O}))
    (h1T : 1 ∈ ({t | ∃ O, γ t ∈ O ∧ GoodOpenIn Γ ℛ O})) :
    IsClosed ({t | ∃ O, γ t ∈ O ∧ GoodOpenIn Γ ℛ O}) := by
  let Z := closure (⋃₀ ℛ)
  let T := {t | ∃ O, γ t ∈ O ∧ GoodOpenIn Γ ℛ O}
  rw [← closure_subset_iff_isClosed]
  intro t₀ ht₀_cl
  rcases eq_or_lt_of_le (unitInterval.nonneg t₀) with h0 | h0
  · exact (Subtype.ext h0.symm : t₀ = 0) ▸ h0T
  rcases eq_or_lt_of_le (unitInterval.le_one t₀) with h1 | h1
  · exact (Subtype.ext h1 : t₀ = 1) ▸ h1T
  have ht₀ : t₀ ∈ Ioo (0 : I) 1 := ⟨h0, h1⟩
  obtain ⟨M, a, b, g₁, g₂, _, g₄, g₅, _, g₇, g₈, g₉, g₁₀, g₁₁⟩ :=
    exists_edge_chart hS Γ he hγ hγ0 hγ1 hinj hγe ht₀ ht₀.1 ht₀.2
  have c : IsEdgeChart Γ γ t₀ M a b := ⟨g₁, g₂, g₄, g₅, g₇, g₈, g₉, g₁₀, g₁₁⟩
  let O : Set S := M '' Metric.ball 0 1
  have hO_open : IsOpen O := by
    change IsOpen (M '' Metric.ball 0 1)
    rw [← c.discInt_eq]
    exact c.isClosedDisc.isOpen_discInt hman
  have ht₀_O : γ t₀ ∈ O := ⟨0, by simp, c.zero⟩
  have hOD : O ⊆ c.disc := image_mono Metric.ball_subset_closedBall
  let K : Set S := c.disc ∩ Z
  have hK_sc : IsSimplyConnectedSet K :=
    IsEdgeChart.isSimplyConnectedSet_inter_closure_regions hS hℛ he hγ hγe ht₀ c (hγ_mem_Z t₀)
  have hKZ : K ⊆ Z := inter_subset_right
  have hOK : O ∩ Z ⊆ K := fun w hw => ⟨hOD hw.1, hw.2⟩
  have h_side : ∀ w ∈ O ∩ ⋃₀ ℛ, w ∈ M '' IsEdgeChart.lower ∨ w ∈ M '' IsEdgeChart.upper := by
    rintro _ ⟨⟨z, hz, rfl⟩, hwℛ⟩
    obtain ⟨r, hrℛ, hwr⟩ := mem_sUnion.mp hwℛ
    have hnU : M z ∉ Γ.U := region_subset (hℛ hrℛ) hwr
    rcases IsEdgeChart.cases_of_closedBall (Metric.ball_subset_closedBall hz) with h | h | h
    · exact Or.inl ⟨z, h, rfl⟩
    · exact absurd ((c.mem_U z (Metric.ball_subset_closedBall hz)).mpr h) hnU
    · exact Or.inr ⟨z, h, rfl⟩
  have hL_in_R : ∀ w ∈ M '' IsEdgeChart.lower, w ∈ ⋃₀ ℛ →
      M '' IsEdgeChart.lower ⊆ ⋃₀ ℛ ∧ M '' IsEdgeChart.lower ⊆ K ∩ (Γ.U \ Γ.V)ᶜ := by
    intro w hwL hwℛ
    obtain ⟨r, hrℛ, hwr⟩ := mem_sUnion.mp hwℛ
    have h_sub_r : M '' IsEdgeChart.lower ⊆ r :=
      subset_region (hℛ hrℛ) c.lower_conn c.lower_disjoint hwL hwr
    have h_sub_ℛ : M '' IsEdgeChart.lower ⊆ ⋃₀ ℛ := h_sub_r.trans (subset_sUnion_of_mem hrℛ)
    refine ⟨h_sub_ℛ, fun u huL => ⟨⟨?_, subset_closure (h_sub_ℛ huL)⟩, ?_⟩⟩
    · obtain ⟨z_u, hz_u, rfl⟩ := huL
      exact ⟨z_u, hz_u.1, rfl⟩
    · exact fun h => disjoint_left.mp c.lower_disjoint huL h.1
  have hU_in_R : ∀ w ∈ M '' IsEdgeChart.upper, w ∈ ⋃₀ ℛ →
      M '' IsEdgeChart.upper ⊆ ⋃₀ ℛ ∧ M '' IsEdgeChart.upper ⊆ K ∩ (Γ.U \ Γ.V)ᶜ := by
    intro w hwU hwℛ
    obtain ⟨r, hrℛ, hwr⟩ := mem_sUnion.mp hwℛ
    have h_sub_r : M '' IsEdgeChart.upper ⊆ r :=
      subset_region (hℛ hrℛ) c.upper_conn c.upper_disjoint hwU hwr
    have h_sub_ℛ : M '' IsEdgeChart.upper ⊆ ⋃₀ ℛ := h_sub_r.trans (subset_sUnion_of_mem hrℛ)
    refine ⟨h_sub_ℛ, fun u huU => ⟨⟨?_, subset_closure (h_sub_ℛ huU)⟩, ?_⟩⟩
    · obtain ⟨z_u, hz_u, rfl⟩ := huU
      exact ⟨z_u, hz_u.1, rfl⟩
    · exact fun h => disjoint_left.mp c.upper_disjoint huU h.1
  obtain ⟨t₁, ⟨ht₁_ab, ⟨O₁, ht₁_O₁, hO₁_open, K₁, hK₁_sc, hK₁Z, hO₁K₁, hO₁_join⟩⟩⟩ :=
    mem_closure_iff.mp ht₀_cl (Ioo a b) isOpen_Ioo ⟨c.left, c.right⟩
  have hγt₁_ball : γ t₁ ∈ M '' {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ z.im = 0} := by
    rw [c.ball_eq]
    exact ⟨t₁, ht₁_ab, rfl⟩
  obtain ⟨z₁, ⟨hz₁_ball, hz₁_im⟩, hMz₁⟩ := hγt₁_ball
  have hγt₁_O : γ t₁ ∈ O₁ ∩ O := ⟨ht₁_O₁, z₁, hz₁_ball, hMz₁⟩
  obtain ⟨E, E', hE, hE', hγt₁_E', hE'E, hE_sub, -⟩ :=
    exists_closedDisc_nbhd hS (hO₁_open.inter hO_open) hγt₁_O
  have hcont_z₁ : ContinuousAt M z₁ :=
    c.cont.continuousAt (mem_of_superset (Metric.isOpen_ball.mem_nhds hz₁_ball)
      Metric.ball_subset_closedBall)
  have hnhds : M ⁻¹' E' ∩ Metric.ball (0 : ℂ) 1 ∈ 𝓝 z₁ :=
    Filter.inter_mem (hcont_z₁.preimage_mem_nhds (hE'.mem_nhds (hMz₁.symm ▸ hγt₁_E')))
      (Metric.isOpen_ball.mem_nhds hz₁_ball)
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hnhds
  let w_low : ℂ := z₁ - ((δ / 2 : ℝ) : ℂ) * Complex.I
  let w_up : ℂ := z₁ + ((δ / 2 : ℝ) : ℂ) * Complex.I
  have hw_low_mem : w_low ∈ Metric.ball z₁ δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos)]
    linarith
  have hw_up_mem : w_up ∈ Metric.ball z₁ δ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos)]
    linarith
  have hw_low_in : w_low ∈ IsEdgeChart.lower := by
    refine ⟨Metric.ball_subset_closedBall (hδ_ball hw_low_mem).2, ?_⟩
    simp [w_low, hz₁_im]
    linarith
  have hw_up_in : w_up ∈ IsEdgeChart.upper := by
    refine ⟨Metric.ball_subset_closedBall (hδ_ball hw_up_mem).2, ?_⟩
    simp [w_up, hz₁_im]
    linarith
  let x_L : S := M w_low
  let x_U : S := M w_up
  have hx_L_L : x_L ∈ M '' IsEdgeChart.lower := ⟨w_low, hw_low_in, rfl⟩
  have hx_U_U : x_U ∈ M '' IsEdgeChart.upper := ⟨w_up, hw_up_in, rfl⟩
  have hx_L_E' : x_L ∈ E' := (hδ_ball hw_low_mem).1
  have hx_U_E' : x_U ∈ E' := (hδ_ball hw_up_mem).1
  refine ⟨O, ht₀_O, hO_open, K, hK_sc, hKZ, hOK, fun x hx y hy => ?_⟩
  rcases h_side x hx with hxL | hxU <;> rcases h_side y hy with hyL | hyU
  · obtain ⟨_, hL_sub⟩ := hL_in_R x hxL hx.2
    obtain ⟨p₀, hp₀⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x hxL y hyL).mono hL_sub
    let p : Path (⟨x, subset_closure hx.2⟩ : Z) ⟨y, subset_closure hy.2⟩ :=
      pathCod p₀ (subset_closure hx.2) (subset_closure hy.2) fun u => hKZ (hp₀ u).1
    exact ⟨p, p, fun u => (hp₀ u).1, fun u => (hp₀ u).2, Path.Homotopic.refl p⟩
  · obtain ⟨hL_ℛ, hL_sub⟩ := hL_in_R x hxL hx.2
    obtain ⟨hU_ℛ, hU_sub⟩ := hU_in_R y hyU hy.2
    have hc_disc_Z : c.disc ⊆ Z := by
      rintro _ ⟨w, hw, rfl⟩
      rcases IsEdgeChart.cases_of_closedBall hw with h | h | h
      · exact subset_closure (hL_ℛ ⟨w, h, rfl⟩)
      · have : M w ∈ γ '' Icc a b := c.closed_eq ▸ ⟨w, ⟨hw, h⟩, rfl⟩
        obtain ⟨t, _, hMt⟩ := this
        rw [← hMt]
        exact hγ_mem_Z t
      · exact subset_closure (hU_ℛ ⟨w, h, rfl⟩)
    have hEZ : E ⊆ Z := fun w hw => hc_disc_Z (hOD (hE_sub hw).2)
    have hEK : E ⊆ K := fun w hw => ⟨hOD (hE_sub hw).2, hEZ hw⟩
    have hEK₁ : E ⊆ K₁ := fun w hw => hO₁K₁ ⟨(hE_sub hw).1, hEZ hw⟩
    have hx_L_O₁ : x_L ∈ O₁ ∩ ⋃₀ ℛ := ⟨(hE_sub (hE'E hx_L_E')).1, hL_ℛ hx_L_L⟩
    have hx_U_O₁ : x_U ∈ O₁ ∩ ⋃₀ ℛ := ⟨(hE_sub (hE'E hx_U_E')).1, hU_ℛ hx_U_U⟩
    obtain ⟨p₁, q₀, hp₁K₁, hq₀G, hp₁q₀⟩ := hO₁_join x_L hx_L_O₁ x_U hx_U_O₁
    obtain ⟨p₀_S, hp₀E⟩ := hE.isPathConnected.joinedIn x_L (hE'E hx_L_E') x_U (hE'E hx_U_E')
    let p₀ : Path (⟨x_L, subset_closure hx_L_O₁.2⟩ : Z) ⟨x_U, subset_closure hx_U_O₁.2⟩ :=
      pathCod p₀_S (subset_closure hx_L_O₁.2) (subset_closure hx_U_O₁.2) fun u => hEZ (hp₀E u)
    have hp₀K : ∀ u, (p₀ u).1 ∈ K := fun u => hEK (hp₀E u)
    have hp₀K₁ : ∀ u, (p₀ u).1 ∈ K₁ := fun u => hEK₁ (hp₀E u)
    have hp₀p₁ : p₀.Homotopic p₁ :=
      homotopic_of_mem hK₁_sc hK₁Z p₀ p₁
        (hO₁K₁ ⟨hx_L_O₁.1, subset_closure hx_L_O₁.2⟩)
        (hO₁K₁ ⟨hx_U_O₁.1, subset_closure hx_U_O₁.2⟩) hp₀K₁ hp₁K₁
    have hp₀q₀ : p₀.Homotopic q₀ := hp₀p₁.trans hp₁q₀
    obtain ⟨α_S, hα⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x hxL x_L hx_L_L).mono
      hL_sub
    obtain ⟨β_S, hβ⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x_U hx_U_U y hyU).mono
      hU_sub
    let α : Path (⟨x, subset_closure hx.2⟩ : Z) ⟨x_L, subset_closure hx_L_O₁.2⟩ :=
      pathCod α_S (subset_closure hx.2) (subset_closure hx_L_O₁.2) fun u => hKZ (hα u).1
    let β : Path (⟨x_U, subset_closure hx_U_O₁.2⟩ : Z) ⟨y, subset_closure hy.2⟩ :=
      pathCod β_S (subset_closure hx_U_O₁.2) (subset_closure hy.2) fun u => hKZ (hβ u).1
    refine ⟨α.trans (p₀.trans β), α.trans (q₀.trans β),
      sub_path_trans_mem (fun u => (hα u).1) (sub_path_trans_mem hp₀K fun u => (hβ u).1),
      sub_path_trans_mem (fun u => (hα u).2) (sub_path_trans_mem hq₀G fun u => (hβ u).2),
      (Path.Homotopic.refl α).hcomp (hp₀q₀.hcomp (Path.Homotopic.refl β))⟩
  · obtain ⟨hU_ℛ, hU_sub⟩ := hU_in_R x hxU hx.2
    obtain ⟨hL_ℛ, hL_sub⟩ := hL_in_R y hyL hy.2
    have hc_disc_Z : c.disc ⊆ Z := by
      rintro _ ⟨w, hw, rfl⟩
      rcases IsEdgeChart.cases_of_closedBall hw with h | h | h
      · exact subset_closure (hL_ℛ ⟨w, h, rfl⟩)
      · have : M w ∈ γ '' Icc a b := c.closed_eq ▸ ⟨w, ⟨hw, h⟩, rfl⟩
        obtain ⟨t, _, hMt⟩ := this
        rw [← hMt]
        exact hγ_mem_Z t
      · exact subset_closure (hU_ℛ ⟨w, h, rfl⟩)
    have hEZ : E ⊆ Z := fun w hw => hc_disc_Z (hOD (hE_sub hw).2)
    have hEK : E ⊆ K := fun w hw => ⟨hOD (hE_sub hw).2, hEZ hw⟩
    have hEK₁ : E ⊆ K₁ := fun w hw => hO₁K₁ ⟨(hE_sub hw).1, hEZ hw⟩
    have hx_L_O₁ : x_L ∈ O₁ ∩ ⋃₀ ℛ := ⟨(hE_sub (hE'E hx_L_E')).1, hL_ℛ hx_L_L⟩
    have hx_U_O₁ : x_U ∈ O₁ ∩ ⋃₀ ℛ := ⟨(hE_sub (hE'E hx_U_E')).1, hU_ℛ hx_U_U⟩
    obtain ⟨p₁, q₀, hp₁K₁, hq₀G, hp₁q₀⟩ := hO₁_join x_L hx_L_O₁ x_U hx_U_O₁
    obtain ⟨p₀_S, hp₀E⟩ := hE.isPathConnected.joinedIn x_L (hE'E hx_L_E') x_U (hE'E hx_U_E')
    let p₀ : Path (⟨x_L, subset_closure hx_L_O₁.2⟩ : Z) ⟨x_U, subset_closure hx_U_O₁.2⟩ :=
      pathCod p₀_S (subset_closure hx_L_O₁.2) (subset_closure hx_U_O₁.2) fun u => hEZ (hp₀E u)
    have hp₀K : ∀ u, (p₀ u).1 ∈ K := fun u => hEK (hp₀E u)
    have hp₀K₁ : ∀ u, (p₀ u).1 ∈ K₁ := fun u => hEK₁ (hp₀E u)
    have hp₀p₁ : p₀.Homotopic p₁ :=
      homotopic_of_mem hK₁_sc hK₁Z p₀ p₁
        (hO₁K₁ ⟨hx_L_O₁.1, subset_closure hx_L_O₁.2⟩)
        (hO₁K₁ ⟨hx_U_O₁.1, subset_closure hx_U_O₁.2⟩) hp₀K₁ hp₁K₁
    have hp₀q₀ : p₀.Homotopic q₀ := hp₀p₁.trans hp₁q₀
    obtain ⟨α_S, hα⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x hxU x_U hx_U_U).mono
      hU_sub
    obtain ⟨β_S, hβ⟩ := ((IsEdgeChart.lower_pathConnected c).joinedIn x_L hx_L_L y hyL).mono
      hL_sub
    let α : Path (⟨x, subset_closure hx.2⟩ : Z) ⟨x_U, subset_closure hx_U_O₁.2⟩ :=
      pathCod α_S (subset_closure hx.2) (subset_closure hx_U_O₁.2) fun u => hKZ (hα u).1
    let β : Path (⟨x_L, subset_closure hx_L_O₁.2⟩ : Z) ⟨y, subset_closure hy.2⟩ :=
      pathCod β_S (subset_closure hx_L_O₁.2) (subset_closure hy.2) fun u => hKZ (hβ u).1
    refine ⟨α.trans (p₀.symm.trans β), α.trans (q₀.symm.trans β),
      sub_path_trans_mem (fun u => (hα u).1) (sub_path_trans_mem (sub_path_symm_mem hp₀K) fun u
        => (hβ u).1),
      sub_path_trans_mem (fun u => (hα u).2) (sub_path_trans_mem (sub_path_symm_mem hq₀G) fun u
        => (hβ u).2),
      (Path.Homotopic.refl α).hcomp ((path_homotopic_symm hp₀q₀).hcomp (Path.Homotopic.refl β))⟩
  · obtain ⟨_, hU_sub⟩ := hU_in_R x hxU hx.2
    obtain ⟨p₀, hp₀⟩ := ((IsEdgeChart.upper_pathConnected c).joinedIn x hxU y hyU).mono hU_sub
    let p : Path (⟨x, subset_closure hx.2⟩ : Z) ⟨y, subset_closure hy.2⟩ :=
      pathCod p₀ (subset_closure hx.2) (subset_closure hy.2) fun u => hKZ (hp₀ u).1
    exact ⟨p, p, fun u => (hp₀ u).1, fun u => (hp₀ u).2, Path.Homotopic.refl p⟩

/-- Case 3: Every point `z ∈ e ∩ closure (⋃₀ ℛ)` (`e ∈ Γ.E`) has a `GoodOpenIn` neighborhood. -/
theorem exists_goodOpenIn_of_mem_edge [ConnectedSpace S] (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) {e : Set S}
    (he : e ∈ Γ.E) {z : S} (hze : z ∈ e) (hzZ : z ∈ closure (⋃₀ ℛ)) :
    ∃ O : Set S, z ∈ O ∧ GoodOpenIn Γ ℛ O := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hZn : IsGammaNice Γ (closure (⋃₀ ℛ)) := isGammaNice_closure_sUnion_regions hS Γ hℛ
  have heZ : e ⊆ closure (⋃₀ ℛ) := nice_edge hZn he ⟨z, hze, hzZ⟩
  have hcl_eZ : closure e ⊆ closure (⋃₀ ℛ) := closure_minimal heZ isClosed_closure
  set Z := closure (⋃₀ ℛ)
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
  have hγ_mem_Z : ∀ t : I, γ t ∈ Z := by
    intro t
    have ht_Ioo : t ∈ closure (Ioo (0 : I) 1) := by
      rw [closure_Ioo (zero_ne_one' I)]
      exact ⟨t.2.1, t.2.2⟩
    have := image_closure_subset_closure_image hγ ⟨t, ht_Ioo, rfl⟩
    rw [hγe] at this
    exact hcl_eZ this
  let T : Set I := {t : I | ∃ O : Set S, γ t ∈ O ∧ GoodOpenIn Γ ℛ O}
  have h0T : (0 : I) ∈ T := exists_goodOpenIn_of_mem_V hS Γ hℛ hγ0 (hγ_mem_Z 0)
  have h1T : (1 : I) ∈ T := exists_goodOpenIn_of_mem_V hS Γ hℛ hγ1 (hγ_mem_Z 1)
  have hT_open : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    rintro t ⟨O, htO, hGO⟩
    exact ⟨γ ⁻¹' O, fun s hs => ⟨O, hs, hGO⟩, hGO.1.preimage hγ, htO⟩
  have hT_closed : IsClosed T := by
    exact good_open_times_closed (S := S) hS Γ (ℛ := ℛ) hℛ (e := e) he hman γ hγ hγ0 hγ1 hinj
      hγe hγ_mem_Z h0T h1T
  have hT_univ : T = univ := IsClopen.eq_univ ⟨hT_closed, hT_open⟩ ⟨0, h0T⟩
  obtain ⟨t, -, rfl⟩ : z ∈ γ '' Ioo 0 1 := hγe.symm ▸ hze
  have htT : t ∈ T := hT_univ.symm ▸ mem_univ t
  exact htT

/-- Every point `z ∈ closure (⋃₀ ℛ)` on a closed surface `S` has a `GoodOpenIn` neighborhood. -/
theorem exists_goodOpenIn [ConnectedSpace S] (hS : IsClosedSurface S) (Γ : Drawing S)
    {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) {z : S} (hzZ : z ∈ closure (⋃₀ ℛ)) :
    ∃ O : Set S, z ∈ O ∧ GoodOpenIn Γ ℛ O := by
  by_cases hzV : z ∈ Γ.V
  · exact exists_goodOpenIn_of_mem_V hS Γ hℛ hzV hzZ
  · by_cases hzU : z ∈ Γ.U
    · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
      exact exists_goodOpenIn_of_mem_edge hS Γ hℛ he hze hzZ
    · exact exists_goodOpenIn_of_notMem_U hS Γ hℛ hzZ hzU

private theorem joinedIn_of_isArcConnected {X : Set S} (hX : IsArcConnected X) {x y : S}
    (hx : x ∈ X) (hy : y ∈ X) : JoinedIn X x y := by
  by_cases hxy : x = y
  · subst hxy; exact JoinedIn.refl hx
  · obtain ⟨L, hL, f, h0, h1⟩ := hX x hx y hy hxy
    exact (show JoinedIn L x y from
      ⟨⟨⟨fun t => (f t).1, by fun_prop⟩, h0, h1⟩, fun t => (f t).2⟩).mono hL

/-- Every path `p : Path a b` in `Z = closure (⋃₀ ℛ)` on a closed surface `S` whose endpoints lie in
`⋃₀ ℛ` is homotopic in `Z` (with fixed endpoints) to a path `q : Path a b` in `Z` with
`∀ t, (q t).1 ∈ (Γ.U \ Γ.V)ᶜ`. -/
theorem exists_homotopic_normal_path_in_closed [ConnectedSpace S] (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R)
    {a b : closure (⋃₀ ℛ)} (ha : a.1 ∈ ⋃₀ ℛ) (hb : b.1 ∈ ⋃₀ ℛ) (p : Path a b) :
    ∃ q : Path a b, p.Homotopic q ∧ ∀ t, (q t).1 ∈ (Γ.U \ Γ.V)ᶜ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let Z := closure (⋃₀ ℛ)
  have hSolid : IsSolid Z := isSolid_of_nice hS isClosed_closure
    (isGammaNice_closure_sUnion_regions hS Γ hℛ)
  have hnotU_of_mem_ℛ : ∀ {w : S}, w ∈ ⋃₀ ℛ → w ∉ Γ.U := by
    rintro w ⟨r, hr, hwr⟩
    exact region_subset (hℛ hr) hwr
  let good : Set I → Prop := fun W => IsOpen W ∧ ∃ U : Set S, GoodOpenIn Γ ℛ U ∧ ∀ t ∈ W,
    (p t).1 ∈ U
  have hp_cont : Continuous fun t : I => (p t).1 := continuous_subtype_val.comp p.continuous
  have hcover : (univ : Set I) ⊆ ⋃ W : {W : Set I // good W}, W.1 := by
    intro t _
    obtain ⟨U, htU, hGU⟩ := exists_goodOpenIn hS Γ hℛ (p t).2
    exact mem_iUnion.mpr ⟨⟨(fun s => (p s).1) ⁻¹' U, hGU.1.preimage hp_cont, U, hGU,
      fun _ hw => hw⟩, htU⟩
  obtain ⟨t, ht0, htmono, ⟨n₀, hn₀⟩, htW⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun W : {W : Set I // good W} => W.2.1) hcover
  have key : ∀ n (U : Set S), IsOpen U → (p (t n)).1 ∈ U →
      ∃ (x : S) (hx : x ∈ U ∩ ⋃₀ ℛ) (α : Path (p (t n)) ⟨x, subset_closure hx.2⟩)
        (q : Path (p 0) ⟨x, subset_closure hx.2⟩),
        (∀ u, (α u).1 ∈ U) ∧ (∀ u, (q u).1 ∈ (Γ.U \ Γ.V)ᶜ) ∧
        (p.subpath 0 (t n)).Homotopic (q.trans α.symm) := by
    intro n
    induction n with
    | zero =>
      intro U _ hpU
      rw [ht0] at hpU ⊢
      have hp0_ℛ : (p 0).1 ∈ ⋃₀ ℛ := by rw [p.source]; exact ha
      have hp0_notU : (p 0).1 ∉ Γ.U := hnotU_of_mem_ℛ hp0_ℛ
      refine ⟨(p 0).1, ⟨hpU, hp0_ℛ⟩, Path.refl (p 0), Path.refl (p 0),
        fun _ => hpU, fun _ h => hp0_notU h.1, ?_⟩
      rw [Path.subpath_self]
      exact (Path.Homotopic.refl_trans (Path.refl (p 0))).symm
    | succ n ih =>
      intro U' hU'_open hp_U'
      obtain ⟨⟨W, _, U_n, hUn, hW_Un⟩, hsub⟩ := htW n
      have hle : t n ≤ t (n + 1) := htmono (Nat.le_succ n)
      have hp_Un : ∀ w ∈ Icc (t n) (t (n + 1)), (p w).1 ∈ U_n := fun w hw => hW_Un w (hsub hw)
      obtain ⟨hUn_open, K_n, hK_n_sc, hK_n_Z, hUn_Kn, hUn_join⟩ := hUn
      obtain ⟨x_n, hx_n, α_n, q_n, hα_n, hq_n, hhom_n⟩ :=
        ih U_n hUn_open (hp_Un (t n) ⟨le_rfl, hle⟩)
      have hp_inter : (p (t (n + 1))).1 ∈ U_n ∩ U' := ⟨hp_Un (t (n + 1)) ⟨hle, le_rfl⟩, hp_U'⟩
      obtain ⟨V, hV_sub, hp_V, hV_open, hZV_arc⟩ :=
        hSolid.1 (p (t (n + 1))).1 (p (t (n + 1))).2 (U_n ∩ U') (hUn_open.inter hU'_open) hp_inter
      obtain ⟨x', hx'_V, hx'_ℛ⟩ := mem_closure_iff.mp (p (t (n + 1))).2 V hV_open hp_V
      have hx'_Un : x' ∈ U_n ∩ ⋃₀ ℛ := ⟨(hV_sub hx'_V).1, hx'_ℛ⟩
      have hx'_U' : x' ∈ U' ∩ ⋃₀ ℛ := ⟨(hV_sub hx'_V).2, hx'_ℛ⟩
      obtain ⟨α'_S, hα'_ZV⟩ :=
        joinedIn_of_isArcConnected hZV_arc
          ⟨(p (t (n + 1))).2, hp_V⟩ ⟨subset_closure hx'_ℛ, hx'_V⟩
      let α' : Path (p (t (n + 1))) ⟨x', subset_closure hx'_ℛ⟩ :=
        pathCod α'_S (p (t (n + 1))).2 (subset_closure hx'_ℛ) fun u => (hα'_ZV u).1
      obtain ⟨r, s, hrK, hsG, hrs⟩ := hUn_join x_n hx_n x' hx'_Un
      have hpiece : ∀ u, ((p.subpath (t n) (t (n + 1))) u).1 ∈ K_n := by
        intro u
        have : (p.subpath (t n) (t (n + 1))) u ∈ p '' uIcc (t n) (t (n + 1)) := by
          rw [← Path.range_subpath]
          exact mem_range_self u
        obtain ⟨v, hv, hv'⟩ := this
        rw [uIcc_of_le hle] at hv
        rw [← hv']
        exact hUn_Kn ⟨hp_Un v hv, (p v).2⟩
      have hα_n_K : ∀ u, (α_n u).1 ∈ K_n := fun u => hUn_Kn ⟨hα_n u, (α_n u).2⟩
      have hα'_K : ∀ u, (α' u).1 ∈ K_n := fun u => hUn_Kn ⟨(hV_sub (hα'_ZV u).2).1, (hα'_ZV u).1⟩
      have h_K_hom : (α_n.symm.trans (p.subpath (t n) (t (n + 1)))).Homotopic (r.trans α'.symm) :=
        homotopic_of_mem hK_n_sc hK_n_Z _ _
          (hUn_Kn ⟨hx_n.1, subset_closure hx_n.2⟩)
          (hUn_Kn ⟨hp_inter.1, (p (t (n + 1))).2⟩)
          (sub_path_trans_mem (sub_path_symm_mem hα_n_K) hpiece)
          (sub_path_trans_mem hrK (sub_path_symm_mem hα'_K))
      have h_step_hom : (p.subpath 0 (t (n + 1))).Homotopic ((q_n.trans s).trans α'.symm) := by
        refine (Path.Homotopic.subpath_trans_subpath p 0 (t n) (t (n + 1))).symm.trans ?_
        refine (hhom_n.hcomp (Path.Homotopic.refl _)).trans ?_
        refine (Path.Homotopic.trans_assoc q_n α_n.symm _).trans ?_
        refine ((Path.Homotopic.refl q_n).hcomp (h_K_hom.trans (hrs.hcomp
          (Path.Homotopic.refl α'.symm)))).trans ?_
        exact (Path.Homotopic.trans_assoc q_n s α'.symm).symm
      exact ⟨x', hx'_U', α', q_n.trans s,
        fun u => (hV_sub (hα'_ZV u).2).2, sub_path_trans_mem hq_n hsG, h_step_hom⟩
  obtain ⟨r_b, hr_b, hb_rb⟩ := hb
  have hr_b_open : IsOpen r_b := region_isOpen (hℛ hr_b)
  have htn₀ : t n₀ = 1 := hn₀ n₀ le_rfl
  have hp_tn₀ : p (t n₀) = b := by rw [htn₀, p.target]
  obtain ⟨x, hx, α, q, hα_rb, hqG, hhom⟩ := key n₀ r_b hr_b_open (hp_tn₀.symm ▸ hb_rb)
  have hα_G : ∀ u, (α.symm u).1 ∈ (Γ.U \ Γ.V)ᶜ := fun u => by
    change (α (σ u)).1 ∈ (Γ.U \ Γ.V)ᶜ
    exact fun h => hnotU_of_mem_ℛ ⟨r_b, hr_b, hα_rb (σ u)⟩ h.1
  let q_final : Path a b := (q.trans α.symm).cast p.source.symm hp_tn₀.symm
  refine ⟨q_final, ?_, fun u => ?_⟩
  · have hsub01 : (p.subpath 0 (t n₀)).cast p.source.symm hp_tn₀.symm = p := by
      ext u
      change ((p.subpath 0 (t n₀)) u).1 = (p u).1
      rw [htn₀, Path.subpath_zero_one]
      rfl
    rw [← hsub01]
    exact Path.Homotopic.pathCast hhom p.source.symm hp_tn₀.symm
  · change ((q.trans α.symm) u).1 ∈ (Γ.U \ Γ.V)ᶜ
    exact sub_path_trans_mem hqG hα_G u

/-- Every closed curve `φ : C(Circle, S)` in `Z = closure (⋃₀ ℛ)` on a closed surface `S` is
homotopic in `Z` (`ClosedCurvesHomotopicIn Z φ ψ`) to a `Γ`-normal closed curve `ψ : C(Circle, S)`
in `Z`. -/
theorem exists_homotopic_normal_curve_in_closed [ConnectedSpace S] (hS : IsClosedSurface S)
    (Γ : Drawing S) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ Γ.R) (φ : C(Circle, S))
    (hφ : range φ ⊆ closure (⋃₀ ℛ)) :
    ∃ ψ : C(Circle, S), range ψ ⊆ closure (⋃₀ ℛ) ∩ (Γ.U \ Γ.V)ᶜ ∧
      ClosedCurvesHomotopicIn (closure (⋃₀ ℛ)) φ ψ := by
  have : T2Space S := hS.2.1
  set Z := closure (⋃₀ ℛ)
  have hSolid : IsSolid Z := isSolid_of_nice hS isClosed_closure
    (isGammaNice_closure_sUnion_regions hS Γ hℛ)
  have hφ_mem : ∀ z : Circle, φ z ∈ Z := fun z => hφ (mem_range_self z)
  obtain ⟨V, _, hp0_V, hV_open, hZV_arc⟩ :=
    hSolid.1 (φ 1) (hφ_mem 1) univ isOpen_univ (mem_univ _)
  obtain ⟨x₀, hx₀_V, hx₀_ℛ⟩ := mem_closure_iff.mp (hφ_mem 1) V hV_open hp0_V
  let z₀ : Z := ⟨x₀, subset_closure hx₀_ℛ⟩
  obtain ⟨α_S, hα_ZV⟩ :=
    joinedIn_of_isArcConnected hZV_arc ⟨hφ_mem 1, hp0_V⟩ ⟨z₀.2, hx₀_V⟩
  let α : Path (⟨φ 1, hφ_mem 1⟩ : Z) z₀ :=
    pathCod α_S (hφ_mem 1) z₀.2 fun u => (hα_ZV u).1
  let p₀ : Path (⟨φ 1, hφ_mem 1⟩ : Z) ⟨φ 1, hφ_mem 1⟩ :=
    { toFun := fun t => ⟨φ (arcParam 1 t), hφ_mem (arcParam 1 t)⟩
      continuous_toFun := Continuous.subtype_mk (φ.continuous.comp (arcParam 1).continuous) _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  let p₁ : Path (⟨φ 1, hφ_mem 1⟩ : Z) ⟨φ 1, hφ_mem 1⟩ := p₀.trans (α.trans α.symm)
  have hp₀_p₁ : p₀.Homotopic p₁ :=
    (Path.Homotopic.trans_refl p₀).symm.trans
      ((Path.Homotopic.refl p₀).hcomp (Path.Homotopic.trans_symm α).symm)
  let f₁ : C(I, S) := ⟨fun t => (p₁ t).1, continuous_subtype_val.comp p₁.continuous⟩
  have hf₁ : f₁ 0 = f₁ 1 := by simp [f₁]
  let φ₁ : C(Circle, S) := loopLift 1 f₁ hf₁
  have hφ₁_mem : ∀ z : Circle, φ₁ z ∈ Z := by
    intro z
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
    change loopLift 1 f₁ hf₁ (arcParam 1 t) ∈ Z
    rw [loopLift_apply]
    exact (p₁ t).2
  have hhom₁ : ClosedCurvesHomotopicIn Z φ φ₁ :=
    closedCurvesHomotopicIn_of_path 1 φ φ₁ p₀ p₁
      (fun _ => rfl)
      (fun t => (loopLift_apply 1 f₁ hf₁ t).symm)
      hp₀_p₁
  have hz₀_range : z₀ ∈ range p₁ := by
    change z₀ ∈ range (p₀.trans (α.trans α.symm))
    rw [Path.trans_range, Path.trans_range]
    exact Or.inr (Or.inl ⟨1, α.target⟩)
  obtain ⟨t₁, ht₁⟩ := hz₀_range
  let w₁ : Circle := arcParam 1 t₁
  have hφ₁_w₁ : (⟨φ₁ w₁, hφ₁_mem w₁⟩ : Z) = z₀ := by
    ext
    change loopLift 1 f₁ hf₁ (arcParam 1 t₁) = x₀
    rw [loopLift_apply]
    exact congrArg Subtype.val ht₁
  let p₂ : Path (⟨φ₁ w₁, hφ₁_mem w₁⟩ : Z) ⟨φ₁ w₁, hφ₁_mem w₁⟩ :=
    { toFun := fun t => ⟨φ₁ (arcParam w₁ t), hφ₁_mem (arcParam w₁ t)⟩
      continuous_toFun := Continuous.subtype_mk (φ₁.continuous.comp (arcParam w₁).continuous) _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  have hw₁_ℛ : (⟨φ₁ w₁, hφ₁_mem w₁⟩ : Z).1 ∈ ⋃₀ ℛ := by
    rw [hφ₁_w₁]
    exact hx₀_ℛ
  obtain ⟨q, hp₂_q, hq_G⟩ := exists_homotopic_normal_path_in_closed hS Γ hℛ hw₁_ℛ hw₁_ℛ p₂
  let f₂ : C(I, S) := ⟨fun t => (q t).1, continuous_subtype_val.comp q.continuous⟩
  have hf₂ : f₂ 0 = f₂ 1 := by simp [f₂]
  let ψ : C(Circle, S) := loopLift w₁ f₂ hf₂
  have hhom₂ : ClosedCurvesHomotopicIn Z φ₁ ψ :=
    closedCurvesHomotopicIn_of_path w₁ φ₁ ψ p₂ q
      (fun _ => rfl)
      (fun t => (loopLift_apply w₁ f₂ hf₂ t).symm)
      hp₂_q
  refine ⟨ψ, ?_, GraphMinor.Surface.ClosedCurvesHomotopicIn.trans hhom₁ hhom₂⟩
  rintro _ ⟨w, rfl⟩
  obtain ⟨t, rfl⟩ := arcParam_surjective w₁ w
  change loopLift w₁ f₂ hf₂ (arcParam w₁ t) ∈ Z ∩ (Γ.U \ Γ.V)ᶜ
  rw [loopLift_apply]
  exact ⟨(q t).2, hq_G t⟩

/-- Every closed curve `φ : C(Circle, S)` in `Z = closure (⋃₀ ℛ)` for a proper drawing `G` on a
connected surface `S` (`ℛ ⊆ G.R`) is homotopic in `Z` (`ClosedCurvesHomotopicIn Z φ ψ`) to a
`G`-normal closed curve `ψ : C(Circle, S)` in `Z`. -/
theorem exists_homotopic_normal_curve_in (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ G.R)
    (φ : C(Circle, S)) (hφ : range φ ⊆ closure (⋃₀ ℛ)) :
    ∃ ψ : C(Circle, S), range ψ ⊆ closure (⋃₀ ℛ) ∩ (G.U \ G.V)ᶜ ∧
      ClosedCurvesHomotopicIn (closure (⋃₀ ℛ)) φ ψ := by
  obtain ⟨T, topT, j, -, Γ, hT, hT_conn, hj, -, -, -, hΓU, -, hΓV, hℛ_map⟩ :=
    exists_capped_drawing hS G hG
  obtain ⟨ℛ_T, hℛ_T, hj_Z, -⟩ := hℛ_map ℛ hℛ
  let φ_T : C(Circle, T) := ⟨j ∘ φ, hj.continuous.comp φ.continuous⟩
  have hφ_T : range φ_T ⊆ closure (⋃₀ ℛ_T) := by
    rintro _ ⟨w, rfl⟩
    rw [← hj_Z]
    exact ⟨φ w, hφ (mem_range_self w), rfl⟩
  obtain ⟨ψ_T, hψ_T, H_T, hH_T, hH0, hH1⟩ :=
    exists_homotopic_normal_curve_in_closed hT Γ hℛ_T φ_T hφ_T
  have hψ_ex : ∀ w : Circle, ∃ x ∈ closure (⋃₀ ℛ), j x = ψ_T w := by
    intro w
    have hw : ψ_T w ∈ closure (⋃₀ ℛ_T) := (hψ_T (mem_range_self w)).1
    rwa [← hj_Z] at hw
  choose ψ₀ hψ₀_Z hψ₀_eq using hψ_ex
  have hψ₀_cont : Continuous ψ₀ := hj.isEmbedding.continuous_iff.mpr (by
    have : j ∘ ψ₀ = ψ_T := funext hψ₀_eq
    rw [this]
    exact ψ_T.continuous)
  let ψ : C(Circle, S) := ⟨ψ₀, hψ₀_cont⟩
  have hH_ex : ∀ p : Circle × I, ∃ x ∈ closure (⋃₀ ℛ), j x = H_T p := by
    intro p
    have hp : H_T p ∈ closure (⋃₀ ℛ_T) := hH_T p
    rwa [← hj_Z] at hp
  choose H₀ hH₀_Z hH₀_eq using hH_ex
  have hH₀_cont : Continuous H₀ := hj.isEmbedding.continuous_iff.mpr (by
    have : j ∘ H₀ = H_T := funext hH₀_eq
    rw [this]
    exact H_T.continuous)
  let H : C(Circle × I, S) := ⟨H₀, hH₀_cont⟩
  refine ⟨ψ, ?_, H, hH₀_Z, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    refine ⟨hψ₀_Z w, ?_⟩
    rintro ⟨hwU, hwV⟩
    have hw_not_bd : ψ w ∉ bd S := fun hbd => hwV (hG ⟨hbd, hwU⟩)
    have hjw_U : ψ_T w ∈ Γ.U := by
      rw [← hψ₀_eq w, hΓU]
      exact ⟨ψ w, Or.inl hwU, rfl⟩
    have hjw_notV : ψ_T w ∉ Γ.V := by
      intro hjV
      obtain ⟨y, hy, hjy⟩ := hΓV hjV
      rw [← hψ₀_eq w] at hjy
      rcases hj.injective hjy ▸ hy with h | h
      · exact hwV h
      · exact hw_not_bd h
    exact (hψ_T (mem_range_self w)).2 ⟨hjw_U, hjw_notV⟩
  · intro w
    exact hj.injective ((hH₀_eq (w, 0)).trans (hH0 w))
  · intro w
    exact hj.injective ((hH₀_eq (w, 1)).trans ((hH1 w).trans (hψ₀_eq w).symm))

/-- **(5.5)** of Graph Minors VII (Section 5, page 231):
"Let $G$ be a proper graph in a connected surface $\Sigma$, and let $Z$ be the closure of the
union of some of the regions of $G$, with $Z \ne \Sigma$. Then $Z$ is planar if and only if
every $G$-normal $O$-arc included in $Z$ is null-homotopic." -/
theorem theorem_5_5_proof (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ G.R)
    {Z : Set S} (hZ : Z = closure (⋃₀ ℛ)) (hZ_ne : Z ≠ univ) :
    IsPlanar Z ↔ ∀ F : Set S, F ⊆ Z → G.IsNormal F → IsOArc F → IsNullHomotopicOArc F := by
  have hZ_solid : IsSolid Z := hZ ▸ isSolid_closure_sUnion_regions hS G hG hℛ
  rw [theorem_5_1_proof hS hZ_solid hZ_ne]
  constructor
  · intro h F hFZ _ hF
    exact h F hF hFZ
  · intro h F₀ hF₀ hF₀Z
    by_contra hF₀_not_null
    obtain ⟨e₀⟩ := hF₀
    let φ₀ : C(Circle, S) := ⟨fun z => (e₀ z).1, continuous_subtype_val.comp e₀.continuous⟩
    have hφ₀_Z : range φ₀ ⊆ closure (⋃₀ ℛ) := by
      rw [← hZ]
      rintro _ ⟨w, rfl⟩
      exact hF₀Z (e₀ w).2
    have hφ₀_not_null : ¬ ClosedCurveIsNullHomotopicIn univ φ₀ := fun hnull =>
      hF₀_not_null ⟨e₀, hnull⟩
    obtain ⟨ψ, hψ_sub, hhom_Z⟩ := exists_homotopic_normal_curve_in hS hG hℛ φ₀ hφ₀_Z
    have hhom_univ : ClosedCurvesHomotopicIn univ φ₀ ψ := by
      obtain ⟨H, _, hH0, hH1⟩ := hhom_Z
      exact ⟨H, fun _ => mem_univ _, hH0, hH1⟩
    have hψ_not_null : ¬ ClosedCurveIsNullHomotopicIn univ ψ := fun hnull =>
      hφ₀_not_null (null_of_homotopic subset_rfl hhom_univ hnull)
    obtain ⟨F, hF_oarc, hF_sub, hF_not_null⟩ := theorem_11_2_proof hS ψ hψ_not_null
    have hFZ : F ⊆ Z := by
      rw [hZ]
      exact fun x hx => (hψ_sub (hF_sub hx)).1
    have hF_norm : G.IsNormal F := fun x ⟨hxF, hxU⟩ =>
      by_contra fun hxV => (hψ_sub (hF_sub hxF)).2 ⟨hxU, hxV⟩
    exact hF_not_null (h F hFZ hF_norm hF_oarc)

/-! ## 3. Proof of (5.6) (page 232) -/

/-- Pushforward of `IsSolid` along a closed embedding `j : S → T`. -/
theorem isSolid_image_of_isClosedEmbedding {T : Type u} [TopologicalSpace T] [T2Space T]
    {j : S → T} (hj : IsClosedEmbedding j) {Z : Set S} (hZ : IsSolid Z) :
    IsSolid (j '' Z) := by
  refine ⟨?_, hj.isClosedMap Z hZ.2⟩
  rintro _ ⟨z, hz, rfl⟩ U_T hU_T hjz_UT
  obtain ⟨V, hV_sub, hzV, hV_open, h_arc⟩ :=
    hZ.1 z hz (j ⁻¹' U_T) (hU_T.preimage hj.continuous) hjz_UT
  obtain ⟨W_T, hW_T_open, hW_T_pre⟩ := hj.isInducing.isOpen_iff.mp hV_open
  have hjz_WT : j z ∈ W_T := by
    change z ∈ j ⁻¹' W_T
    rwa [hW_T_pre]
  refine ⟨W_T ∩ U_T, inter_subset_right, ⟨hjz_WT, hjz_UT⟩, hW_T_open.inter hU_T, ?_⟩
  rintro _ ⟨⟨a, haZ, rfl⟩, haW, haU⟩ _ ⟨⟨b, hbZ, rfl⟩, hbW, hbU⟩ hab
  have haV : a ∈ Z ∩ V := ⟨haZ, hW_T_pre ▸ haW⟩
  have hbV : b ∈ Z ∩ V := ⟨hbZ, hW_T_pre ▸ hbW⟩
  obtain ⟨L, hL_sub, hL_line⟩ := h_arc a haV b hbV (fun h => hab (congrArg j h))
  refine ⟨j '' L, ?_, hL_line.map_of_embedding hj.isEmbedding⟩
  rintro _ ⟨x, hxL, rfl⟩
  obtain ⟨hxZ, hxV⟩ := hL_sub hxL
  have hjx_WT : j x ∈ W_T := by
    change x ∈ j ⁻¹' W_T
    rwa [hW_T_pre]
  exact ⟨⟨x, hxZ, rfl⟩, hjx_WT, hV_sub hxV⟩

/-- Pullback of `IsOArc` along an embedding `j : S → T` when `F' ⊆ range j`. -/
theorem IsOArc.pull_of_embedding [T2Space S] {T : Type u} [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {F' : Set T} (hF' : IsOArc F') (hsub : F' ⊆ range j) :
    IsOArc (j ⁻¹' F') := by
  obtain ⟨e'⟩ := id hF'
  have hex : ∀ w : Circle, ∃ x : S, j x = (e' w).1 := fun w => hsub (e' w).2
  choose f hf using hex
  have hfc : Continuous f := hj.continuous_iff.mpr (by
    have : j ∘ f = fun w => (e' w).1 := funext hf
    rw [this]
    exact continuous_subtype_val.comp e'.continuous)
  let g : Circle → j ⁻¹' F' := fun w => ⟨f w, by
    change j (f w) ∈ F'
    rw [hf w]
    exact (e' w).2⟩
  have hgc : Continuous g := Continuous.subtype_mk hfc _
  have hgbij : Function.Bijective g := by
    refine ⟨fun w₁ w₂ h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · have h1 : j (f w₁) = j (f w₂) := congrArg (fun u : j ⁻¹' F' => j u.1) h
      rw [hf w₁, hf w₂] at h1
      exact e'.injective (Subtype.ext h1)
    · obtain ⟨w, hw⟩ := e'.surjective ⟨j x, hx⟩
      refine ⟨w, Subtype.ext (hj.injective ?_)⟩
      rw [hf w]
      exact congrArg Subtype.val hw
  exact ⟨hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgbij)⟩

/-- Capped-cuff version of (5.5): if `(S', j, D)` is a capped cuff of `(S, C)` and
`Z = closure (⋃₀ ℛ)` (`ℛ ⊆ G.R`), then `j '' Z` is planar in `S'` if and only if for every
`G`-normal `O`-arc `F ⊆ Z`, `j '' F` is null-homotopic in `S'`. -/
theorem theorem_5_5_cappedCuff (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {ℛ : Set (Set S)} (hℛ : ℛ ⊆ G.R)
    {Z : Set S} (hZ : Z = closure (⋃₀ ℛ))
    {C : Set S} {S' : Type u} [TopologicalSpace S'] {j : S → S'} {D : Set S'}
    (hCap : IsCappedCuff C S' j D) :
    IsPlanar (j '' Z) ↔
      ∀ F : Set S, F ⊆ Z → G.IsNormal F → IsOArc F → IsNullHomotopicOArc (j '' F) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hS' : IsSurface S' := hCap.isSurface
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := hCap.connectedSpace hS
  have hj_closed : IsClosedEmbedding j :=
    hCap.isEmbedding.continuous.isClosedEmbedding hCap.isEmbedding.injective
  have hZ_solid : IsSolid (j '' Z) :=
    isSolid_image_of_isClosedEmbedding hj_closed (hZ ▸ isSolid_closure_sUnion_regions hS G hG hℛ)
  have hjZ_ne : j '' Z ≠ univ := by
    intro heq
    obtain ⟨w, hwD, hw_not_bd⟩ := hCap.isClosedDisc.nonempty_discInt
    have hw_range : w ∈ range j := (image_subset_range j Z) (heq.symm ▸ mem_univ w)
    have hw_inter : w ∈ range j ∩ D := ⟨hw_range, hwD⟩
    rw [hCap.inter_eq, ← hCap.discBd_eq] at hw_inter
    exact hw_not_bd hw_inter
  rw [theorem_5_1_proof hS' hZ_solid hjZ_ne]
  constructor
  · intro h F hFZ _ hF
    exact h (j '' F) (isOArc_image hF hCap.isEmbedding.continuous.continuousOn
      hCap.isEmbedding.injective.injOn)
      (image_mono hFZ)
  · intro h F' hF' hF'Z
    by_contra hF'_not_null
    obtain ⟨e₀'⟩ := hF'
    have hex : ∀ w : Circle, ∃ x ∈ Z, j x = (e₀' w).1 := fun w => hF'Z (e₀' w).2
    choose φ₀_fun hφ₀_mem hφ₀_eq using hex
    have hφ₀_cont : Continuous φ₀_fun := hCap.isEmbedding.continuous_iff.mpr (by
      have : j ∘ φ₀_fun = fun w => (e₀' w).1 := funext hφ₀_eq
      rw [this]
      exact continuous_subtype_val.comp e₀'.continuous)
    let φ₀ : C(Circle, S) := ⟨φ₀_fun, hφ₀_cont⟩
    have hφ₀_Z : range φ₀ ⊆ closure (⋃₀ ℛ) := by
      rw [← hZ]
      rintro _ ⟨w, rfl⟩
      exact hφ₀_mem w
    obtain ⟨ψ, hψ_sub, hhom_Z⟩ := exists_homotopic_normal_curve_in hS hG hℛ φ₀ hφ₀_Z
    let φ₀' : C(Circle, S') := ⟨fun w => (e₀' w).1, continuous_subtype_val.comp e₀'.continuous⟩
    let ψ' : C(Circle, S') := ⟨j ∘ ψ, hCap.isEmbedding.continuous.comp ψ.continuous⟩
    have hhom_S' : ClosedCurvesHomotopicIn univ φ₀' ψ' := by
      obtain ⟨H, _, hH0, hH1⟩ := hhom_Z
      refine ⟨⟨j ∘ H, hCap.isEmbedding.continuous.comp H.continuous⟩, fun _ => mem_univ _, ?_, ?_⟩
      · intro w; exact (congrArg j (hH0 w)).trans (hφ₀_eq w)
      · intro w; exact congrArg j (hH1 w)
    have hφ₀'_not_null : ¬ ClosedCurveIsNullHomotopicIn univ φ₀' := fun hnull =>
      hF'_not_null ⟨e₀', hnull⟩
    have hψ'_not_null : ¬ ClosedCurveIsNullHomotopicIn univ ψ' := fun hnull =>
      hφ₀'_not_null (null_of_homotopic subset_rfl hhom_S' hnull)
    obtain ⟨F₁', hF₁'_oarc, hF₁'_sub, hF₁'_not_null⟩ := theorem_11_2_proof hS' ψ' hψ'_not_null
    have hF₁'_range : F₁' ⊆ range j := by
      intro y hy
      obtain ⟨w, rfl⟩ := hF₁'_sub hy
      exact ⟨ψ w, rfl⟩
    let F₁ : Set S := j ⁻¹' F₁'
    have hF₁_oarc : IsOArc F₁ := IsOArc.pull_of_embedding hCap.isEmbedding hF₁'_oarc hF₁'_range
    have hjF₁ : j '' F₁ = F₁' := image_preimage_eq_of_subset hF₁'_range
    have hF₁_Z : F₁ ⊆ Z := by
      rw [hZ]
      intro x hx
      obtain ⟨w, hw⟩ := hF₁'_sub hx
      have hxw : ψ w = x := hCap.isEmbedding.injective hw
      exact hxw ▸ (hψ_sub (mem_range_self w)).1
    have hF₁_norm : G.IsNormal F₁ := by
      rintro x ⟨hxF₁, hxU⟩
      obtain ⟨w, hw⟩ := hF₁'_sub hxF₁
      have hxw : ψ w = x := hCap.isEmbedding.injective hw
      by_contra hxV
      exact (hψ_sub (mem_range_self w)).2 (hxw.symm ▸ ⟨hxU, hxV⟩)
    exact hF₁'_not_null (hjF₁ ▸ h F₁ hF₁_Z hF₁_norm hF₁_oarc)

/-- Every open subset of a surface `S` is locally arc-connected (`IsLocallyArcConnected`). -/
theorem isLocallyArcConnected_of_isOpen (hS : IsSurface S) {Z : Set S} (hZ : IsOpen Z) :
    IsLocallyArcConnected Z := by
  intro x hx A hA hxA
  obtain ⟨W, hW_sub, hxW, hW_open, hW_arc, _, _⟩ :=
    exists_chart_ball_subset hS x (hZ.inter hA) ⟨hx, hxA⟩
  exact ⟨W, hW_sub.trans inter_subset_right, hxW, hW_open,
    (inter_eq_right.mpr (hW_sub.trans inter_subset_left)).symm ▸ hW_arc⟩

/-- Every connected open subset of a surface `S` is arc-connected (`IsArcConnected`). -/
theorem isArcConnected_of_isOpen_of_isConnected (hS : IsSurface S) {Z : Set S}
    (hZ_open : IsOpen Z) (hZ_conn : IsConnected Z) : IsArcConnected Z :=
  theorem_11_4_proof hS hZ_conn (isLocallyArcConnected_of_isOpen hS hZ_open)

/-- For any proper drawing `G` on a connected surface `S`, `G.R` is finite. -/
theorem finite_regions_of_isProper (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) : G.R.Finite := by
  obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, -, -, -, -, -, -, hℛ_map⟩ :=
    exists_capped_drawing hS G hG
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  have hfinΓ : Γ.R.Finite := finite_R hT Γ
  have hex : ∀ r : G.R, ∃ R' ∈ Γ.R, R' ⊆ j '' (r.1 \ bd S) := by
    rintro ⟨r, hr⟩
    obtain ⟨ℛ_T, hℛ_T, -, hsU⟩ := hℛ_map {r} (singleton_subset_iff.mpr hr)
    rw [sUnion_singleton] at hsU
    obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
    have hx₀_cl : x₀ ∈ closure (bd S)ᶜ := mem_closure_compl_bd (hS.2.2 x₀)
    obtain ⟨x, hxr, hx_bd⟩ := mem_closure_iff.mp hx₀_cl r (region_isOpen hr) hx₀r
    have hjx : j x ∈ ⋃₀ ℛ_T := hsU ▸ ⟨x, ⟨hxr, hx_bd⟩, rfl⟩
    obtain ⟨R', hR'ℛ, hjxR'⟩ := mem_sUnion.mp hjx
    exact ⟨R', hℛ_T hR'ℛ, (subset_sUnion_of_mem hR'ℛ).trans (le_of_eq hsU)⟩
  choose f hf_mem hf_sub using hex
  have : Finite Γ.R := hfinΓ.to_subtype
  have h_inj : Function.Injective (fun r : G.R => (⟨f r, hf_mem r⟩ : Γ.R)) := by
    intro r₁ r₂ heq
    have hfeq : f r₁ = f r₂ := congrArg Subtype.val heq
    obtain ⟨y, hy⟩ := region_nonempty (hf_mem r₁)
    obtain ⟨x₁, ⟨hx₁, _⟩, hjx₁⟩ := hf_sub r₁ hy
    obtain ⟨x₂, ⟨hx₂, _⟩, hjx₂⟩ := hf_sub r₂ (hfeq ▸ hy)
    have hxx : x₁ = x₂ := hj.injective (hjx₁.trans hjx₂.symm)
    exact Subtype.ext (region_eq_of_mem r₁.2 r₂.2 hx₁ (hxx ▸ hx₂))
  exact Finite.of_injective _ h_inj

/-- For any proper drawing `G` on a connected surface `S`, `closure (⋃₀ G.R) = univ`. -/
theorem closure_sUnion_regions_eq_univ (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) : closure (⋃₀ G.R) = univ := by
  obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, hK, hunion, hinter, hΓU, -, -, -⟩ :=
    exists_capped_drawing hS G hG
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  apply eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro O hO hxO
  have hx_cl : x ∈ closure (bd S)ᶜ := mem_closure_compl_bd (hS.2.2 x)
  obtain ⟨w, hwO, hw_bd⟩ := mem_closure_iff.mp hx_cl O hO hxO
  obtain ⟨W_T, hW_T_open, hW_T_pre⟩ := hj.isInducing.isOpen_iff.mp hO
  have hjw_WT : j w ∈ W_T ∩ Kᶜ := by
    refine ⟨?_, fun hjwK => ?_⟩
    · change w ∈ j ⁻¹' W_T; rwa [hW_T_pre]
    · have : j w ∈ range j ∩ K := ⟨⟨w, rfl⟩, hjwK⟩
      rw [hinter] at this
      obtain ⟨w', hw'bd, hjw'⟩ := this
      exact hw_bd (hj.injective hjw' ▸ hw'bd)
  obtain ⟨y, ⟨hyWT, hyK⟩, hyU⟩ :=
    exists_notMem_U (Γ := Γ) hT (hW_T_open.inter hK.isOpen_compl) ⟨j w, hjw_WT⟩
  have hy_range : y ∈ range j := (hunion.symm ▸ mem_univ y).resolve_right hyK
  obtain ⟨z, rfl⟩ := hy_range
  have hzO : z ∈ O := by rw [← hW_T_pre]; exact hyWT
  have hzU : z ∉ G.U := fun hzG => hyU (hΓU ▸ ⟨z, Or.inl hzG, rfl⟩)
  obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
  exact ⟨z, hzO, mem_sUnion.mpr ⟨r, hr, hzr⟩⟩

/-- Every point `a ∈ closure r ∩ (G.U \ G.V)ᶜ` (`r ∈ G.R`) is joined in `r ∪ {a}` to some point
of `r`. -/
theorem joinedIn_region_of_mem_closure (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {r : Set S} (hr : r ∈ G.R)
    {a : S} (har : a ∈ closure r) (ha_norm : a ∈ (G.U \ G.V)ᶜ) :
    ∃ w ∈ r, JoinedIn (r ∪ {a}) a w := by
  classical
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  by_cases haU : a ∈ G.U
  · have haV : a ∈ G.V := by_contra fun haV => ha_norm ⟨haU, haV⟩
    obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, -, -, -, hΓU, hGV, -, hℛ_map⟩ :=
      exists_capped_drawing hS G hG
    have : T2Space T := hT.2.1
    have : LocallyPathConnectedSpace T := IsClosedSurface.locallyPathConnectedSpace hT
    obtain ⟨ℛ_T, hℛ_T, h_cl_eq, hsU⟩ := hℛ_map {r} (singleton_subset_iff.mpr hr)
    rw [sUnion_singleton] at h_cl_eq hsU
    have hja_V : j a ∈ Γ.V := hGV ⟨a, haV, rfl⟩
    have hja_cl : j a ∈ closure (⋃₀ ℛ_T) := h_cl_eq ▸ ⟨a, har, rfl⟩
    have hfinℛ : ℛ_T.Finite := (finite_R hT Γ).subset hℛ_T
    have hja_bi : j a ∈ ⋃ p ∈ ℛ_T, closure p := by
      have heq : closure (⋃₀ ℛ_T) = ⋃ p ∈ ℛ_T, closure p := by
        rw [sUnion_eq_biUnion, hfinℛ.closure_biUnion]
      rwa [← heq]
    obtain ⟨p, hpℛ, hjap⟩ := mem_iUnion₂.mp hja_bi
    have hp : p ∈ Γ.R := hℛ_T hpℛ
    have hp_sub : p ⊆ j '' r :=
      (subset_sUnion_of_mem hpℛ).trans ((le_of_eq hsU).trans (image_mono sdiff_subset))
    obtain ⟨γ, hγ⟩ := exists_edgePar Γ
    rcases isEmpty_or_nonempty (halfEdges Γ γ (j a)) with h0 | ⟨⟨he_pair, hhe_mem⟩⟩
    · have h2 : ¬ 2 ≤ Nat.card (halfEdges Γ γ (j a)) := by
        have : Nat.card (halfEdges Γ γ (j a)) = 0 := Nat.card_eq_zero.mpr (Or.inl h0)
        omega
      obtain ⟨W_p, hW_p, hja_Wp, hWp_sub⟩ := exists_nbhd_of_few hT hγ hja_V h2 hp hjap
      have hno : ∀ g ∈ Γ.E, j a ∉ closure g := by
        intro g hg hjag
        obtain ⟨b, hb⟩ := exists_end_eq hγ hg hja_V hjag
        exact h0.false ⟨(g, b), hg, hb⟩
      let T_cl : Set T := (Γ.V \ {j a}) ∪ ⋃ g ∈ Γ.E, closure g
      have hT_cl : IsClosed T_cl := (Γ.finite_V.subset sdiff_subset).isClosed.union
        (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
      have hja_Tcl : j a ∉ T_cl := by
        rintro (h | h)
        · exact h.2 rfl
        · obtain ⟨g, hg, hjag⟩ := mem_iUnion₂.mp h
          exact hno g hg hjag
      obtain ⟨D, D', hD, hD', hja_D', hD'D, hDT, -⟩ :=
        exists_closedDisc_nbhd hT (hW_p.inter hT_cl.isOpen_compl) ⟨hja_Wp, hja_Tcl⟩
      obtain ⟨y, hyD', hyp⟩ := mem_closure_iff.mp hjap D' hD' hja_D'
      have hD_sub : D ⊆ p ∪ {j a} := by
        intro u huD
        by_cases hu_ja : u = j a
        · exact Or.inr hu_ja
        · left
          have hu_cl : u ∈ closure p := hWp_sub (hDT huD).1
          have hu_notU : u ∉ Γ.U := by
            intro huU
            by_cases huV : u ∈ Γ.V
            · exact (hDT huD).2 (Or.inl ⟨huV, hu_ja⟩)
            · obtain ⟨g, hg, hug⟩ := Γ.exists_edge_of_mem huU huV
              exact (hDT huD).2 (Or.inr (mem_iUnion₂.mpr ⟨g, hg, subset_closure hug⟩))
          obtain ⟨q, hq, huq⟩ := exists_region_of_notMem hu_notU
          obtain ⟨z, hzq, hzp⟩ := mem_closure_iff.mp hu_cl q (region_isOpen hq) huq
          exact region_eq_of_mem hq hp hzq hzp ▸ huq
      obtain ⟨q_T, hq_T⟩ :=
        (hD.isPathConnected.joinedIn (j a) (hD'D hja_D') y (hD'D hyD')).mono hD_sub
      obtain ⟨w, hwr, hjw⟩ := hp_sub hyp
      have hex_q : ∀ t : I, ∃ x ∈ r ∪ {a}, j x = q_T t := by
        intro t
        rcases hq_T t with htp | ht_eq
        · obtain ⟨x, hxr, hjx⟩ := hp_sub htp
          exact ⟨x, Or.inl hxr, hjx⟩
        · exact ⟨a, Or.inr rfl, (mem_singleton_iff.mp ht_eq).symm⟩
      choose q_S hq_S_mem hq_S_eq using hex_q
      have hq_S_cont : Continuous q_S := hj.isEmbedding.continuous_iff.mpr (by
        have : j ∘ q_S = q_T := funext hq_S_eq
        rw [this]
        exact q_T.continuous)
      refine ⟨w, hwr, ⟨⟨q_S, hq_S_cont⟩, ?_, ?_⟩, hq_S_mem⟩
      · exact hj.injective ((hq_S_eq 0).trans q_T.source)
      · exact hj.injective ((hq_S_eq 1).trans (q_T.target.trans hjw.symm))
    · obtain ⟨g, hg_cont, hg0, hgt⟩ := exists_access hT Γ hγ hja_V ⟨he_pair, hhe_mem⟩ hp hjap
      have hg1 : g 1 ∈ p := hgt 1 zero_lt_one
      obtain ⟨w, hwr, hjw⟩ := hp_sub hg1
      have hex_g : ∀ t : I, ∃ x ∈ r ∪ {a}, j x = g t := by
        intro t
        rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | ht_pos
        · have ht0 : t = 0 := Subtype.ext h0.symm
          rw [ht0, hg0]
          exact ⟨a, Or.inr rfl, rfl⟩
        · obtain ⟨x, hxr, hjx⟩ := hp_sub (hgt t ht_pos)
          exact ⟨x, Or.inl hxr, hjx⟩
      choose g_S hg_S_mem hg_S_eq using hex_g
      have hg_S_cont : Continuous g_S := hj.isEmbedding.continuous_iff.mpr (by
        have : j ∘ g_S = g := funext hg_S_eq
        rw [this]
        exact hg_cont)
      refine ⟨w, hwr, ⟨⟨g_S, hg_S_cont⟩, ?_, ?_⟩, hg_S_mem⟩
      · exact hj.injective ((hg_S_eq 0).trans hg0)
      · exact hj.injective ((hg_S_eq 1).trans hjw.symm)
  · obtain ⟨r', hr', har'⟩ := exists_region_of_notMem haU
    obtain ⟨z, hzr', hzr⟩ := mem_closure_iff.mp har r' (region_isOpen hr') har'
    have har_mem : a ∈ r := region_eq_of_mem hr' hr hzr' hzr ▸ har'
    exact ⟨a, har_mem, JoinedIn.refl (Or.inl har_mem)⟩

/-- Any two points `a, b ∈ closure r ∩ (G.U \ G.V)ᶜ` (`r ∈ G.R`) are joined in `r ∪ {a, b}`. -/
theorem joinedIn_region_union_pair (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {r : Set S} (hr : r ∈ G.R)
    {a b : S} (har : a ∈ closure r) (ha_norm : a ∈ (G.U \ G.V)ᶜ)
    (hbr : b ∈ closure r) (hb_norm : b ∈ (G.U \ G.V)ᶜ) :
    JoinedIn (r ∪ {a, b}) a b := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨w_a, hwa, hja⟩ := joinedIn_region_of_mem_closure hS hG hr har ha_norm
  obtain ⟨w_b, hwb, hjb⟩ := joinedIn_region_of_mem_closure hS hG hr hbr hb_norm
  have hr_arc : IsArcConnected r :=
    isArcConnected_of_isOpen_of_isConnected hS (region_isOpen hr)
      ⟨region_nonempty hr, region_isPreconnected hr⟩
  have hj_mid : JoinedIn r w_a w_b :=
    isArcConnected_iff_joinedIn.mp hr_arc w_a hwa w_b hwb
  have h1 : JoinedIn (r ∪ {a, b}) a w_a :=
    hja.mono (union_subset_union_right r (fun _ hx => Or.inl hx))
  have h2 : JoinedIn (r ∪ {a, b}) w_a w_b := hj_mid.mono subset_union_left
  have h3 : JoinedIn (r ∪ {a, b}) w_b b :=
    hjb.symm.mono (union_subset_union_right r (fun _ hx => Or.inr hx))
  exact (h1.trans h2).trans h3

/-- Every point `x ∈ S` is joined in `(G.U \ G.V)ᶜ ∪ {x}` to a point of `⋃₀ G.R`. -/
theorem joinedIn_regions_of_any (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) (x : S) :
    ∃ w ∈ ⋃₀ G.R, JoinedIn ((G.U \ G.V)ᶜ ∪ {x}) x w := by
  have : T2Space S := hS.2.1
  by_cases hx : x ∈ (G.U \ G.V)ᶜ
  · have hfinR : G.R.Finite := finite_regions_of_isProper hS hG
    have hx_cl : x ∈ closure (⋃₀ G.R) := (closure_sUnion_regions_eq_univ hS hG).symm ▸ mem_univ x
    have hx_bi : x ∈ ⋃ r ∈ G.R, closure r := by
      have heq : closure (⋃₀ G.R) = ⋃ r ∈ G.R, closure r := by
        rw [sUnion_eq_biUnion, hfinR.closure_biUnion]
      rwa [← heq]
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx_bi
    obtain ⟨w, hwr, hjw⟩ := joinedIn_region_of_mem_closure hS hG hr hxr hx
    refine ⟨w, mem_sUnion.mpr ⟨r, hr, hwr⟩, hjw.mono ?_⟩
    rintro z (hzr | hzx)
    · exact Or.inl (fun h => region_subset hr hzr h.1)
    · exact Or.inr hzx
  · rw [mem_compl_iff, not_not] at hx
    have hx_not_bd : x ∉ bd S := fun hbd => hx.2 (hG ⟨hbd, hx.1⟩)
    obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, hK, hunion, hinter, hΓU, -, hΓV, -⟩ :=
      exists_capped_drawing hS G hG
    have : T2Space T := hT.2.1
    have hjx_U : j x ∈ Γ.U := hΓU ▸ ⟨x, Or.inl hx.1, rfl⟩
    have hjx_notV : j x ∉ Γ.V := by
      intro hjV
      obtain ⟨y, hy, hjy⟩ := hΓV hjV
      rcases hj.injective hjy ▸ hy with h | h
      · exact hx.2 h
      · exact hx_not_bd h
    have hjx_notK : j x ∉ K := by
      intro hjK
      have : j x ∈ range j ∩ K := ⟨⟨x, rfl⟩, hjK⟩
      rw [hinter] at this
      obtain ⟨x', hx'bd, hjx'⟩ := this
      exact hx_not_bd (hj.injective hjx' ▸ hx'bd)
    obtain ⟨e, he, hjxe⟩ := Γ.exists_edge_of_mem hjx_U hjx_notV
    obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
    obtain ⟨t₀, ht₀, hγt₀⟩ : j x ∈ γ '' Ioo 0 1 := hγe.symm ▸ hjxe
    obtain ⟨M, a, b, g₁, g₂, _, g₄, g₅, _, g₇, g₈, g₉, g₁₀, g₁₁⟩ :=
      exists_edge_chart hT Γ he hγ hγ0 hγ1 hinj hγe ht₀ ht₀.1 ht₀.2
    have c : IsEdgeChart Γ γ t₀ M a b := ⟨g₁, g₂, g₄, g₅, g₇, g₈, g₉, g₁₀, g₁₁⟩
    let seg : I → ℂ := fun s => ((s : ℝ) / 2 : ℂ) * Complex.I
    have hseg_ball : ∀ s : I, seg s ∈ Metric.closedBall (0 : ℂ) 1 := by
      intro s
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_div, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
        abs_of_nonneg (unitInterval.nonneg s)]
      linarith [unitInterval.le_one s]
    have hseg_cont : Continuous fun s : I => M (seg s) :=
      c.cont.comp_continuous (by fun_prop) hseg_ball
    have hseg_zero : M (seg 0) = j x := by
      change M (((0 : ℝ) / 2 : ℂ) * Complex.I) = j x
      simp [c.zero, hγt₀]
    have hseg_pos : ∀ s : I, (0 : I) < s → M (seg s) ∈ M '' IsEdgeChart.upper := by
      intro s hs
      have hs' : (0 : ℝ) < (s : ℝ) := hs
      refine ⟨seg s, ⟨hseg_ball s, ?_⟩, rfl⟩
      have him : (seg s).im = (s : ℝ) / 2 := by
        simp [seg, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
          Complex.ofReal_re]
      linarith [him, hs']
    obtain ⟨u₀, hu₀_pos, _, hu₀_notK⟩ :=
      exists_pos_le hseg_cont hK.isOpen_compl (hseg_zero.symm ▸ hjx_notK) (zero_lt_one' I)
    let m : I → I := fun t => ⟨(t : ℝ) * (u₀ : ℝ), mul_nonneg t.2.1 u₀.2.1,
      by nlinarith [t.2.1, t.2.2, u₀.2.1, u₀.2.2]⟩
    have hm_cont : Continuous m := Continuous.subtype_mk (by fun_prop) _
    have hm_le : ∀ t : I, m t ≤ u₀ := fun t => by
      change (t : ℝ) * (u₀ : ℝ) ≤ (u₀ : ℝ)
      nlinarith [t.2.2, u₀.2.1]
    have hex_q : ∀ t : I, ∃ z ∈ (G.U \ G.V)ᶜ ∪ {x}, j z = M (seg (m t)) := by
      intro t
      rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | ht_pos
      · have ht0 : t = 0 := Subtype.ext h0.symm
        have hm0 : m t = 0 := Subtype.ext (by simp [m, ht0])
        rw [hm0, hseg_zero]
        exact ⟨x, Or.inr rfl, rfl⟩
      · have hmt_pos : (0 : I) < m t := by
          change (0 : ℝ) < (t : ℝ) * (u₀ : ℝ)
          exact mul_pos ht_pos hu₀_pos
        have h_notK : M (seg (m t)) ∈ Kᶜ := hu₀_notK (m t) (hm_le t)
        have h_range : M (seg (m t)) ∈ range j :=
          (hunion.symm ▸ mem_univ _).resolve_right h_notK
        obtain ⟨z, hjz⟩ := h_range
        have hz_notU : z ∉ G.U := fun hzU =>
          disjoint_left.mp c.upper_disjoint (hseg_pos (m t) hmt_pos)
            (hΓU ▸ ⟨z, Or.inl hzU, hjz⟩)
        exact ⟨z, Or.inl (fun h => hz_notU h.1), hjz⟩
    choose q_S hq_S_mem hq_S_eq using hex_q
    have hq_S_cont : Continuous q_S := hj.isEmbedding.continuous_iff.mpr (by
      have : j ∘ q_S = fun t => M (seg (m t)) := funext hq_S_eq
      rw [this]
      exact hseg_cont.comp hm_cont)
    have hq1_notU : q_S 1 ∉ G.U := by
      intro hU
      have hm1 : m 1 = u₀ := Subtype.ext (by simp [m])
      exact disjoint_left.mp c.upper_disjoint
        (hm1 ▸ hseg_pos u₀ hu₀_pos)
        (hΓU ▸ ⟨q_S 1, Or.inl hU, hq_S_eq 1⟩)
    obtain ⟨r, hr, hq1r⟩ := exists_region_of_notMem hq1_notU
    refine ⟨q_S 1, mem_sUnion.mpr ⟨r, hr, hq1r⟩, ⟨⟨q_S, hq_S_cont⟩, ?_, rfl⟩, hq_S_mem⟩
    have hm0 : m 0 = 0 := Subtype.ext (by simp [m])
    exact hj.injective ((hq_S_eq 0).trans (hm0.symm ▸ hseg_zero))

/-- Any two points `w₁, w₂ ∈ ⋃₀ G.R` are joined in `(G.U \ G.V)ᶜ`. -/
theorem joinedIn_normal_of_mem_regions (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {w₁ w₂ : S}
    (hw₁ : w₁ ∈ ⋃₀ G.R) (hw₂ : w₂ ∈ ⋃₀ G.R) :
    JoinedIn (G.U \ G.V)ᶜ w₁ w₂ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨r₁, hr₁, hw₁r₁⟩ := mem_sUnion.mp hw₁
  obtain ⟨r₂, hr₂, hw₂r₂⟩ := mem_sUnion.mp hw₂
  obtain ⟨w₁', hw₁'r₁, hw₁'_bd⟩ :=
    mem_closure_iff.mp (mem_closure_compl_bd (hS.2.2 w₁)) r₁ (region_isOpen hr₁) hw₁r₁
  obtain ⟨w₂', hw₂'r₂, hw₂'_bd⟩ :=
    mem_closure_iff.mp (mem_closure_compl_bd (hS.2.2 w₂)) r₂ (region_isOpen hr₂) hw₂r₂
  have hj₁ : JoinedIn (G.U \ G.V)ᶜ w₁ w₁' := by
    have hr₁_arc := isArcConnected_of_isOpen_of_isConnected hS (region_isOpen hr₁)
      ⟨region_nonempty hr₁, region_isPreconnected hr₁⟩
    exact (isArcConnected_iff_joinedIn.mp hr₁_arc w₁ hw₁r₁ w₁' hw₁'r₁).mono
      fun z hz h => region_subset hr₁ hz h.1
  have hj₂ : JoinedIn (G.U \ G.V)ᶜ w₂' w₂ := by
    have hr₂_arc := isArcConnected_of_isOpen_of_isConnected hS (region_isOpen hr₂)
      ⟨region_nonempty hr₂, region_isPreconnected hr₂⟩
    exact (isArcConnected_iff_joinedIn.mp hr₂_arc w₂' hw₂'r₂ w₂ hw₂r₂).mono
      fun z hz h => region_subset hr₂ hz h.1
  obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, -, -, -, hΓU, -, hΓV, hℛ_map⟩ :=
    exists_capped_drawing hS G hG
  have : T2Space T := hT.2.1
  obtain ⟨ℛ_T, hℛ_T, h_cl_eq, hsU⟩ := hℛ_map G.R Subset.rfl
  have hcl_S : closure (⋃₀ G.R) = univ := closure_sUnion_regions_eq_univ hS hG
  have hS_arc : IsArcConnected (univ : Set S) :=
    isArcConnected_of_isOpen_of_isConnected hS isOpen_univ isConnected_univ
  obtain ⟨p_S, _⟩ := isArcConnected_iff_joinedIn.mp hS_arc w₁' (mem_univ _) w₂' (mem_univ _)
  have h_in_cl : ∀ z : S, j z ∈ closure (⋃₀ ℛ_T) := fun z => by
    rw [← h_cl_eq, hcl_S]
    exact ⟨z, mem_univ z, rfl⟩
  let a_T : closure (⋃₀ ℛ_T) := ⟨j w₁', h_in_cl w₁'⟩
  let b_T : closure (⋃₀ ℛ_T) := ⟨j w₂', h_in_cl w₂'⟩
  have ha_T : a_T.1 ∈ ⋃₀ ℛ_T := by
    change j w₁' ∈ ⋃₀ ℛ_T
    rw [hsU]
    exact ⟨w₁', ⟨mem_sUnion.mpr ⟨r₁, hr₁, hw₁'r₁⟩, hw₁'_bd⟩, rfl⟩
  have hb_T : b_T.1 ∈ ⋃₀ ℛ_T := by
    change j w₂' ∈ ⋃₀ ℛ_T
    rw [hsU]
    exact ⟨w₂', ⟨mem_sUnion.mpr ⟨r₂, hr₂, hw₂'r₂⟩, hw₂'_bd⟩, rfl⟩
  let p_T : Path a_T b_T :=
    { toFun := fun t => ⟨j (p_S t), h_in_cl (p_S t)⟩
      continuous_toFun := Continuous.subtype_mk (hj.continuous.comp p_S.continuous) _
      source' := Subtype.ext (congrArg j p_S.source)
      target' := Subtype.ext (congrArg j p_S.target) }
  obtain ⟨q_T, -, hq_T_norm⟩ := exists_homotopic_normal_path_in_closed hT Γ hℛ_T ha_T hb_T p_T
  have hex_q : ∀ t : I, ∃ z ∈ (G.U \ G.V)ᶜ, j z = (q_T t).1 := by
    intro t
    have ht_cl : (q_T t).1 ∈ j '' closure (⋃₀ G.R) := h_cl_eq.symm ▸ (q_T t).2
    obtain ⟨z, _, hjz⟩ := ht_cl
    refine ⟨z, ?_, hjz⟩
    rintro ⟨hzU, hzV⟩
    have hz_not_bd : z ∉ bd S := fun hbd => hzV (hG ⟨hbd, hzU⟩)
    have hjz_U : (q_T t).1 ∈ Γ.U := hjz ▸ hΓU ▸ ⟨z, Or.inl hzU, rfl⟩
    have hjz_notV : (q_T t).1 ∉ Γ.V := by
      intro hjV
      obtain ⟨y, hy, hjy⟩ := hΓV (hjz ▸ hjV)
      rcases hj.injective hjy ▸ hy with h | h
      · exact hzV h
      · exact hz_not_bd h
    exact hq_T_norm t ⟨hjz_U, hjz_notV⟩
  choose q_S hq_S_mem hq_S_eq using hex_q
  have hq_S_cont : Continuous q_S := hj.isEmbedding.continuous_iff.mpr (by
    have : j ∘ q_S = fun t => (q_T t).1 := funext hq_S_eq
    rw [this]
    exact continuous_subtype_val.comp q_T.continuous)
  have hj_mid : JoinedIn (G.U \ G.V)ᶜ w₁' w₂' := by
    refine ⟨⟨⟨q_S, hq_S_cont⟩, ?_, ?_⟩, hq_S_mem⟩
    · exact hj.injective ((hq_S_eq 0).trans (congrArg Subtype.val q_T.source))
    · exact hj.injective ((hq_S_eq 1).trans (congrArg Subtype.val q_T.target))
  exact (hj₁.trans hj_mid).trans hj₂

/-- For any two distinct points `x, y ∈ S` on a connected surface `S` with a proper drawing `G`,
there is a `[0, 1]`-arc `X` with ends `x, y` such that `(G.U ∩ X).Finite` (and in fact
`G.U ∩ X ⊆ G.V ∪ {x, y}`). -/
theorem exists_lineWithEnds_finite_inter_U (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {x y : S} (hxy : x ≠ y) :
    ∃ X : Set S, IsLineWithEnds X x y ∧ G.U ∩ X ⊆ G.V ∪ {x, y} ∧ (G.U ∩ X).Finite := by
  have : T2Space S := hS.2.1
  obtain ⟨w_x, hwx, hjx⟩ := joinedIn_regions_of_any hS hG x
  obtain ⟨w_y, hwy, hjy⟩ := joinedIn_regions_of_any hS hG y
  have hj_mid := joinedIn_normal_of_mem_regions hS hG hwx hwy
  have h1 : JoinedIn ((G.U \ G.V)ᶜ ∪ {x, y}) x w_x :=
    hjx.mono (union_subset_union_right _ (by intro z hz; exact Or.inl hz))
  have h2 : JoinedIn ((G.U \ G.V)ᶜ ∪ {x, y}) w_x w_y := hj_mid.mono subset_union_left
  have h3 : JoinedIn ((G.U \ G.V)ᶜ ∪ {x, y}) w_y y :=
    hjy.symm.mono (union_subset_union_right _ (fun _ hz => Or.inr (mem_singleton_iff.mpr hz)))
  have hj_xy := (h1.trans h2).trans h3
  obtain ⟨X, hX_sub, hX_line⟩ :=
    ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := (G.U \ G.V)ᶜ ∪ {x, y})
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))).mp hj_xy).resolve_left hxy
  have hUX : G.U ∩ X ⊆ G.V ∪ {x, y} := by
    rintro z ⟨hzU, hzX⟩
    rcases hX_sub hzX with hz_norm | hz_xy
    · exact Or.inl (by_contra fun hzV => hz_norm ⟨hzU, hzV⟩)
    · exact Or.inr hz_xy
  exact ⟨X, hX_line, hUX, (G.finite_V.union ((finite_singleton y).insert x)).subset hUX⟩

/-- Any `[0, 1]`-arc `X` with ends `x, y` and `(G.U ∩ X).Finite` bounds `distPoint G x y`. -/
theorem distPoint_le_of_lineWithEnds {G : Drawing S} {X : Set S} {x y : S}
    (hX : IsLineWithEnds X x y) (hfin : (G.U ∩ X).Finite) :
    distPoint G x y ≤ (G.U ∩ X).ncard := by
  have hxy : x ≠ y := hX.ne'
  simp only [distPoint, hxy, ↓reduceIte]
  exact Nat.sInf_le ⟨X, hX, hfin, rfl⟩

/-- For distinct points `x, y ∈ S`, `distPoint G x y` is attained by a `[0, 1]`-arc `X`. -/
theorem distPoint_exists_arc (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {x y : S} (hxy : x ≠ y) :
    ∃ X : Set S, IsLineWithEnds X x y ∧ (G.U ∩ X).Finite ∧ (G.U ∩ X).ncard = distPoint G x y := by
  obtain ⟨X₀, hX₀, _, hfin₀⟩ := exists_lineWithEnds_finite_inter_U hS hG hxy
  have hne : {n : ℕ | ∃ X : Set S, IsLineWithEnds X x y ∧ (G.U ∩ X).Finite ∧ (G.U ∩ X).ncard
    = n}.Nonempty :=
    ⟨(G.U ∩ X₀).ncard, X₀, hX₀, hfin₀, rfl⟩
  obtain ⟨X, hX, hfin, hcard⟩ := Nat.sInf_mem hne
  refine ⟨X, hX, hfin, ?_⟩
  simp only [distPoint, hxy, ↓reduceIte, hcard]

/-- If a region `r ∈ G.R` meets `nearSet G t A`, then `r ⊆ nearSet G t A`. -/
theorem region_subset_nearSet_of_mem (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {r A : Set S} {t : ℕ}
    (hr : r ∈ G.R) {x : S} (hxr : x ∈ r) (hxA : x ∈ nearSet G t A) :
    r ⊆ nearSet G t A := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  intro x' hx'r
  obtain ⟨y, hyA, hxy_le⟩ := hxA
  refine ⟨y, hyA, ?_⟩
  by_cases hx'y : x' = y
  · subst hx'y
    have hx'_notU : x' ∉ G.U := region_subset hr hx'r
    simp [distPoint, hx'_notU]
  · have hr_arc : IsArcConnected r :=
      isArcConnected_of_isOpen_of_isConnected hS (region_isOpen hr)
        ⟨region_nonempty hr, region_isPreconnected hr⟩
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨L, hLr, hL_line⟩ := hr_arc x' hx'r x hxr hx'y
      have hUL_empty : G.U ∩ L = ∅ := eq_empty_iff_forall_notMem.mpr
        fun z ⟨hzU, hzL⟩ => region_subset hr (hLr hzL) hzU
      have hle := distPoint_le_of_lineWithEnds (G := G) hL_line (by simp [hUL_empty])
      simp only [hUL_empty, ncard_empty, Nat.le_zero] at hle
      exact hle ▸ Nat.zero_le t
    · obtain ⟨X, hX_line, hX_fin, hX_card⟩ := distPoint_exists_arc hS hG hxy
      have hj_r : JoinedIn r x' x := isArcConnected_iff_joinedIn.mp hr_arc x' hx'r x hxr
      have hj_X : JoinedIn X x y :=
        (joinedIn_iff_eq_or_exists_isLineWithEnds (Z := X) hX_line.left_mem hX_line.right_mem).mpr
          (Or.inr ⟨X, Subset.rfl, hX_line⟩)
      have hj_union : JoinedIn (r ∪ X) x' y :=
        (hj_r.mono subset_union_left).trans (hj_X.mono subset_union_right)
      obtain ⟨X', hX'_sub, hX'_line⟩ :=
        ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := r ∪ X)
          (Or.inl hx'r) (Or.inr hX_line.right_mem)).mp hj_union).resolve_left hx'y
      have hUX'_sub : G.U ∩ X' ⊆ G.U ∩ X := by
        rintro z ⟨hzU, hzX'⟩
        rcases hX'_sub hzX' with hzr | hzX
        · exact False.elim (region_subset hr hzr hzU)
        · exact ⟨hzU, hzX⟩
      have hX'_fin : (G.U ∩ X').Finite := hX_fin.subset hUX'_sub
      calc distPoint G x' y
        _ ≤ (G.U ∩ X').ncard := distPoint_le_of_lineWithEnds hX'_line hX'_fin
        _ ≤ (G.U ∩ X).ncard := ncard_le_ncard hUX'_sub hX_fin
        _ = distPoint G x y := hX_card
        _ ≤ t := hxy_le

/-- For any `G`-normal subset `F₀ ⊆ S`, `closure (nearSet G t F₀)` is the closure of the union of
the regions of `G` contained in `nearSet G t F₀`. -/
theorem closure_nearSet_eq_closure_sUnion_regions (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {F₀ : Set S} (hF₀_norm : G.IsNormal F₀) (t : ℕ) :
    closure (nearSet G t F₀) = closure (⋃₀ {r ∈ G.R | r ⊆ nearSet G t F₀}) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  apply Subset.antisymm
  · refine closure_minimal (fun x hx => ?_) isClosed_closure
    obtain ⟨y, hyF₀, hxy_le⟩ := hx
    by_cases hxy : x = y
    · subst hxy
      have hfinR : G.R.Finite := finite_regions_of_isProper hS hG
      have hx_cl : x ∈ closure (⋃₀ G.R) := (closure_sUnion_regions_eq_univ hS hG).symm ▸ mem_univ x
      have hx_bi : x ∈ ⋃ r ∈ G.R, closure r := by
        have heq : closure (⋃₀ G.R) = ⋃ r ∈ G.R, closure r := by
          rw [sUnion_eq_biUnion, hfinR.closure_biUnion]
        rwa [← heq]
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx_bi
      have hx_norm : x ∈ (G.U \ G.V)ᶜ := fun ⟨hxU, hxV⟩ => hxV (hF₀_norm ⟨hyF₀, hxU⟩)
      obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
      have hr_sub : r ⊆ nearSet G t F₀ := by
        by_cases hx₀x : x₀ = x
        · subst hx₀x
          exact region_subset_nearSet_of_mem hS hG hr hx₀r ⟨x₀, hyF₀, hxy_le⟩
        · have hj := joinedIn_region_union_pair hS hG hr (subset_closure hx₀r)
            (fun h => region_subset hr hx₀r h.1) hxr hx_norm
          obtain ⟨L, hL_sub, hL_line⟩ :=
            ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := r ∪ {x₀, x})
              (Or.inl hx₀r) (Or.inr (Or.inr rfl))).mp hj).resolve_left hx₀x
          have hUL_sub : G.U ∩ L ⊆ G.U ∩ {x} := by
            rintro z ⟨hzU, hzL⟩
            rcases hL_sub hzL with hzr | (rfl | hz_x)
            · exact False.elim (region_subset hr hzr hzU)
            · exact False.elim (region_subset hr hx₀r hzU)
            · exact ⟨hzU, hz_x⟩
          have hUL_fin : (G.U ∩ L).Finite := ((finite_singleton x).inter_of_right G.U).subset
            hUL_sub
          have hx₀_near : x₀ ∈ nearSet G t F₀ := by
            refine ⟨x, hyF₀, ?_⟩
            calc distPoint G x₀ x
              _ ≤ (G.U ∩ L).ncard := distPoint_le_of_lineWithEnds hL_line hUL_fin
              _ ≤ (G.U ∩ {x}).ncard := ncard_le_ncard hUL_sub ((finite_singleton x).inter_of_right
                G.U)
              _ = distPoint G x x := by
                by_cases hxU : x ∈ G.U
                · have heq : G.U ∩ {x} = {x} := inter_eq_right.mpr (singleton_subset_iff.mpr hxU)
                  simp [distPoint, hxU]
                · have heq : G.U ∩ {x} = ∅ := eq_empty_iff_forall_notMem.mpr
                    fun z ⟨hzU, hzx⟩ => hxU (mem_singleton_iff.mp hzx ▸ hzU)
                  simp [distPoint, hxU, heq]
              _ ≤ t := hxy_le
          exact region_subset_nearSet_of_mem hS hG hr hx₀r hx₀_near
      have hr_mem : r ∈ {r ∈ G.R | r ⊆ nearSet G t F₀} := ⟨hr, hr_sub⟩
      exact closure_mono (subset_sUnion_of_mem hr_mem) hxr
    · obtain ⟨X, hX_line, hX_fin, hX_card⟩ := distPoint_exists_arc hS hG hxy
      obtain ⟨e, he0, he1⟩ := id hX_line
      let g : I → S := fun s => (e s).1
      have hgc : Continuous g := continuous_subtype_val.comp e.continuous
      have hgi : Function.Injective g := Subtype.val_injective.comp e.injective
      have hg0 : g 0 = x := he0
      have hg1 : g 1 = y := he1
      have hfin_sdiff : ((G.U ∩ X) \ {x}).Finite := hX_fin.subset sdiff_subset
      have h_open : IsOpen (((G.U ∩ X) \ {x})ᶜ) := hfin_sdiff.isClosed.isOpen_compl
      have hx_mem_open : g 0 ∈ ((G.U ∩ X) \ {x})ᶜ := by
        rw [hg0]
        exact fun h => h.2 rfl
      obtain ⟨u₀, hu₀_pos, _, hu₀_mem⟩ :=
        exists_pos_le hgc h_open hx_mem_open (zero_lt_one' I)
      have h_disj_U : ∀ s ∈ Ioc (0 : I) u₀, g s ∉ G.U := by
        intro s ⟨hs_pos, hs_le⟩ hsU
        have hs_ne0 : s ≠ 0 := ne_of_gt hs_pos
        have hgs_ne_x : g s ≠ x := fun h => hs_ne0 (hgi (h.trans hg0.symm))
        exact hu₀_mem s hs_le ⟨⟨hsU, (e s).2⟩, hgs_ne_x⟩
      have hgu₀_notU : g u₀ ∉ G.U := h_disj_U u₀ ⟨hu₀_pos, le_rfl⟩
      obtain ⟨r, hr, hgu₀_r⟩ := exists_region_of_notMem hgu₀_notU
      have hIoc_conn : IsPreconnected (g '' Ioc 0 u₀) :=
        (isPreconnected_Ioc (a := (0 : I)) (b := u₀)).image g hgc.continuousOn
      have hIoc_disj : Disjoint (g '' Ioc 0 u₀) G.U :=
        disjoint_left.mpr (by rintro _ ⟨s, hs, rfl⟩; exact h_disj_U s hs)
      have hIoc_sub_r : g '' Ioc 0 u₀ ⊆ r :=
        subset_region hr hIoc_conn hIoc_disj ⟨u₀, ⟨hu₀_pos, le_rfl⟩, rfl⟩ hgu₀_r
      have hxr : x ∈ closure r := by
        have h0_cl : (0 : I) ∈ closure (Ioc (0 : I) u₀) := by
          rw [closure_Ioc (ne_of_lt hu₀_pos)]
          exact ⟨le_rfl, hu₀_pos.le⟩
        have hgx := image_closure_subset_closure_image hgc ⟨0, h0_cl, hg0⟩
        exact closure_mono hIoc_sub_r hgx
      have hgu₀_near : g u₀ ∈ nearSet G t F₀ := by
        refine ⟨y, hyF₀, ?_⟩
        rcases eq_or_lt_of_le (unitInterval.le_one u₀) with hu₀1 | hu₀_lt1
        · have hu₀_eq1 : u₀ = 1 := Subtype.ext hu₀1
          rw [hu₀_eq1, hg1] at hgu₀_notU ⊢
          simp [distPoint, hgu₀_notU]
        · have hL_sub : g '' Icc u₀ 1 ⊆ X := by
            rintro _ ⟨s, _, rfl⟩
            exact (e s).2
          have hL_line : IsLineWithEnds (g '' Icc u₀ 1) (g u₀) y :=
            hg1 ▸ isLine_piece hgc hgi hu₀_lt1
          have hUL_sub : G.U ∩ (g '' Icc u₀ 1) ⊆ G.U ∩ X := inter_subset_inter_right G.U hL_sub
          have hUL_fin : (G.U ∩ (g '' Icc u₀ 1)).Finite := hX_fin.subset hUL_sub
          calc distPoint G (g u₀) y
            _ ≤ (G.U ∩ (g '' Icc u₀ 1)).ncard := distPoint_le_of_lineWithEnds hL_line hUL_fin
            _ ≤ (G.U ∩ X).ncard := ncard_le_ncard hUL_sub hX_fin
            _ = distPoint G x y := hX_card
            _ ≤ t := hxy_le
      have hr_sub : r ⊆ nearSet G t F₀ :=
        region_subset_nearSet_of_mem hS hG hr hgu₀_r hgu₀_near
      have hr_mem : r ∈ {r ∈ G.R | r ⊆ nearSet G t F₀} := ⟨hr, hr_sub⟩
      exact closure_mono (subset_sUnion_of_mem hr_mem) hxr
  · exact closure_mono (sUnion_subset fun _ hr => hr.2)

/-- For a proper drawing `G` on a connected surface `S`, if an edge `e ∈ G.E` meets `closure r` for
a region `r ∈ G.R`, then `closure e ⊆ closure r`. -/
theorem edge_closure_subset_closure_region (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {e r : Set S} (he : e ∈ G.E) (hr : r ∈ G.R)
    {z : S} (hze : z ∈ e) (hzr : z ∈ closure r) :
    closure e ⊆ closure r := by
  obtain ⟨T, topT, j, K, Γ, hT, hT_conn, hj, -, -, -, hΓU, -, hΓV, hℛ_map⟩ :=
    exists_capped_drawing hS G hG
  have : T2Space T := hT.2.1
  obtain ⟨ℛ_T, hℛ_T, h_cl_eq, -⟩ := hℛ_map {r} (singleton_subset_iff.mpr hr)
  rw [sUnion_singleton] at h_cl_eq
  have hnice := isGammaNice_closure_sUnion_regions hT Γ hℛ_T
  have hjx_UV : ∀ x ∈ e, j x ∈ Γ.U ∧ j x ∉ Γ.V := by
    intro x hxe
    have hxU : x ∈ G.U := (he.2.1 hxe).1
    have hxV : x ∉ G.V := (he.2.1 hxe).2
    have hx_not_bd : x ∉ bd S := fun hbd => hxV (hG ⟨hbd, hxU⟩)
    refine ⟨hΓU ▸ ⟨x, Or.inl hxU, rfl⟩, fun hjV => ?_⟩
    obtain ⟨y, hy, hjy⟩ := hΓV hjV
    rcases hj.injective hjy ▸ hy with h | h
    · exact hxV h
    · exact hx_not_bd h
  obtain ⟨e_T, he_T, hjz_eT⟩ := Γ.exists_edge_of_mem (hjx_UV z hze).1 (hjx_UV z hze).2
  have he_T_sub : e_T ⊆ closure (⋃₀ ℛ_T) :=
    nice_edge hnice he_T ⟨j z, hjz_eT, h_cl_eq ▸ ⟨z, hzr, rfl⟩⟩
  have he_sub : e ⊆ closure r := by
    by_contra hnot
    obtain ⟨w, hwe, hwr⟩ := not_subset.mp hnot
    let O₁ : Set S := j ⁻¹' (Γ.U \ e_T)ᶜ
    have hO₁ : IsOpen O₁ := (isClosed_U_sdiff_edge Γ he_T).isOpen_compl.preimage hj.continuous
    have hO₂' : IsOpen (j ⁻¹' (closure e_T)ᶜ) :=
      isClosed_closure.isOpen_compl.preimage hj.continuous
    have hcov : e ⊆ O₁ ∪ j ⁻¹' (closure e_T)ᶜ := by
      intro x hxe
      by_cases hjx : j x ∈ e_T
      · exact Or.inl fun h => h.2 hjx
      · refine Or.inr fun hjx_cl => ?_
        have hjx_in : j x ∈ closure e_T \ Γ.V := ⟨hjx_cl, (hjx_UV x hxe).2⟩
        rw [Γ.closure_diff_V he_T] at hjx_in
        exact hjx hjx_in
    have hz_O₁ : z ∈ e ∩ O₁ := ⟨hze, fun h => h.2 hjz_eT⟩
    have hw_O₂ : w ∈ e ∩ j ⁻¹' (closure e_T)ᶜ := by
      refine ⟨hwe, fun hjw_cl => hwr ?_⟩
      have hjw_r : j w ∈ j '' closure r :=
        h_cl_eq.symm ▸ closure_minimal he_T_sub isClosed_closure hjw_cl
      obtain ⟨w', hw', hjw'⟩ := hjw_r
      exact hj.injective hjw' ▸ hw'
    obtain ⟨x, hxe, hxO₁, hxO₂⟩ :=
      he.2.2.1.isConnected.isPreconnected O₁ (j ⁻¹' (closure e_T)ᶜ) hO₁ hO₂' hcov ⟨z, hz_O₁⟩ ⟨w,
        hw_O₂⟩
    have hjx_eT : j x ∈ e_T := by_contra fun h => hxO₁ ⟨(hjx_UV x hxe).1, h⟩
    exact hxO₂ (subset_closure hjx_eT)
  exact closure_minimal he_sub isClosed_closure

/-- If `z ∈ G.U ∩ closure r₁ ∩ closure r₂` for regions `r₁, r₂ ∈ G.R` of a proper drawing `G`,
then there is a vertex `v ∈ G.V ∩ closure r₁ ∩ closure r₂`. -/
theorem exists_vertex_in_closure_regions (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {r₁ r₂ : Set S} (hr₁ : r₁ ∈ G.R) (hr₂ : r₂ ∈ G.R)
    {z : S} (hzU : z ∈ G.U) (hz₁ : z ∈ closure r₁) (hz₂ : z ∈ closure r₂) :
    ∃ v ∈ G.V, v ∈ closure r₁ ∧ v ∈ closure r₂ := by
  have : T2Space S := hS.2.1
  by_cases hzV : z ∈ G.V
  · exact ⟨z, hzV, hz₁, hz₂⟩
  · obtain ⟨e, he, hze⟩ := G.exists_edge_of_mem hzU hzV
    obtain ⟨γ, hγ, hγ0, -, -, hγe⟩ := exists_edge_param G he
    have he_cl₁ := edge_closure_subset_closure_region hS hG he hr₁ hze hz₁
    have he_cl₂ := edge_closure_subset_closure_region hS hG he hr₂ hze hz₂
    have h0_cl : γ 0 ∈ closure e := by
      rw [← hγe]
      have h0 : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
        rw [closure_Ioo zero_ne_one]
        exact ⟨le_rfl, zero_le_one⟩
      exact image_closure_subset_closure_image hγ ⟨0, h0, rfl⟩
    exact ⟨γ 0, hγ0, he_cl₁ h0_cl, he_cl₂ h0_cl⟩

/-- Auxiliary induction for `exists_normal_arc_of_lineWithEnds`: for any `[0, 1]`-arc `X` with ends
`a, b ∈ (G.U \ G.V)ᶜ` and `(G.U ∩ X).Finite`, there is a finite subset `W ⊆ G.V` of cardinality at
most `(G.U ∩ (X \ {a, b})).ncard` such that `JoinedIn (G.Uᶜ ∪ W ∪ {a, b}) a b`. -/
theorem exists_joinedIn_normal_of_lineWithEnds (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) :
    ∀ m : ℕ, ∀ {a b : S} {X : Set S},
      a ∈ (G.U \ G.V)ᶜ → b ∈ (G.U \ G.V)ᶜ →
      IsLineWithEnds X a b → (G.U ∩ X).Finite → (G.U ∩ (X \ {a, b})).ncard ≤ m →
      ∃ W ⊆ G.V, W.Finite ∧ W.ncard ≤ m ∧ JoinedIn (G.Uᶜ ∪ W ∪ {a, b}) a b := by
  have : T2Space S := hS.2.1
  intro m
  induction m with
  | zero =>
    intro a b X _ _ hX hX_fin hm
    have hfin_int : (G.U ∩ (X \ {a, b})).Finite :=
      hX_fin.subset (inter_subset_inter_right _ sdiff_subset)
    have hempty : G.U ∩ (X \ {a, b}) = ∅ :=
      (ncard_eq_zero hfin_int).mp (Nat.eq_zero_of_le_zero hm)
    refine ⟨∅, empty_subset _, finite_empty, by simp, ?_⟩
    have hjX : JoinedIn X a b :=
      (joinedIn_iff_eq_or_exists_isLineWithEnds (Z := X) hX.left_mem hX.right_mem).mpr
        (Or.inr ⟨X, Subset.rfl, hX⟩)
    refine hjX.mono fun z hzX => ?_
    by_cases hz_ab : z ∈ ({a, b} : Set S)
    · exact Or.inr hz_ab
    · refine Or.inl (Or.inl fun hzU => ?_)
      have : z ∈ G.U ∩ (X \ {a, b}) := ⟨hzU, hzX, hz_ab⟩
      rw [hempty] at this
      exact this
  | succ m ih =>
    intro a b X ha hb hX hX_fin hm
    have hfin_int : (G.U ∩ (X \ {a, b})).Finite :=
      hX_fin.subset (inter_subset_inter_right _ sdiff_subset)
    rcases le_or_gt (G.U ∩ (X \ {a, b})).ncard m with hle | hgt
    · obtain ⟨W, hWV, hWfin, hWcard, hj⟩ := ih ha hb hX hX_fin hle
      exact ⟨W, hWV, hWfin, hWcard.trans (Nat.le_succ m), hj⟩
    · have hm_eq : (G.U ∩ (X \ {a, b})).ncard = m + 1 := le_antisymm hm hgt
      obtain ⟨e, he0, he1⟩ := id hX
      let g : I → S := fun s => (e s).1
      have hgc : Continuous g := continuous_subtype_val.comp e.continuous
      have hgi : Function.Injective g := Subtype.val_injective.comp e.injective
      have hg0 : g 0 = a := he0
      have hg1 : g 1 = b := he1
      let M : Set I := {s : I | s ∈ Ioo (0 : I) 1 ∧ g s ∈ G.U}
      have hM_image : g '' M = G.U ∩ (X \ {a, b}) := by
        ext z
        constructor
        · rintro ⟨s, ⟨⟨hs0, hs1⟩, hsU⟩, rfl⟩
          refine ⟨hsU, (e s).2, ?_⟩
          rintro (hza | hzb)
          · exact ne_of_gt hs0 (hgi (hza.trans hg0.symm))
          · exact ne_of_lt hs1 (hgi (hzb.trans hg1.symm))
        · rintro ⟨hzU, hzX, hz_ab⟩
          let s : I := e.symm ⟨z, hzX⟩
          have hgs : g s = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hzX⟩)
          have hs0 : (0 : I) < s := lt_of_le_of_ne (unitInterval.nonneg s) fun h =>
            hz_ab (Or.inl (hgs.symm.trans (h ▸ hg0)))
          have hs1 : s < 1 := lt_of_le_of_ne (unitInterval.le_one s) fun h =>
            hz_ab (Or.inr (hgs.symm.trans (h ▸ hg1)))
          exact ⟨s, ⟨⟨hs0, hs1⟩, hgs.symm ▸ hzU⟩, hgs⟩
      have hM_fin : M.Finite := hfin_int.preimage hgi.injOn |>.subset fun s hs => by
        rw [mem_preimage, ← hM_image]
        exact ⟨s, hs, rfl⟩
      have h_int_ne : (G.U ∩ (X \ {a, b})).Nonempty :=
        ncard_pos hfin_int |>.mp (by omega)
      have hM_ne : M.Nonempty := by
        obtain ⟨z, hz⟩ := h_int_ne
        rw [← hM_image] at hz
        obtain ⟨s, hs, _⟩ := hz
        exact ⟨s, hs⟩
      let s₁ : I := hM_fin.toFinset.min' (hM_fin.toFinset_nonempty.mpr hM_ne)
      have hs₁_M : s₁ ∈ M := hM_fin.mem_toFinset.mp (Finset.min'_mem _ _)
      have hs₁_min : ∀ s ∈ M, s₁ ≤ s := fun s hs =>
        Finset.min'_le _ _ (hM_fin.mem_toFinset.mpr hs)
      have hs₁_pos : (0 : I) < s₁ := hs₁_M.1.1
      have hs₁_lt1 : s₁ < 1 := hs₁_M.1.2
      have h_disj₁ : ∀ s ∈ Ioo (0 : I) s₁, g s ∉ G.U := by
        intro s ⟨hs0, hss₁⟩ hsU
        have hs_M : s ∈ M := ⟨⟨hs0, hss₁.trans hs₁_lt1⟩, hsU⟩
        exact not_le_of_gt hss₁ (hs₁_min s hs_M)
      let mid₁ : I := ⟨(s₁ : ℝ) / 2, by linarith [s₁.2.1], by linarith [s₁.2.2]⟩
      have hmid₁_mem : mid₁ ∈ Ioo (0 : I) s₁ := by
        have hs₁_r : (0 : ℝ) < (s₁ : ℝ) := hs₁_pos
        exact ⟨by change (0 : ℝ) < (s₁ : ℝ) / 2; linarith,
          by change (s₁ : ℝ) / 2 < (s₁ : ℝ); linarith⟩
      obtain ⟨r₁, hr₁, hmid₁_r₁⟩ := exists_region_of_notMem (h_disj₁ mid₁ hmid₁_mem)
      have hIoo₁_conn : IsPreconnected (g '' Ioo 0 s₁) :=
        (isPreconnected_Ioo (a := (0 : I)) (b := s₁)).image g hgc.continuousOn
      have hIoo₁_disj : Disjoint (g '' Ioo 0 s₁) G.U :=
        disjoint_left.mpr (by rintro _ ⟨s, hs, rfl⟩; exact h_disj₁ s hs)
      have hIoo₁_sub : g '' Ioo 0 s₁ ⊆ r₁ :=
        subset_region hr₁ hIoo₁_conn hIoo₁_disj ⟨mid₁, hmid₁_mem, rfl⟩ hmid₁_r₁
      have ha_cl₁ : a ∈ closure r₁ := by
        have h0 : (0 : I) ∈ closure (Ioo (0 : I) s₁) := by
          rw [closure_Ioo (ne_of_lt hs₁_pos)]
          exact ⟨le_rfl, hs₁_pos.le⟩
        exact closure_mono hIoo₁_sub (image_closure_subset_closure_image hgc ⟨0, h0, hg0⟩)
      have hz₁_cl₁ : g s₁ ∈ closure r₁ := by
        have hs₁_cl : s₁ ∈ closure (Ioo (0 : I) s₁) := by
          rw [closure_Ioo (ne_of_lt hs₁_pos)]
          exact ⟨hs₁_pos.le, le_rfl⟩
        exact closure_mono hIoo₁_sub (image_closure_subset_closure_image hgc ⟨s₁, hs₁_cl, rfl⟩)
      -- Now find s₁' ∈ Ioo s₁ 1 such that g '' Ioc s₁ s₁' ∩ G.U = ∅
      have hex_s₂ : ∃ s₂ : I, s₁ < s₂ ∧ ∀ s ∈ Ioo s₁ s₂, g s ∉ G.U := by
        have hM₂_fin : (M \ {s₁}).Finite := hM_fin.subset sdiff_subset
        rcases (M \ {s₁}).eq_empty_or_nonempty with h_emp | h_ne
        · refine ⟨1, hs₁_lt1, fun s ⟨hss₁, hs1⟩ hsU => ?_⟩
          have hs_M : s ∈ M \ {s₁} := ⟨⟨⟨hs₁_pos.trans hss₁, hs1⟩, hsU⟩, ne_of_gt hss₁⟩
          rw [h_emp] at hs_M
          exact hs_M
        · let s₂ : I := hM₂_fin.toFinset.min' (hM₂_fin.toFinset_nonempty.mpr h_ne)
          have hs₂_mem : s₂ ∈ M \ {s₁} := hM₂_fin.mem_toFinset.mp (Finset.min'_mem _ _)
          have hs₂_min : ∀ s ∈ M \ {s₁}, s₂ ≤ s := fun s hs =>
            Finset.min'_le _ _ (hM₂_fin.mem_toFinset.mpr hs)
          have hs₁_lt_s₂ : s₁ < s₂ :=
            lt_of_le_of_ne (hs₁_min s₂ hs₂_mem.1) (Ne.symm hs₂_mem.2)
          refine ⟨s₂, hs₁_lt_s₂, fun s ⟨hss₁, hss₂⟩ hsU => ?_⟩
          have hs_M₂ : s ∈ M \ {s₁} :=
            ⟨⟨⟨hs₁_pos.trans hss₁, hss₂.trans hs₂_mem.1.1.2⟩, hsU⟩, ne_of_gt hss₁⟩
          exact not_le_of_gt hss₂ (hs₂_min s hs_M₂)
      obtain ⟨s₂, hs₁_lt_s₂, h_disj_s₂⟩ := hex_s₂
      let s₁' : I := ⟨((s₁ : ℝ) + (s₂ : ℝ)) / 2,
        by linarith [s₁.2.1, s₂.2.1], by linarith [s₁.2.2, s₂.2.2]⟩
      have hs₁_r_lt : (s₁ : ℝ) < (s₂ : ℝ) := hs₁_lt_s₂
      have hs₁_lt_s₁' : s₁ < s₁' := by
        change (s₁ : ℝ) < ((s₁ : ℝ) + (s₂ : ℝ)) / 2
        linarith
      have hs₁'_lt_s₂ : s₁' < s₂ := by
        change ((s₁ : ℝ) + (s₂ : ℝ)) / 2 < (s₂ : ℝ)
        linarith
      have hs₁'_lt1 : s₁' < 1 := lt_of_lt_of_le hs₁'_lt_s₂ (unitInterval.le_one s₂)
      have h_disj₂ : ∀ s ∈ Ioc s₁ s₁', g s ∉ G.U := fun s ⟨h1, h2⟩ =>
        h_disj_s₂ s ⟨h1, lt_of_le_of_lt h2 hs₁'_lt_s₂⟩
      have hgs₁'_notU : g s₁' ∉ G.U := h_disj₂ s₁' ⟨hs₁_lt_s₁', le_rfl⟩
      obtain ⟨r₂, hr₂, hgs₁'_r₂⟩ := exists_region_of_notMem hgs₁'_notU
      have hIoc₂_conn : IsPreconnected (g '' Ioc s₁ s₁') :=
        (isPreconnected_Ioc (a := s₁) (b := s₁')).image g hgc.continuousOn
      have hIoc₂_disj : Disjoint (g '' Ioc s₁ s₁') G.U :=
        disjoint_left.mpr (by rintro _ ⟨s, hs, rfl⟩; exact h_disj₂ s hs)
      have hIoc₂_sub : g '' Ioc s₁ s₁' ⊆ r₂ :=
        subset_region hr₂ hIoc₂_conn hIoc₂_disj ⟨s₁', ⟨hs₁_lt_s₁', le_rfl⟩, rfl⟩ hgs₁'_r₂
      have hz₁_cl₂ : g s₁ ∈ closure r₂ := by
        have hs₁_cl : s₁ ∈ closure (Ioc s₁ s₁') := by
          rw [closure_Ioc (ne_of_lt hs₁_lt_s₁')]
          exact ⟨le_rfl, hs₁_lt_s₁'.le⟩
        exact closure_mono hIoc₂_sub (image_closure_subset_closure_image hgc ⟨s₁, hs₁_cl, rfl⟩)
      obtain ⟨v₁, hv₁V, hv₁_cl₁, hv₁_cl₂⟩ :=
        exists_vertex_in_closure_regions hS hG hr₁ hr₂ hs₁_M.2 hz₁_cl₁ hz₁_cl₂
      have hv₁_norm : v₁ ∈ (G.U \ G.V)ᶜ := fun h => h.2 hv₁V
      have hj_av₁ : JoinedIn (r₁ ∪ {a, v₁}) a v₁ :=
        joinedIn_region_union_pair hS hG hr₁ ha_cl₁ ha hv₁_cl₁ hv₁_norm
      have hj_v₁x' : JoinedIn (r₂ ∪ {v₁, g s₁'}) v₁ (g s₁') :=
        joinedIn_region_union_pair hS hG hr₂ hv₁_cl₂ hv₁_norm (subset_closure hgs₁'_r₂)
          (fun h => hgs₁'_notU h.1)
      -- Apply IH to X' = g '' Icc s₁' 1
      let X' : Set S := g '' Icc s₁' 1
      have hX'_line : IsLineWithEnds X' (g s₁') b := hg1 ▸ isLine_piece hgc hgi hs₁'_lt1
      have hX'_sub : X' ⊆ X := by rintro _ ⟨s, _, rfl⟩; exact (e s).2
      have hX'_fin : (G.U ∩ X').Finite := hX_fin.subset (inter_subset_inter_right _ hX'_sub)
      have hX'_int_sub : G.U ∩ (X' \ {g s₁', b}) ⊆ (G.U ∩ (X \ {a, b})) \ {g s₁} := by
        rintro z ⟨hzU, ⟨⟨s, ⟨hss₁', hs1⟩, rfl⟩, hz_end⟩⟩
        have hs_gt : s₁' < s := lt_of_le_of_ne hss₁' fun h => hz_end (Or.inl (congrArg g h.symm))
        have hs_lt1 : s < 1 := lt_of_le_of_ne hs1 fun h => hz_end (Or.inr (h ▸ hg1))
        have hs_gt1 : s₁ < s := hs₁_lt_s₁'.trans hs_gt
        have hs_M : s ∈ M := ⟨⟨hs₁_pos.trans hs_gt1, hs_lt1⟩, hzU⟩
        refine ⟨hM_image ▸ ⟨s, hs_M, rfl⟩, ?_⟩
        intro h_eq
        exact ne_of_gt hs_gt1 (hgi h_eq)
      have hgs₁_mem : g s₁ ∈ G.U ∩ (X \ {a, b}) := hM_image ▸ ⟨s₁, hs₁_M, rfl⟩
      have hX'_card : (G.U ∩ (X' \ {g s₁', b})).ncard ≤ m := by
        calc (G.U ∩ (X' \ {g s₁', b})).ncard
          _ ≤ ((G.U ∩ (X \ {a, b})) \ {g s₁}).ncard :=
            ncard_le_ncard hX'_int_sub (hfin_int.subset sdiff_subset)
          _ = (G.U ∩ (X \ {a, b})).ncard - 1 := ncard_sdiff_singleton_of_mem hgs₁_mem
          _ = m := by omega
      obtain ⟨W', hW'V, hW'fin, hW'card, hj_x'b⟩ :=
        ih (fun h => hgs₁'_notU h.1) hb hX'_line hX'_fin hX'_card
      refine ⟨insert v₁ W', insert_subset hv₁V hW'V, hW'fin.insert v₁, ?_, ?_⟩
      · calc (insert v₁ W').ncard
          _ ≤ W'.ncard + 1 := ncard_insert_le v₁ W'
          _ ≤ m + 1 := Nat.add_le_add_right hW'card 1
      · have hsub₁ : r₁ ∪ {a, v₁} ⊆ G.Uᶜ ∪ insert v₁ W' ∪ {a, b} := by
          rintro z (hzr₁ | (rfl | hzv₁))
          · exact Or.inl (Or.inl (region_subset hr₁ hzr₁))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl (Or.inr (mem_singleton_iff.mp hzv₁ ▸ mem_insert v₁ W'))
        have hsub₂ : r₂ ∪ {v₁, g s₁'} ⊆ G.Uᶜ ∪ insert v₁ W' ∪ {a, b} := by
          rintro z (hzr₂ | (rfl | hzx'))
          · exact Or.inl (Or.inl (region_subset hr₂ hzr₂))
          · exact Or.inl (Or.inr (mem_insert z W'))
          · exact Or.inl (Or.inl (mem_singleton_iff.mp hzx' ▸ hgs₁'_notU))
        have hsub₃ : G.Uᶜ ∪ W' ∪ {g s₁', b} ⊆ G.Uᶜ ∪ insert v₁ W' ∪ {a, b} := by
          rintro z ((hzUc | hzW') | (rfl | hzb))
          · exact Or.inl (Or.inl hzUc)
          · exact Or.inl (Or.inr (mem_insert_of_mem v₁ hzW'))
          · exact Or.inl (Or.inl hgs₁'_notU)
          · exact Or.inr (Or.inr (mem_singleton_iff.mp hzb))
        exact ((hj_av₁.mono hsub₁).trans (hj_v₁x'.mono hsub₂)).trans (hj_x'b.mono hsub₃)

/-- For any distinct `a, b ∈ (G.U \ G.V)ᶜ` and any `[0, 1]`-arc `X` with ends `a, b` and
`(G.U ∩ X).Finite`, there is a `G`-normal `[0, 1]`-arc `P` with ends `a, b` such that
`(G.V ∩ P).ncard ≤ (G.U ∩ X).ncard`. -/
theorem exists_normal_arc_of_lineWithEnds (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {a b : S}
    (ha : a ∈ (G.U \ G.V)ᶜ) (hb : b ∈ (G.U \ G.V)ᶜ) {X : Set S}
    (hX : IsLineWithEnds X a b) (hX_fin : (G.U ∩ X).Finite) :
    ∃ P : Set S, IsLineWithEnds P a b ∧ G.IsNormal P ∧ (G.V ∩ P).ncard ≤ (G.U ∩ X).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨W, hWV, hWfin, hWcard, hj⟩ :=
    exists_joinedIn_normal_of_lineWithEnds hS hG (G.U ∩ (X \ {a, b})).ncard ha hb hX hX_fin le_rfl
  obtain ⟨P, hP_sub, hP_line⟩ :=
    ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := G.Uᶜ ∪ W ∪ {a, b})
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))).mp hj).resolve_left hX.ne'
  have hP_norm : G.IsNormal P := by
    rintro z ⟨hzP, hzU⟩
    rcases hP_sub hzP with (hzUc | hzW) | (rfl | hzb)
    · exact False.elim (hzUc hzU)
    · exact hWV hzW
    · exact by_contra fun hzV => ha ⟨hzU, hzV⟩
    · exact by_contra fun hzV => hb ⟨mem_singleton_iff.mp hzb ▸ hzU, mem_singleton_iff.mp hzb ▸ hzV⟩
  have hVP_sub : G.V ∩ P ⊆ (G.V ∩ (P \ {a, b})) ∪ (G.U ∩ (X ∩ {a, b})) := by
    rintro z ⟨hzV, hzP⟩
    by_cases hz_ab : z ∈ ({a, b} : Set S)
    · refine Or.inr ⟨G.V_subset_U hzV, ?_, hz_ab⟩
      rcases hz_ab with rfl | hzb
      · exact hX.left_mem
      · exact mem_singleton_iff.mp hzb ▸ hX.right_mem
    · exact Or.inl ⟨hzV, hzP, hz_ab⟩
  have hVP_diff_sub : G.V ∩ (P \ {a, b}) ⊆ W := by
    rintro z ⟨hzV, hzP, hz_ab⟩
    rcases hP_sub hzP with (hzUc | hzW) | hz_ab'
    · exact False.elim (hzUc (G.V_subset_U hzV))
    · exact hzW
    · exact False.elim (hz_ab hz_ab')
  have hfin1 : (G.V ∩ (P \ {a, b})).Finite := hWfin.subset hVP_diff_sub
  have hfin2 : (G.U ∩ (X ∩ {a, b})).Finite := hX_fin.subset (inter_subset_inter_right _
    inter_subset_left)
  have hfin3 : (G.U ∩ (X \ {a, b})).Finite := hX_fin.subset (inter_subset_inter_right _
    sdiff_subset)
  have hX_split : G.U ∩ X = (G.U ∩ (X \ {a, b})) ∪ (G.U ∩ (X ∩ {a, b})) := by
    ext z
    simp only [mem_inter_iff, mem_union, Set.mem_sdiff]
    by_cases h : z ∈ ({a, b} : Set S) <;> tauto
  have hX_disj : Disjoint (G.U ∩ (X \ {a, b})) (G.U ∩ (X ∩ {a, b})) :=
    disjoint_left.mpr fun _ ⟨_, _, h1⟩ ⟨_, _, h2⟩ => h1 h2
  refine ⟨P, hP_line, hP_norm, ?_⟩
  calc (G.V ∩ P).ncard
    _ ≤ ((G.V ∩ (P \ {a, b})) ∪ (G.U ∩ (X ∩ {a, b}))).ncard :=
      ncard_le_ncard hVP_sub (hfin1.union hfin2)
    _ ≤ (G.V ∩ (P \ {a, b})).ncard + (G.U ∩ (X ∩ {a, b})).ncard :=
      ncard_union_le _ _
    _ ≤ W.ncard + (G.U ∩ (X ∩ {a, b})).ncard :=
      Nat.add_le_add_right (ncard_le_ncard hVP_diff_sub hWfin) _
    _ ≤ (G.U ∩ (X \ {a, b})).ncard + (G.U ∩ (X ∩ {a, b})).ncard :=
      Nat.add_le_add_right hWcard _
    _ = (G.U ∩ X).ncard := by
      rw [hX_split, ncard_union_eq hX_disj hfin3 hfin2]

/-- If `C ∈ cuffs S` and `IsPlanar X`, then `IsPlanarInCappedCuff C X`. -/
theorem isPlanarInCappedCuff_of_isPlanar (hS : IsSurface S) {C X : Set S}
    (hC : C ∈ cuffs S) (hX : IsPlanar X) :
    IsPlanarInCappedCuff C X := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨c₀, hc₀⟩ := isOArc_nonempty (cuff_isOArc hS hC)
  have : Nonempty S := ⟨c₀⟩
  have h_all : ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsPlanar (j '' X) := by
    intro S' _ j D hCap
    have : T2Space S' := hCap.isSurface.2.1
    obtain ⟨Δ, hΔ, hXΔ⟩ := hX
    obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn hΔ.isCompact
      hCap.isEmbedding.continuous.continuousOn hCap.isEmbedding.injective.injOn
    exact ⟨j '' Δ, (hΔ.image hCap.isEmbedding.continuous.continuousOn hd'c hd'l).1, image_mono hXΔ⟩
  obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ :=
    paste_disc S C hS hC
  have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
  exact ⟨hC, ⟨S', topS', j, D, hCap, h_all S' j D hCap⟩, h_all⟩

/-- If `g : I → S` is continuous, `a < b` in `I`, and `InjOn g (Icc a b)`, then `g '' Icc a b` is a
`[0, 1]`-arc with ends `g a` and `g b`. -/
theorem isLineWithEnds_image_Icc_of_injOn [T2Space S] {g : I → S} (hgc : Continuous g)
    {a b : I} (hab : a < b) (hinj : InjOn g (Icc a b)) :
    IsLineWithEnds (g '' Icc a b) (g a) (g b) := by
  have hab_r : (a : ℝ) < (b : ℝ) := hab
  have hm_mem : ∀ t : I, (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ∈ Icc (a : ℝ) (b : ℝ) := by
    intro t
    exact ⟨by nlinarith [t.2.1, t.2.2, hab_r], by nlinarith [t.2.1, t.2.2, hab_r]⟩
  let m : I → I := fun t => ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    a.2.1.trans (hm_mem t).1, (hm_mem t).2.trans b.2.2⟩
  have hm_cont : Continuous m := Continuous.subtype_mk (by fun_prop) _
  have hm_inj : Function.Injective m := by
    intro t₁ t₂ h
    have hr_eq : (1 - (t₁ : ℝ)) * (a : ℝ) + (t₁ : ℝ) * (b : ℝ) =
        (1 - (t₂ : ℝ)) * (a : ℝ) + (t₂ : ℝ) * (b : ℝ) := congrArg Subtype.val h
    exact Subtype.ext (by nlinarith [hab_r, hr_eq])
  have hgm_inj : Function.Injective (g ∘ m) := fun t₁ t₂ h =>
    hm_inj (hinj (hm_mem t₁) (hm_mem t₂) h)
  have hrange : range (g ∘ m) = g '' Icc a b := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨m t, hm_mem t, rfl⟩
    · rintro ⟨s, ⟨hsa, hsb⟩, rfl⟩
      have hba_pos : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr hab_r
      have hsa_r : (a : ℝ) ≤ (s : ℝ) := hsa
      have hsb_r : (s : ℝ) ≤ (b : ℝ) := hsb
      let t : I := ⟨((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)),
        div_nonneg (sub_nonneg.mpr hsa_r) hba_pos.le,
        (div_le_one hba_pos).mpr (sub_le_sub_right hsb_r (a : ℝ))⟩
      refine ⟨t, congrArg g (Subtype.ext ?_)⟩
      change (1 - ((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (a : ℝ) +
        (((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (b : ℝ) = (s : ℝ)
      have hne : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt hba_pos
      calc (1 - ((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (a : ℝ) +
          (((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (b : ℝ)
        _ = (a : ℝ) + (((s : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * ((b : ℝ) - (a : ℝ)) := by ring
        _ = (a : ℝ) + ((s : ℝ) - (a : ℝ)) := by rw [div_mul_cancel₀ _ hne]
        _ = (s : ℝ) := by ring
  have hemb : IsEmbedding (g ∘ m) := ((hgc.comp hm_cont).isClosedEmbedding hgm_inj).isEmbedding
  rw [← hrange]
  refine ⟨hemb.toHomeomorph, ?_, ?_⟩
  · change g (m 0) = g a
    have hm0 : m 0 = a := Subtype.ext (by simp [m])
    rw [hm0]
  · change g (m 1) = g b
    have hm1 : m 1 = b := Subtype.ext (by simp [m])
    rw [hm1]

/-- An embedding `j : S → T` maps components of `X ⊆ S` to components of `j '' X ⊆ T`. -/
theorem image_mem_componentsIn_of_isEmbedding {T : Type*} [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {X B : Set S} (hB : B ∈ componentsIn X) :
    j '' B ∈ componentsIn (j '' X) := by
  obtain ⟨z, hzX, rfl⟩ := hB
  refine ⟨j z, mem_image_of_mem j hzX, ?_⟩
  apply Subset.antisymm
  · intro y hy
    have hex : ∀ w : connectedComponentIn (j '' X) (j z), ∃ x ∈ X, j x = w.1 :=
      fun w => connectedComponentIn_subset (j '' X) (j z) w.2
    choose f hfX hfeq using hex
    have hf_cont : Continuous f := hj.continuous_iff.mpr (by
      have : j ∘ f = Subtype.val := funext hfeq
      rw [this]
      exact continuous_subtype_val)
    have : PreconnectedSpace (connectedComponentIn (j '' X) (j z)) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
    have h_range_pre : IsPreconnected (range f) := isPreconnected_range hf_cont
    let w₀ : connectedComponentIn (j '' X) (j z) := ⟨j z, mem_connectedComponentIn
      (mem_image_of_mem j hzX)⟩
    have hfw₀ : f w₀ = z := hj.injective (hfeq w₀)
    have h_sub : range f ⊆ connectedComponentIn X z :=
      h_range_pre.subset_connectedComponentIn ⟨w₀, hfw₀⟩ (by rintro _ ⟨w, rfl⟩; exact hfX w)
    exact ⟨f ⟨y, hy⟩, h_sub ⟨⟨y, hy⟩, rfl⟩, hfeq ⟨y, hy⟩⟩
  · have h_pre : IsPreconnected (j '' connectedComponentIn X z) :=
      isPreconnected_connectedComponentIn.image j hj.continuous.continuousOn
    exact h_pre.subset_connectedComponentIn
      (mem_image_of_mem j (mem_connectedComponentIn hzX))
      (image_mono (connectedComponentIn_subset X z))

/-- For any `v ∈ closure (nearSet G t F₀) ∩ (G.U \ G.V)ᶜ` where `F₀` is a `G`-normal `O`-arc, there
is a point `u ∈ F₀` and a `G`-normal `[0, 1]`-arc `P` with ends `v, u` such that
`(G.V ∩ P).ncard ≤ t + 1`. -/
theorem exists_normal_arc_to_F0 (hS : IsSurface S) [ConnectedSpace S]
    {G : Drawing S} (hG : G.IsProper) {F₀ : Set S} (hF₀_oarc : IsOArc F₀)
    (hF₀_norm : G.IsNormal F₀) {t : ℕ} {v : S}
    (hv_cl : v ∈ closure (nearSet G t F₀)) (hv_norm : v ∈ (G.U \ G.V)ᶜ) :
    ∃ (u : S) (P : Set S), u ∈ F₀ ∧ IsLineWithEnds P v u ∧ G.IsNormal P ∧
      (G.V ∩ P).ncard ≤ t + 1 := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  rw [closure_nearSet_eq_closure_sUnion_regions hS hG hF₀_norm t] at hv_cl
  let ℛ : Set (Set S) := {r ∈ G.R | r ⊆ nearSet G t F₀}
  have hfinℛ : ℛ.Finite := (finite_regions_of_isProper hS hG).subset (sep_subset _ _)
  have hv_bi : v ∈ ⋃ r ∈ ℛ, closure r := by
    have heq : closure (⋃₀ ℛ) = ⋃ r ∈ ℛ, closure r := by
      rw [sUnion_eq_biUnion, hfinℛ.closure_biUnion]
    rwa [← heq]
  obtain ⟨r, ⟨hr, hr_sub⟩, hvr⟩ := mem_iUnion₂.mp hv_bi
  obtain ⟨x₀, hx₀r⟩ := region_nonempty hr
  obtain ⟨y, hyF₀, hx₀y_le⟩ := hr_sub hx₀r
  have hy_norm : y ∈ (G.U \ G.V)ᶜ := fun ⟨hyU, hyV⟩ => hyV (hF₀_norm ⟨hyF₀, hyU⟩)
  by_cases hvy : v = y
  · subst hvy
    obtain ⟨φ₀⟩ := id hF₀_oarc
    let w₀ : Circle := φ₀.symm ⟨v, hyF₀⟩
    let g₀ : I → S := fun s => (φ₀ (arcParam w₀ s)).1
    have hg₀c : Continuous g₀ :=
      continuous_subtype_val.comp (φ₀.continuous.comp (arcParam w₀).continuous)
    have hg₀0 : g₀ 0 = v := by
      change (φ₀ (arcParam w₀ 0)).1 = v
      rw [arcParam_zero, φ₀.apply_symm_apply]
    have hV_open : IsOpen ((G.V \ {v})ᶜ) := (G.finite_V.subset sdiff_subset).isClosed.isOpen_compl
    have hg₀_mem : g₀ 0 ∈ (G.V \ {v})ᶜ := by rw [hg₀0]; exact fun h => h.2 rfl
    let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
    have hhalf_pos : (0 : I) < half := by change (0 : ℝ) < 1 / 2; norm_num
    obtain ⟨u₀, hu₀_pos, hu₀_le_half, hu₀_mem⟩ :=
      exists_pos_le hg₀c hV_open hg₀_mem hhalf_pos
    have hu₀_lt1 : u₀ < 1 := by
      change (u₀ : ℝ) < 1
      have : (u₀ : ℝ) ≤ 1 / 2 := hu₀_le_half
      linarith
    let P : Set S := g₀ '' Icc 0 u₀
    have hg₀_inj_Icc : InjOn g₀ (Icc 0 u₀) := by
      intro s₁ hs₁ s₂ hs₂ heq
      have hφ_eq : φ₀ (arcParam w₀ s₁) = φ₀ (arcParam w₀ s₂) := Subtype.ext heq
      rcases arcParam_eq_iff w₀ (φ₀.injective hφ_eq) with h | ⟨_, h1⟩ | ⟨h1, _⟩
      · exact h
      · exact False.elim (ne_of_lt (lt_of_le_of_lt hs₂.2 hu₀_lt1) h1)
      · exact False.elim (ne_of_lt (lt_of_le_of_lt hs₁.2 hu₀_lt1) h1)
    have hP_line : IsLineWithEnds P v (g₀ u₀) := by
      have hm_le : ∀ s : I, (s : ℝ) * (u₀ : ℝ) ≤ (u₀ : ℝ) := fun s =>
        mul_le_of_le_one_left u₀.2.1 s.2.2
      let m : I → I := fun s => ⟨(s : ℝ) * (u₀ : ℝ), mul_nonneg s.2.1 u₀.2.1,
        (hm_le s).trans u₀.2.2⟩
      have hm_cont : Continuous m := Continuous.subtype_mk (by fun_prop) _
      have hm_inj : Function.Injective m := by
        intro s₁ s₂ h
        have hr_eq : (s₁ : ℝ) * (u₀ : ℝ) = (s₂ : ℝ) * (u₀ : ℝ) := congrArg Subtype.val h
        have hu₀_r : (0 : ℝ) < (u₀ : ℝ) := hu₀_pos
        exact Subtype.ext (mul_right_cancel₀ (ne_of_gt hu₀_r) hr_eq)
      have hgm_inj : Function.Injective (g₀ ∘ m) := fun s₁ s₂ h =>
        hm_inj (hg₀_inj_Icc ⟨(m s₁).2.1, hm_le s₁⟩ ⟨(m s₂).2.1, hm_le s₂⟩ h)
      have hrange : range (g₀ ∘ m) = P := by
        ext z
        constructor
        · rintro ⟨s, rfl⟩
          exact ⟨m s, ⟨(m s).2.1, hm_le s⟩, rfl⟩
        · rintro ⟨s, ⟨hs0, hsu₀⟩, rfl⟩
          have hu₀_r : (0 : ℝ) < (u₀ : ℝ) := hu₀_pos
          let t : I := ⟨(s : ℝ) / (u₀ : ℝ), div_nonneg hs0 hu₀_r.le, (div_le_one hu₀_r).mpr hsu₀⟩
          refine ⟨t, congrArg g₀ (Subtype.ext ?_)⟩
          change ((s : ℝ) / (u₀ : ℝ)) * (u₀ : ℝ) = (s : ℝ)
          exact div_mul_cancel₀ (s : ℝ) (ne_of_gt hu₀_r)
      have hemb : IsEmbedding (g₀ ∘ m) := ((hg₀c.comp hm_cont).isClosedEmbedding
        hgm_inj).isEmbedding
      rw [← hrange]
      refine ⟨hemb.toHomeomorph, ?_, ?_⟩
      · change g₀ (m 0) = v
        have hm0 : m 0 = 0 := Subtype.ext (by simp [m])
        rw [hm0, hg₀0]
      · change g₀ (m 1) = g₀ u₀
        have hm1 : m 1 = u₀ := Subtype.ext (by simp [m])
        rw [hm1]
    have hP_sub : P ⊆ F₀ := by rintro _ ⟨s, _, rfl⟩; exact (φ₀ (arcParam w₀ s)).2
    have hVP_sub : G.V ∩ P ⊆ {v} := by
      rintro z ⟨hzV, s, ⟨_, hsu₀⟩, rfl⟩
      by_contra hzv
      exact hu₀_mem s hsu₀ ⟨hzV, hzv⟩
    refine ⟨g₀ u₀, P, (φ₀ (arcParam w₀ u₀)).2, hP_line,
      fun z ⟨hzP, hzU⟩ => hF₀_norm ⟨hP_sub hzP, hzU⟩, ?_⟩
    calc (G.V ∩ P).ncard
      _ ≤ ({v} : Set S).ncard := ncard_le_ncard hVP_sub (finite_singleton v)
      _ = 1 := ncard_singleton v
      _ ≤ t + 1 := Nat.le_add_left 1 t
  · have hdist_vy : distPoint G v y ≤ t + 1 := by
      by_cases hx₀v : x₀ = v
      · subst hx₀v
        exact hx₀y_le.trans (Nat.le_succ t)
      · have hj_vx₀ := joinedIn_region_union_pair hS hG hr hvr hv_norm (subset_closure hx₀r)
          (fun h => region_subset hr hx₀r h.1)
        by_cases hx₀y : x₀ = y
        · subst hx₀y
          obtain ⟨L, hL_sub, hL_line⟩ :=
            ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := r ∪ {v, x₀})
              (Or.inr (Or.inl rfl)) (Or.inl hx₀r)).mp hj_vx₀).resolve_left hvy
          have hUL_sub : G.U ∩ L ⊆ {v} := by
            rintro z ⟨hzU, hzL⟩
            rcases hL_sub hzL with hzr | (rfl | hzx₀)
            · exact False.elim (region_subset hr hzr hzU)
            · rfl
            · exact False.elim (region_subset hr (mem_singleton_iff.mp hzx₀ ▸ hx₀r) hzU)
          have hUL_fin : (G.U ∩ L).Finite := (finite_singleton v).subset hUL_sub
          calc distPoint G v x₀
            _ ≤ (G.U ∩ L).ncard := distPoint_le_of_lineWithEnds hL_line hUL_fin
            _ ≤ ({v} : Set S).ncard := ncard_le_ncard hUL_sub (finite_singleton v)
            _ = 1 := ncard_singleton v
            _ ≤ t + 1 := Nat.le_add_left 1 t
        · obtain ⟨X, hX_line, hX_fin, hX_card⟩ := distPoint_exists_arc hS hG hx₀y
          have hj_X : JoinedIn X x₀ y :=
            (joinedIn_iff_eq_or_exists_isLineWithEnds (Z := X) hX_line.left_mem
              hX_line.right_mem).mpr
              (Or.inr ⟨X, Subset.rfl, hX_line⟩)
          have hj_vy : JoinedIn ((r ∪ {v, x₀}) ∪ X) v y :=
            (hj_vx₀.mono subset_union_left).trans (hj_X.mono subset_union_right)
          obtain ⟨X', hX'_sub, hX'_line⟩ :=
            ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := (r ∪ {v, x₀}) ∪ X)
              (Or.inl (Or.inr (Or.inl rfl))) (Or.inr hX_line.right_mem)).mp hj_vy).resolve_left hvy
          have hUX'_sub : G.U ∩ X' ⊆ insert v (G.U ∩ X) := by
            rintro z ⟨hzU, hzX'⟩
            rcases hX'_sub hzX' with (hzr | (rfl | hzx₀)) | hzX
            · exact False.elim (region_subset hr hzr hzU)
            · exact mem_insert z (G.U ∩ X)
            · exact False.elim (region_subset hr (mem_singleton_iff.mp hzx₀ ▸ hx₀r) hzU)
            · exact mem_insert_of_mem v ⟨hzU, hzX⟩
          have hUX'_fin : (G.U ∩ X').Finite := (hX_fin.insert v).subset hUX'_sub
          calc distPoint G v y
            _ ≤ (G.U ∩ X').ncard := distPoint_le_of_lineWithEnds hX'_line hUX'_fin
            _ ≤ (insert v (G.U ∩ X)).ncard := ncard_le_ncard hUX'_sub (hX_fin.insert v)
            _ ≤ (G.U ∩ X).ncard + 1 := ncard_insert_le v (G.U ∩ X)
            _ = distPoint G x₀ y + 1 := by rw [hX_card]
            _ ≤ t + 1 := Nat.add_le_add_right hx₀y_le 1
    obtain ⟨X, hX_line, hX_fin, hX_card⟩ := distPoint_exists_arc hS hG hvy
    obtain ⟨P, hP_line, hP_norm, hP_card⟩ :=
      exists_normal_arc_of_lineWithEnds hS hG hv_norm hy_norm hX_line hX_fin
    exact ⟨y, P, hyF₀, hP_line, hP_norm, hP_card.trans (hX_card ▸ hdist_vy)⟩

/-- Given an `O`-arc `F₀`, distinct points `x, y ∈ F₀`, and a finite set `V : Set S`, there is a
component `B ∈ componentsIn (F₀ \ {x, y})` such that `B ⊆ F₀`, `2 * (V ∩ B).ncard ≤ (V ∩ F₀).ncard`,
and `IsLineWithEnds (B ∪ {x, y}) x y`. -/
theorem exists_short_component_oArc_diff_pair [T2Space S] {F₀ V : Set S} (hF₀ : IsOArc F₀)
    (hV : V.Finite) {x y : S} (hx : x ∈ F₀) (hy : y ∈ F₀) (hxy : x ≠ y) :
    ∃ B ∈ componentsIn (F₀ \ {x, y}), B ⊆ F₀ ∧ 2 * (V ∩ B).ncard ≤ (V ∩ F₀).ncard ∧
      IsLineWithEnds (B ∪ {x, y}) x y := by
  obtain ⟨B₁, B₂, hcomponents, hdisjoint, hcover, hline₁, hline₂⟩ :=
    Net.oArc_components_diff_pair hF₀ hx hy hxy
  have hsub : B₁ ∪ B₂ ⊆ F₀ := by
    rw [← hcover]
    exact sdiff_subset
  have hsub₁ : B₁ ⊆ F₀ := subset_union_left.trans hsub
  have hsub₂ : B₂ ⊆ F₀ := subset_union_right.trans hsub
  have hsum : (V ∩ B₁).ncard + (V ∩ B₂).ncard ≤ (V ∩ F₀).ncard := by
    rw [← ncard_union_eq (hdisjoint.mono inter_subset_right inter_subset_right)
      (hV.inter_of_left B₁) (hV.inter_of_left B₂)]
    exact ncard_le_ncard
      (union_subset (inter_subset_inter_right V hsub₁) (inter_subset_inter_right V hsub₂))
      (hV.inter_of_left F₀)
  rcases le_or_gt (2 * (V ∩ B₁).ncard) (V ∩ F₀).ncard with hle | hgt
  · exact ⟨B₁, by rw [hcomponents]; exact mem_insert _ _, hsub₁, hle, hline₁⟩
  · exact ⟨B₂, by rw [hcomponents]; exact mem_insert_of_mem _ rfl, hsub₂, by omega, hline₂⟩

/-- Every `O`-arc is connected (`IsConnected`). -/
theorem isConnected_of_isOArc {F : Set S} (hF : IsOArc F) : IsConnected F := by
  obtain ⟨φ⟩ := id hF
  have hrange : F = range (fun w : Circle => (φ w).1) := by
    ext x
    exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨w, rfl⟩; exact (φ w).2⟩
  rw [hrange]
  exact isConnected_range (continuous_subtype_val.comp φ.continuous)

/-- Every `O`-arc in a surface `S` is solid (`IsSolid`). -/
theorem isSolid_of_isOArc (hS : IsSurface S) {F : Set S} (hF : IsOArc F) : IsSolid F := by
  have : T2Space S := hS.2.1
  obtain ⟨φ⟩ := id hF
  let g : I → S := fun s => (φ (arcParam 1 s)).1
  have hgc : Continuous g :=
    continuous_subtype_val.comp (φ.continuous.comp (arcParam 1).continuous)
  let h : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have h0h : (0 : I) < h := Subtype.mk_lt_mk.mpr (by norm_num)
  have hh1 : h < (1 : I) := Subtype.mk_lt_mk.mpr (by norm_num)
  have hinj1 : InjOn g (Icc 0 h) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have hφ_eq : φ (arcParam 1 s₁) = φ (arcParam 1 s₂) := Subtype.ext heq
    rcases arcParam_eq_iff 1 (φ.injective hφ_eq) with h_eq | ⟨_, h1⟩ | ⟨h1, _⟩
    · exact h_eq
    · exact False.elim (ne_of_lt (lt_of_le_of_lt hs₂.2 hh1) h1)
    · exact False.elim (ne_of_lt (lt_of_le_of_lt hs₁.2 hh1) h1)
  have hinj2 : InjOn g (Icc h 1) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have hφ_eq : φ (arcParam 1 s₁) = φ (arcParam 1 s₂) := Subtype.ext heq
    rcases arcParam_eq_iff 1 (φ.injective hφ_eq) with h_eq | ⟨h0, _⟩ | ⟨_, h0⟩
    · exact h_eq
    · exact False.elim (ne_of_gt (lt_of_lt_of_le h0h hs₁.1) h0)
    · exact False.elim (ne_of_gt (lt_of_lt_of_le h0h hs₂.1) h0)
  have hL1 : IsLineWithEnds (g '' Icc 0 h) (g 0) (g h) :=
    isLineWithEnds_image_Icc_of_injOn hgc h0h hinj1
  have hL2 : IsLineWithEnds (g '' Icc h 1) (g h) (g 1) :=
    isLineWithEnds_image_Icc_of_injOn hgc hh1 hinj2
  have hF_eq : F = g '' Icc 0 h ∪ g '' Icc h 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨τ, hτ⟩ := arcParam_surjective 1 (φ.symm ⟨z, hz⟩)
      have hz_eq : g τ = z := by simp [g, hτ]
      rcases le_total τ h with hle | hge
      · exact Or.inl ⟨τ, ⟨unitInterval.nonneg τ, hle⟩, hz_eq⟩
      · exact Or.inr ⟨τ, ⟨hge, unitInterval.le_one τ⟩, hz_eq⟩
    · rintro (⟨τ, _, rfl⟩ | ⟨τ, _, rfl⟩) <;> exact (φ (arcParam 1 τ)).2
  rw [hF_eq]
  exact theorem_11_6_proof hS (isSolid_of_isLineWithEnds hS hL1) (isSolid_of_isLineWithEnds hS hL2)

/-- Every `[0, 1]`-arc is connected (`IsConnected`). -/
theorem isConnected_of_isLineWithEnds {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    IsConnected L := by
  obtain ⟨e, -, -⟩ := id hL
  have hrange : L = range (fun t : I => (e t).1) := by
    ext x
    exact ⟨fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (e t).2⟩
  rw [hrange]
  exact isConnected_range (continuous_subtype_val.comp e.continuous)

theorem left_mem_of_isLineWithEnds {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : a ∈ L := by
  obtain ⟨e, he0, -⟩ := id hL
  exact he0 ▸ (e 0).2

theorem right_mem_of_isLineWithEnds {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : b ∈ L := by
  obtain ⟨e, -, he1⟩ := id hL
  exact he1 ▸ (e 1).2

/-- Pushforward of `IsLineWithEnds` along an embedding `j : S → T`. -/
theorem image_of_isLineWithEnds {T : Type*} [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) :
    IsLineWithEnds (j '' L) (j a) (j b) := by
  obtain ⟨e, he0, he1⟩ := id hL
  let f : I → T := fun t => j (e t).1
  have hrange : range f = j '' L := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(e t).1, (e t).2, rfl⟩
    · rintro ⟨x, hxL, rfl⟩
      exact ⟨e.symm ⟨x, hxL⟩, by simp [f]⟩
  have hemb : IsEmbedding f := hj.comp (IsEmbedding.subtypeVal.comp e.isEmbedding)
  rw [← hrange]
  exact ⟨hemb.toHomeomorph, congrArg j he0, congrArg j he1⟩

omit [TopologicalSpace S] in
/-- Given a finite subset `V ⊆ S` and a parameterization `g : I → S` injective on `Ico 0 1`,
there is a strictly increasing partition `0 = s 0 < s 1 < ... < s r = 1` of `[0, 1]` such that
`g '' Ioo (s i) (s (i + 1))` is disjoint from `V` for all `i < r`. -/
theorem exists_partition_of_oArc {V : Set S} (hV : V.Finite) {g : I → S}
    (hg_inj_Ico : InjOn g (Ico 0 1)) :
    ∃ (r : ℕ) (_ : 0 < r) (s : ℕ → I),
      s 0 = 0 ∧ s r = 1 ∧ (∀ i < r, s i < s (i + 1)) ∧
      (∀ i < r, ∀ τ ∈ Ioo (s i) (s (i + 1)), g τ ∉ V) := by
  classical
  let S_V : Set I := (g ⁻¹' V ∩ Ico 0 1) ∪ {0, 1}
  have hSV_fin : S_V.Finite :=
    ((hV.subset (by rintro _ ⟨s, ⟨hsV, _⟩, rfl⟩; exact hsV)).of_finite_image
      (hg_inj_Ico.mono inter_subset_right)).union ((finite_singleton (1 : I)).insert 0)
  let L : Finset I := hSV_fin.toFinset
  have h0_L : (0 : I) ∈ L := hSV_fin.mem_toFinset.mpr (Or.inr (Or.inl rfl))
  have h1_L : (1 : I) ∈ L := hSV_fin.mem_toFinset.mpr (Or.inr (Or.inr rfl))
  have hL_card2 : 2 ≤ L.card := by
    have hsub : ({0, 1} : Finset I) ⊆ L := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx1
      · exact h0_L
      · exact (Finset.mem_singleton.mp hx1) ▸ h1_L
    have hpair : ({0, 1} : Finset I).card = 2 := Finset.card_pair zero_ne_one
    exact hpair ▸ Finset.card_le_card hsub
  let r : ℕ := L.card - 1
  have hr : 0 < r := by omega
  have hL_card : L.card = r + 1 := by omega
  let emb : Fin (r + 1) ↪o I := L.orderEmbOfFin hL_card
  have hemb0 : emb ⟨0, Nat.succ_pos r⟩ = 0 := by
    have h0_mem : (0 : I) ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact h0_L
    obtain ⟨k, hk⟩ := h0_mem
    have hle : emb ⟨0, Nat.succ_pos r⟩ ≤ 0 := hk ▸ emb.monotone (Fin.zero_le k)
    exact le_antisymm hle (Subtype.mk_le_mk.mpr (unitInterval.nonneg _))
  have hembr : emb ⟨r, Nat.lt_succ_self r⟩ = 1 := by
    have h1_mem : (1 : I) ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact h1_L
    obtain ⟨k, hk⟩ := h1_mem
    have hge : (1 : I) ≤ emb ⟨r, Nat.lt_succ_self r⟩ := hk ▸ emb.monotone (Fin.le_last k)
    exact le_antisymm (Subtype.mk_le_mk.mpr (unitInterval.le_one _)) hge
  let s : ℕ → I := fun i => if hi : i ≤ r then emb ⟨i, Nat.lt_succ_of_le hi⟩ else 1
  refine ⟨r, hr, s, by simpa [s] using hemb0, by simp [s, hembr], ?_, ?_⟩
  · intro i hi
    have hi1 : i + 1 ≤ r := hi
    have hi0 : i ≤ r := Nat.le_of_succ_le hi1
    simp only [s, hi0, hi1, ↓reduceDIte]
    exact emb.strictMono (Nat.lt_succ_self i)
  · intro i hi τ ⟨hτ1, hτ2⟩ hτV
    have hi1 : i + 1 ≤ r := hi
    have hi0 : i ≤ r := Nat.le_of_succ_le hi1
    have hs0_le : (0 : I) ≤ s i := Subtype.mk_le_mk.mpr (unitInterval.nonneg _)
    have hsr_le : s (i + 1) ≤ 1 := Subtype.mk_le_mk.mpr (unitInterval.le_one _)
    have hτ_Ico : τ ∈ Ico (0 : I) 1 := ⟨hs0_le.trans hτ1.le, lt_of_lt_of_le hτ2 hsr_le⟩
    have hτ_L : τ ∈ L := hSV_fin.mem_toFinset.mpr (Or.inl ⟨hτV, hτ_Ico⟩)
    have hτ_range : τ ∈ Set.range emb := by rwa [Finset.range_orderEmbOfFin]
    obtain ⟨k, hk⟩ := hτ_range
    simp only [s, hi0, hi1, ↓reduceDIte, ← hk] at hτ1 hτ2
    have hk1 : i < k.1 := emb.strictMono.lt_iff_lt.mp hτ1
    have hk2 : k.1 < i + 1 := emb.strictMono.lt_iff_lt.mp hτ2
    omega

private theorem closed_arc_segment_solid_connected
    {S : Type u}
    [TopologicalSpace S]
    (hS : IsSurface S)
    [T2Space S]
    (F : Set S)
    (hF_oarc : IsOArc F)
    (φ : Circle ≃ₜ ↑F)
    (g : ↑I → S)
    (hg_def : ∀ (s : ↑I), g s = ↑(φ ((arcParam 1) s)))
    (hgc : Continuous g)
    (hg_mem : ∀ (s : ↑I), g s ∈ F)
    (r : ℕ)
    (hr : 0 < r)
    (s : ℕ → ↑I)
    (hs0 : s 0 = 0)
    (hsr : s r = 1)
    (hs_lt : ∀ i < r, s i < s (i + 1))
    (v : ℕ → S)
    (hv_def : ∀ (i : ℕ), v i = g (s i))
    (Abar : ℕ → Set S)
    (hAbar_def : ∀ (i : ℕ), Abar i = g '' Icc (s i) (s (i + 1))) :
    ∀ i < r, IsSolid (Abar i) ∧ IsConnected (Abar i) := by
  intro i hi
  by_cases hr1 : r = 1
  · have hi0 : i = 0 := by omega
    subst hi0
    have hs1 : s 1 = 1 := by rw [← hr1]; exact hsr
    have heq_F : Abar 0 = F := by
      rw [hAbar_def, hs0, hs1]
      ext z
      constructor
      · rintro ⟨τ, _, rfl⟩; exact hg_mem τ
      · intro hz
        obtain ⟨τ, hτ⟩ := arcParam_surjective 1 (φ.symm ⟨z, hz⟩)
        exact ⟨τ, ⟨Subtype.mk_le_mk.mpr (unitInterval.nonneg τ),
          Subtype.mk_le_mk.mpr (unitInterval.le_one τ)⟩, by simp [hg_def, hτ]⟩
    rw [heq_F]
    exact ⟨isSolid_of_isOArc hS hF_oarc, isConnected_of_isOArc hF_oarc⟩
  · have h_not_01 : ¬ (s i = 0 ∧ s (i + 1) = 1) := by
      rintro ⟨hsi0, hsi1⟩
      rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi_pos
      · have hlt := hs_lt 1 (by omega)
        have hle : s 2 ≤ 1 := Subtype.mk_le_mk.mpr (unitInterval.le_one (s 2))
        rw [hsi1] at hlt
        exact not_lt_of_ge hle hlt
      · have h0_lt : s 0 < s i := by
          clear hsi0 hsi1
          induction i, hi_pos using Nat.le_induction with
          | base => exact hs_lt 0 (by omega)
          | succ k hk ih => exact (ih (by omega)).trans (hs_lt k (by omega))
        rw [hs0, hsi0] at h0_lt
        exact lt_irrefl 0 h0_lt
    have hinj_Icc : InjOn g (Icc (s i) (s (i + 1))) := by
      intro τ₁ hτ₁ τ₂ hτ₂ heq
      rw [hg_def, hg_def] at heq
      have hφ_eq : φ (arcParam 1 τ₁) = φ (arcParam 1 τ₂) := Subtype.ext heq
      rcases arcParam_eq_iff 1 (φ.injective hφ_eq) with h | ⟨h0, h1⟩ | ⟨h1, h0⟩
      · exact h
      · exfalso
        have hsi0 : s i = 0 :=
          le_antisymm (h0 ▸ hτ₁.1) (Subtype.mk_le_mk.mpr (unitInterval.nonneg _))
        have hsi1 : s (i + 1) = 1 :=
          le_antisymm (Subtype.mk_le_mk.mpr (unitInterval.le_one _)) (h1 ▸ hτ₂.2)
        exact h_not_01 ⟨hsi0, hsi1⟩
      · exfalso
        have hsi0 : s i = 0 :=
          le_antisymm (h0 ▸ hτ₂.1) (Subtype.mk_le_mk.mpr (unitInterval.nonneg _))
        have hsi1 : s (i + 1) = 1 :=
          le_antisymm (Subtype.mk_le_mk.mpr (unitInterval.le_one _)) (h1 ▸ hτ₁.2)
        exact h_not_01 ⟨hsi0, hsi1⟩
    have hline : IsLineWithEnds (Abar i) (v i) (v (i + 1)) := by
      rw [hAbar_def, hv_def, hv_def]
      exact isLineWithEnds_image_Icc_of_injOn hgc (hs_lt i hi) hinj_Icc
    exact ⟨isSolid_of_isLineWithEnds hS hline, isConnected_of_isLineWithEnds hline⟩

private theorem short_return_arc_for_subdivision
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    {F₀ : Set S}
    (hF₀_oarc : IsOArc F₀)
    {t : ℕ}
    [T2Space S]
    (r : ℕ)
    (v : ℕ → S)
    (u : ℕ → S)
    (P : ℕ → Set S)
    (hP_props : ∀ i ≤ r, u i ∈ F₀ ∧ IsLineWithEnds (P i) (v i) (u i) ∧ G.IsNormal (P i) ∧ (G.V ∩ P
      i).ncard ≤ t + 1) :
    ∀ i : ℕ, ∃ B : Set S, i < r →
      (u i = u (i + 1) ∧ B = ∅ ∨
        u i ≠ u (i + 1) ∧ B ∈ componentsIn (F₀ \ {u i, u (i + 1)}) ∧
          IsLineWithEnds (B ∪ {u i, u (i + 1)}) (u i) (u (i + 1))) ∧
      B ⊆ F₀ ∧ 2 * (G.V ∩ B).ncard ≤ (G.V ∩ F₀).ncard := by
  intro i
  by_cases hi : i < r
  · by_cases hueq : u i = u (i + 1)
    · exact ⟨∅, fun _ => ⟨Or.inl ⟨hueq, rfl⟩, empty_subset _, by simp⟩⟩
    · obtain ⟨B, hB_comp, hB_sub, hB_card, hB_line⟩ :=
        exists_short_component_oArc_diff_pair hF₀_oarc G.finite_V
          (hP_props i hi.le).1 (hP_props (i + 1) hi).1 hueq
      exact ⟨B, fun _ => ⟨Or.inr ⟨hueq, hB_comp, hB_line⟩, hB_sub, hB_card⟩⟩
  · exact ⟨∅, fun h => False.elim (hi h)⟩

private theorem subdivision_cycle_planar_in_cap
    {S : Type u}
    [TopologicalSpace S]
    (hS : IsSurface S)
    [ConnectedSpace S]
    (hnot_small : ∀ c ≤ 2, IsEmpty (S ≃ₜ SurfaceModel 0 0 c))
    {G : Drawing S}
    {C : Set S}
    {F₀ : Set S}
    (hC : C ∈ cuffs S)
    (hF₀_oarc : IsOArc F₀)
    (hF₀_norm : G.IsNormal F₀)
    (hF₀_surr : SurroundsCuff F₀ C)
    {t : ℕ}
    (ht_low : (G.V ∩ F₀).ncard ≤ t)
    (ht_high : 9 * (t + 1) ≤ 2 * alpha G)
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (D : Set S')
    (hCap : IsCappedCuff C S' j D)
    (F : Set S)
    (hF_norm : G.IsNormal F)
    (g : ↑I → S)
    (hg_mem : ∀ (s : ↑I), g s ∈ F)
    (r : ℕ)
    (s : ℕ → ↑I)
    (hs_disj_V : ∀ i < r, ∀ τ ∈ Ioo (s i) (s (i + 1)), g τ ∉ G.V)
    (v : ℕ → S)
    (u : ℕ → S)
    (P : ℕ → Set S)
    (hP_wrap : P 0 = P r ∧ u 0 = u r)
    (hP_props : ∀ i ≤ r, u i ∈ F₀ ∧ IsLineWithEnds (P i) (v i) (u i) ∧ G.IsNormal (P i) ∧ (G.V ∩ P
      i).ncard ≤ t + 1)
    (A : ℕ → Set S)
    (hA_def : ∀ (i : ℕ), A i = g '' Ioo (s i) (s (i + 1)))
    (Abar : ℕ → Set S)
    (hAbar_eq : ∀ i < r, Abar i = A i ∪ {v i, v (i + 1)})
    (hAbar_sol_conn : ∀ i < r, IsSolid (Abar i) ∧ IsConnected (Abar i))
    (B : ℕ → Set S)
    (hB_props : ∀ i < r, (u i = u (i + 1) ∧ B i = ∅ ∨ u i ≠ u (i + 1) ∧ B i ∈ componentsIn (F₀ \
      {u i, u (i + 1)}) ∧ IsLineWithEnds (B i ∪ {u i, u (i + 1)}) (u i) (u (i + 1))) ∧ B i ⊆ F₀ ∧
      2 * (G.V ∩ B i).ncard ≤ (G.V ∩ F₀).ncard) :
    ∀ i < r, IsPlanar (j '' (P i ∪ P (i + 1) ∪ A i ∪ B i)) := by
  intro i hi
  obtain ⟨Ci, hCi_def⟩ : ∃ Ci : Set S, Ci = P i ∪ P (i + 1) ∪ A i ∪ B i := ⟨_, rfl⟩
  rw [← hCi_def]
  have hPi := hP_props i hi.le
  have hPi1 := hP_props (i + 1) hi
  have hBi := hB_props i hi
  have hCi_3 : P i ∪ P (i + 1) ∪ A i = P i ∪ P (i + 1) ∪ Abar i := by
    rw [hAbar_eq i hi]
    ext z
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ((h1 | h2) | h3)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr (Or.inl h3)
    · rintro ((h1 | h2) | (h3 | (rfl | rfl)))
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr h3
      · exact Or.inl (Or.inl (left_mem_of_isLineWithEnds hPi.2.1))
      · exact Or.inl (Or.inr (left_mem_of_isLineWithEnds hPi1.2.1))
  have h3_sol : IsSolid (P i ∪ P (i + 1) ∪ A i) := by
    rw [hCi_3]
    exact theorem_11_6_proof hS
      (theorem_11_6_proof hS (isSolid_of_isLineWithEnds hS hPi.2.1)
        (isSolid_of_isLineWithEnds hS hPi1.2.1))
      (hAbar_sol_conn i hi).1
  have h3_conn : IsConnected (P i ∪ P (i + 1) ∪ A i) := by
    rw [hCi_3]
    have h_PA : IsConnected (P i ∪ Abar i) := by
      refine ⟨⟨v i, Or.inl (left_mem_of_isLineWithEnds hPi.2.1)⟩,
        (isConnected_of_isLineWithEnds hPi.2.1).2.union' ⟨v i, left_mem_of_isLineWithEnds
          hPi.2.1, ?_⟩ (hAbar_sol_conn i hi).2.2⟩
      rw [hAbar_eq i hi]
      exact Or.inr (Or.inl rfl)
    have h_eq_ord : P i ∪ P (i + 1) ∪ Abar i = (P i ∪ Abar i) ∪ P (i + 1) := by
      ext z
      simp only [mem_union]
      tauto
    rw [h_eq_ord]
    refine ⟨⟨v (i + 1), Or.inr (left_mem_of_isLineWithEnds hPi1.2.1)⟩,
      h_PA.2.union' ⟨v (i + 1), Or.inr ?_, left_mem_of_isLineWithEnds hPi1.2.1⟩
        (isConnected_of_isLineWithEnds hPi1.2.1).2⟩
    rw [hAbar_eq i hi]
    exact Or.inr (Or.inr rfl)
  have hCi_sol_conn : IsSolid Ci ∧ IsConnected Ci := by
    rcases hBi.1 with ⟨_, hB_emp⟩ | ⟨_, _, hB_line⟩
    · rw [hCi_def, hB_emp, union_empty]
      exact ⟨h3_sol, h3_conn⟩
    · have hCi_4 : Ci = (P i ∪ P (i + 1) ∪ A i) ∪ (B i ∪ {u i, u (i + 1)}) := by
        rw [hCi_def]
        ext z
        simp only [mem_union, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro (((h1 | h2) | h3) | h4)
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inl (Or.inr h2))
          · exact Or.inl (Or.inr h3)
          · exact Or.inr (Or.inl h4)
        · rintro (((h1 | h2) | h3) | (h4 | (rfl | rfl)))
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inl (Or.inr h2))
          · exact Or.inl (Or.inr h3)
          · exact Or.inr h4
          · exact Or.inl (Or.inl (Or.inl (right_mem_of_isLineWithEnds hPi.2.1)))
          · exact Or.inl (Or.inl (Or.inr (right_mem_of_isLineWithEnds hPi1.2.1)))
      rw [hCi_4]
      refine ⟨theorem_11_6_proof hS h3_sol (isSolid_of_isLineWithEnds hS hB_line),
        ⟨⟨u i, Or.inl (Or.inl (Or.inl (right_mem_of_isLineWithEnds hPi.2.1)))⟩,
          h3_conn.2.union' ⟨u i, Or.inl (Or.inl (right_mem_of_isLineWithEnds hPi.2.1)), Or.inr
            (Or.inl rfl)⟩
            (isConnected_of_isLineWithEnds hB_line).2⟩⟩
  have hCi_norm : G.IsNormal Ci := by
    rw [hCi_def, hA_def]
    rintro z ⟨((hz1 | hz2) | ⟨τ, _, rfl⟩) | hz4, hzU⟩
    · exact hPi.2.2.1 ⟨hz1, hzU⟩
    · exact hPi1.2.2.1 ⟨hz2, hzU⟩
    · exact hF_norm ⟨hg_mem τ, hzU⟩
    · exact hF₀_norm ⟨hBi.2.1 hz4, hzU⟩
  have hCi_V_sub : G.V ∩ Ci ⊆ (G.V ∩ P i) ∪ (G.V ∩ P (i + 1)) ∪ (G.V ∩ B i) := by
    rw [hCi_def, hA_def]
    rintro z ⟨hzV, ((hz1 | hz2) | ⟨τ, hτ, rfl⟩) | hz4⟩
    · exact Or.inl (Or.inl ⟨hzV, hz1⟩)
    · exact Or.inl (Or.inr ⟨hzV, hz2⟩)
    · exact False.elim (hs_disj_V i hi τ hτ hzV)
    · exact Or.inr ⟨hzV, hz4⟩
  have hB_card : (G.V ∩ B i).ncard ≤ t / 2 := by
    have h2 : 2 * (G.V ∩ B i).ncard ≤ t := hBi.2.2.trans ht_low
    omega
  let m_bound : ℕ := 2 * t + t / 2 + 2
  have hCi_card : (G.V ∩ Ci).ncard ≤ m_bound := by
    calc (G.V ∩ Ci).ncard
      _ ≤ ((G.V ∩ P i) ∪ (G.V ∩ P (i + 1)) ∪ (G.V ∩ B i)).ncard :=
        ncard_le_ncard hCi_V_sub
          (((G.finite_V.inter_of_left _).union (G.finite_V.inter_of_left _)).union
            (G.finite_V.inter_of_left _))
      _ ≤ ((G.V ∩ P i) ∪ (G.V ∩ P (i + 1))).ncard + (G.V ∩ B i).ncard := ncard_union_le _ _
      _ ≤ (G.V ∩ P i).ncard + (G.V ∩ P (i + 1)).ncard + (G.V ∩ B i).ncard :=
        Nat.add_le_add_right (ncard_union_le _ _) _
      _ ≤ (t + 1) + (t + 1) + t / 2 :=
        Nat.add_le_add (Nat.add_le_add hPi.2.2.2 hPi1.2.2.2) hB_card
      _ = m_bound := by omega
  have hCi_np : IsNearPlanar Ci := by
    by_contra hnot_np
    have hcand : IsAlphaCandidate G Ci := ⟨hCi_sol_conn.1, hCi_sol_conn.2, hCi_norm, hnot_np⟩
    have h_le_alpha : alpha G ≤ (Ci ∩ G.V).ncard := Nat.sInf_le ⟨Ci, hcand, rfl⟩
    rw [inter_comm Ci G.V] at h_le_alpha
    omega
  have hCi_capped : IsPlanarInCappedCuff C Ci := by
    by_cases hpl : IsPlanar Ci
    · exact isPlanarInCappedCuff_of_isPlanar hS hC hpl
    · rcases hCi_np with hpl' | ⟨C', hC', hplC'⟩
      · exact False.elim (hpl hpl')
      · rcases eq_or_ne C' C with rfl | hC'C
        · exact hplC'
        · exfalso
          have hnot_cyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) := by
            rintro ⟨e⟩
            exact (hnot_small 2 le_rfl).false e
          have h_empty := theorem_5_3_proof hS hnot_cyl G hC' hC hC'C (r := m_bound) (r' := t)
            (by omega)
          have hui_C' : u i ∈ scriptA G m_bound C' := by
            refine mem_sUnion.mpr ⟨Ci, ⟨hCi_sol_conn.1, hCi_sol_conn.2, hCi_norm,
              ⟨hC', hplC', hpl⟩, hCi_card⟩, ?_⟩
            rw [hCi_def]
            exact Or.inl (Or.inl (Or.inl (right_mem_of_isLineWithEnds hPi.2.1)))
          have hui_C : u i ∈ scriptA G t C := by
            refine mem_sUnion.mpr ⟨F₀, ⟨isSolid_of_isOArc hS hF₀_oarc,
              isConnected_of_isOArc hF₀_oarc, hF₀_norm,
              hF₀_surr, ht_low⟩, hPi.1⟩
          have hui_inter : u i ∈ scriptA G m_bound C' ∩ scriptA G t C := ⟨hui_C', hui_C⟩
          rw [h_empty] at hui_inter
          exact hui_inter
  exact hCi_capped.2.2 S' j D hCap

/-- Graph Minors VII, (5.6) (page 232):
"Let $\Sigma$ be a connected surface such that $\Sigma \not\cong \Sigma(0, 0, c)(c = 0, 1,
2)$, and let $G$ be a proper graph in $\Sigma$. Let $C$ be a cuff of $\Sigma$, and let $F_0$
be a $G$-normal $O$-arc surrounding $C$. Let $t$ be an integer with* $$ |V(G) \cap F_0| \le
t \le \frac{2}{9}\alpha(G) - 1. $$ *Then $Y_t(F_0)$ is planar in $\Sigma + \hat{C}$." -/
theorem theorem_5_6_proof
    (hS : IsSurface S) [ConnectedSpace S]
    (hnot_small : ∀ c ≤ 2, IsEmpty (S ≃ₜ SurfaceModel 0 0 c))
    {G : Drawing S} (hG : G.IsProper)
    {C F₀ : Set S} (hC : C ∈ cuffs S)
    (hF₀_oarc : IsOArc F₀) (hF₀_norm : G.IsNormal F₀) (hF₀_surr : SurroundsCuff F₀ C)
    {t : ℕ} (ht_low : (G.V ∩ F₀).ncard ≤ t) (ht_high : 9 * (t + 1) ≤ 2 * alpha G) :
    IsPlanarInCappedCuff C (nearSet G t F₀) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  let Z : Set S := closure (nearSet G t F₀)
  let ℛ : Set (Set S) := {r ∈ G.R | r ⊆ nearSet G t F₀}
  have hZ : Z = closure (⋃₀ ℛ) := closure_nearSet_eq_closure_sUnion_regions hS hG hF₀_norm t
  suffices hZ_pl : IsPlanarInCappedCuff C Z from hZ_pl.mono subset_closure
  have h_all : ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
      IsCappedCuff C S' j D → IsPlanar (j '' Z) := by
    intro S' _ j D hCap
    rw [theorem_5_5_cappedCuff hS hG (sep_subset _ _) hZ hCap]
    intro F hFZ hF_norm hF_oarc
    obtain ⟨φ⟩ := id hF_oarc
    obtain ⟨g, hg_def⟩ : ∃ g : I → S, ∀ s : I, g s = (φ (arcParam 1 s)).1 := ⟨_, fun _ => rfl⟩
    have hgc : Continuous g := by
      have : g = fun s => (φ (arcParam 1 s)).1 := funext hg_def
      rw [this]
      exact continuous_subtype_val.comp (φ.continuous.comp (arcParam 1).continuous)
    have hg01 : g 0 = g 1 := by simp [hg_def]
    have hg_mem : ∀ s : I, g s ∈ F := fun s => hg_def s ▸ (φ (arcParam 1 s)).2
    have hg_inj_Ico : InjOn g (Ico 0 1) := by
      intro s₁ hs₁ s₂ hs₂ heq
      rw [hg_def, hg_def] at heq
      have hφ_eq : φ (arcParam 1 s₁) = φ (arcParam 1 s₂) := Subtype.ext heq
      rcases arcParam_eq_iff 1 (φ.injective hφ_eq) with h | ⟨_, h1⟩ | ⟨h1, _⟩
      · exact h
      · exact False.elim (ne_of_lt hs₂.2 h1)
      · exact False.elim (ne_of_lt hs₁.2 h1)
    obtain ⟨r, hr, s, hs0, hsr, hs_lt, hs_disj_V⟩ :=
      exists_partition_of_oArc G.finite_V hg_inj_Ico
    have hs_mono : ∀ i < r, s i ≤ s (i + 1) := fun i hi => (hs_lt i hi).le
    obtain ⟨v, hv_def⟩ : ∃ v : ℕ → S, ∀ i, v i = g (s i) := ⟨_, fun _ => rfl⟩
    have hv_eq : ∀ i ≤ r, v i = (φ (arcParam 1 (s i))).1 := fun i _ => by rw [hv_def, hg_def]
    have hv0r : v 0 = v r := by rw [hv_def, hv_def, hs0, hsr, hg01]
    have hex_uP : ∀ i : ℕ, ∃ (u : S) (P : Set S), u ∈ F₀ ∧ IsLineWithEnds P (v i) u ∧
        G.IsNormal P ∧ (G.V ∩ P).ncard ≤ t + 1 := by
      intro i
      have hvi_F : v i ∈ F := hv_def i ▸ hg_mem (s i)
      exact exists_normal_arc_to_F0 hS hG hF₀_oarc hF₀_norm (hFZ hvi_F)
        (fun ⟨hU, hV⟩ => hV (hF_norm ⟨hvi_F, hU⟩))
    choose u₀ P₀ hu₀_F₀ hP₀_line hP₀_norm hP₀_card using hex_uP
    obtain ⟨u, P, hP_wrap, hP_props⟩ : ∃ (u : ℕ → S) (P : ℕ → Set S),
        (P 0 = P r ∧ u 0 = u r) ∧
        (∀ i ≤ r, u i ∈ F₀ ∧ IsLineWithEnds (P i) (v i) (u i) ∧
          G.IsNormal (P i) ∧ (G.V ∩ P i).ncard ≤ t + 1) := by
      refine ⟨fun i => if i = r then u₀ 0 else u₀ i,
        fun i => if i = r then P₀ 0 else P₀ i, ?_, ?_⟩
      · dsimp only
        have h0r : (0 : ℕ) ≠ r := ne_of_lt hr
        simp [h0r]
      · intro i hi
        dsimp only
        split_ifs with h
        · subst h
          exact ⟨hu₀_F₀ 0, hv0r ▸ hP₀_line 0, hP₀_norm 0, hP₀_card 0⟩
        · exact ⟨hu₀_F₀ i, hP₀_line i, hP₀_norm i, hP₀_card i⟩
    obtain ⟨A, hA_def⟩ : ∃ A : ℕ → Set S, ∀ i, A i = g '' Ioo (s i) (s (i + 1)) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨Abar, hAbar_def⟩ : ∃ Abar : ℕ → Set S, ∀ i, Abar i = g '' Icc (s i) (s (i + 1)) :=
      ⟨_, fun _ => rfl⟩
    have hAbar_eq : ∀ i < r, Abar i = A i ∪ {v i, v (i + 1)} := by
      intro i hi
      rw [hAbar_def, hA_def, hv_def, hv_def]
      ext z
      constructor
      · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact Or.inr (Or.inl rfl)
        · rcases eq_or_lt_of_le h2 with rfl | h2'
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl ⟨τ, ⟨h1', h2'⟩, rfl⟩
      · rintro (⟨τ, ⟨h1, h2⟩, rfl⟩ | (rfl | hz))
        · exact ⟨τ, ⟨h1.le, h2.le⟩, rfl⟩
        · exact ⟨s i, ⟨le_rfl, (hs_lt i hi).le⟩, rfl⟩
        · rw [mem_singleton_iff.mp hz]
          exact ⟨s (i + 1), ⟨(hs_lt i hi).le, le_rfl⟩, rfl⟩
    have hAbar_sol_conn : ∀ i < r, IsSolid (Abar i) ∧ IsConnected (Abar i) := by
      exact closed_arc_segment_solid_connected (S := S) hS F hF_oarc
        φ g hg_def hgc hg_mem r hr s hs0 hsr hs_lt v hv_def Abar hAbar_def
    have hex_B : ∀ i : ℕ, ∃ B : Set S,
        i < r →
          (((u i = u (i + 1) ∧ B = ∅) ∨
            (u i ≠ u (i + 1) ∧ B ∈ componentsIn (F₀ \ {u i, u (i + 1)}) ∧
              IsLineWithEnds (B ∪ {u i, u (i + 1)}) (u i) (u (i + 1)))) ∧
          B ⊆ F₀ ∧ 2 * (G.V ∩ B).ncard ≤ (G.V ∩ F₀).ncard) := by
      exact short_return_arc_for_subdivision (S := S) (G := G) (F₀ := F₀) hF₀_oarc (t := t) r v u
        P hP_props
    choose B hB_props using hex_B
    -- Prove each C_i = P i ∪ P (i + 1) ∪ A i ∪ B i is planar in Σ + Ĉ
    have hCi_planar : ∀ i < r, IsPlanar (j '' (P i ∪ P (i + 1) ∪ A i ∪ B i)) := by
      exact subdivision_cycle_planar_in_cap (S := S) hS hnot_small (G := G) (C := C) (F₀ := F₀) hC
        hF₀_oarc hF₀_norm hF₀_surr (t := t) ht_low ht_high S' j D hCap F hF_norm g hg_mem r s
        hs_disj_V v u P hP_wrap hP_props A hA_def Abar hAbar_eq hAbar_sol_conn B hB_props
    -- Apply (5.4) in S'
    have hS' : IsSurface S' := hCap.isSurface
    have : T2Space S' := hS'.2.1
    have hj_emb : IsEmbedding j := hCap.isEmbedding
    have hjF_oarc : IsOArc (j '' F) :=
      isOArc_image hF_oarc hj_emb.continuous.continuousOn hj_emb.injective.injOn
    have hjF₀_oarc : IsOArc (j '' F₀) :=
      isOArc_image hF₀_oarc hj_emb.continuous.continuousOn hj_emb.injective.injOn
    have hjF₀_null : IsNullHomotopicOArc (j '' F₀) :=
      (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hjF₀_oarc).mp
        (hF₀_surr.2.1.2.2 S' j D hCap)
    have hrange_jF : range (j ∘ (Subtype.val : F → S)) = j '' F := by
      ext y
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩,
        by rintro ⟨x, hxF, rfl⟩; exact ⟨⟨x, hxF⟩, rfl⟩⟩
    let jF_homeo : F ≃ₜ j '' F :=
      (hj_emb.comp IsEmbedding.subtypeVal).toHomeomorph.trans (Homeomorph.setCongr hrange_jF)
    let φ' : Circle ≃ₜ j '' F := φ.trans jF_homeo
    let v' : ℕ → S' := fun i => j (v i)
    let u' : ℕ → S' := fun i => j (u i)
    let A' : ℕ → Set S' := fun i => j '' A i
    let P' : ℕ → Set S' := fun i => j '' P i
    let B' : ℕ → Set S' := fun i => j '' B i
    refine theorem_5_4_proof hS' hjF_oarc hjF₀_oarc hjF₀_null hr φ' s hs0 hsr hs_mono v' u' A' P' B'
      (fun i hi => by
        change j (v i) = j (φ (arcParam 1 (s i))).1
        exact congrArg j (hv_eq i hi))
      (fun i hi => ?_)
      (fun i hi => ⟨image_of_isLineWithEnds hj_emb (hP_props i hi).2.1,
        mem_image_of_mem j (hP_props i hi).1⟩)
      ⟨congrArg (j '' ·) hP_wrap.1, congrArg j hP_wrap.2⟩
      (fun i hi => ?_)
      (fun i hi => ?_)
    · dsimp only [A']
      rw [hA_def]
      refine ⟨?_, image_mono (by rintro _ ⟨τ, _, rfl⟩; exact hg_mem τ)⟩
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨g τ, ⟨τ, hτ, rfl⟩, ?_⟩
      change j (g τ) = j (φ (arcParam 1 τ)).1
      exact congrArg j (hg_def τ)
    · rcases (hB_props i hi).1 with ⟨hueq, hBemp⟩ | ⟨hune, hBcomp, _⟩
      · exact Or.inl ⟨congrArg j hueq, by simp [B', hBemp]⟩
      · refine Or.inr ⟨fun h => hune (hj_emb.injective h), ?_⟩
        have h_diff_eq : j '' F₀ \ {u' i, u' (i + 1)} = j '' (F₀ \ {u i, u (i + 1)}) := by
          ext y
          constructor
          · rintro ⟨⟨x, hxF₀, rfl⟩, hy_end⟩
            refine ⟨x, ⟨hxF₀, ?_⟩, rfl⟩
            rintro (rfl | h)
            · exact hy_end (Or.inl rfl)
            · exact hy_end (Or.inr (mem_singleton_iff.mpr (congrArg j (mem_singleton_iff.mp h))))
          · rintro ⟨x, ⟨hxF₀, hx_end⟩, rfl⟩
            refine ⟨⟨x, hxF₀, rfl⟩, ?_⟩
            rintro (h | h)
            · exact hx_end (Or.inl (hj_emb.injective h))
            · exact hx_end (Or.inr (mem_singleton_iff.mpr (hj_emb.injective
                (mem_singleton_iff.mp h))))
        rw [h_diff_eq]
        exact image_mem_componentsIn_of_isEmbedding hj_emb hBcomp
    · have heq_img : P' i ∪ P' (i + 1) ∪ A' i ∪ B' i = j '' (P i ∪ P (i + 1) ∪ A i ∪ B i) := by
        simp only [P', A', B', image_union]
      rw [heq_img]
      exact hCi_planar i hi
  obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC)
  have : Nonempty S := ⟨c₀⟩
  obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C hS hC
  have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
  exact ⟨hC, ⟨S', topS', j, D, hCap, h_all S' j D hCap⟩, h_all⟩

/-! ## 5. Proof of (5.7) -/

/-- If `F ⊆ S` is a `G`-normal set with `(G.V ∩ F).ncard ≤ r`, then `F ⊆ nearSet G r F`. -/
theorem subset_nearSet_of_isNormal {G : Drawing S} {F : Set S} (hF_norm : G.IsNormal F)
    {r : ℕ} (hr : (G.V ∩ F).ncard ≤ r) :
    F ⊆ nearSet G r F := by
  intro y hyF
  refine ⟨y, hyF, ?_⟩
  by_cases hyU : y ∈ G.U
  · have hyV : y ∈ G.V ∩ F := ⟨hF_norm ⟨hyF, hyU⟩, hyF⟩
    have h1 : 1 ≤ (G.V ∩ F).ncard := by
      have hsub : ({y} : Set S) ⊆ G.V ∩ F := singleton_subset_iff.mpr hyV
      simpa using ncard_le_ncard hsub (G.finite_V.inter_of_left F)
    have hdyy : distPoint G y y = 1 := by simp [distPoint, hyU]
    omega
  · have hdyy : distPoint G y y = 0 := by simp [distPoint, hyU]
    omega

/-- In any capped cuff `(S', j, D)` of `C`, an `O`-arc `F` surrounding `C` bounds a closed disc
`Δ ⊆ S'` with `discBd Δ = j '' F` and `discInt D ⊆ discInt Δ`. -/
theorem surroundsCuff_bounds_disc_containing_cap
    (hS : IsSurface S) [ConnectedSpace S]
    {C F : Set S} (hF : IsOArc F) (hFC : SurroundsCuff F C)
    {S' : Type u} [TopologicalSpace S'] {j : S → S'} {D : Set S'}
    (hCap : IsCappedCuff C S' j D) :
    ∃ Δ : Set S', IsClosedDisc Δ ∧ discBd Δ = j '' F ∧ discInt D ⊆ discInt Δ := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hS' : IsSurface S' := hCap.isSurface
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := hCap.connectedSpace hS
  have hj : IsEmbedding j := hCap.isEmbedding
  have hD : IsClosedDisc D := hCap.isClosedDisc
  have hbdD : discBd D = j '' C := hCap.discBd_eq
  have hmeet : range j ∩ D = j '' C := hCap.inter_eq
  have hcov : range j ∪ D = univ := hCap.union_eq
  have hjF_oarc : IsOArc (j '' F) :=
    isOArc_image hF hj.continuous.continuousOn hj.injective.injOn
  have hjF_pl : IsPlanar (j '' F) := hFC.2.1.2.2 S' j D hCap
  have hjF_null : IsNullHomotopicOArc (j '' F) :=
    (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hjF_oarc).mp hjF_pl
  obtain ⟨Δ, hΔ_disc, hΔ_bd⟩ := nullHomotopicOArc_bounds_disc hS' hjF_oarc hjF_null
  have hdisj_int : Disjoint (discInt D) (discBd Δ) := by
    rw [hΔ_bd]
    refine disjoint_left.mpr ?_
    rintro _ ⟨hxD, hxbd⟩ ⟨x, _, rfl⟩
    have : j x ∈ range j ∩ D := ⟨mem_range_self x, hxD⟩
    rw [hmeet, ← hbdD] at this
    exact hxbd this
  have h_int_sub : discInt D ⊆ discInt Δ := by
    rcases hΔ_disc.side hS'.2.2 hD.isPreconnected_discInt hdisj_int with hsub | hdisj
    · exact hsub
    · exfalso
      have hΔ_range : Δ ⊆ range j := by
        intro y hy
        rcases (hcov ▸ mem_univ y : y ∈ range j ∪ D) with hy_r | hy_D
        · exact hy_r
        · by_cases hy_bd : y ∈ discBd D
          · rw [hbdD, ← hmeet] at hy_bd
            exact hy_bd.1
          · exact (disjoint_right.mp hdisj hy ⟨hy_D, hy_bd⟩).elim
      obtain ⟨φΔ⟩ := id hΔ_disc
      have hpre_disc : IsClosedDisc (j ⁻¹' Δ) := by
        refine ⟨Homeomorph.trans φΔ ?_⟩
        have h_inv_cont : Continuous (fun x : (j ⁻¹' Δ : Set S) => (⟨j x.1, x.2⟩ : Δ)) :=
          Continuous.subtype_mk (hj.continuous.comp continuous_subtype_val) _
        have : CompactSpace (j ⁻¹' Δ : Set S) :=
          isCompact_iff_compactSpace.mp (hΔ_disc.isCompact.isClosed.preimage
            hj.continuous).isCompact
        exact (h_inv_cont.homeoOfEquivCompactToT2 (f := {
          toFun := fun x => ⟨j x.1, x.2⟩
          invFun := fun z => ⟨Classical.choose (hΔ_range z.2), by
            have hspec := Classical.choose_spec (hΔ_range z.2)
            simp [hspec]⟩
          left_inv := fun x => Subtype.ext (hj.injective
            (Classical.choose_spec (hΔ_range x.2)))
          right_inv := fun z => Subtype.ext (Classical.choose_spec (hΔ_range z.2)) })).symm
      have hF_sub : F ⊆ j ⁻¹' Δ := by
        intro x hx
        have : j x ∈ discBd Δ := hΔ_bd ▸ mem_image_of_mem j hx
        exact Surface.discBd_subset Δ this
      exact hFC.2.2 ⟨j ⁻¹' Δ, hpre_disc, hF_sub⟩
  exact ⟨Δ, hΔ_disc, hΔ_bd, h_int_sub⟩

/-- Pulling back a `[0, 1]`-arc along an embedding `j : S → T` when the arc lies in `range j`. -/
theorem pull_of_isLineWithEnds [T2Space S] {T : Type*} [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {L : Set T} {a b : S}
    (hL : IsLineWithEnds L (j a) (j b)) (hsub : L ⊆ range j) :
    IsLineWithEnds (j ⁻¹' L) a b ∧ j '' (j ⁻¹' L) = L := by
  have himg : j '' (j ⁻¹' L) = L := image_preimage_eq_of_subset hsub
  obtain ⟨e, he0, he1⟩ := id hL
  have hex : ∀ t : I, ∃ x ∈ j ⁻¹' L, j x = (e t).1 := by
    intro t
    obtain ⟨x, hx⟩ := hsub (e t).2
    exact ⟨x, by change j x ∈ L; rw [hx]; exact (e t).2, hx⟩
  choose f hf_mem hf_eq using hex
  have hfc : Continuous f := hj.continuous_iff.mpr (by
    have : j ∘ f = Subtype.val ∘ e := funext hf_eq
    rw [this]
    exact continuous_subtype_val.comp e.continuous)
  have hfinj : Function.Injective f := fun t₁ t₂ h => by
    have : (e t₁).1 = (e t₂).1 := by rw [← hf_eq t₁, ← hf_eq t₂, h]
    exact e.injective (Subtype.ext this)
  have hrange : range f = j ⁻¹' L := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact hf_mem t
    · intro hx
      let t := e.symm ⟨j x, hx⟩
      refine ⟨t, hj.injective ?_⟩
      rw [hf_eq t]
      simp [t]
  have hemb : IsEmbedding f := (hfc.isClosedEmbedding hfinj).isEmbedding
  refine ⟨?_, himg⟩
  rw [← hrange]
  refine ⟨hemb.toHomeomorph, ?_, ?_⟩
  · exact hj.injective (by change j (f 0) = j a; rw [hf_eq 0, he0])
  · exact hj.injective (by change j (f 1) = j b; rw [hf_eq 1, he1])

/-- If `Δ, Δ'` are closed discs in a surface `S'` with `Δ ⊆ discInt Δ'`, then there is a `[0,
1]`-arc
`Q₁ ⊆ Δ'` with one end `p ∈ discBd Δ'` and the other end `q ∈ discBd Δ` such that
`Q₁ \ {p} ⊆ discInt Δ'` and `Q₁ \ {q} ⊆ Δ' \ Δ`. -/
theorem exists_subarc_in_annulus {S' : Type u} [TopologicalSpace S'] (hS' : IsSurface S')
    {Δ Δ' : Set S'} (hΔ : IsClosedDisc Δ) (hΔ' : IsClosedDisc Δ')
    (hsub : Δ ⊆ discInt Δ') :
    ∃ (Q₁ : Set S') (p q : S'),
      p ∈ discBd Δ' ∧ q ∈ discBd Δ ∧ IsLineWithEnds Q₁ p q ∧
      Q₁ ⊆ Δ' \ discInt Δ ∧ Q₁ \ {p, q} ⊆ discInt Δ' \ Δ := by
  have : T2Space S' := hS'.2.1
  obtain ⟨z₀, hz₀_bd⟩ := isOArc_nonempty hΔ'.isOArc_discBd
  obtain ⟨y₀, hy₀_bd⟩ := isOArc_nonempty hΔ.isOArc_discBd
  have hz₀_Δ' : z₀ ∈ Δ' := Surface.discBd_subset Δ' hz₀_bd
  have hy₀_Δ : y₀ ∈ Δ := Surface.discBd_subset Δ hy₀_bd
  have hy₀_Δ' : y₀ ∈ Δ' := (hsub hy₀_Δ).1
  have hz₀_not_Δ : z₀ ∉ Δ := fun h => (hsub h).2 hz₀_bd
  have hne_zy : z₀ ≠ y₀ := fun h => hz₀_not_Δ (h ▸ hy₀_Δ)
  have hjoined : JoinedIn Δ' z₀ y₀ := hΔ'.isPathConnected.joinedIn z₀ hz₀_Δ' y₀ hy₀_Δ'
  obtain ⟨P₀, hP₀_sub, e, he0, he1⟩ :=
    ((joinedIn_iff_eq_or_exists_isLineWithEnds hz₀_Δ' hy₀_Δ').mp hjoined).resolve_left hne_zy
  let γ : I → S' := fun t => (e t).1
  have hγc : Continuous γ := continuous_subtype_val.comp e.continuous
  have hγ_inj : Function.Injective γ := Subtype.val_injective.comp e.injective
  have hγ_mem : ∀ t : I, γ t ∈ Δ' := fun t => hP₀_sub (e t).2
  have hγ0 : γ 0 = z₀ := he0
  have hγ1 : γ 1 = y₀ := he1
  let K₁ : Set I := γ ⁻¹' Δ
  have hK₁_closed : IsClosed K₁ := hΔ.isCompact.isClosed.preimage hγc
  have hK₁_ne : K₁.Nonempty := ⟨1, by change γ 1 ∈ Δ; rw [hγ1]; exact hy₀_Δ⟩
  let t₁ : I := sInf K₁
  have ht₁_mem : t₁ ∈ K₁ := hK₁_closed.csInf_mem hK₁_ne (OrderBot.bddBelow K₁)
  have hγt₁_Δ : γ t₁ ∈ Δ := ht₁_mem
  have ht₁_lt_not_Δ : ∀ t : I, t < t₁ → γ t ∉ Δ :=
    fun t hlt ht => not_lt_of_ge (csInf_le (OrderBot.bddBelow K₁) ht) hlt
  have ht₁_pos : (0 : I) < t₁ := by
    rcases eq_or_lt_of_le (show (0 : I) ≤ t₁ from Subtype.mk_le_mk.mpr
      (unitInterval.nonneg t₁)) with h0 | hlt
    · exfalso
      have : γ 0 ∈ Δ := h0.symm ▸ hγt₁_Δ
      rw [hγ0] at this
      exact hz₀_not_Δ this
    · exact hlt
  have hγt₁_not_int : γ t₁ ∉ discInt Δ := by
    intro hint
    have hU_open : IsOpen (γ ⁻¹' discInt Δ) := (hΔ.isOpen_discInt hS'.2.2).preimage hγc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open t₁ hint
    have ht₁_r : 0 < (t₁ : ℝ) := ht₁_pos
    let δ : ℝ := min ((t₁ : ℝ) / 2) (ε / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_le : δ ≤ (t₁ : ℝ) / 2 := min_le_left _ _
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    let t' : I := ⟨(t₁ : ℝ) - δ, by linarith, by linarith [unitInterval.le_one t₁]⟩
    have ht'_lt : t' < t₁ := show (t' : ℝ) < (t₁ : ℝ) from by dsimp [t']; linarith
    have ht'_ball : t' ∈ Metric.ball t₁ ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have : |(t₁ : ℝ) - δ - (t₁ : ℝ)| = δ := by
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ_pos]
      linarith
    exact ht₁_lt_not_Δ t' ht'_lt (discInt_subset Δ (hball ht'_ball))
  have hγt₁_bd : γ t₁ ∈ discBd Δ := by
    by_contra hnot_bd
    exact hγt₁_not_int ⟨hγt₁_Δ, hnot_bd⟩
  let K₀ : Set I := γ ⁻¹' discBd Δ' ∩ Icc 0 t₁
  have hbdΔ'_closed : IsClosed (discBd Δ') := hΔ'.isOArc_discBd.isCompact.isClosed
  have hK₀_closed : IsClosed K₀ := (hbdΔ'_closed.preimage hγc).inter isClosed_Icc
  have hK₀_ne : K₀.Nonempty :=
    ⟨0, by change γ 0 ∈ discBd Δ'; rw [hγ0]; exact hz₀_bd,
      le_rfl, Subtype.mk_le_mk.mpr (unitInterval.nonneg t₁)⟩
  let t₀ : I := sSup K₀
  have ht₀_mem : t₀ ∈ K₀ := hK₀_closed.csSup_mem hK₀_ne (OrderTop.bddAbove K₀)
  have hγt₀_bd : γ t₀ ∈ discBd Δ' := ht₀_mem.1
  have ht₀_le_t₁ : t₀ ≤ t₁ := ht₀_mem.2.2
  have ht₀_lt_t₁ : t₀ < t₁ := by
    rcases eq_or_lt_of_le ht₀_le_t₁ with heq | hlt
    · exfalso
      have : γ t₁ ∈ discBd Δ' := heq ▸ hγt₀_bd
      exact (hsub hγt₁_Δ).2 this
    · exact hlt
  refine ⟨γ '' Icc t₀ t₁, γ t₀, γ t₁, hγt₀_bd, hγt₁_bd,
    isLineWithEnds_image_Icc_of_injOn hγc ht₀_lt_t₁ hγ_inj.injOn, ?_, ?_⟩
  · rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨hγ_mem t, ?_⟩
    rcases eq_or_lt_of_le ht1 with rfl | hlt
    · exact hγt₁_not_int
    · exact fun hint => ht₁_lt_not_Δ t hlt hint.1
  · rintro _ ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hnot_end⟩
    have ht0_lt : t₀ < t :=
      lt_of_le_of_ne ht0 (fun h => hnot_end (Or.inl (congrArg γ h.symm)))
    have ht1_lt : t < t₁ :=
      lt_of_le_of_ne ht1 (fun h => hnot_end (Or.inr (mem_singleton_iff.mpr (congrArg γ h))))
    have hnot_K₀ : t ∉ K₀ :=
      fun ht => not_lt_of_ge (le_csSup (OrderTop.bddAbove K₀) ht) ht0_lt
    have ht_Icc : t ∈ Icc (0 : I) t₁ :=
      ⟨Subtype.mk_le_mk.mpr (unitInterval.nonneg t), ht1⟩
    have hnot_bdΔ' : γ t ∉ discBd Δ' := fun h => hnot_K₀ ⟨h, ht_Icc⟩
    exact ⟨⟨hγ_mem t, hnot_bdΔ'⟩, ht₁_lt_not_Δ t ht1_lt⟩

private theorem disc_score_le_drawing_size {G : Drawing S} (A : Set S) :
    (G.V ∩ A).ncard + {e ∈ G.E | e ⊆ A}.ncard ≤ G.V.ncard + G.E.ncard :=
  Nat.add_le_add (ncard_le_ncard inter_subset_left G.finite_V)
    (ncard_le_ncard (sep_subset _ _) G.finite_edges)

omit [TopologicalSpace S] in
private theorem minimal_score_deficit_maximizes_score
    (ℱ : Set (Set S)) (score : (F : Set S) → F ∈ ℱ → ℕ) (M : ℕ)
    (hscore_le_M : ∀ (F : Set S) (hF : F ∈ ℱ), score F hF ≤ M)
    (F : Set S) (hF : F ∈ ℱ)
    (hF_min : M - score F hF = sInf {k | ∃ F, ∃ (hF : F ∈ ℱ), M - score F hF = k}) :
    ∀ (F' : Set S) (hF' : F' ∈ ℱ), score F' hF' ≤ score F hF := by
  intro F' hF'
  have hle : sInf {k : ℕ | ∃ (F : Set S) (hF : F ∈ ℱ), M - score F hF = k} ≤
      M - score F' hF' := Nat.sInf_le ⟨F', hF', rfl⟩
  have h1 := hscore_le_M F hF
  have h2 := hscore_le_M F' hF'
  omega

private theorem disjoint_curve_lies_outside_disc
    {S : Type u}
    [TopologicalSpace S]
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (hS' : IsSurface S')
    [T2Space S']
    (hj : IsEmbedding j)
    (Δ : Set S')
    (hΔ_disc : IsClosedDisc Δ)
    (x : S)
    (hjx_Δ : j x ∉ Δ)
    (X : Set S)
    (hxX : x ∈ X)
    (hX_conn : IsConnected X)
    (hdisj_X_bdΔ : Disjoint (j '' X) (discBd Δ)) :
    Disjoint (discInt Δ) (j '' X) := by
  rcases hΔ_disc.side hS'.2.2 (hX_conn.isPreconnected.image j hj.continuous.continuousOn)
    hdisj_X_bdΔ with hsub_X | hdisj
  · exact False.elim (hjx_Δ (discInt_subset Δ (hsub_X (mem_image_of_mem j hxX))))
  · exact hdisj.symm.mono_left (discInt_subset Δ)

private theorem nested_capped_discs_strictly_inside
    {S : Type u}
    [TopologicalSpace S]
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (hj : IsEmbedding j)
    (F : Set S)
    (Δ : Set S')
    (hΔ_bd : discBd Δ = j '' F)
    (X : Set S)
    (hXF : X ∩ F = ∅)
    (F' : Set S)
    (hF'_sub_X : F' ⊆ X)
    (Δ' : Set S')
    (hΔ'_bd : discBd Δ' = j '' F')
    (hdisj_intΔ_bdΔ' : Disjoint (discInt Δ) (discBd Δ'))
    (hΔ_sub_Δ' : Δ ⊆ Δ') :
    Δ ⊆ discInt Δ' := by
  intro y hyΔ
  refine ⟨hΔ_sub_Δ' hyΔ, fun hy_bd' => ?_⟩
  by_cases hy_bd : y ∈ discBd Δ
  · rw [hΔ_bd] at hy_bd
    rw [hΔ'_bd] at hy_bd'
    obtain ⟨z₁, hz₁F, rfl⟩ := hy_bd
    obtain ⟨z₂, hz₂F', heq⟩ := hy_bd'
    have : z₁ ∈ X ∩ F := ⟨hF'_sub_X (hj.injective heq ▸ hz₂F'), hz₁F⟩
    rw [hXF] at this
    exact this
  · exact disjoint_left.mp hdisj_intΔ_bdΔ' ⟨hyΔ, hy_bd⟩ hy_bd'

private theorem vertices_in_strictly_nested_discs
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (F : Set S)
    (Δ : Set S')
    (Δ' : Set S')
    (hpre_sub_V : G.V ∩ j ⁻¹' discInt Δ ∪ G.V ∩ F ⊆ G.V ∩ j ⁻¹' discInt Δ')
    (hdisj_VF : Disjoint (G.V ∩ j ⁻¹' discInt Δ) (G.V ∩ F)) :
    (G.V ∩ j ⁻¹' discInt Δ).ncard + (G.V ∩ F).ncard ≤ (G.V ∩ j ⁻¹' discInt Δ').ncard := by
  rw [← ncard_union_eq hdisj_VF (G.finite_V.inter_of_left _) (G.finite_V.inter_of_left _)]
  exact ncard_le_ncard hpre_sub_V (G.finite_V.inter_of_left _)

private theorem boundary_without_vertices_avoids_drawing {G : Drawing S} {F : Set S}
    (hF : G.IsNormal F) (hVF_empty : G.V ∩ F = ∅) :
    G.U ∩ F = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzVF : z ∈ G.V ∩ F := ⟨hF ⟨hz.2, hz.1⟩, hz.2⟩
  rwa [hVF_empty] at hzVF

private theorem equal_disc_scores_leave_annulus_disjoint
    {S : Type u}
    [TopologicalSpace S]
    {G : Drawing S}
    (S' : Type u)
    [TopologicalSpace S']
    (j : S → S')
    (hS' : IsSurface S')
    [T2Space S']
    (hj : IsEmbedding j)
    (Δ : Set S')
    (F' : Set S)
    (hF'_norm : G.IsNormal F')
    (Δ' : Set S')
    (hΔ'_disc : IsClosedDisc (Δ'))
    (hΔ'_bd : discBd (Δ') = j '' F')
    (hV_eq : G.V ∩ j ⁻¹' discInt Δ = G.V ∩ j ⁻¹' discInt Δ')
    (hE_eq : {e | e ∈ G.E ∧ e ⊆ j ⁻¹' discInt Δ} = {e | e ∈ G.E ∧ e ⊆ j ⁻¹' discInt Δ'}) :
    ∀ (z : S), j z ∈ discInt Δ' \ Δ → z ∉ G.U := by
  intro z ⟨hz_int', hz_not_Δ⟩ hzU
  by_cases hzV : z ∈ G.V
  · have hz_mem' : z ∈ G.V ∩ j ⁻¹' discInt Δ' := ⟨hzV, hz_int'⟩
    rw [← hV_eq] at hz_mem'
    exact hz_not_Δ (discInt_subset Δ hz_mem'.2)
  · obtain ⟨e, heE, hze⟩ := G.exists_edge_of_mem hzU hzV
    have he_disj_bdΔ' : Disjoint (j '' e) (discBd Δ') := by
      rw [hΔ'_bd, disjoint_left]
      rintro _ ⟨w₁, hw₁e, rfl⟩ ⟨w₂, hw₂F', heq⟩
      have hw₁F' : w₁ ∈ F' := hj.injective heq ▸ hw₂F'
      have hw₁U : w₁ ∈ G.U \ G.V := heE.2.1 hw₁e
      exact hw₁U.2 (hF'_norm ⟨hw₁F', hw₁U.1⟩)
    have he_conn : IsPreconnected (j '' e) :=
      (heE.2.2.1.isConnected.isPreconnected).image j hj.continuous.continuousOn
    have he_sub' : j '' e ⊆ discInt Δ' := by
      rcases hΔ'_disc.side hS'.2.2 he_conn he_disj_bdΔ' with hsub_e | hdisj_e
      · exact hsub_e
      · exact False.elim (disjoint_right.mp hdisj_e (discInt_subset Δ' hz_int')
          (mem_image_of_mem j hze))
    have he_mem' : e ∈ {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'} :=
      ⟨heE, image_subset_iff.mp he_sub'⟩
    rw [← hE_eq] at he_mem'
    exact hz_not_Δ (discInt_subset Δ (he_mem'.2 hze))

private theorem mem_nearSet_through_annulus [T2Space S]
    {S' : Type u} [TopologicalSpace S']
    {G : Drawing S} {C F X : Set S} {D Δ Δ' Q₁ : Set S'}
    {j : S → S'} {x z w : S} {r : ℕ}
    (hCap : IsCappedCuff C S' j D) (hj : IsEmbedding j) (hD_sub_Δ : discInt D ⊆ discInt Δ)
    (hxX : x ∈ X) (hzX : z ∈ X) (hwF : w ∈ F) (hX_arc : IsArcConnected X)
    (hX_norm : G.IsNormal X) (hX_card : (G.V ∩ X).ncard ≤ r)
    (hXF : X ∩ F = ∅) (hUF : G.U ∩ F = ∅)
    (hU_annulus : ∀ y : S, j y ∈ discInt Δ' \ Δ → y ∉ G.U)
    (hQ₁ : IsLineWithEnds Q₁ (j z) (j w))
    (hQ₁_sub : Q₁ ⊆ Δ' \ discInt Δ)
    (hQ₁_int : Q₁ \ {j z, j w} ⊆ discInt Δ' \ Δ) :
    x ∈ nearSet G r F := by
  have hQ₁_range : Q₁ ⊆ range j := by
    intro y hy
    have hy_not_intD : y ∉ discInt D := fun h => (hQ₁_sub hy).2 (hD_sub_Δ h)
    rcases (hCap.union_eq ▸ mem_univ y : y ∈ range j ∪ D) with hy_r | hy_D
    · exact hy_r
    · have hy_bdD : y ∈ discBd D := by
        by_contra h
        exact hy_not_intD ⟨hy_D, h⟩
      rw [hCap.discBd_eq, ← hCap.inter_eq] at hy_bdD
      exact hy_bdD.1
  obtain ⟨hQ_line, _⟩ := pull_of_isLineWithEnds hj hQ₁ hQ₁_range
  let Q : Set S := j ⁻¹' Q₁
  have hUQ_sub : G.U ∩ Q ⊆ G.V ∩ X := by
    intro y ⟨hyU, hyQ⟩
    by_cases hy_end : j y ∈ ({j z, j w} : Set S')
    · rcases mem_insert_iff.mp hy_end with hyz | hyw
      · have h : y = z := hj.injective hyz
        subst y
        exact ⟨hX_norm ⟨hzX, hyU⟩, hzX⟩
      · have h : y = w := hj.injective (mem_singleton_iff.mp hyw)
        subst y
        have hy : w ∈ G.U ∩ F := ⟨hyU, hwF⟩
        rw [hUF] at hy
        exact hy.elim
    · exact (hU_annulus y (hQ₁_int ⟨hyQ, hy_end⟩) hyU).elim
  have hx_XQ : x ∈ X ∪ Q := Or.inl hxX
  have hw_XQ : w ∈ X ∪ Q := Or.inr (right_mem_of_isLineWithEnds hQ_line)
  have hxz := (isArcConnected_iff_joinedIn.mp hX_arc x hxX z hzX).mono
    (subset_union_left : X ⊆ X ∪ Q)
  have hzw : JoinedIn (X ∪ Q) z w :=
    (joinedIn_iff_eq_or_exists_isLineWithEnds (Or.inl hzX) hw_XQ).mpr
      (Or.inr ⟨Q, subset_union_right, hQ_line⟩)
  have hxw_ne : x ≠ w := fun h => by
    have hx : x ∈ X ∩ F := ⟨hxX, h ▸ hwF⟩
    rwa [hXF] at hx
  obtain ⟨L, hL_sub, hL_line⟩ :=
    ((joinedIn_iff_eq_or_exists_isLineWithEnds hx_XQ hw_XQ).mp (hxz.trans hzw)).resolve_left hxw_ne
  have hUL_sub : G.U ∩ L ⊆ G.V ∩ X := by
    rintro y ⟨hyU, hyL⟩
    rcases hL_sub hyL with hyX | hyQ
    · exact ⟨hX_norm ⟨hyX, hyU⟩, hyX⟩
    · exact hUQ_sub ⟨hyU, hyQ⟩
  have hfin := G.finite_V.inter_of_left X
  refine ⟨w, hwF, (distPoint_le_of_lineWithEnds hL_line (hfin.subset hUL_sub)).trans ?_⟩
  exact (ncard_le_ncard hUL_sub hfin).trans hX_card

/-- Graph Minors VII, (5.7) (page 232):
"Let $\Sigma \cong \Sigma(a, b, c)$, where $3a + 3b + c \ge 3$, and let $G$ be a proper graph in
$\Sigma$. Let $C$ be a cuff, and let $r \ge 0$ be an integer with $r \le \frac{2}{9}\alpha(G) - 1$.
Then $\mathscr{A}_r(C)$ is planar in $\Sigma + \hat{C}$." -/
theorem theorem_5_7_proof
    (hS : IsSurface S) [ConnectedSpace S]
    {a b c : ℕ} (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (habc : 3 ≤ 3 * a + 3 * b + c)
    {G : Drawing S} (hG : G.IsProper)
    {C : Set S} (hC : C ∈ cuffs S)
    {r : ℕ} (hr : 9 * (r + 1) ≤ 2 * alpha G) :
    IsPlanarInCappedCuff C (scriptA G r C) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hnot_small : ∀ c' ≤ 2, IsEmpty (S ≃ₜ SurfaceModel 0 0 c') := by
    intro c' hc'
    refine ⟨fun e' => ?_⟩
    obtain ⟨e₀⟩ := hmodel
    have hcrit := (modelCriterion.2 a b c 0 0 c').mp ⟨e₀.symm.trans e'⟩
    have hb0 : b = 0 := hcrit.2.2.mpr rfl
    omega
  by_cases hA_ne : (scriptA G r C).Nonempty
  · have h_all : ∀ (S' : Type u) [TopologicalSpace S'] (j : S → S') (D : Set S'),
        IsCappedCuff C S' j D → IsPlanar (j '' scriptA G r C) := by
      intro S' _ j D hCap
      have hS' : IsSurface S' := hCap.isSurface
      have : CompactSpace S' := hS'.1
      have : T2Space S' := hS'.2.1
      have : ConnectedSpace S' := hCap.connectedSpace hS
      have hj : IsEmbedding j := hCap.isEmbedding
      have hns_S' : ¬ IsSphere S' := by
        intro hsph
        obtain ⟨hc1, ⟨e₁⟩⟩ := cappedCuff_homeo_model hS hmodel hC hCap
        obtain ⟨e_sph⟩ := id hsph
        obtain ⟨e_m0⟩ := GraphMinor.GM19.isSphere_model
        have hcrit := (modelCriterion.2 a b (c - 1) 0 0 0).mp ⟨e₁.symm.trans
          (e_sph.trans e_m0.symm)⟩
        have hb0 : b = 0 := hcrit.2.2.mpr rfl
        omega
      let ℱ : Set (Set S) :=
        {F : Set S | IsOArc F ∧ G.IsNormal F ∧ SurroundsCuff F C ∧ (G.V ∩ F).ncard ≤ r}
      have hℱ_ne : ℱ.Nonempty := by
        obtain ⟨x₀, hx₀⟩ := hA_ne
        obtain ⟨X₀, ⟨hX₀_sol, _, hX₀_norm, hX₀_surr, hX₀_card⟩, -⟩ := mem_sUnion.mp hx₀
        obtain ⟨F₀, hF₀_oarc, hF₀_sub, hF₀_surr⟩ :=
          (theorem_5_2_proof hS hX₀_sol hX₀_surr.2.1).mp hX₀_surr
        refine ⟨F₀, hF₀_oarc, fun z ⟨hzF, hzU⟩ => hX₀_norm ⟨hF₀_sub hzF, hzU⟩, hF₀_surr, ?_⟩
        exact (ncard_le_ncard (inter_subset_inter_right G.V hF₀_sub)
          (G.finite_V.inter_of_left X₀)).trans hX₀_card
      let discOf : (F : Set S) → F ∈ ℱ → Set S' := fun F hF =>
        Classical.choose (surroundsCuff_bounds_disc_containing_cap hS hF.1 hF.2.2.1 hCap)
      have hdiscOf_spec : ∀ (F : Set S) (hF : F ∈ ℱ),
          IsClosedDisc (discOf F hF) ∧ discBd (discOf F hF) = j '' F ∧
          discInt D ⊆ discInt (discOf F hF) :=
        fun F hF => Classical.choose_spec
          (surroundsCuff_bounds_disc_containing_cap hS hF.1 hF.2.2.1 hCap)
      let score : (F : Set S) → F ∈ ℱ → ℕ := fun F hF =>
        (G.V ∩ j ⁻¹' discInt (discOf F hF)).ncard +
          {e ∈ G.E | e ⊆ j ⁻¹' discInt (discOf F hF)}.ncard
      let M : ℕ := G.V.ncard + G.E.ncard
      have hscore_le_M : ∀ (F : Set S) (hF : F ∈ ℱ), score F hF ≤ M := by
        intro F hF
        exact disc_score_le_drawing_size (G := G) (j ⁻¹' discInt (discOf F hF))
      have hK_ne : {k : ℕ | ∃ (F : Set S) (hF : F ∈ ℱ), M - score F hF = k}.Nonempty := by
        obtain ⟨F₀, hF₀⟩ := hℱ_ne
        exact ⟨M - score F₀ hF₀, F₀, hF₀, rfl⟩
      obtain ⟨F, hF, hF_min⟩ := Nat.sInf_mem hK_ne
      have hF_max : ∀ (F' : Set S) (hF' : F' ∈ ℱ), score F' hF' ≤ score F hF := by
        exact minimal_score_deficit_maximizes_score ℱ score M hscore_le_M F hF hF_min
      let Δ : Set S' := discOf F hF
      obtain ⟨hΔ_disc, hΔ_bd, hD_sub_Δ⟩ := hdiscOf_spec F hF
      -- Show Δ ∪ j '' nearSet G r F is planar in S'
      have hY_capped : IsPlanarInCappedCuff C (nearSet G r F) :=
        theorem_5_6_proof hS hnot_small hG hC hF.1 hF.2.1 hF.2.2.1 hF.2.2.2 hr
      obtain ⟨Δ₀, hΔ₀_disc, hY_sub_Δ₀⟩ := hY_capped.2.2 S' j D hCap
      have hF_sub_Y : F ⊆ nearSet G r F := subset_nearSet_of_isNormal hF.2.1 hF.2.2.2
      have hbdΔ_sub_Δ₀ : discBd Δ ⊆ Δ₀ :=
        hΔ_bd ▸ (image_mono hF_sub_Y).trans hY_sub_Δ₀
      have hjF_oarc : IsOArc (j '' F) :=
        isOArc_image hF.1 hj.continuous.continuousOn hj.injective.injOn
      obtain ⟨Δ'', ⟨hΔ''_sub_Δ₀, hΔ''_disc, hΔ''_bd, -⟩, -⟩ :=
        disc_oArc Δ₀ (j '' F) hΔ₀_disc (hΔ_bd ▸ hbdΔ_sub_Δ₀) hjF_oarc
      have hΔ_eq_Δ'' : Δ = Δ'' :=
        eq_of_discBd_eq hS' hns_S' hΔ_disc hΔ''_disc (hΔ_bd.trans hΔ''_bd.symm)
      have hΔ_sub_Δ₀ : Δ ⊆ Δ₀ := hΔ_eq_Δ'' ▸ hΔ''_sub_Δ₀
      refine ⟨Δ₀, hΔ₀_disc, ?_⟩
      rintro _ ⟨x, hxA, rfl⟩
      by_cases hjx_Δ : j x ∈ Δ
      · exact hΔ_sub_Δ₀ hjx_Δ
      -- Suffices to show x ∈ nearSet G r F when j x ∉ Δ
      suffices hxY : x ∈ nearSet G r F from hY_sub_Δ₀ (mem_image_of_mem j hxY)
      obtain ⟨X, ⟨hX_sol, hX_conn, hX_norm, hX_surr, hX_card⟩, hxX⟩ := mem_sUnion.mp hxA
      have hX_arc : IsArcConnected X :=
        theorem_11_4_proof hS hX_conn hX_sol.1
      by_cases hXF : (X ∩ F).Nonempty
      · obtain ⟨w₀, hw₀X, hw₀F⟩ := hXF
        rcases eq_or_ne x w₀ with rfl | hxw₀
        · exact hF_sub_Y hw₀F
        · obtain ⟨L, hLX, hL_line⟩ := hX_arc x hxX w₀ hw₀X hxw₀
          have hUL_sub : G.U ∩ L ⊆ G.V ∩ X := fun z ⟨hzU, hzL⟩ =>
            ⟨hX_norm ⟨hLX hzL, hzU⟩, hLX hzL⟩
          have hUL_fin : (G.U ∩ L).Finite := (G.finite_V.inter_of_left X).subset hUL_sub
          have hdist : distPoint G x w₀ ≤ r :=
            (distPoint_le_of_lineWithEnds hL_line hUL_fin).trans
              ((ncard_le_ncard hUL_sub (G.finite_V.inter_of_left X)).trans hX_card)
          exact ⟨w₀, hw₀F, hdist⟩
      · rw [not_nonempty_iff_eq_empty] at hXF
        obtain ⟨F', hF'_oarc, hF'_sub_X, hF'_surr⟩ :=
          (theorem_5_2_proof hS hX_sol hX_surr.2.1).mp hX_surr
        have hF'_norm : G.IsNormal F' := fun z ⟨hzF', hzU⟩ => hX_norm ⟨hF'_sub_X hzF', hzU⟩
        have hF'_card : (G.V ∩ F').ncard ≤ r :=
          (ncard_le_ncard (inter_subset_inter_right G.V hF'_sub_X)
            (G.finite_V.inter_of_left X)).trans hX_card
        have hF'_mem : F' ∈ ℱ := ⟨hF'_oarc, hF'_norm, hF'_surr, hF'_card⟩
        let Δ' : Set S' := discOf F' hF'_mem
        obtain ⟨hΔ'_disc, hΔ'_bd, hD_sub_Δ'⟩ := hdiscOf_spec F' hF'_mem
        -- Show Disjoint (discInt Δ) (j '' X)
        have hdisj_X_bdΔ : Disjoint (j '' X) (discBd Δ) := by
          rw [hΔ_bd, disjoint_left]
          rintro _ ⟨z₁, hz₁X, rfl⟩ ⟨z₂, hz₂F, heq⟩
          have hz₁F : z₁ ∈ F := hj.injective heq ▸ hz₂F
          have : z₁ ∈ X ∩ F := ⟨hz₁X, hz₁F⟩
          rw [hXF] at this
          exact this
        have hdisj_intΔ_X : Disjoint (discInt Δ) (j '' X) := by
          exact disjoint_curve_lies_outside_disc (S := S) S' j hS' hj Δ hΔ_disc x
            hjx_Δ X hxX hX_conn hdisj_X_bdΔ
        have hdisj_intΔ_bdΔ' : Disjoint (discInt Δ) (discBd Δ') := by
          rw [hΔ'_bd]
          exact hdisj_intΔ_X.mono_right (image_mono hF'_sub_X)
        -- Show Δ ⊆ discInt Δ'
        have hintΔ_sub_intΔ' : discInt Δ ⊆ discInt Δ' := by
          rcases hΔ'_disc.side hS'.2.2 hΔ_disc.isPreconnected_discInt hdisj_intΔ_bdΔ' with
            hsub_int | hdisj_int
          · exact hsub_int
          · exfalso
            obtain ⟨d₀, hd₀⟩ := hCap.isClosedDisc.nonempty_discInt
            exact disjoint_left.mp hdisj_int (hD_sub_Δ hd₀) (discInt_subset Δ' (hD_sub_Δ' hd₀))
        have hΔ_sub_Δ' : Δ ⊆ Δ' :=
          hΔ_disc.subset_closure_discInt.trans
            (closure_minimal (hintΔ_sub_intΔ'.trans (discInt_subset Δ'))
              hΔ'_disc.isCompact.isClosed)
        have hΔ_sub_intΔ' : Δ ⊆ discInt Δ' := by
          exact nested_capped_discs_strictly_inside (S := S) S' j hj F Δ hΔ_bd X hXF
            F' hF'_sub_X Δ' hΔ'_bd hdisj_intΔ_bdΔ' hΔ_sub_Δ'
        -- Use maximality of score F to deduce G.V ∩ F = ∅ and no vertices/edges in discInt Δ' \ Δ
        have hpre_sub_V :
            (G.V ∩ j ⁻¹' discInt Δ) ∪ (G.V ∩ F) ⊆ G.V ∩ j ⁻¹' discInt Δ' := by
          rintro z (⟨hzV, hzj⟩ | ⟨hzV, hzF⟩)
          · exact ⟨hzV, hintΔ_sub_intΔ' hzj⟩
          · refine ⟨hzV, hΔ_sub_intΔ' ?_⟩
            have : j z ∈ discBd Δ := hΔ_bd ▸ mem_image_of_mem j hzF
            exact Surface.discBd_subset Δ this
        have hdisj_VF : Disjoint (G.V ∩ j ⁻¹' discInt Δ) (G.V ∩ F) := by
          refine disjoint_left.mpr fun z ⟨_, hzj⟩ ⟨_, hzF⟩ => ?_
          exact hzj.2 (hΔ_bd ▸ mem_image_of_mem j hzF)
        have hV_ineq :
            (G.V ∩ j ⁻¹' discInt Δ).ncard + (G.V ∩ F).ncard ≤
              (G.V ∩ j ⁻¹' discInt Δ').ncard := by
          exact vertices_in_strictly_nested_discs (S := S) (G := G) S' j F Δ Δ' hpre_sub_V
            hdisj_VF
        have hE_sub :
            {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ} ⊆ {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'} :=
          fun e ⟨heE, he_sub⟩ => ⟨heE, he_sub.trans (preimage_mono hintΔ_sub_intΔ')⟩
        have hE_ineq :
            {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ}.ncard ≤
              {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'}.ncard :=
          ncard_le_ncard hE_sub (G.finite_edges.subset (sep_subset _ _))
        have hmax_F' :
            (G.V ∩ j ⁻¹' discInt Δ').ncard + {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'}.ncard ≤
              (G.V ∩ j ⁻¹' discInt Δ).ncard + {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ}.ncard :=
          hF_max F' hF'_mem
        have hVF_zero : (G.V ∩ F).ncard = 0 := by omega
        have hV_ncard_le :
            (G.V ∩ j ⁻¹' discInt Δ').ncard ≤ (G.V ∩ j ⁻¹' discInt Δ).ncard := by omega
        have hE_ncard_le :
            {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'}.ncard ≤
              {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ}.ncard := by omega
        have hVF_empty : G.V ∩ F = ∅ :=
          (ncard_eq_zero (G.finite_V.inter_of_left F)).mp hVF_zero
        have hUF_empty : G.U ∩ F = ∅ := by
          exact boundary_without_vertices_avoids_drawing hF.2.1 hVF_empty
        have hV_eq : G.V ∩ j ⁻¹' discInt Δ = G.V ∩ j ⁻¹' discInt Δ' :=
          eq_of_subset_of_ncard_le
            (inter_subset_inter_right G.V (preimage_mono hintΔ_sub_intΔ'))
            hV_ncard_le (G.finite_V.inter_of_left _)
        have hE_eq :
            {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ} = {e ∈ G.E | e ⊆ j ⁻¹' discInt Δ'} :=
          eq_of_subset_of_ncard_le hE_sub hE_ncard_le (G.finite_edges.subset (sep_subset _ _))
        -- Show G.U is disjoint from j ⁻¹' (discInt Δ' \ Δ)
        have hU_annulus_empty : ∀ z : S, j z ∈ discInt Δ' \ Δ → z ∉ G.U := by
          exact equal_disc_scores_leave_annulus_disjoint (S := S) (G := G) S' j hS' hj Δ
            F' hF'_norm Δ' hΔ'_disc hΔ'_bd hV_eq hE_eq
        -- Construct the subarc Q₁ in Δ' \ discInt Δ and pull back to S
        obtain ⟨Q₁, p, q, hp_bd', hq_bd, hQ₁_line, hQ₁_sub, hQ₁_int⟩ :=
          exists_subarc_in_annulus hS' hΔ_disc hΔ'_disc hΔ_sub_intΔ'
        rw [hΔ'_bd] at hp_bd'
        rw [hΔ_bd] at hq_bd
        obtain ⟨z₁, hz₁F', rfl⟩ := hp_bd'
        obtain ⟨w₀, hw₀F, rfl⟩ := hq_bd
        exact mem_nearSet_through_annulus hCap hj hD_sub_Δ hxX (hF'_sub_X hz₁F') hw₀F
          hX_arc hX_norm hX_card hXF hUF_empty hU_annulus_empty hQ₁_line hQ₁_sub hQ₁_int
    obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC)
    have : Nonempty S := ⟨c₀⟩
    obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C hS hC
    have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
    exact ⟨hC, ⟨S', topS', j, D, hCap, h_all S' j D hCap⟩, h_all⟩
  · rw [not_nonempty_iff_eq_empty.mp hA_ne]
    obtain ⟨c₀, _⟩ := isOArc_nonempty (cuff_isOArc hS hC)
    have : Nonempty S := ⟨c₀⟩
    obtain ⟨S', topS', j, D, hS', hj, hD, hunion, hinter, hbdD⟩ := paste_disc S C hS hC
    have hCap : IsCappedCuff C S' j D := ⟨hC, hS', hj.isEmbedding, hD, hbdD.1, hunion, hinter⟩
    exact ⟨hC, ⟨S', topS', j, D, hCap, ⟨D, hD, by simp⟩⟩,
      fun _ _ _ D' hCap' => ⟨D', hCap'.isClosedDisc, by simp⟩⟩

end GraphMinor.GM07
