/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section3SpanGlue
public import LeanPool.GraphMinor.GM15.Section4
public import LeanPool.GraphMinor.Surface.HandleModel
public import LeanPool.GraphMinor.Surface.AddHandle
public import LeanPool.GraphMinor.Surface.AddCrosscap
public import LeanPool.GraphMinor.Surface.DiscRemove
public import LeanPool.GraphMinor.Surface.CircleMove
public import LeanPool.GraphMinor.GM11.Theorem65
import LeanPool.GraphMinor.GM14.DiscBoundaryHomeomorphism

/-!
# Closed Discs from Regions in Graph Minors XV, Section 3

This file proves that for a 2-cell drawing `H` in a closed connected surface `S` with a respectful
tangle `T` of order `θ ≥ 3`, the closure `closure Λ` of any region `Λ ∈ H.R` whose boundary
`subBd Λ` is an `O`-arc is a closed disc with boundary `subBd Λ`, and the complement of one or two
such regions with disjoint closures is a connected surface whose boundary consists of the
corresponding `O`-arcs.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14

universe w

variable {S : Type w} [TopologicalSpace S]

/-- Removing one point from `Circle` leaves a preconnected set. -/
theorem isPreconnected_circle_compl_singleton (w₀ : Circle) :
    IsPreconnected ((univ : Set Circle) \ {w₀}) := by
  obtain ⟨t₀, rfl⟩ := ee_surjective w₀
  have hEq : (univ : Set Circle) \ {ee t₀} = ee '' Ioo t₀ (t₀ + 1) := by
    ext w
    constructor
    · rintro ⟨-, hw⟩
      obtain ⟨t, rfl⟩ := ee_surjective w
      let u := t₀ + Int.fract (t - t₀)
      have hu_def : u = t₀ + Int.fract (t - t₀) := rfl
      have hu_eq : ee u = ee t := by
        apply ee_eq_iff.mpr
        refine ⟨-⌊t - t₀⌋, ?_⟩
        rw [hu_def, Int.fract]
        push_cast
        ring
      have h0 : 0 < Int.fract (t - t₀) := by
        refine lt_of_le_of_ne (Int.fract_nonneg (t - t₀)) fun h => hw ?_
        apply mem_singleton_iff.mpr
        rw [← hu_eq, hu_def, ← h, add_zero]
      have h1 : Int.fract (t - t₀) < 1 := Int.fract_lt_one (t - t₀)
      exact ⟨u, ⟨by linarith, by linarith⟩, hu_eq⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨mem_univ _, fun h => ?_⟩
      obtain ⟨m, hm⟩ := ee_eq_iff.mp (mem_singleton_iff.mp h)
      have hlt1 : (0 : ℝ) < m := by linarith
      have hlt2 : (m : ℝ) < 1 := by linarith
      have hm1 : (0 : ℤ) < m := by exact_mod_cast hlt1
      have hm2 : m < (1 : ℤ) := by exact_mod_cast hlt2
      omega
  rw [hEq]
  exact isPreconnected_Ioo.image ee continuous_ee.continuousOn

/-- Removing a finite set of at most one point from an `O`-arc leaves a preconnected set. -/
theorem IsOArc.isPreconnected_sdiff_of_ncard_le_one {F A : Set S} (hF : IsOArc F)
    (hfin : (A ∩ F).Finite) (hcard : (A ∩ F).ncard ≤ 1) : IsPreconnected (F \ A) := by
  have hEq : F \ A = F \ (A ∩ F) := by
    ext x
    exact ⟨fun ⟨hxF, hxA⟩ => ⟨hxF, fun h => hxA h.1⟩,
      fun ⟨hxF, h⟩ => ⟨hxF, fun hxA => h ⟨hxA, hxF⟩⟩⟩
  rw [hEq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · have hemp : A ∩ F = ∅ := (ncard_eq_zero hfin).mp h0
    rw [hemp, sdiff_empty]
    exact hF.isPreconnected
  · obtain ⟨x₀, hx₀⟩ := ncard_eq_one.mp h1
    have hx₀F : x₀ ∈ F := by
      have : x₀ ∈ A ∩ F := hx₀ ▸ mem_singleton x₀
      exact this.2
    rw [hx₀]
    obtain ⟨φ⟩ := id hF
    let w₀ : Circle := φ.symm ⟨x₀, hx₀F⟩
    have himg : F \ {x₀} = (fun w : Circle => (φ w).1) '' ((univ : Set Circle) \ {w₀}) := by
      ext x
      constructor
      · rintro ⟨hxF, hne⟩
        refine ⟨φ.symm ⟨x, hxF⟩, ⟨mem_univ _, fun h => hne ?_⟩, ?_⟩
        · have h' := congrArg (fun z : Circle => (φ z).1) (mem_singleton_iff.mp h)
          simp only [w₀, Homeomorph.apply_symm_apply] at h'
          exact mem_singleton_iff.mpr h'
        · change (φ (φ.symm ⟨x, hxF⟩)).1 = x
          rw [Homeomorph.apply_symm_apply]
      · rintro ⟨w, ⟨-, hw⟩, rfl⟩
        refine ⟨(φ w).2, fun h => hw ?_⟩
        have hw_eq : (φ w).1 = x₀ := mem_singleton_iff.mp h
        apply mem_singleton_iff.mpr
        apply φ.injective
        change φ w = φ (φ.symm ⟨x₀, hx₀F⟩)
        rw [Homeomorph.apply_symm_apply]
        exact Subtype.ext hw_eq
    rw [himg]
    exact (isPreconnected_circle_compl_singleton w₀).image _
      (continuous_subtype_val.comp φ.continuous).continuousOn

/-- If `Λ` is an open disc in a connected surface `S` with `Disjoint (closure Λ) (bd S)`,
`IsOArc (closure Λ \ Λ)`, and `(closure Λ)ᶜ.Nonempty`, then every point of `closure Λ \ Λ` lies in
`closure (closure Λ)ᶜ`, and `closure Λ` is a closed disc with boundary `closure Λ \ Λ`. -/
theorem closure_disc_of_compl_nonempty [ConnectedSpace S] (hS : IsSurface S)
    {Λ : Set S} (hΛ : IsOpenDisc Λ) (hbd : Disjoint (closure Λ) (bd S))
    (hF : IsOArc (closure Λ \ Λ)) (hcompl : (closure Λ)ᶜ.Nonempty) :
    (∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) ∧
      IsClosedDisc (closure Λ) ∧ discBd (closure Λ) = closure Λ \ Λ := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hΛo : IsOpen Λ := hΛ.1
  obtain ⟨φ₀⟩ := id hF
  have hneΛ : (closure Λ).Nonempty := ⟨(φ₀ 1).1, (φ₀ 1).2.1⟩
  have hfr_ne : (frontier (closure Λ)).Nonempty := by
    by_contra hfr_emp
    have hclop : IsClopen (closure Λ) :=
      isClopen_iff_frontier_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hfr_emp)
    have huniv : closure Λ = univ := hclop.eq_univ hneΛ
    obtain ⟨z, hz⟩ := hcompl
    exact hz (huniv ▸ mem_univ z)
  obtain ⟨x₀, hx₀_cl, hx₀_nint⟩ := hfr_ne
  rw [closure_closure] at hx₀_cl
  have hx₀_out : x₀ ∈ closure (closure Λ)ᶜ := by
    rw [closure_compl]
    exact hx₀_nint
  have hx₀_nΛ : x₀ ∉ Λ := fun hxΛ => hx₀_nint (interior_maximal subset_closure hΛo hxΛ)
  have hx₀_C : x₀ ∈ closure Λ \ Λ := ⟨hx₀_cl, hx₀_nΛ⟩
  set C : Set S := closure Λ \ Λ with hC_def
  have hbC : Disjoint C (bd S) := hbd.mono_left sdiff_subset
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsplit, -⟩ := exists_cut_loop hS hF hbC
  have hcY : CompactSpace Y := hY.1
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hsurj := hψ.2.1
  have hc := hψ.1
  have hbdC : ψ ⁻¹' C ⊆ bd Y := hψ.2.2.2.2
  set O₁ : Set Y := ψ ⁻¹' Λ with hO₁
  set O₂ : Set Y := ψ ⁻¹' (closure Λ)ᶜ with hO₂
  have hO₁o : IsOpen O₁ := hΛo.preimage hc
  have hO₂o : IsOpen O₂ := isClosed_closure.isOpen_compl.preimage hc
  have hcover : ∀ y : Y, y ∈ O₁ ∨ y ∈ O₂ ∨ y ∈ ψ ⁻¹' C := fun y => by
    by_cases h1 : ψ y ∈ Λ
    · exact Or.inl h1
    · by_cases h2 : ψ y ∈ closure Λ
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
      · exact Or.inr (Or.inl h2)
  have hdis12 : Disjoint O₁ O₂ :=
    disjoint_left.mpr fun y hy1 hy2 => hy2 (subset_closure hy1)
  have key : ∀ y ∈ ψ ⁻¹' C, y ∉ closure O₁ ∨ y ∉ closure O₂ := by
    intro y hy
    obtain ⟨V, P, hV, hyV, -, hPV, hPc, hPi, hVc⟩ :=
      (hY.2.2 y).exists_half isOpen_univ (mem_univ y)
    have hsub : P ⊆ O₁ ∪ O₂ := fun z hz => by
      rcases hcover z with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hPi z hz) (hbdC h)
    rcases hPc.subset_or_subset hO₁o hO₂o hdis12 hsub with h | h
    · right
      intro hcl2
      obtain ⟨z, ⟨hz1, hz2⟩⟩ :=
        mem_closure_iff_nhds.mp hcl2 _ (hV.mem_nhds hyV) |>.imp fun _ h => h
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp (hVc hz1) _ hO₂o hz2
      exact disjoint_left.mp hdis12 (h hw2) hw1
    · left
      intro hcl1
      obtain ⟨z, ⟨hz1, hz2⟩⟩ :=
        mem_closure_iff_nhds.mp hcl1 _ (hV.mem_nhds hyV) |>.imp fun _ h => h
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp (hVc hz1) _ hO₁o hz2
      exact disjoint_left.mp hdis12 hw1 (h hw2)
  set N₁ : Set Y := (closure O₂)ᶜ with hN₁
  set N₂ : Set Y := (closure O₁)ᶜ with hN₂
  have hN₁o : IsOpen N₁ := isClosed_closure.isOpen_compl
  have hN₂o : IsOpen N₂ := isClosed_closure.isOpen_compl
  have hN₁s : ∀ y ∈ N₁, y ∈ O₁ ∨ y ∈ ψ ⁻¹' C := fun y hy => by
    rcases hcover y with h | h | h
    · exact Or.inl h
    · exact absurd (subset_closure h) hy
    · exact Or.inr h
  have hNd : Disjoint N₁ N₂ := by
    refine disjoint_left.mpr fun y h3 h4 => ?_
    have hN : IsOpen (N₁ ∩ N₂) := hN₁o.inter hN₂o
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hY.2.2 y)) _ hN ⟨h3, h4⟩
    rcases hN₁s z hz.1 with h | h
    · exact hz.2 (subset_closure h)
    · exact hz' (hbdC h)
  have hkey2 : ψ ⁻¹' C ⊆ N₁ ∪ N₂ := fun y hy => by
    rcases key y hy with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hN₂_cl : N₂ ⊆ closure O₂ := fun y hy => by
    have hbd_compl : (bd Y)ᶜ ⊆ O₁ ∪ O₂ := fun z hz => by
      rcases hcover z with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hbdC h) hz
    have hcl_u : y ∈ closure O₁ ∪ closure O₂ := by
      rw [← closure_union]
      exact closure_mono hbd_compl (mem_closure_compl_bd (hY.2.2 y))
    exact hcl_u.resolve_left hy
  have hy₀_ex : ∃ y₀ ∈ ψ ⁻¹' C, y₀ ∈ N₂ := by
    have h3 : (closure Λ)ᶜ ⊆ ψ '' closure O₂ := fun z hz => by
      obtain ⟨y, rfl⟩ := hsurj z
      exact ⟨y, subset_closure hz, rfl⟩
    have h4 : x₀ ∈ ψ '' closure O₂ := (hcl _ isClosed_closure).closure_subset_iff.mpr h3 hx₀_out
    obtain ⟨y₀, hy₀_cl, rfl⟩ := h4
    rcases hkey2 hx₀_C with h | h
    · exact absurd hy₀_cl h
    · exact ⟨y₀, hx₀_C, h⟩
  obtain ⟨y₀, hy₀C, hy₀N₂⟩ := hy₀_ex
  have hout : ∀ x ∈ C, x ∈ closure (closure Λ)ᶜ := by
    have himg_cl : ψ '' closure O₂ ⊆ closure (closure Λ)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      have hsub : ψ '' O₂ ⊆ (closure Λ)ᶜ := by
        rintro _ ⟨z, hz, rfl⟩
        exact hz
      exact closure_mono hsub (image_closure_subset_closure_image hc ⟨y, hy, rfl⟩)
    intro x hx
    rcases hsplit with ⟨X, X', -, hXX', hXO, hX'O, hbijX, hbijX'⟩ | hO_pre
    · have hy₀XX' : y₀ ∈ X ∪ X' := hXX'.symm ▸ hy₀C
      rcases hy₀XX' with hy₀X | hy₀X'
      · have hX_sub : X ⊆ N₂ :=
          hXO.isPreconnected.subset_right_of_subset_union hN₁o hN₂o hNd
            (subset_union_left.trans (hXX' ▸ hkey2)) ⟨y₀, hy₀X, hy₀N₂⟩
        obtain ⟨y, hyX, rfl⟩ := hbijX.surjOn hx
        exact himg_cl ⟨y, hN₂_cl (hX_sub hyX), rfl⟩
      · have hX'_sub : X' ⊆ N₂ :=
          hX'O.isPreconnected.subset_right_of_subset_union hN₁o hN₂o hNd
            (subset_union_right.trans (hXX' ▸ hkey2)) ⟨y₀, hy₀X', hy₀N₂⟩
        obtain ⟨y, hyX', rfl⟩ := hbijX'.surjOn hx
        exact himg_cl ⟨y, hN₂_cl (hX'_sub hyX'), rfl⟩
    · have hpre_sub : ψ ⁻¹' C ⊆ N₂ :=
        hO_pre.isPreconnected.subset_right_of_subset_union hN₁o hN₂o hNd hkey2 ⟨y₀, hy₀C, hy₀N₂⟩
      obtain ⟨y, rfl⟩ := hsurj x
      exact himg_cl ⟨y, hN₂_cl (hpre_sub hx), rfl⟩
  exact ⟨hout, closure_disc hS hΛ hbd hF hout⟩

/-- In a 2-cell drawing `H` in a closed connected surface `S` with a respectful tangle `T` of
order `θ ≥ 3`, every region `Λ ∈ H.R` whose boundary `subBd Λ` is an `O`-arc has
`(closure Λ)ᶜ.Nonempty`. -/
theorem compl_closure_nonempty_of_region_tangle [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 3 ≤ θ)
    {Λ : Set S} (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ)) :
    (closure Λ)ᶜ.Nonempty := by
  classical
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_contra hcompl
  have hcl_univ : closure Λ = univ := compl_empty_iff.mp (not_nonempty_iff_eq_empty.mp hcompl)
  have hΛo : IsOpen Λ := GM11.region_isOpen hΛ
  have hsubBd_eq : subBd Λ = closure Λ \ Λ := by
    rw [subBd_eq_frontier, hΛo.frontier_eq]
  have hHU_eq : H.U = subBd Λ := by
    apply subset_antisymm
    · intro x hx
      rw [hsubBd_eq, hcl_univ]
      exact ⟨mem_univ x, fun hxΛ => GM11.region_subset hΛ hxΛ hx⟩
    · intro x hx
      rw [hsubBd_eq] at hx
      by_contra hxU
      obtain ⟨r, hr, hxr⟩ := GM11.exists_region_of_notMem hxU
      obtain ⟨y, hyr, hyΛ⟩ := mem_closure_iff.mp hx.1 r (GM11.region_isOpen hr) hxr
      have hrΛ := GM11.region_eq_of_mem hr hΛ hyr hyΛ
      exact hx.2 (hrΛ ▸ hxr)
  have hall_R : ∀ r ∈ H.R, r = Λ := fun r hr => by
    obtain ⟨x, hxr⟩ := GM11.region_nonempty hr
    have hxcl : x ∈ closure Λ := hcl_univ ▸ mem_univ x
    obtain ⟨y, hyr, hyΛ⟩ := mem_closure_iff.mp hxcl r (GM11.region_isOpen hr) hxr
    exact GM11.region_eq_of_mem hr hΛ hyr hyΛ
  obtain ⟨K, hK⟩ := GM11.exists_radialDrawing hS hT.1
  have hpre : GM11.PreRad (PaintingOrDrawing.drawing H) K := ⟨hK.1, hK.2.1⟩
  have hmax : GM11.RadMax (PaintingOrDrawing.drawing H) K := hK.2.2
  obtain ⟨ins, hins⟩ := exists_derivedSlope hT hK.2.1
  have hE : H.E.Nonempty := edges_nonempty_of_tangle hS hT (by omega)
  have hpretangle : GM11.IsPretangle H.toHypergraph θ T :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt, hT.2.1.axiom1, hT.2.1.axiom2⟩
  have heven : IsEvenSlope K (2 * θ) ins :=
    (GM11.theorem_6_5_proof hS hE hpretangle hT.2.2 hK hins).1 hT.2.1
  obtain ⟨c₀, ⟨hc₀Λ, hc₀V⟩, -⟩ := hK.2.1.2.2.1 Λ hΛ
  have hKV_diff : K.V \ H.V ⊆ {c₀} := by
    rintro w ⟨hwV, hwn⟩
    obtain ⟨r, hr, hwr⟩ := hK.2.1.2.2.2.1 w ⟨hwV, hwn⟩
    rw [hall_R r hr] at hwr
    exact mem_singleton_iff.mpr (GM11.hub_unique hpre hΛ hc₀Λ hc₀V hwr hwV)
  obtain ⟨e₀, he₀⟩ := id hE
  obtain ⟨p₀, hp₀⟩ := he₀.1
  have hp₀K : p₀ ∉ K.U :=
    disjoint_left.mp (GM11.edge_disjoint hpre he₀) hp₀
  obtain ⟨s, hs, hp₀s⟩ := exists_region_of_notMem hp₀K
  have he₀s : e₀ ⊆ s :=
    subset_region hs he₀.2.2.1.isConnected.isPreconnected (GM11.edge_disjoint hpre he₀) hp₀ hp₀s
  have hperim : GM11.perimeterLength K s < 2 * θ :=
    (GM11.perimeterLength_le_four hpre hS hmax hE hs).trans_lt (by omega)
  obtain ⟨C_s, hCs_circ, hCs_sub, hCs_len, hs_sub⟩ := heven s hs hperim
  obtain ⟨hΔ_disc, hΔ_bd, hΔ_mem⟩ := hins C_s hCs_circ hCs_sub hCs_len
  have hbip := GM11.bipartite_of_preRadial hK.2.1
  have hbC : ∀ e x y, C_s.toGraph.IsLink e x y → (x ∈ K.V \ H.V ↔ y ∉ K.V \ H.V) := by
    intro e x y hl
    have hlinkK : K.toGraph.IsLink e x y := by
      refine ⟨hCs_sub.2 hl.1, hCs_sub.1 hl.2.1, hCs_sub.1 hl.2.2.1, ?_⟩
      rw [← hCs_sub.closure_inter_V hl.1]
      exact hl.2.2.2
    have hxy := hbip e x y hlinkK
    have hxK : x ∈ K.V := hCs_sub.1 hl.2.1
    have hyK : y ∈ K.V := hCs_sub.1 hl.2.2.1
    simp only [mem_sdiff, hxK, hyK, true_and]
    tauto
  obtain ⟨u₀, W, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := id hCs_circ
  have hlenW : C_s.length = W.length := by
    rw [Drawing.length, hCE]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup hed]
    rfl
  have hcW := GM11.two_mul_count_le (K.V \ H.V) hbC W
  have htail_sub : ((W.support.tail.filter (· ∈ K.V \ H.V)).toFinset : Set S) ⊆ {c₀} := by
    intro x hx
    have hx' : x ∈ W.support.tail ∧ x ∈ K.V \ H.V := by simpa using hx
    exact hKV_diff hx'.2
  have hcount_le : W.support.tail.countP (· ∈ K.V \ H.V) ≤ 1 := by
    have hf : (W.support.tail.filter (· ∈ K.V \ H.V)).Nodup := hnd.filter _
    have hle := ncard_le_ncard htail_sub (finite_singleton c₀)
    rw [ncard_coe_finset, List.toFinset_card_of_nodup hf, ← List.countP_eq_length_filter,
      ncard_singleton] at hle
    exact hle
  obtain ⟨_, _, hcard2⟩ := circuit_props_of_preRadial hK.2.1 hCs_circ hCs_sub
  have hcard_HV : (C_s.U ∩ H.V).ncard ≤ 1 := by omega
  have hinter_eq : C_s.U ∩ subBd Λ = C_s.U ∩ H.V := by
    rw [← hHU_eq]
    ext x
    constructor
    · rintro ⟨hxC, hxH⟩
      have : x ∈ (PaintingOrDrawing.drawing H).U ∩ K.U := ⟨hxH, hCs_sub.U_subset hxC⟩
      rw [hK.2.1.1] at this
      exact ⟨hxC, this⟩
    · rintro ⟨hxC, hxV⟩
      exact ⟨hxC, H.V_subset_U hxV⟩
  have hcard_bd : (C_s.U ∩ subBd Λ).ncard ≤ 1 := by
    rw [hinter_eq]
    exact hcard_HV
  have hfin_bd : (C_s.U ∩ subBd Λ).Finite := by
    rw [hinter_eq]
    exact H.finite_V.subset inter_subset_right
  have hconn_sdiff : IsPreconnected (subBd Λ \ C_s.U) :=
    IsOArc.isPreconnected_sdiff_of_ncard_le_one hOArc hfin_bd hcard_bd
  have hfr_ins : frontier (ins C_s) = C_s.U := by
    rw [← subBd_eq_frontier, hΔ_bd]
  have hdis_fr : Disjoint (subBd Λ \ C_s.U) (frontier (ins C_s)) := by
    rw [hfr_ins]
    exact disjoint_sdiff_left
  have hp₀_sdiff : p₀ ∈ subBd Λ \ C_s.U :=
    ⟨hHU_eq ▸ (he₀.2.1 hp₀).1, fun h => hp₀K (hCs_sub.U_subset h)⟩
  have hp₀_ins : p₀ ∈ ins C_s := hs_sub (he₀s hp₀)
  have hsub_ins : subBd Λ \ C_s.U ⊆ ins C_s :=
    (GM11.subset_or_disjoint_of_frontier hΔ_disc.isCompact.isClosed hconn_sdiff
      hdis_fr).resolve_right
      fun hd => disjoint_left.mp hd hp₀_sdiff hp₀_ins
  have hHU_sub_ins : H.U ⊆ ins C_s := by
    rw [hHU_eq]
    intro x hx
    by_cases hxC : x ∈ C_s.U
    · rw [← hfr_ins] at hxC
      exact hΔ_disc.isCompact.isClosed.frontier_subset hxC
    · exact hsub_ins ⟨hx, hxC⟩
  refine hT.2.1.axiom2 hΔ_mem hΔ_mem hΔ_mem (Hypergraph.ext ?_ ?_ ?_) |>.elim
  · ext v
    exact ⟨by rintro ((h | h) | h) <;> exact h.1,
      fun hv => Or.inl (Or.inl ⟨hv, hHU_sub_ins (H.V_subset_U hv)⟩)⟩
  · ext e
    exact ⟨by rintro ((h | h) | h) <;> exact h.1,
      fun he => Or.inl (Or.inl ⟨he, fun x hx => hHU_sub_ins ((he.2.1 hx).1)⟩)⟩
  · funext e v
    apply propext
    exact ⟨by rintro ((h | h) | h) <;> exact h.1,
      fun hi => Or.inl (Or.inl ⟨hi,
        fun x hx => hHU_sub_ins ((hi.1.2.1 hx).1),
        hHU_sub_ins (H.V_subset_U hi.2.1)⟩)⟩

/-- In a 2-cell drawing `H` in a closed connected surface `S` with a respectful tangle `T` of
order `θ ≥ 3`, the closure `closure Λ` of any region `Λ ∈ H.R` whose boundary `subBd Λ` is an
`O`-arc is a closed disc with boundary `subBd Λ` and interior `Λ`. -/
theorem isClosedDisc_closure_of_region_tangle [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 3 ≤ θ)
    {Λ : Set S} (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ)) :
    (∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) ∧
      IsClosedDisc (closure Λ) ∧ discBd (closure Λ) = subBd Λ ∧
      subBd (closure Λ) = subBd Λ ∧ discInt (closure Λ) = Λ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hS_surf : IsSurface S := IsClosedSurface.isSurface hS
  have hbd_empty : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS.2.2 x)
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  have hΛ_disc : IsOpenDisc Λ := hT.1.2 Λ hΛ
  have hsubBd_eq : closure Λ \ Λ = subBd Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  have hbd_disj : Disjoint (closure Λ) (bd S) := by
    rw [hbd_empty]
    exact disjoint_empty _
  have hcompl := compl_closure_nonempty_of_region_tangle hS hT hθ hΛ hOArc
  obtain ⟨hout, hCD, hdiscBd⟩ :=
    closure_disc_of_compl_nonempty hS_surf hΛ_disc hbd_disj (hsubBd_eq ▸ hOArc) hcompl
  rw [hsubBd_eq] at hdiscBd
  have hsubBd_cl : subBd (closure Λ) = subBd Λ := by
    rw [subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hCD, hdiscBd]
  have hdiscInt : discInt (closure Λ) = Λ := by
    rw [discInt, hdiscBd, ← hsubBd_eq]
    ext x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨subset_closure hx, fun _ => hx⟩⟩
  exact ⟨hout, hCD, hdiscBd, hsubBd_cl, hdiscInt⟩

private lemma isManifoldPoint_of_open_nhd {A B U : Set S} (hU : IsOpen U)
    (hUA : A ∩ U = B ∩ U) {x : ↥A} (hxU : x.1 ∈ U) (hxB : x.1 ∈ B)
    (hm : IsManifoldPoint (⟨x.1, hxB⟩ : ↥B)) : IsManifoldPoint x := by
  have hUA' : IsOpen (Subtype.val ⁻¹' U : Set ↥A) := hU.preimage continuous_subtype_val
  have hUB' : IsOpen (Subtype.val ⁻¹' U : Set ↥B) := hU.preimage continuous_subtype_val
  let e : ↥(Subtype.val ⁻¹' U : Set ↥A) ≃ₜ ↥(Subtype.val ⁻¹' U : Set ↥B) :=
    { toFun := fun z => ⟨⟨z.1.1, ((Set.ext_iff.mp hUA z.1.1).mp ⟨z.1.2, z.2⟩).1⟩, z.2⟩
      invFun := fun z => ⟨⟨z.1.1, ((Set.ext_iff.mp hUA z.1.1).mpr ⟨z.1.2, z.2⟩).1⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := Continuous.subtype_mk
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
      continuous_invFun := Continuous.subtype_mk
        (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _ }
  have h1 : IsManifoldPoint (⟨⟨x.1, hxB⟩, hxU⟩ : ↥(Subtype.val ⁻¹' U : Set ↥B)) :=
    isManifoldPoint_sub hUB' hm
  have h2 : IsManifoldPoint (⟨x, hxU⟩ : ↥(Subtype.val ⁻¹' U : Set ↥A)) :=
    (isManifoldPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mp h1
  exact isManifoldPoint_of_isOpenEmbedding hUA'.isOpenEmbedding_subtypeVal h2

/-- Removing an open set `Λ` with `IsOArc (subBd Λ)` and `∀ x ∈ closure Λ \ Λ, x ∈ closure (closure
Λ)ᶜ`
from a closed connected surface `S` gives a connected surface `↥(univ \ Λ)` with boundary
`Subtype.val ⁻¹' subBd Λ`, which is an `O`-arc. -/
theorem compl_open_isSurface [ConnectedSpace S] (hS : IsClosedSurface S)
    {Λ : Set S} (hΛ_open : IsOpen Λ) (hOArc : IsOArc (subBd Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) :
    IsSurface ↥(univ \ Λ : Set S) ∧ ConnectedSpace ↥(univ \ Λ : Set S) ∧
      bd ↥(univ \ Λ : Set S) = Subtype.val ⁻¹' subBd Λ ∧
      IsOArc (bd ↥(univ \ Λ : Set S)) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hS_surf : IsSurface S := IsClosedSurface.isSurface hS
  have hbd_empty : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS.2.2 x)
  have hsubBd_eq : closure Λ \ Λ = subBd Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  have hsurf_compl : IsSurface ↥(Λᶜ : Set S) :=
    compl_surface hS_surf hbd_empty hΛ_open (hsubBd_eq.symm ▸ hOArc) hout
  have hset_eq : (Λᶜ : Set S) = univ \ Λ := compl_eq_univ_sdiff Λ
  let e : ↥(Λᶜ : Set S) ≃ₜ ↥(univ \ Λ : Set S) := Homeomorph.setCongr hset_eq
  have hsurf : IsSurface ↥(univ \ Λ : Set S) := isSurface_of_homeo e hsurf_compl
  have hbd : bd ↥(univ \ Λ : Set S) = Subtype.val ⁻¹' subBd Λ := by
    ext x
    have hx := bd_subset_iff hS.2.2 x
    have hcompl_eq : (univ \ Λ : Set S)ᶜ = Λ := by
      ext z; simp
    rw [hx, hcompl_eq, mem_preimage, ← hsubBd_eq]
    exact ⟨fun h => ⟨h, x.2.2⟩, fun h => h.1⟩
  have hval : IsEmbedding (Subtype.val : ↥(univ \ Λ : Set S) → S) := IsEmbedding.subtypeVal
  have himg_bd : Subtype.val '' bd ↥(univ \ Λ : Set S) = subBd Λ := by
    rw [hbd, Subtype.image_preimage_coe]
    refine inter_eq_right.mpr fun x hx => ⟨mem_univ x, ?_⟩
    have hx' : x ∈ closure Λ \ Λ := hsubBd_eq.symm ▸ hx
    exact hx'.2
  have hOArc_bd : IsOArc (bd ↥(univ \ Λ : Set S)) :=
    isOArc_of_image hval (himg_bd ▸ hOArc)
  obtain ⟨φ⟩ := id hOArc
  have hmeet : closure Λ ∩ (univ \ Λ) = subBd Λ := by
    rw [← hsubBd_eq]
    ext z
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, mem_univ z, h2⟩⟩
  have hφ_not_Λ : (φ 1).1 ∉ Λ := by
    have hmem : (φ 1).1 ∈ closure Λ \ Λ := hsubBd_eq.symm ▸ (φ 1).2
    exact hmem.2
  have hconn : ConnectedSpace ↥(univ \ Λ : Set S) := by
    refine connected_compl (isClosed_univ.sdiff hΛ_open) ⟨(φ 1).1, mem_univ _, hφ_not_Λ⟩
      (𝓖 := {closure Λ}) (by simp) ?_ ?_ ?_ ?_ ?_
    · rintro G rfl
      exact isClosed_closure
    · rintro G rfl
      rw [hmeet]
      exact hOArc.isPreconnected
    · rintro G rfl
      rw [hmeet]
      exact ⟨(φ 1).1, (φ 1).2⟩
    · rintro G rfl G' rfl hne
      exact absurd rfl hne
    · rw [eq_univ_iff_forall]
      intro z
      by_cases hz : z ∈ Λ
      · exact Or.inr ⟨closure Λ, mem_singleton _, subset_closure hz⟩
      · exact Or.inl ⟨mem_univ z, hz⟩
  exact ⟨hsurf, hconn, hbd, hOArc_bd⟩

/-- Removing one region `Λ ∈ H.R` with `IsOArc (subBd Λ)` from `S` gives a connected surface
`↥(univ \ Λ)` with boundary `Subtype.val ⁻¹' subBd Λ`, which is an `O`-arc. -/
theorem compl_region_isSurface [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 3 ≤ θ)
    {Λ : Set S} (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ)) :
    IsSurface ↥(univ \ Λ : Set S) ∧ ConnectedSpace ↥(univ \ Λ : Set S) ∧
      bd ↥(univ \ Λ : Set S) = Subtype.val ⁻¹' subBd Λ ∧
      IsOArc (bd ↥(univ \ Λ : Set S)) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hout, _, _, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hT hθ hΛ hOArc
  exact compl_open_isSurface hS (GM11.region_isOpen hΛ) hOArc hout

/-- Removing two open sets `Λ₁, Λ₂` with disjoint closures and `O`-arc boundaries from `S`
gives a connected surface `↥(univ \ (Λ₁ ∪ Λ₂))` with boundary
`Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂)`. -/
theorem compl_two_open_isSurface [ConnectedSpace S] (hS : IsClosedSurface S)
    {Λ₁ Λ₂ : Set S} (hΛ₁_open : IsOpen Λ₁) (hΛ₂_open : IsOpen Λ₂)
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    (hdisj_cl : Disjoint (closure Λ₁) (closure Λ₂)) :
    IsSurface ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ∧
      ConnectedSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ∧
      bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) = Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hsurf₁, _, _, _⟩ := compl_open_isSurface hS hΛ₁_open hOArc₁ hout₁
  obtain ⟨hsurf₂, _, _, _⟩ := compl_open_isSurface hS hΛ₂_open hOArc₂ hout₂
  have hsubBd₁_eq : closure Λ₁ \ Λ₁ = subBd Λ₁ := by
    rw [subBd_eq_frontier, hΛ₁_open.frontier_eq]
  have hsubBd₂_eq : closure Λ₂ \ Λ₂ = subBd Λ₂ := by
    rw [subBd_eq_frontier, hΛ₂_open.frontier_eq]
  have hcl₁₂ : IsClosed (univ \ (Λ₁ ∪ Λ₂) : Set S) :=
    isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open)
  have hsurf : IsSurface ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) := by
    refine ⟨isCompact_iff_compactSpace.mp hcl₁₂.isCompact, inferInstance, fun x => ?_⟩
    by_cases hx₂ : x.1 ∈ closure Λ₂
    · have hx₁ : x.1 ∈ (closure Λ₁)ᶜ :=
        fun h1 => disjoint_left.mp hdisj_cl h1 hx₂
      have hxB₂ : x.1 ∈ (univ \ Λ₂ : Set S) := ⟨mem_univ _, fun h => x.2.2 (Or.inr h)⟩
      refine isManifoldPoint_of_open_nhd isClosed_closure.isOpen_compl ?_ hx₁ hxB₂ (hsurf₂.2.2 _)
      ext z
      exact ⟨fun ⟨⟨_, hz⟩, hzc⟩ => ⟨⟨mem_univ z, fun h => hz (Or.inr h)⟩, hzc⟩,
        fun ⟨⟨_, hz⟩, hzc⟩ => ⟨⟨mem_univ z, fun h => h.elim (fun h1 => hzc
          (subset_closure h1)) hz⟩, hzc⟩⟩
    · have hxB₁ : x.1 ∈ (univ \ Λ₁ : Set S) := ⟨mem_univ _, fun h => x.2.2 (Or.inl h)⟩
      refine isManifoldPoint_of_open_nhd isClosed_closure.isOpen_compl ?_ hx₂ hxB₁ (hsurf₁.2.2 _)
      ext z
      exact ⟨fun ⟨⟨_, hz⟩, hzc⟩ => ⟨⟨mem_univ z, fun h => hz (Or.inl h)⟩, hzc⟩,
        fun ⟨⟨_, hz⟩, hzc⟩ => ⟨⟨mem_univ z, fun h => h.elim hz (fun h2 => hzc
          (subset_closure h2))⟩, hzc⟩⟩
  have hbd : bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) = Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂) := by
    ext x
    have hx := bd_subset_iff hS.2.2 x
    have hcompl_eq : (univ \ (Λ₁ ∪ Λ₂) : Set S)ᶜ = Λ₁ ∪ Λ₂ := by
      rw [← compl_eq_univ_sdiff, compl_compl]
    rw [hx, hcompl_eq, closure_union, mem_preimage, mem_union, ← hsubBd₁_eq, ← hsubBd₂_eq]
    exact ⟨fun h => h.imp (fun h1 => ⟨h1, fun h' => x.2.2 (Or.inl h')⟩)
        (fun h2 => ⟨h2, fun h' => x.2.2 (Or.inr h')⟩),
      fun h => h.imp And.left And.left⟩
  obtain ⟨φ₁⟩ := id hOArc₁
  obtain ⟨φ₂⟩ := id hOArc₂
  have hmeet₁ : closure Λ₁ ∩ (univ \ (Λ₁ ∪ Λ₂)) = subBd Λ₁ := by
    rw [← hsubBd₁_eq]
    ext z
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, fun h => h2 (Or.inl h)⟩,
      fun ⟨h1, h2⟩ => ⟨h1, mem_univ z, fun h =>
        h.elim h2 fun h' => disjoint_left.mp hdisj_cl h1 (subset_closure h')⟩⟩
  have hmeet₂ : closure Λ₂ ∩ (univ \ (Λ₁ ∪ Λ₂)) = subBd Λ₂ := by
    rw [← hsubBd₂_eq]
    ext z
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, fun h => h2 (Or.inr h)⟩,
      fun ⟨h1, h2⟩ => ⟨h1, mem_univ z, fun h =>
        h.elim (fun h' => disjoint_left.mp hdisj_cl (subset_closure h') h1) h2⟩⟩
  have hconn : ConnectedSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) := by
    have hmem₁ : (φ₁ 1).1 ∈ closure Λ₁ ∩ (univ \ (Λ₁ ∪ Λ₂)) := by
      rw [hmeet₁]
      exact (φ₁ 1).2
    refine connected_compl (isClosed_univ.sdiff (hΛ₁_open.union hΛ₂_open))
      ⟨(φ₁ 1).1, hmem₁.2⟩ (𝓖 := {closure Λ₁, closure Λ₂}) (by simp) ?_ ?_ ?_ ?_ ?_
    · rintro G (rfl | rfl) <;> exact isClosed_closure
    · rintro G (rfl | rfl)
      · rw [hmeet₁]; exact hOArc₁.isPreconnected
      · rw [hmeet₂]; exact hOArc₂.isPreconnected
    · rintro G (rfl | rfl)
      · rw [hmeet₁]; exact ⟨(φ₁ 1).1, (φ₁ 1).2⟩
      · rw [hmeet₂]; exact ⟨(φ₂ 1).1, (φ₂ 1).2⟩
    · rintro G (rfl | rfl) G' (rfl | rfl) hne
      · exact absurd rfl hne
      · exact hdisj_cl
      · exact hdisj_cl.symm
      · exact absurd rfl hne
    · rw [eq_univ_iff_forall]
      intro z
      by_cases h1 : z ∈ Λ₁
      · exact Or.inr ⟨closure Λ₁, Or.inl rfl, subset_closure h1⟩
      · by_cases h2 : z ∈ Λ₂
        · exact Or.inr ⟨closure Λ₂, Or.inr rfl, subset_closure h2⟩
        · exact Or.inl ⟨mem_univ z, fun h => h.elim h1 h2⟩
  exact ⟨hsurf, hconn, hbd⟩

/-- Removing two regions `Λ₁, Λ₂ ∈ H.R` with disjoint closures and `O`-arc boundaries from `S`
gives a connected surface `↥(univ \ (Λ₁ ∪ Λ₂))` with boundary
`Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂)`. -/
theorem compl_two_regions_isSurface [ConnectedSpace S] (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsRespectfulDrawingTangle H θ T) (hθ : 3 ≤ θ)
    {Λ₁ Λ₂ : Set S} (hΛ₁ : Λ₁ ∈ H.R) (hΛ₂ : Λ₂ ∈ H.R)
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hdisj_cl : Disjoint (closure Λ₁) (closure Λ₂)) :
    IsSurface ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ∧
      ConnectedSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ∧
      bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) = Subtype.val ⁻¹' (subBd Λ₁ ∪ subBd Λ₂) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hout₁, _, _, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hT hθ hΛ₁ hOArc₁
  obtain ⟨hout₂, _, _, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hT hθ hΛ₂ hOArc₂
  exact compl_two_open_isSurface hS (GM11.region_isOpen hΛ₁) (GM11.region_isOpen hΛ₂)
    hOArc₁ hOArc₂ hout₁ hout₂ hdisj_cl

/-- For any region `Λ ∈ H.R` whose boundary `subBd Λ` is an `O`-arc, `H.interSet (subBd Λ)` is a
circuit of `H` with `(H.interSet (subBd Λ)).U = subBd Λ` and
`(H.interSet (subBd Λ)).V = H.V ∩ subBd Λ`. -/
theorem interSet_subBd_isCircuit_and_U_eq [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {Λ : Set S}
    (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ)) :
    (H.interSet (subBd Λ)).IsCircuit ∧
      (H.interSet (subBd Λ)).U = subBd Λ ∧
      (H.interSet (subBd Λ)).V = H.V ∩ subBd Λ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hSubBd_U : subBd Λ ⊆ H.U := by
    intro z hz
    by_contra hz_not_U
    obtain ⟨r, hr, hzr⟩ := GM11.exists_region_of_notMem hz_not_U
    obtain ⟨w, hwr, hwΛ⟩ := mem_closure_iff.mp hz.1 r (GM11.region_isOpen hr) hzr
    have hrΛ : r = Λ := GM11.region_eq_of_mem hr hΛ hwr hwΛ
    have hzΛ : z ∈ Λ := hrΛ ▸ hzr
    have hz_fr : z ∈ frontier Λ := subBd_eq_frontier Λ ▸ hz
    exact ((GM11.region_isOpen hΛ).interior_eq ▸ hz_fr.2) hzΛ
  have hcl_bd : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
  obtain ⟨C_bd, hC_bd, hCH_bd, hCU_bd⟩ := exists_circuit_of_oArc hOArc hSubBd_U
  have hEq_C : H.interSet (subBd Λ) = C_bd := by
    refine Drawing.ext_of_V_E ?_ ?_
    · rw [interSet_V_of_isClosed H hcl_bd]
      ext x
      simp only [mem_inter_iff]
      refine ⟨fun ⟨hxV, hxbd⟩ => ?_, fun hxC => ⟨hCH_bd.1 hxC, hCU_bd ▸ C_bd.V_subset_U hxC⟩⟩
      by_contra hxnot
      obtain ⟨e, heC, hxe⟩ := C_bd.exists_edge_of_mem (hCU_bd.symm ▸ hxbd) hxnot
      exact ((hCH_bd.2 heC).2.1 hxe).2 hxV
    · rw [interSet_E H]
      ext e
      simp only [mem_ofPred_eq]
      refine ⟨fun ⟨heH, hebd⟩ => ?_,
        fun heC => ⟨hCH_bd.2 heC, hCU_bd ▸ subset_closure.trans (C_bd.closure_subset_U heC)⟩⟩
      obtain ⟨x, hxe⟩ := heH.1
      have hxnotV : x ∉ C_bd.V := fun hxC => (heH.2.1 hxe).2 (hCH_bd.1 hxC)
      obtain ⟨f, hfC, hxf⟩ := C_bd.exists_edge_of_mem (hCU_bd.symm ▸ hebd hxe) hxnotV
      have hef : e = f :=
        atom_eq_of_mem (Or.inl (Or.inr heH)) (Or.inl (Or.inr (hCH_bd.2 hfC))) hxe hxf
      exact hef ▸ hfC
  exact ⟨hEq_C ▸ hC_bd, hEq_C ▸ hCU_bd, interSet_V_of_isClosed H hcl_bd⟩

/-- In Graph Minors XV, (3.5), if `Λ₁, Λ₂ ∈ H.R` are distinct regions with `O`-arc boundaries,
`H.V ∩ subBd Λ₁` is nonempty, and no region of `H` has closure meeting both `H.V ∩ subBd Λ₁` and
`H.V ∩ subBd Λ₂`, then `Disjoint (closure Λ₁) (closure Λ₂)`. -/
theorem disjoint_closure_of_no_common_region [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {Λ₁ Λ₂ : Set S}
    (hΛ₁ : Λ₁ ∈ H.R) (hΛ₂ : Λ₂ ∈ H.R) (hne : Λ₁ ≠ Λ₂)
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hne_V₁ : (H.V ∩ subBd Λ₁).Nonempty)
    (hNo_common_region : ∀ r ∈ H.R, (closure r ∩ (H.V ∩ subBd Λ₁)).Nonempty →
      Disjoint (closure r) (H.V ∩ subBd Λ₂)) :
    Disjoint (closure Λ₁) (closure Λ₂) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hΛ₁_open : IsOpen Λ₁ := GM11.region_isOpen hΛ₁
  have hΛ₂_open : IsOpen Λ₂ := GM11.region_isOpen hΛ₂
  have hdisj_reg : Disjoint Λ₁ Λ₂ := by
    rw [disjoint_iff_inter_eq_empty]
    by_contra h
    obtain ⟨w, hw₁, hw₂⟩ := nonempty_iff_ne_empty.mpr h
    exact hne (GM11.region_eq_of_mem hΛ₁ hΛ₂ hw₁ hw₂)
  obtain ⟨v₁, hv₁V, hv₁_bd⟩ := hne_V₁
  have hdisj_cl₁_V₂ : Disjoint (closure Λ₁) (H.V ∩ subBd Λ₂) :=
    hNo_common_region Λ₁ hΛ₁ ⟨v₁, hv₁_bd.1, hv₁V, hv₁_bd⟩
  obtain ⟨_, hU₁, hV₁⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ₁ hOArc₁
  obtain ⟨hC₂, hU₂, hV₂⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ₂ hOArc₂
  rw [disjoint_left]
  intro z hz₁ hz₂
  have hz_not_Λ₁ : z ∉ Λ₁ :=
    fun h => disjoint_left.mp (hdisj_reg.closure_right hΛ₁_open) h hz₂
  have hz_not_Λ₂ : z ∉ Λ₂ :=
    fun h => disjoint_right.mp (hdisj_reg.closure_left hΛ₂_open) h hz₁
  have hz_bd₁ : z ∈ subBd Λ₁ := by
    rw [subBd_eq_frontier, hΛ₁_open.frontier_eq]
    exact ⟨hz₁, hz_not_Λ₁⟩
  have hz_bd₂ : z ∈ subBd Λ₂ := by
    rw [subBd_eq_frontier, hΛ₂_open.frontier_eq]
    exact ⟨hz₂, hz_not_Λ₂⟩
  by_cases hzV : z ∈ H.V
  · exact disjoint_left.mp hdisj_cl₁_V₂ hz₁ ⟨hzV, hz_bd₂⟩
  · have hz_not_V₁ : z ∉ (H.interSet (subBd Λ₁)).V := fun h => hzV (hV₁ ▸ h).1
    have hz_not_V₂ : z ∉ (H.interSet (subBd Λ₂)).V := fun h => hzV (hV₂ ▸ h).1
    obtain ⟨e₁, he₁, hze₁⟩ := (H.interSet (subBd Λ₁)).exists_edge_of_mem
      (hU₁.symm ▸ hz_bd₁) hz_not_V₁
    obtain ⟨e₂, he₂, hze₂⟩ := (H.interSet (subBd Λ₂)).exists_edge_of_mem
      (hU₂.symm ▸ hz_bd₂) hz_not_V₂
    rw [interSet_E H] at he₁ he₂
    have he_eq : e₁ = e₂ :=
      atom_eq_of_mem (Or.inl (Or.inr he₁.1)) (Or.inl (Or.inr he₂.1)) hze₁ hze₂
    obtain ⟨u, W, _, _, hCV, hCE⟩ := hC₂
    have he₂_W : e₂ ∈ W.edges := by
      have h : e₂ ∈ (H.interSet (subBd Λ₂)).E := (interSet_E H (subBd Λ₂)).symm ▸ he₂
      rwa [hCE] at h
    have hex_end : ∀ {a b : S} (W' : GraphWalk (H.interSet (subBd Λ₂)).toGraph a b),
        e₂ ∈ W'.edges → ∃ w ∈ W'.support, w ∈ closure e₂ := by
      intro a b W' hmem
      induction W' with
      | nil _ => simp [GraphWalk.edges] at hmem
      | @cons a y b e hl r ih =>
        rcases List.mem_cons.mp hmem with rfl | hmem
        · refine ⟨a, (GraphWalk.cons hl r).start_mem_support, ?_⟩
          have ha_mem : a ∈ closure e₂ ∩ (H.interSet (subBd Λ₂)).V := by
            rw [hl.2.2.2]
            exact mem_insert a {y}
          exact ha_mem.1
        · obtain ⟨w, hw1, hw2⟩ := ih hmem
          exact ⟨w, List.mem_cons_of_mem _ hw1, hw2⟩
    obtain ⟨w, hw_supp, hw_cl₂⟩ := hex_end W he₂_W
    have hw_cl : w ∈ closure e₁ := he_eq ▸ hw_cl₂
    have hw_V₂ : w ∈ H.V ∩ subBd Λ₂ := by
      rw [← hV₂, hCV]
      exact hw_supp
    have hw_cl₁ : w ∈ closure Λ₁ :=
      isClosed_closure.closure_subset_iff.mpr (he₁.2.trans inter_subset_left) hw_cl
    exact disjoint_left.mp hdisj_cl₁_V₂ hw_cl₁ hw_V₂

/-- Map a cylinder point to the annulus with radius the square root of its first coordinate. -/
noncomputable def cylToAnnulus (p : ClosedCylinder) : EuclideanPlane :=
  Real.sqrt p.1.1 • complexPlane (p.1.2 : ℂ)

theorem continuous_cylToAnnulus : Continuous cylToAnnulus := by
  unfold cylToAnnulus
  fun_prop

theorem norm_cylToAnnulus (p : ClosedCylinder) :
    ‖cylToAnnulus p‖ = Real.sqrt p.1.1 := by
  have hr : 0 ≤ Real.sqrt p.1.1 := Real.sqrt_nonneg _
  simp [cylToAnnulus, norm_smul, abs_of_nonneg hr]

theorem injective_cylToAnnulus : Function.Injective cylToAnnulus := by
  intro p q hpq
  have hnorm : ‖cylToAnnulus p‖ = ‖cylToAnnulus q‖ := congrArg norm hpq
  rw [norm_cylToAnnulus, norm_cylToAnnulus] at hnorm
  have hp1 : 0 ≤ p.1.1 := by linarith [p.2.1.1]
  have hq1 : 0 ≤ q.1.1 := by linarith [q.2.1.1]
  have hr_eq : p.1.1 = q.1.1 := (Real.sqrt_inj hp1 hq1).mp hnorm
  have hpos : Real.sqrt p.1.1 ≠ 0 := by
    have : 0 < p.1.1 := by linarith [p.2.1.1]
    exact Real.sqrt_ne_zero'.mpr this
  have hsmul : Real.sqrt p.1.1 • complexPlane (p.1.2 : ℂ) =
      Real.sqrt p.1.1 • complexPlane (q.1.2 : ℂ) := by
    simpa [cylToAnnulus, hr_eq] using hpq
  have hcp := smul_right_injective EuclideanPlane hpos hsmul
  have hcircle : p.1.2 = q.1.2 := Subtype.ext (complexPlane.injective hcp)
  exact Subtype.ext (Prod.ext hr_eq hcircle)

theorem norm_sq_euclideanPlane (v : EuclideanPlane) :
    ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

theorem range_cylToAnnulus :
    range cylToAnnulus = GM12.ClosedAnnulus := by
  ext v
  simp only [mem_range, GM12.ClosedAnnulus, mem_ofPred_eq, ← norm_sq_euclideanPlane]
  constructor
  · rintro ⟨p, rfl⟩
    rw [norm_cylToAnnulus, Real.sq_sqrt (by linarith [p.2.1.1])]
    exact ⟨p.2.1.1, p.2.1.2⟩
  · rintro ⟨h1, h2⟩
    have hv_pos : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
    have hv_ne : ‖v‖ ≠ 0 := ne_of_gt hv_pos
    let r : ℝ := ‖v‖ ^ 2
    have hr : r ∈ Icc (1 : ℝ) 2 := ⟨h1, h2⟩
    let z : ℂ := complexPlane.symm v / (‖v‖ : ℂ)
    have hz_norm : ‖z‖ = 1 := by simp [z, div_self hv_ne]
    let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz_norm⟩
    refine ⟨⟨(r, u), hr, trivial⟩, ?_⟩
    dsimp [cylToAnnulus, r, u, z]
    rw [Real.sqrt_sq hv_pos.le]
    apply complexPlane.symm.injective
    rw [map_smul, LinearIsometryEquiv.symm_apply_apply, Complex.real_smul]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hv_ne)

/-- `ClosedCylinder` is homeomorphic to `GM12.ClosedAnnulus`. -/
noncomputable def closedCylinderHomeoAnnulus : ClosedCylinder ≃ₜ GM12.ClosedAnnulus :=
  haveI : CompactSpace ClosedCylinder :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_univ)
  (continuous_cylToAnnulus.isClosedEmbedding
    injective_cylToAnnulus).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr range_cylToAnnulus)

/-- The radial pinch factor `1 - (1 / 4) * min 1 (Metric.infDist u S_pts)` on `EuclideanPlane`. -/
noncomputable def pinchScale (S_pts : Set EuclideanPlane) (u : EuclideanPlane) : ℝ :=
  1 - (1 / 4 : ℝ) * min 1 (Metric.infDist u S_pts)

/-- The unit direction vector `‖x‖⁻¹ • x` (equal to `0` at `x = 0`). -/
noncomputable def unitDir (x : EuclideanPlane) : EuclideanPlane :=
  ‖x‖⁻¹ • x

theorem pinchScale_bounds (S_pts : Set EuclideanPlane) (u : EuclideanPlane) :
    3 / 4 ≤ pinchScale S_pts u ∧ pinchScale S_pts u ≤ 1 := by
  have hmin_nonneg : 0 ≤ min 1 (Metric.infDist u S_pts) :=
    le_min zero_le_one Metric.infDist_nonneg
  have hmin_le : min 1 (Metric.infDist u S_pts) ≤ 1 := min_le_left 1 _
  unfold pinchScale
  constructor <;> linarith

theorem pinchScale_pos (S_pts : Set EuclideanPlane) (u : EuclideanPlane) :
    0 < pinchScale S_pts u := by
  linarith [(pinchScale_bounds S_pts u).1]

theorem continuous_pinchScale (S_pts : Set EuclideanPlane) :
    Continuous (pinchScale S_pts) := by
  unfold pinchScale
  exact continuous_const.sub (continuous_const.mul (continuous_const.min
    (Metric.continuous_infDist_pt S_pts)))

theorem unitDir_smul {c : ℝ} (hc : 0 < c) (x : EuclideanPlane) :
    unitDir (c • x) = unitDir x := by
  simp only [unitDir, norm_smul, Real.norm_of_nonneg hc.le, mul_inv_rev, ← mul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

theorem unitDir_of_mem_unitCircle {u : EuclideanPlane} (hu : u ∈ UnitCircle) :
    unitDir u = u := by
  have hnorm : ‖u‖ = 1 := by simpa [UnitCircle] using hu
  simp [unitDir, hnorm]

theorem norm_unitDir {x : EuclideanPlane} (hx : x ≠ 0) :
    ‖unitDir x‖ = 1 := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp [unitDir, norm_smul, inv_mul_cancel₀ hpos.ne']

theorem unitDir_mem_unitCircle {x : EuclideanPlane} (hx : ‖x‖ ≠ 0) :
    unitDir x ∈ UnitCircle := by
  simpa [UnitCircle] using norm_unitDir (norm_ne_zero_iff.mp hx)

theorem norm_smul_unitDir (x : EuclideanPlane) :
    ‖x‖ • unitDir x = x := by
  by_cases hx : ‖x‖ = 0
  · simp [norm_eq_zero.mp hx]
  · simp [unitDir, smul_smul, mul_inv_cancel₀ hx]

theorem continuousAt_unitDir {x : EuclideanPlane} (hx : x ≠ 0) :
    ContinuousAt unitDir x :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

/-- The radial pinch map `x ↦ pinchScale S_pts (unitDir x) • x`. -/
noncomputable def pinchMap (S_pts : Set EuclideanPlane) (x : EuclideanPlane) : EuclideanPlane :=
  pinchScale S_pts (unitDir x) • x

/-- The inverse radial unpinch map `y ↦ (pinchScale S_pts (unitDir y))⁻¹ • y`. -/
noncomputable def unpinchMap (S_pts : Set EuclideanPlane) (y : EuclideanPlane) : EuclideanPlane :=
  (pinchScale S_pts (unitDir y))⁻¹ • y

theorem unpinchMap_pinchMap (S_pts : Set EuclideanPlane) (x : EuclideanPlane) :
    unpinchMap S_pts (pinchMap S_pts x) = x := by
  have hc : 0 < pinchScale S_pts (unitDir x) := pinchScale_pos S_pts (unitDir x)
  simp only [pinchMap, unpinchMap, unitDir_smul hc]
  exact inv_smul_smul₀ hc.ne' x

theorem pinchMap_unpinchMap (S_pts : Set EuclideanPlane) (y : EuclideanPlane) :
    pinchMap S_pts (unpinchMap S_pts y) = y := by
  have hc : 0 < pinchScale S_pts (unitDir y) := pinchScale_pos S_pts (unitDir y)
  have hcinv : 0 < (pinchScale S_pts (unitDir y))⁻¹ := inv_pos.mpr hc
  simp only [pinchMap, unpinchMap, unitDir_smul hcinv]
  exact smul_inv_smul₀ hc.ne' y

theorem norm_pinchMap (S_pts : Set EuclideanPlane) (x : EuclideanPlane) :
    ‖pinchMap S_pts x‖ = pinchScale S_pts (unitDir x) * ‖x‖ := by
  have hc : 0 < pinchScale S_pts (unitDir x) := pinchScale_pos S_pts (unitDir x)
  simp [pinchMap, norm_smul, abs_of_pos hc]

theorem norm_unpinchMap (S_pts : Set EuclideanPlane) (y : EuclideanPlane) :
    ‖unpinchMap S_pts y‖ = (pinchScale S_pts (unitDir y))⁻¹ * ‖y‖ := by
  have hc : 0 < pinchScale S_pts (unitDir y) := pinchScale_pos S_pts (unitDir y)
  simp [unpinchMap, norm_smul, abs_of_pos hc]

theorem continuous_pinchMap (S_pts : Set EuclideanPlane) :
    Continuous (pinchMap S_pts) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : pinchMap S_pts 0 = 0 := by simp [pinchMap]
    unfold ContinuousAt
    rw [h0]
    refine squeeze_zero_norm (a := fun z : EuclideanPlane => ‖z‖) (fun z => ?_)
      (by simpa using (continuous_norm (E := EuclideanPlane)).tendsto 0)
    rw [norm_pinchMap]
    exact mul_le_of_le_one_left (norm_nonneg z) (pinchScale_bounds S_pts (unitDir z)).2
  · exact ((continuous_pinchScale S_pts).continuousAt.comp (continuousAt_unitDir hx)).smul
      continuousAt_id

theorem continuous_unpinchMap (S_pts : Set EuclideanPlane) :
    Continuous (unpinchMap S_pts) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : unpinchMap S_pts 0 = 0 := by simp [unpinchMap]
    unfold ContinuousAt
    rw [h0]
    have hcont : Continuous (fun z : EuclideanPlane => (4 / 3 : ℝ) * ‖z‖) :=
      continuous_const.mul continuous_norm
    refine squeeze_zero_norm (a := fun z : EuclideanPlane => (4 / 3 : ℝ) * ‖z‖) (fun z => ?_)
      (by simpa using hcont.tendsto 0)
    rw [norm_unpinchMap]
    have hle : (pinchScale S_pts (unitDir z))⁻¹ ≤ 4 / 3 := by
      have h1 := (pinchScale_bounds S_pts (unitDir z)).1
      rw [inv_le_comm₀ (pinchScale_pos S_pts (unitDir z)) (by norm_num)]
      linarith
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg z)
  · exact (((continuous_pinchScale S_pts).continuousAt.comp (continuousAt_unitDir hx)).inv₀
      (pinchScale_pos S_pts (unitDir x)).ne').smul continuousAt_id

/-- The global homeomorphism of `EuclideanPlane` pinching `ClosedUnitDisc` inward away from
`UnitCircle \ S_pts` while fixing `S_pts ⊆ UnitCircle` pointwise. -/
noncomputable def pinchHomeo (S_pts : Set EuclideanPlane) : EuclideanPlane ≃ₜ EuclideanPlane where
  toFun := pinchMap S_pts
  invFun := unpinchMap S_pts
  left_inv := unpinchMap_pinchMap S_pts
  right_inv := pinchMap_unpinchMap S_pts
  continuous_toFun := continuous_pinchMap S_pts
  continuous_invFun := continuous_unpinchMap S_pts

theorem mem_image_pinchHomeo_iff (S_pts : Set EuclideanPlane) (A : Set EuclideanPlane)
    (y : EuclideanPlane) :
    y ∈ pinchHomeo S_pts '' A ↔ unpinchMap S_pts y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change unpinchMap S_pts (pinchMap S_pts x) ∈ A
    rwa [unpinchMap_pinchMap]
  · intro hy
    exact ⟨unpinchMap S_pts y, hy, pinchMap_unpinchMap S_pts y⟩

theorem mem_image_closedUnitDisc_pinchHomeo (S_pts : Set EuclideanPlane) (y : EuclideanPlane) :
    y ∈ pinchHomeo S_pts '' ClosedUnitDisc ↔ ‖y‖ ≤ pinchScale S_pts (unitDir y) := by
  rw [mem_image_pinchHomeo_iff]
  simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_unpinchMap]
  rw [inv_mul_le_iff₀ (pinchScale_pos S_pts (unitDir y)), mul_one]

theorem mem_image_openUnitDisc_pinchHomeo (S_pts : Set EuclideanPlane) (y : EuclideanPlane) :
    y ∈ pinchHomeo S_pts '' OpenUnitDisc ↔ ‖y‖ < pinchScale S_pts (unitDir y) := by
  rw [mem_image_pinchHomeo_iff]
  simp only [OpenUnitDisc, Metric.mem_ball, dist_zero_right, norm_unpinchMap]
  rw [inv_mul_lt_iff₀ (pinchScale_pos S_pts (unitDir y)), mul_one]

theorem mem_image_unitCircle_pinchHomeo (S_pts : Set EuclideanPlane) (y : EuclideanPlane) :
    y ∈ pinchHomeo S_pts '' UnitCircle ↔ ‖y‖ = pinchScale S_pts (unitDir y) := by
  rw [mem_image_pinchHomeo_iff]
  simp only [UnitCircle, Metric.mem_sphere, dist_zero_right, norm_unpinchMap]
  rw [inv_mul_eq_iff_eq_mul₀ (pinchScale_pos S_pts (unitDir y)).ne', mul_one]

theorem pinchScale_eq_one_iff {S_pts : Set EuclideanPlane}
    (hS_cl : IsClosed S_pts) (hS_ne : S_pts.Nonempty) (u : EuclideanPlane) :
    pinchScale S_pts u = 1 ↔ u ∈ S_pts := by
  unfold pinchScale
  have h1 : 1 - (1 / 4 : ℝ) * min 1 (Metric.infDist u S_pts) = 1 ↔
      min 1 (Metric.infDist u S_pts) = 0 := by
    constructor <;> intro h <;> linarith
  rw [h1]
  have h2 : min 1 (Metric.infDist u S_pts) = 0 ↔ Metric.infDist u S_pts = 0 := by
    constructor
    · intro h
      rcases min_choice 1 (Metric.infDist u S_pts) with hmin | hmin <;> linarith
    · intro h
      rw [h, min_eq_right zero_le_one]
  rw [h2, ← Metric.mem_closure_iff_infDist_zero hS_ne, hS_cl.closure_eq]

theorem pinchHomeo_apply_of_mem {S_pts : Set EuclideanPlane}
    (hS_cl : IsClosed S_pts) (hS_ne : S_pts.Nonempty) (hS_sub : S_pts ⊆ UnitCircle)
    {u : EuclideanPlane} (hu : u ∈ S_pts) :
    pinchHomeo S_pts u = u := by
  change pinchMap S_pts u = u
  unfold pinchMap
  rw [unitDir_of_mem_unitCircle (hS_sub hu), (pinchScale_eq_one_iff hS_cl hS_ne u).mpr hu, one_smul]

theorem image_closedUnitDisc_pinchHomeo_subset (S_pts : Set EuclideanPlane) :
    pinchHomeo S_pts '' ClosedUnitDisc ⊆ ClosedUnitDisc := by
  intro y hy
  rw [mem_image_closedUnitDisc_pinchHomeo] at hy
  simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right]
  exact hy.trans (pinchScale_bounds S_pts (unitDir y)).2

theorem image_openUnitDisc_pinchHomeo_subset (S_pts : Set EuclideanPlane) :
    pinchHomeo S_pts '' OpenUnitDisc ⊆ OpenUnitDisc := by
  intro y hy
  rw [mem_image_openUnitDisc_pinchHomeo] at hy
  simp only [OpenUnitDisc, Metric.mem_ball, dist_zero_right]
  exact hy.trans_le (pinchScale_bounds S_pts (unitDir y)).2

theorem image_closedUnitDisc_pinchHomeo_inter_unitCircle {S_pts : Set EuclideanPlane}
    (hS_cl : IsClosed S_pts) (hS_ne : S_pts.Nonempty) (hS_sub : S_pts ⊆ UnitCircle) :
    (pinchHomeo S_pts '' ClosedUnitDisc) ∩ UnitCircle = S_pts := by
  ext y
  simp only [mem_inter_iff, mem_image_closedUnitDisc_pinchHomeo]
  constructor
  · rintro ⟨hy_le, hy_circ⟩
    have hy_norm : ‖y‖ = 1 := by simpa [UnitCircle] using hy_circ
    have hscale : pinchScale S_pts (unitDir y) = 1 :=
      le_antisymm (pinchScale_bounds S_pts (unitDir y)).2 (hy_norm ▸ hy_le)
    rw [unitDir_of_mem_unitCircle hy_circ] at hscale
    exact (pinchScale_eq_one_iff hS_cl hS_ne y).mp hscale
  · intro hy
    have hy_circ : y ∈ UnitCircle := hS_sub hy
    have hy_norm : ‖y‖ = 1 := by simpa [UnitCircle] using hy_circ
    rw [hy_norm, unitDir_of_mem_unitCircle hy_circ, (pinchScale_eq_one_iff hS_cl hS_ne y).mpr hy]
    exact ⟨le_rfl, hy_circ⟩

theorem image_unitCircle_pinchHomeo_inter_unitCircle {S_pts : Set EuclideanPlane}
    (hS_cl : IsClosed S_pts) (hS_ne : S_pts.Nonempty) (hS_sub : S_pts ⊆ UnitCircle) :
    (pinchHomeo S_pts '' UnitCircle) ∩ UnitCircle = S_pts := by
  ext y
  simp only [mem_inter_iff, mem_image_unitCircle_pinchHomeo]
  constructor
  · rintro ⟨hy_eq, hy_circ⟩
    have hy_norm : ‖y‖ = 1 := by simpa [UnitCircle] using hy_circ
    have hscale : pinchScale S_pts (unitDir y) = 1 := hy_eq.symm.trans hy_norm
    rw [unitDir_of_mem_unitCircle hy_circ] at hscale
    exact (pinchScale_eq_one_iff hS_cl hS_ne y).mp hscale
  · intro hy
    have hy_circ : y ∈ UnitCircle := hS_sub hy
    have hy_norm : ‖y‖ = 1 := by simpa [UnitCircle] using hy_circ
    rw [hy_norm, unitDir_of_mem_unitCircle hy_circ, (pinchScale_eq_one_iff hS_cl hS_ne y).mpr hy]
    exact ⟨rfl, hy_circ⟩

theorem closure_image_openUnitDisc_pinchHomeo (S_pts : Set EuclideanPlane) :
    closure (pinchHomeo S_pts '' OpenUnitDisc) = pinchHomeo S_pts '' ClosedUnitDisc := by
  rw [← (pinchHomeo S_pts).image_closure]
  congr 1
  exact closure_ball (0 : EuclideanPlane) one_ne_zero

theorem image_closedUnitDisc_sdiff_openUnitDisc_pinchHomeo (S_pts : Set EuclideanPlane) :
    (pinchHomeo S_pts '' ClosedUnitDisc) \ (pinchHomeo S_pts '' OpenUnitDisc) =
      pinchHomeo S_pts '' UnitCircle := by
  rw [← image_sdiff (pinchHomeo S_pts).injective]
  congr 1
  exact Metric.closedBall_sdiff_ball

theorem mem_closure_openUnitDisc_sdiff_pinchHomeo {S_pts : Set EuclideanPlane}
    (hS_cl : IsClosed S_pts) (hS_ne : S_pts.Nonempty) (hS_sub : S_pts ⊆ UnitCircle)
    {y : EuclideanPlane} (hy : y ∈ (pinchHomeo S_pts '' UnitCircle) \ S_pts) :
    y ∈ closure (OpenUnitDisc \ (pinchHomeo S_pts '' ClosedUnitDisc)) := by
  obtain ⟨hy_C, hy_not_S⟩ := hy
  have hy_norm_eq : ‖y‖ = pinchScale S_pts (unitDir y) :=
    (mem_image_unitCircle_pinchHomeo S_pts y).mp hy_C
  have hy_pos : 0 < ‖y‖ := hy_norm_eq.symm ▸ pinchScale_pos S_pts (unitDir y)
  have hy_lt_one : ‖y‖ < 1 := by
    refine lt_of_le_of_ne (hy_norm_eq.symm ▸ (pinchScale_bounds S_pts (unitDir y)).2) ?_
    intro h1
    have hy_unit : y ∈ UnitCircle := by simpa [UnitCircle] using h1
    have hy_in_S : y ∈ S_pts :=
      image_unitCircle_pinchHomeo_inter_unitCircle hS_cl hS_ne hS_sub ▸ ⟨hy_C, hy_unit⟩
    exact hy_not_S hy_in_S
  have hinv_gt_one : 1 < ‖y‖⁻¹ := one_lt_inv₀ hy_pos |>.mpr hy_lt_one
  rw [mem_closure_iff_nhds]
  intro V hV
  have hcont_smul : Continuous (fun t : ℝ => t • y) := continuous_id.smul continuous_const
  have hpre : {t : ℝ | t • y ∈ V} ∈ 𝓝 (1 : ℝ) := by
    apply hcont_smul.continuousAt.preimage_mem_nhds
    simpa using hV
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := 1 + min (ε / 2) ((‖y‖⁻¹ - 1) / 2)
  have ht_gt_one : 1 < t := by
    dsimp [t]
    have : 0 < min (ε / 2) ((‖y‖⁻¹ - 1) / 2) := lt_min (by linarith) (by linarith)
    linarith
  have ht_lt_inv : t < ‖y‖⁻¹ := by
    dsimp [t]
    have : min (ε / 2) ((‖y‖⁻¹ - 1) / 2) ≤ (‖y‖⁻¹ - 1) / 2 := min_le_right _ _
    linarith
  have ht_ball : t ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hle : min (ε / 2) ((‖y‖⁻¹ - 1) / 2) ≤ ε / 2 := min_le_left _ _
    have hpos : 0 < min (ε / 2) ((‖y‖⁻¹ - 1) / 2) := lt_min (by linarith) (by linarith)
    rw [abs_of_pos (by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  have ht_pos : 0 < t := by linarith
  refine ⟨t • y, hε_sub ht_ball, ?_, ?_⟩
  · simp only [OpenUnitDisc, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg ht_pos.le]
    calc t * ‖y‖ < ‖y‖⁻¹ * ‖y‖ := mul_lt_mul_of_pos_right ht_lt_inv hy_pos
    _ = 1 := inv_mul_cancel₀ hy_pos.ne'
  · rw [mem_image_closedUnitDisc_pinchHomeo, unitDir_smul ht_pos,
      norm_smul, Real.norm_of_nonneg ht_pos.le, ← hy_norm_eq]
    exact not_le.mpr (lt_mul_of_one_lt_left hy_pos ht_gt_one)

/-- Given strictly increasing sequences `a, b : ℕ → ℝ` and `n : ℕ`, there is a continuous
strictly increasing function `τ : ℝ → ℝ` on `[a 0, a (n + 1)]` with `τ (a i) = b i` for all
`i ≤ n + 1`. -/
theorem exists_strictMonoOn_interp (n : ℕ) (a b : ℕ → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ (Icc (a 0) (a (n + 1))) ∧
      StrictMonoOn τ (Icc (a 0) (a (n + 1))) ∧
      ∀ i ≤ n + 1, τ (a i) = b i :=
  GM14.exists_strictMonoOn_interp n a b ha hb

/-- Given `m ≥ 1` and strictly increasing sequences `t₁, t₂ : ℕ → ℝ` with
`t₁ i < t₁ 0 + 2π` and `t₂ i < t₂ 0 + 2π` for `i < m`, there is a homeomorphism
`h_circ : Circle ≃ₜ Circle` mapping `Circle.exp (t₁ i)` to `Circle.exp (t₂ i)` for all `i < m`. -/
theorem exists_circle_homeo_matching_angles (m : ℕ) (hm : 1 ≤ m)
    (t₁ t₂ : ℕ → ℝ) (ht₁ : StrictMono t₁) (ht₂ : StrictMono t₂)
    (hbd₁ : ∀ i < m, t₁ i < t₁ 0 + 2 * Real.pi)
    (hbd₂ : ∀ i < m, t₂ i < t₂ 0 + 2 * Real.pi) :
    ∃ h_circ : Circle ≃ₜ Circle,
      ∀ i < m, h_circ (Circle.exp (t₁ i)) = Circle.exp (t₂ i) :=
  GM14.exists_circle_homeo_matching_angles m hm t₁ t₂ ht₁ ht₂ hbd₁ hbd₂

theorem exists_subline_of_closed_cover_Ordered [T2Space S]
    {K₀ S₁ K₁ : Set S} (hK₀ : IsClosed K₀) (hS₁ : IsClosed S₁) (hK₁ : IsClosed K₁)
    (hdisj : Disjoint K₀ K₁)
    {a : unitInterval → S} (ha : IsArcMap a)
    (hsub : range a ⊆ K₀ ∪ S₁ ∪ K₁)
    {t₀ t₁ : unitInterval} (hle : (t₀ : ℝ) ≤ (t₁ : ℝ))
    (ha₀ : a t₀ ∈ K₀) (ha₁ : a t₁ ∈ K₁) :
    ∃ F_sub ⊆ range a, IsLine F_sub ∧ F_sub ⊆ S₁ ∧
      (F_sub ∩ (K₀ ∩ S₁)).Nonempty ∧ (F_sub ∩ (K₁ ∩ S₁)).Nonempty := by
  have ha_cont : Continuous (extI a) := continuous_extI ha.1
  have hmem_range : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → extI a r ∈ range a := by
    intro r hr
    exact ⟨⟨r, hr⟩, (extI_of_mem a hr).symm⟩
  let A₀ : Set ℝ := Icc (t₀ : ℝ) (t₁ : ℝ) ∩ (extI a) ⁻¹' K₀
  have hA₀_cl : IsClosed A₀ := isClosed_Icc.inter (hK₀.preimage ha_cont)
  have hA₀_ne : A₀.Nonempty := ⟨t₀, ⟨le_rfl, hle⟩, by simpa [extI_coe] using ha₀⟩
  have hA₀_bdd : BddAbove A₀ := ⟨t₁, fun x hx => hx.1.2⟩
  let s₀ : ℝ := sSup A₀
  have hs₀_mem : s₀ ∈ A₀ := hA₀_cl.csSup_mem hA₀_ne hA₀_bdd
  have hs₀_Icc : s₀ ∈ Icc (t₀ : ℝ) (t₁ : ℝ) := hs₀_mem.1
  have has₀_K₀ : extI a s₀ ∈ K₀ := hs₀_mem.2
  have hs₀_lt_t₁ : s₀ < (t₁ : ℝ) := by
    refine lt_of_le_of_ne hs₀_Icc.2 ?_
    intro heq
    have ht₁_K₀ : a t₁ ∈ K₀ := by simpa [heq, extI_coe] using has₀_K₀
    exact disjoint_left.mp hdisj ht₁_K₀ ha₁
  let B₁ : Set ℝ := Icc s₀ (t₁ : ℝ) ∩ (extI a) ⁻¹' K₁
  have hB₁_cl : IsClosed B₁ := isClosed_Icc.inter (hK₁.preimage ha_cont)
  have hB₁_ne : B₁.Nonempty := ⟨t₁, ⟨hs₀_Icc.2, le_rfl⟩, by simpa [extI_coe] using ha₁⟩
  have hB₁_bdd : BddBelow B₁ := ⟨s₀, fun x hx => hx.1.1⟩
  let s₁ : ℝ := sInf B₁
  have hs₁_mem : s₁ ∈ B₁ := hB₁_cl.csInf_mem hB₁_ne hB₁_bdd
  have hs₁_Icc : s₁ ∈ Icc s₀ (t₁ : ℝ) := hs₁_mem.1
  have has₁_K₁ : extI a s₁ ∈ K₁ := hs₁_mem.2
  have hs₀_lt_s₁ : s₀ < s₁ := by
    refine lt_of_le_of_ne hs₁_Icc.1 ?_
    intro heq
    exact disjoint_left.mp hdisj has₀_K₀ (heq ▸ has₁_K₁)
  have hIoo_S₁ : ∀ t ∈ Ioo s₀ s₁, extI a t ∈ S₁ := by
    intro t ht
    have ht_not_A₀ : t ∉ A₀ := fun h => not_le.mpr ht.1 (le_csSup hA₀_bdd h)
    have ht_not_B₁ : t ∉ B₁ := fun h => not_le.mpr ht.2 (csInf_le hB₁_bdd h)
    have ht_Icc₀ : t ∈ Icc (t₀ : ℝ) (t₁ : ℝ) := ⟨hs₀_Icc.1.trans ht.1.le, ht.2.le.trans hs₁_Icc.2⟩
    have ht_Icc₁ : t ∈ Icc s₀ (t₁ : ℝ) := ⟨ht.1.le, ht.2.le.trans hs₁_Icc.2⟩
    have ht_01 : t ∈ Icc (0 : ℝ) 1 := ⟨t₀.2.1.trans ht_Icc₀.1, ht_Icc₀.2.trans t₁.2.2⟩
    have hat_not_K₀ : extI a t ∉ K₀ := fun h => ht_not_A₀ ⟨ht_Icc₀, h⟩
    have hat_not_K₁ : extI a t ∉ K₁ := fun h => ht_not_B₁ ⟨ht_Icc₁, h⟩
    rcases hsub (hmem_range t ht_01) with (h | h) | h
    · exact (hat_not_K₀ h).elim
    · exact h
    · exact (hat_not_K₁ h).elim
  have hIcc_S₁ : extI a '' Icc s₀ s₁ ⊆ S₁ := by
    rw [← closure_Ioo hs₀_lt_s₁.ne]
    exact (image_closure_subset_closure_image ha_cont).trans
      (hS₁.closure_subset_iff.mpr (image_subset_iff.mpr hIoo_S₁))
  let F_sub : Set S := range (pieceA a s₀ s₁)
  have hF_sub_eq : F_sub = extI a '' Icc s₀ s₁ :=
    range_pieceA a (t₀.2.1.trans hs₀_Icc.1) hs₀_lt_s₁.le (hs₁_Icc.2.trans t₁.2.2)
  have hF_sub_line : IsLine F_sub := by
    obtain ⟨f_sub, _, _⟩ :=
      (isArcMap_pieceA ha (t₀.2.1.trans hs₀_Icc.1) hs₀_lt_s₁ (hs₁_Icc.2.trans
        t₁.2.2)).isLineWithEnds
    exact ⟨f_sub⟩
  refine ⟨F_sub, ?_, hF_sub_line, hF_sub_eq ▸ hIcc_S₁, ?_, ?_⟩
  · rw [hF_sub_eq]
    rintro x ⟨r, hr, rfl⟩
    exact hmem_range r ⟨(t₀.2.1.trans hs₀_Icc.1).trans hr.1, hr.2.trans (hs₁_Icc.2.trans t₁.2.2)⟩
  · refine ⟨extI a s₀, ?_, has₀_K₀, hIcc_S₁ ⟨s₀, ⟨le_rfl, hs₀_lt_s₁.le⟩, rfl⟩⟩
    rw [hF_sub_eq]
    exact ⟨s₀, ⟨le_rfl, hs₀_lt_s₁.le⟩, rfl⟩
  · refine ⟨extI a s₁, ?_, has₁_K₁, hIcc_S₁ ⟨s₁, ⟨hs₀_lt_s₁.le, le_rfl⟩, rfl⟩⟩
    rw [hF_sub_eq]
    exact ⟨s₁, ⟨hs₀_lt_s₁.le, le_rfl⟩, rfl⟩

/-- If `F ⊆ K₀ ∪ S₁ ∪ K₁` is a line meeting the disjoint closed sets `K₀` and `K₁` (with `S₁`
closed),
then `F` contains a subline `F_sub ⊆ S₁` meeting both `K₀ ∩ S₁` and `K₁ ∩ S₁`. -/
theorem exists_subline_of_closed_cover [T2Space S]
    {K₀ S₁ K₁ F : Set S} (hK₀ : IsClosed K₀) (hS₁ : IsClosed S₁) (hK₁ : IsClosed K₁)
    (hdisj : Disjoint K₀ K₁) (hF : IsLine F)
    (hsub : F ⊆ K₀ ∪ S₁ ∪ K₁)
    (hF₀ : (F ∩ K₀).Nonempty) (hF₁ : (F ∩ K₁).Nonempty) :
    ∃ F_sub ⊆ F, IsLine F_sub ∧ F_sub ⊆ S₁ ∧
      (F_sub ∩ (K₀ ∩ S₁)).Nonempty ∧ (F_sub ∩ (K₁ ∩ S₁)).Nonempty := by
  obtain ⟨f⟩ := hF
  have hLuv : IsLineWithEnds F (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
  obtain ⟨a, ha, rfl, -, -⟩ := hLuv.exists_arc
  obtain ⟨_, ⟨t₀, rfl⟩, ha₀⟩ := hF₀
  obtain ⟨_, ⟨t₁, rfl⟩, ha₁⟩ := hF₁
  rcases le_total (t₀ : ℝ) (t₁ : ℝ) with hle | hle
  · exact exists_subline_of_closed_cover_Ordered hK₀ hS₁ hK₁ hdisj ha hsub hle ha₀ ha₁
  · have hsub' : range a ⊆ K₁ ∪ S₁ ∪ K₀ := by
      intro x hx
      rcases hsub hx with (h | h) | h
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
    obtain ⟨F_sub, h1, h2, h3, h4, h5⟩ :=
      exists_subline_of_closed_cover_Ordered hK₁ hS₁ hK₀ hdisj.symm ha hsub' hle ha₁ ha₀
    exact ⟨F_sub, h1, h2, h3, h5, h4⟩

private theorem closed_disc_coordinates_map_interior
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hsubBd_eq : closure Λ \ Λ = subBd Λ)
    (φ₀ : ↑ClosedUnitDisc ≃ₜ ↑(closure Λ))
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_def : f₀ = fun x => (φ₀ x).1)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_range : range f₀ = closure Λ)
    (hf₀_bd : f₀ '' {x | ↑x ∈ UnitCircle} = subBd Λ)
    (hCD_split : ∀ (x : ↑ClosedUnitDisc), ↑x ∈ OpenUnitDisc ↔ ↑x ∉ UnitCircle) :
    f₀ '' {x | ↑x ∈ OpenUnitDisc} = Λ := by
  subst f₀
  let f₀ : ClosedUnitDisc → S := fun x => (φ₀ x).1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx_cl : f₀ x ∈ closure Λ := (φ₀ x).2
    have hx_not_bd : f₀ x ∉ subBd Λ := by
      rw [← hf₀_bd]
      rintro ⟨x', hx', h_eq⟩
      have hxx' : x = x' := hf₀_inj h_eq.symm
      exact (hCD_split x).mp hx (hxx' ▸ hx')
    by_contra hyΛ
    exact hx_not_bd (hsubBd_eq ▸ ⟨hx_cl, hyΛ⟩)
  · intro hy
    obtain ⟨x, rfl⟩ : y ∈ range f₀ := hf₀_range ▸ subset_closure hy
    refine ⟨x, (hCD_split x).mpr fun hx_unit => ?_, rfl⟩
    have h_in_bd : f₀ x ∈ closure Λ \ Λ := by
      rw [hsubBd_eq, ← hf₀_bd]
      exact ⟨x, hx_unit, rfl⟩
    exact h_in_bd.2 hy

private theorem boundary_coordinates_are_surjective
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (g : Circle ≃ₜ ↑(subBd Λ))
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_bd : f₀ '' {x | ↑x ∈ UnitCircle} = subBd Λ)
    (α₀ : Circle → ↑ClosedUnitDisc)
    (α : Circle → EuclideanPlane)
    (hα_def : α = fun z => (α₀ z).1)
    (hf₀_α₀ : ∀ (z : Circle), f₀ (α₀ z) = ↑(g z))
    (hα_unit : ∀ (z : Circle), α z ∈ UnitCircle) :
    range α = UnitCircle := by
  subst α
  let α : Circle → EuclideanPlane := fun z => (α₀ z).1
  refine subset_antisymm (range_subset_iff.mpr hα_unit) ?_
  intro u hu
  have hu_cl : u ∈ ClosedUnitDisc := Metric.sphere_subset_closedBall hu
  have hfu_bd : f₀ ⟨u, hu_cl⟩ ∈ subBd Λ := hf₀_bd ▸ ⟨⟨u, hu_cl⟩, hu, rfl⟩
  let z : Circle := g.symm ⟨f₀ ⟨u, hu_cl⟩, hfu_bd⟩
  refine ⟨z, ?_⟩
  have hfz : f₀ (α₀ z) = f₀ ⟨u, hu_cl⟩ := by
    rw [hf₀_α₀]
    exact congrArg Subtype.val (g.apply_symm_apply ⟨f₀ ⟨u, hu_cl⟩, hfu_bd⟩)
  exact congrArg Subtype.val (hf₀_inj hfz)

private theorem pinched_disc_image_is_open
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (hΛ_open : IsOpen Λ)
    (φ₀ : ↑ClosedUnitDisc ≃ₜ ↑(closure Λ))
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_def : f₀ = fun x => (φ₀ x).1)
    (U_sub : Set ↑ClosedUnitDisc)
    (D : Set S)
    (hD_def : D = f₀ '' U_sub)
    (hU_sub_open : IsOpen U_sub)
    (hD_sub_Λ : D ⊆ Λ) :
    IsOpen D := by
  subst f₀ D
  let f₀ : ClosedUnitDisc → S := fun x => (φ₀ x).1
  let D : Set S := f₀ '' U_sub
  have hopen_cl : IsOpen (φ₀ '' U_sub) := φ₀.isOpenMap _ hU_sub_open
  obtain ⟨V, hV_open, hV_eq⟩ := isOpen_induced_iff.mp hopen_cl
  have hD_eq : D = V ∩ Λ := by
    ext y
    constructor
    · intro hy
      have hy_Λ : y ∈ Λ := hD_sub_Λ hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx_V : (φ₀ x).1 ∈ V := by
        change φ₀ x ∈ Subtype.val ⁻¹' V
        rw [hV_eq]
        exact ⟨x, hx, rfl⟩
      exact ⟨hx_V, hy_Λ⟩
    · rintro ⟨hy_V, hy_Λ⟩
      have hy_cl : y ∈ closure Λ := subset_closure hy_Λ
      have h_in : (⟨y, hy_cl⟩ : ↥(closure Λ)) ∈ φ₀ '' U_sub := by
        rw [← hV_eq]
        exact hy_V
      rcases h_in with ⟨x, hx, h_eq⟩
      exact ⟨x, hx, congrArg Subtype.val h_eq⟩
  change IsOpen D
  rw [hD_eq]
  exact hV_open.inter hΛ_open

private theorem closure_of_pinched_open_unit_disc
    (S_pts : Set EuclideanPlane)
    (U_E : Set EuclideanPlane)
    (hU_E_def : U_E = pinchHomeo S_pts '' OpenUnitDisc)
    (U_sub : Set ↑ClosedUnitDisc)
    (hU_sub_def : U_sub = Subtype.val ⁻¹' U_E)
    (K_sub : Set ↑ClosedUnitDisc)
    (hK_sub_def : K_sub = Subtype.val ⁻¹' (pinchHomeo S_pts '' ClosedUnitDisc))
    (hU_E_sub_open : U_E ⊆ OpenUnitDisc) :
    closure U_sub = K_sub := by
  subst U_E U_sub K_sub
  let U_E : Set EuclideanPlane := pinchHomeo S_pts '' OpenUnitDisc
  let U_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' U_E
  let K_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' (pinchHomeo S_pts '' ClosedUnitDisc)
  apply subset_antisymm
  · have hK_sub_cl : IsClosed K_sub :=
      ((pinchHomeo S_pts).isClosedMap _ Metric.isClosed_closedBall).preimage continuous_subtype_val
    exact hK_sub_cl.closure_subset_iff.mpr fun x hx =>
      image_mono Metric.ball_subset_closedBall hx
  · intro x hx
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨V', hV'_open, rfl⟩ := isOpen_induced_iff.mp hV
    have hx_clE : x.1 ∈ closure U_E := by
      rw [closure_image_openUnitDisc_pinchHomeo]
      exact hx
    obtain ⟨y, hyV', hyU⟩ := mem_closure_iff.mp hx_clE V' hV'_open hxV
    exact ⟨⟨y, Metric.ball_subset_closedBall (hU_E_sub_open hyU)⟩, hyV', hyU⟩

private theorem pinched_closed_disc_image
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_cont : Continuous f₀)
    (hf₀_inj : Function.Injective f₀)
    (S_pts : Set EuclideanPlane)
    (K_E : Set EuclideanPlane)
    (hK_E_def : K_E = pinchHomeo S_pts '' ClosedUnitDisc)
    (K_sub : Set ↑ClosedUnitDisc)
    (hK_sub_def : K_sub = Subtype.val ⁻¹' K_E)
    (D : Set S)
    (hK_E_sub_cl : K_E ⊆ ClosedUnitDisc)
    (hcl_D : closure D = f₀ '' K_sub) :
    IsClosedDisc (closure D) := by
  subst K_E K_sub
  let K_E : Set EuclideanPlane := pinchHomeo S_pts '' ClosedUnitDisc
  let K_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' K_E
  let ψ_D : ClosedUnitDisc → S := fun x =>
    f₀ ⟨pinchHomeo S_pts x.1, hK_E_sub_cl ⟨x.1, x.2, rfl⟩⟩
  have hψ_cont : Continuous ψ_D :=
    hf₀_cont.comp (Continuous.subtype_mk ((pinchHomeo S_pts).continuous.comp
      continuous_subtype_val) _)
  have hψ_inj : Function.Injective ψ_D := by
    intro x₁ x₂ h
    have h1 := Subtype.ext_iff.mp (hf₀_inj h)
    exact Subtype.ext ((pinchHomeo S_pts).injective h1)
  have hψ_emb : IsEmbedding ψ_D :=
    ( hψ_cont.isClosedEmbedding hψ_inj ).isEmbedding
  have hψ_range : range ψ_D = closure D := by
    rw [hcl_D]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨pinchHomeo S_pts x.1, hK_E_sub_cl ⟨x.1, x.2, rfl⟩⟩, ⟨x.1, x.2, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, hzx⟩, rfl⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      dsimp [ψ_D]
      congr 1
      exact Subtype.ext hzx
  exact ⟨hψ_emb.toHomeomorph.trans (Homeomorph.setCongr hψ_range)⟩

private theorem pinched_disc_boundary_is_closed_curve
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_cont : Continuous f₀)
    (hf₀_inj : Function.Injective f₀)
    (α : Circle → EuclideanPlane)
    (hα_cont : Continuous α)
    (hα_inj : Function.Injective α)
    (hα_unit : ∀ (z : Circle), α z ∈ UnitCircle)
    (hα_range : range α = UnitCircle)
    (S_pts : Set EuclideanPlane)
    (K_E : Set EuclideanPlane)
    (hK_E_def : K_E = pinchHomeo S_pts '' ClosedUnitDisc)
    (C_sub : Set ↑ClosedUnitDisc)
    (hC_sub_def : C_sub = Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle))
    (D : Set S)
    (hK_E_sub_cl : K_E ⊆ ClosedUnitDisc)
    (hsubBd_D_f₀ : subBd D = f₀ '' C_sub) :
    IsOArc (subBd D) := by
  subst K_E C_sub
  let K_E : Set EuclideanPlane := pinchHomeo S_pts '' ClosedUnitDisc
  let C_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle)
  let g_D : Circle → S := fun z =>
    f₀ ⟨pinchHomeo S_pts (α z), hK_E_sub_cl ⟨α z, Metric.sphere_subset_closedBall (hα_unit z), rfl⟩⟩
  have hg_D_cont : Continuous g_D :=
    hf₀_cont.comp (Continuous.subtype_mk ((pinchHomeo S_pts).continuous.comp hα_cont) _)
  have hg_D_inj : Function.Injective g_D := by
    intro z₁ z₂ h
    have h1 := Subtype.ext_iff.mp (hf₀_inj h)
    exact hα_inj ((pinchHomeo S_pts).injective h1)
  have hg_D_emb : IsEmbedding g_D :=
    (hg_D_cont.isClosedEmbedding hg_D_inj).isEmbedding
  have hg_D_range : range g_D = subBd D := by
    rw [hsubBd_D_f₀]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨pinchHomeo S_pts (α z), hK_E_sub_cl ⟨α z, Metric.sphere_subset_closedBall
        (hα_unit z), rfl⟩⟩,
        ⟨α z, hα_unit z, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨u, hu, hxu⟩, rfl⟩
      obtain ⟨z, rfl⟩ : u ∈ range α := hα_range ▸ hu
      refine ⟨z, ?_⟩
      dsimp [g_D]
      congr 1
      exact Subtype.ext hxu
  exact ⟨hg_D_emb.toHomeomorph.trans (Homeomorph.setCongr hg_D_range)⟩

private theorem pinched_boundary_meets_original_at_marks
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (g : Circle ≃ₜ ↑(subBd Λ))
    {W_pts : Set Circle}
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_bd : f₀ '' {x | ↑x ∈ UnitCircle} = subBd Λ)
    (α₀ : Circle → ↑ClosedUnitDisc)
    (α : Circle → EuclideanPlane)
    (hα_def : α = fun z => (α₀ z).1)
    (hf₀_α₀ : ∀ (z : Circle), f₀ (α₀ z) = ↑(g z))
    (S_pts : Set EuclideanPlane)
    (hS_pts_def : S_pts = α '' W_pts)
    (hS_cl : IsClosed S_pts)
    (hS_ne : S_pts.Nonempty)
    (hS_sub : S_pts ⊆ UnitCircle)
    (C_sub : Set ↑ClosedUnitDisc)
    (hC_sub_def : C_sub = Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle))
    (D : Set S)
    (hsubBd_D_f₀ : subBd D = f₀ '' C_sub) :
    subBd D ∩ subBd Λ = (fun z => ↑(g z)) '' W_pts := by
  subst α S_pts C_sub
  let α : Circle → EuclideanPlane := fun z => (α₀ z).1
  let S_pts : Set EuclideanPlane := α '' W_pts
  let C_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle)
  have hinter_sub : C_sub ∩ {x : ClosedUnitDisc | x.1 ∈ UnitCircle} = α₀ '' W_pts := by
    ext x
    change x.1 ∈ (pinchHomeo S_pts '' UnitCircle) ∩ UnitCircle ↔ x ∈ α₀ '' W_pts
    rw [image_unitCircle_pinchHomeo_inter_unitCircle hS_cl hS_ne hS_sub]
    constructor
    · rintro ⟨z, hz, hzx⟩
      refine ⟨z, hz, Subtype.ext hzx⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  calc subBd D ∩ subBd Λ
    _ = f₀ '' C_sub ∩ f₀ '' {x : ClosedUnitDisc | x.1 ∈ UnitCircle} := by
      rw [hsubBd_D_f₀, hf₀_bd]
    _ = f₀ '' (C_sub ∩ {x : ClosedUnitDisc | x.1 ∈ UnitCircle}) :=
      (image_inter hf₀_inj).symm
    _ = (f₀ ∘ α₀) '' W_pts := by rw [hinter_sub, ← image_comp]
    _ = (fun z => (g z).1) '' W_pts := image_congr fun z _ => hf₀_α₀ z

private theorem pinched_boundary_off_marks_in_outer_closure
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (g : Circle ≃ₜ ↑(subBd Λ))
    {W_pts : Set Circle}
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_cont : Continuous f₀)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_int : f₀ '' {x | ↑x ∈ OpenUnitDisc} = Λ)
    (α₀ : Circle → ↑ClosedUnitDisc)
    (α : Circle → EuclideanPlane) (hα_def : α = fun z => (α₀ z).1)
    (hf₀_α₀ : ∀ (z : Circle), f₀ (α₀ z) = ↑(g z))
    (S_pts : Set EuclideanPlane)
    (hS_pts_def : S_pts = α '' W_pts)
    (hS_cl : IsClosed S_pts)
    (hS_ne : S_pts.Nonempty)
    (hS_sub : S_pts ⊆ UnitCircle)
    (K_E : Set EuclideanPlane)
    (hK_E_def : K_E = pinchHomeo S_pts '' ClosedUnitDisc)
    (K_sub : Set ↑ClosedUnitDisc)
    (hK_sub_def : K_sub = Subtype.val ⁻¹' K_E)
    (C_sub : Set ↑ClosedUnitDisc)
    (hC_sub_def : C_sub = Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle))
    (D : Set S)
    (hcl_D : closure D = f₀ '' K_sub)
    (hsubBd_D_f₀ : subBd D = f₀ '' C_sub) :
    subBd D \ (fun z => ↑(g z)) '' W_pts ⊆ closure (Λ \ closure D) := by
  subst α S_pts K_E K_sub C_sub
  let α : Circle → EuclideanPlane := fun z => (α₀ z).1
  let S_pts : Set EuclideanPlane := α '' W_pts
  let K_E : Set EuclideanPlane := pinchHomeo S_pts '' ClosedUnitDisc
  let K_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' K_E
  let C_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle)
  intro y hy
  rcases (hsubBd_D_f₀ ▸ hy.1) with ⟨x, hxC, rfl⟩
  have hx_not_S : x.1 ∉ S_pts := by
    rintro ⟨z, hz, hzx⟩
    apply hy.2
    refine ⟨z, hz, ?_⟩
    dsimp only
    rw [← hf₀_α₀]
    congr 1
    exact Subtype.ext (show (α₀ z).1 = x.1 from hzx)
  have hx_clE : x.1 ∈ closure (OpenUnitDisc \ K_E) :=
    mem_closure_openUnitDisc_sdiff_pinchHomeo hS_cl hS_ne hS_sub ⟨hxC, hx_not_S⟩
  let W_sub : Set ClosedUnitDisc := {w : ClosedUnitDisc | w.1 ∈ OpenUnitDisc \ K_E}
  have hx_clW : x ∈ closure W_sub := by
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨V', hV'_open, rfl⟩ := isOpen_induced_iff.mp hV
    obtain ⟨w, hwV', hwW⟩ := mem_closure_iff.mp hx_clE V' hV'_open hxV
    exact ⟨⟨w, Metric.ball_subset_closedBall hwW.1⟩, hwV', hwW⟩
  have hfx_cl : f₀ x ∈ closure (f₀ '' W_sub) :=
    image_closure_subset_closure_image hf₀_cont ⟨x, hx_clW, rfl⟩
  refine closure_mono ?_ hfx_cl
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hf₀_int]
    exact ⟨w, hw.1, rfl⟩
  · rw [hcl_D]
    rintro ⟨w', hw', h_eq⟩
    have hww' : w = w' := hf₀_inj h_eq.symm
    exact hw.2 (hww' ▸ hw')

private theorem radial_collar_map_injective
    {S : Type w}
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_inj : Function.Injective f₀)
    (α : Circle → EuclideanPlane)
    (hα_inj : Function.Injective α)
    (hα_norm : ∀ (z : Circle), ‖α z‖ = 1)
    (δ : Circle → ℝ)
    (hδ_bounds : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (hcMap_mem : ∀ (p : ℝ × Circle), max 0 (min 1 (1 - p.1)) • α p.2 ∈ ClosedUnitDisc)
    (cMap : ℝ × Circle → S)
    (hcMap_def : cMap = fun p : ℝ × Circle =>
      f₀ (⟨max (0 : ℝ) (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩ : ClosedUnitDisc))
    (hcMap_clamp : ∀ (p : ℝ × Circle), 0 ≤ p.1 → p.1 ≤ δ p.2 → max 0 (min 1 (1 - p.1)) = 1 - p.1) :
    InjOn cMap {p | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} := by
  subst cMap
  let cMap : ℝ × Circle → S := fun p => f₀ ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
  intro p₁ hp₁ p₂ hp₂ heq
  have hsub := Subtype.ext_iff.mp (hf₀_inj heq)
  dsimp only at hsub
  rw [hcMap_clamp p₁ hp₁.1 hp₁.2, hcMap_clamp p₂ hp₂.1 hp₂.2] at hsub
  have hr₁_pos : 0 < 1 - p₁.1 := by linarith [(hδ_bounds p₁.2).2, hp₁.2]
  have hr₂_pos : 0 < 1 - p₂.1 := by linarith [(hδ_bounds p₂.2).2, hp₂.2]
  have hnorm := congrArg norm hsub
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hr₁_pos.le, Real.norm_of_nonneg hr₂_pos.le,
    hα_norm p₁.2, hα_norm p₂.2, mul_one, mul_one] at hnorm
  have hp_fst : p₁.1 = p₂.1 := by linarith
  have hα_eq : α p₁.2 = α p₂.2 := by
    rw [← hnorm] at hsub
    exact smul_right_injective _ hr₁_pos.ne' hsub
  exact Prod.ext hp_fst (hα_inj hα_eq)

private theorem radial_collar_covers_disc_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (φ₀ : ↑ClosedUnitDisc ≃ₜ ↑(closure Λ))
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_def : f₀ = fun x => (φ₀ x).1)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_range : range f₀ = closure Λ)
    (α : Circle → EuclideanPlane)
    (hα_unit : ∀ (z : Circle), α z ∈ UnitCircle)
    (hα_norm : ∀ (z : Circle), ‖α z‖ = 1)
    (hα_range : range α = UnitCircle)
    (S_pts : Set EuclideanPlane)
    (δ : Circle → ℝ)
    (hδ_def : δ = fun z => 1 - pinchScale S_pts (α z))
    (hδ_bounds : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (U_E : Set EuclideanPlane)
    (hU_E_def : U_E = pinchHomeo S_pts '' OpenUnitDisc)
    (U_sub : Set ↑ClosedUnitDisc)
    (hU_sub_def : U_sub = Subtype.val ⁻¹' U_E)
    (D : Set S)
    (hD_def : D = f₀ '' U_sub)
    (hcMap_mem : ∀ (p : ℝ × Circle), max 0 (min 1 (1 - p.1)) • α p.2 ∈ ClosedUnitDisc)
    (cMap : ℝ × Circle → S)
    (hcMap_def : cMap = fun p : ℝ × Circle =>
      f₀ (⟨max (0 : ℝ) (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩ : ClosedUnitDisc))
    (hcMap_clamp : ∀ (p : ℝ × Circle), 0 ≤ p.1 → p.1 ≤ δ p.2 → max 0 (min 1 (1 - p.1)) = 1 - p.1) :
    cMap '' {p | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} = closure Λ \ D := by
  subst f₀ δ U_E U_sub D cMap
  let f₀ : ClosedUnitDisc → S := fun x => (φ₀ x).1
  let δ : Circle → ℝ := fun z => 1 - pinchScale S_pts (α z)
  let U_E : Set EuclideanPlane := pinchHomeo S_pts '' OpenUnitDisc
  let U_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' U_E
  let D : Set S := f₀ '' U_sub
  let cMap : ℝ × Circle → S := fun p => f₀ ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
  ext y
  constructor
  · rintro ⟨p, ⟨hp0, hpδ⟩, rfl⟩
    let x : ClosedUnitDisc := ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
    have hx_eq : x.1 = (1 - p.1) • α p.2 := by
      dsimp [x]
      rw [hcMap_clamp p hp0 hpδ]
    have hr_pos : 0 < 1 - p.1 := by linarith [(hδ_bounds p.2).2, hpδ]
    have hx_norm : ‖x.1‖ = 1 - p.1 := by
      rw [hx_eq, norm_smul, Real.norm_of_nonneg hr_pos.le, hα_norm p.2, mul_one]
    have hx_dir : unitDir x.1 = α p.2 := by
      rw [hx_eq, unitDir_smul hr_pos, unitDir_of_mem_unitCircle (hα_unit p.2)]
    refine ⟨(φ₀ x).2, ?_⟩
    rintro ⟨x', hx', h_eq⟩
    have hxx' : x = x' := hf₀_inj h_eq.symm
    have hx_in_UE : x.1 ∈ U_E := hxx' ▸ hx'
    have hlt : ‖x.1‖ < pinchScale S_pts (unitDir x.1) :=
      (mem_image_openUnitDisc_pinchHomeo S_pts x.1).mp hx_in_UE
    rw [hx_norm, hx_dir] at hlt
    dsimp only at hpδ
    linarith
  · rintro ⟨hy_cl, hy_not_D⟩
    obtain ⟨x, rfl⟩ : y ∈ range f₀ := hf₀_range ▸ hy_cl
    have hx_not_UE : x.1 ∉ U_E := fun hx => hy_not_D ⟨x, hx, rfl⟩
    have hge : pinchScale S_pts (unitDir x.1) ≤ ‖x.1‖ :=
      not_lt.mp (mt (mem_image_openUnitDisc_pinchHomeo S_pts x.1).mpr hx_not_UE)
    have hx_pos : 0 < ‖x.1‖ := (pinchScale_pos S_pts (unitDir x.1)).trans_le hge
    have hx_le_one : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
    obtain ⟨z, hz⟩ : unitDir x.1 ∈ range α := hα_range ▸ unitDir_mem_unitCircle hx_pos.ne'
    let t : ℝ := 1 - ‖x.1‖
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have htδ : t ≤ δ z := by
      dsimp [t, δ]
      rw [hz]
      linarith
    refine ⟨(t, z), ⟨ht0, htδ⟩, ?_⟩
    apply congrArg f₀
    apply Subtype.ext
    change max (0 : ℝ) (min 1 (1 - t)) • α z = x.1
    rw [hcMap_clamp (t, z) ht0 htδ]
    have h1 : 1 - t = ‖x.1‖ := by dsimp [t]; ring
    rw [h1, hz, norm_smul_unitDir]

private theorem radial_collar_inner_edge_is_disc_boundary
    {S : Type w}
    [TopologicalSpace S]
    (f₀ : ↑ClosedUnitDisc → S)
    (α : Circle → EuclideanPlane)
    (hα_unit : ∀ (z : Circle), α z ∈ UnitCircle)
    (hα_norm : ∀ (z : Circle), ‖α z‖ = 1)
    (hα_range : range α = UnitCircle)
    (S_pts : Set EuclideanPlane)
    (δ : Circle → ℝ)
    (hδ_def : δ = fun z => 1 - pinchScale S_pts (α z))
    (hδ_bounds : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (C_sub : Set ↑ClosedUnitDisc)
    (hC_sub_def : C_sub = Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle))
    (D : Set S)
    (hsubBd_D_f₀ : subBd D = f₀ '' C_sub)
    (hcMap_mem : ∀ (p : ℝ × Circle), max 0 (min 1 (1 - p.1)) • α p.2 ∈ ClosedUnitDisc)
    (cMap : ℝ × Circle → S)
    (hcMap_def : cMap = fun p : ℝ × Circle =>
      f₀ (⟨max (0 : ℝ) (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩ : ClosedUnitDisc))
    (hcMap_clamp : ∀ (p : ℝ × Circle), 0 ≤ p.1 → p.1 ≤ δ p.2 → max 0 (min 1 (1 - p.1)) = 1 - p.1) :
    cMap '' {p | p.1 = δ p.2} = subBd D := by
  subst δ C_sub cMap
  let δ : Circle → ℝ := fun z => 1 - pinchScale S_pts (α z)
  let C_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' (pinchHomeo S_pts '' UnitCircle)
  let cMap : ℝ × Circle → S := fun p => f₀ ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
  rw [hsubBd_D_f₀]
  ext y
  constructor
  · rintro ⟨p, hp_eq, rfl⟩
    have hp0 : 0 ≤ p.1 := hp_eq.symm ▸ (hδ_bounds p.2).1
    have hpδ : p.1 ≤ δ p.2 := hp_eq.le
    let x : ClosedUnitDisc := ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
    refine ⟨x, ?_, rfl⟩
    change x.1 ∈ pinchHomeo S_pts '' UnitCircle
    rw [mem_image_unitCircle_pinchHomeo]
    have hx_eq : x.1 = (1 - δ p.2) • α p.2 := by
      dsimp [x]
      rw [hcMap_clamp p hp0 hpδ, hp_eq]
    have hr_pos : 0 < 1 - δ p.2 := by linarith [(hδ_bounds p.2).2]
    rw [hx_eq, norm_smul, Real.norm_of_nonneg hr_pos.le, hα_norm p.2, mul_one,
      unitDir_smul hr_pos, unitDir_of_mem_unitCircle (hα_unit p.2)]
    dsimp [δ]
    ring
  · rintro ⟨x, hxC, rfl⟩
    have hnorm_eq : ‖x.1‖ = pinchScale S_pts (unitDir x.1) :=
      (mem_image_unitCircle_pinchHomeo S_pts x.1).mp hxC
    have hx_pos : 0 < ‖x.1‖ := hnorm_eq.symm ▸ pinchScale_pos S_pts (unitDir x.1)
    obtain ⟨z, hz⟩ : unitDir x.1 ∈ range α := hα_range ▸ unitDir_mem_unitCircle hx_pos.ne'
    refine ⟨(δ z, z), rfl, ?_⟩
    apply congrArg f₀
    apply Subtype.ext
    change max (0 : ℝ) (min 1 (1 - δ z)) • α z = x.1
    rw [hcMap_clamp (δ z, z) (hδ_bounds z).1 le_rfl]
    have h1 : 1 - δ z = ‖x.1‖ := by
      dsimp [δ]
      rw [hz, hnorm_eq]
      ring
    rw [h1, hz, norm_smul_unitDir]

private theorem open_radial_collar_covers_closed_disc_complement
    {S : Type w}
    [TopologicalSpace S]
    {Λ : Set S}
    (φ₀ : ↑ClosedUnitDisc ≃ₜ ↑(closure Λ))
    (f₀ : ↑ClosedUnitDisc → S)
    (hf₀_def : f₀ = fun x => (φ₀ x).1)
    (hf₀_inj : Function.Injective f₀)
    (hf₀_range : range f₀ = closure Λ)
    (α : Circle → EuclideanPlane)
    (hα_unit : ∀ (z : Circle), α z ∈ UnitCircle)
    (hα_norm : ∀ (z : Circle), ‖α z‖ = 1)
    (hα_range : range α = UnitCircle)
    (S_pts : Set EuclideanPlane)
    (δ : Circle → ℝ)
    (hδ_def : δ = fun z => 1 - pinchScale S_pts (α z))
    (hδ_bounds : ∀ (z : Circle), 0 ≤ δ z ∧ δ z ≤ 1 / 4)
    (K_E : Set EuclideanPlane)
    (hK_E_def : K_E = pinchHomeo S_pts '' ClosedUnitDisc)
    (K_sub : Set ↑ClosedUnitDisc)
    (hK_sub_def : K_sub = Subtype.val ⁻¹' K_E)
    (D : Set S)
    (hcl_D : closure D = f₀ '' K_sub)
    (hcMap_mem : ∀ (p : ℝ × Circle), max 0 (min 1 (1 - p.1)) • α p.2 ∈ ClosedUnitDisc)
    (cMap : ℝ × Circle → S)
    (hcMap_def : cMap = fun p : ℝ × Circle =>
      f₀ (⟨max (0 : ℝ) (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩ : ClosedUnitDisc))
    (hcMap_clamp : ∀ (p : ℝ × Circle), 0 ≤ p.1 → p.1 ≤ δ p.2 → max 0 (min 1 (1 - p.1)) = 1 - p.1) :
    cMap '' {p | 0 ≤ p.1 ∧ p.1 < δ p.2} = closure Λ \ closure D := by
  subst f₀ δ K_E K_sub cMap
  let f₀ : ClosedUnitDisc → S := fun x => (φ₀ x).1
  let δ : Circle → ℝ := fun z => 1 - pinchScale S_pts (α z)
  let K_E : Set EuclideanPlane := pinchHomeo S_pts '' ClosedUnitDisc
  let K_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' K_E
  let cMap : ℝ × Circle → S := fun p => f₀ ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
  ext y
  constructor
  · rintro ⟨p, ⟨hp0, hpδ⟩, rfl⟩
    let x : ClosedUnitDisc := ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
    have hx_eq : x.1 = (1 - p.1) • α p.2 := by
      dsimp [x]
      rw [hcMap_clamp p hp0 hpδ.le]
    have hr_pos : 0 < 1 - p.1 := by linarith [(hδ_bounds p.2).2, hpδ]
    have hx_norm : ‖x.1‖ = 1 - p.1 := by
      rw [hx_eq, norm_smul, Real.norm_of_nonneg hr_pos.le, hα_norm p.2, mul_one]
    have hx_dir : unitDir x.1 = α p.2 := by
      rw [hx_eq, unitDir_smul hr_pos, unitDir_of_mem_unitCircle (hα_unit p.2)]
    refine ⟨(φ₀ x).2, ?_⟩
    rw [hcl_D]
    rintro ⟨x', hx', h_eq⟩
    have hxx' : x = x' := hf₀_inj h_eq.symm
    have hx_in_KE : x.1 ∈ K_E := hxx' ▸ hx'
    have hle : ‖x.1‖ ≤ pinchScale S_pts (unitDir x.1) :=
      (mem_image_closedUnitDisc_pinchHomeo S_pts x.1).mp hx_in_KE
    rw [hx_norm, hx_dir] at hle
    dsimp only at hpδ
    linarith
  · rintro ⟨hy_cl, hy_not_clD⟩
    obtain ⟨x, rfl⟩ : y ∈ range f₀ := hf₀_range ▸ hy_cl
    have hx_not_KE : x.1 ∉ K_E := fun hx => hy_not_clD (hcl_D ▸ ⟨x, hx, rfl⟩)
    have hgt : pinchScale S_pts (unitDir x.1) < ‖x.1‖ :=
      not_le.mp (mt (mem_image_closedUnitDisc_pinchHomeo S_pts x.1).mpr hx_not_KE)
    have hx_pos : 0 < ‖x.1‖ := (pinchScale_pos S_pts (unitDir x.1)).trans hgt
    have hx_le_one : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
    obtain ⟨z, hz⟩ : unitDir x.1 ∈ range α := hα_range ▸ unitDir_mem_unitCircle hx_pos.ne'
    let t : ℝ := 1 - ‖x.1‖
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have htδ : t < δ z := by
      dsimp [t, δ]
      rw [hz]
      linarith
    refine ⟨(t, z), ⟨ht0, htδ⟩, ?_⟩
    apply congrArg f₀
    apply Subtype.ext
    change max (0 : ℝ) (min 1 (1 - t)) • α z = x.1
    rw [hcMap_clamp (t, z) ht0 htδ.le]
    have h1 : 1 - t = ‖x.1‖ := by dsimp [t]; ring
    rw [h1, hz, norm_smul_unitDir]

/-- Given a region `Λ` of `S` whose closure is a closed disc with boundary `subBd Λ`, a boundary
parametrization `g : Circle ≃ₜ subBd Λ`, and a nonempty closed subset `W_pts ⊆ Circle`, there exist
a continuous radial collar depth `δ : Circle → ℝ`, an open subdisc `D ⊆ Λ`, and a continuous map
`cMap : ℝ × Circle → S` parametrizing the pinched collar `closure Λ \ D`. -/
theorem exists_pinched_subdisc_of_region (hS : IsClosedSurface S)
    {Λ : Set S} (hΛ_open : IsOpen Λ) (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (g : Circle ≃ₜ subBd Λ)
    {W_pts : Set Circle} (hW_cl : IsClosed W_pts) (hW_ne : W_pts.Nonempty) :
    ∃ (δ : Circle → ℝ) (D : Set S) (cMap : ℝ × Circle → S),
      Continuous δ ∧
      (∀ z, 0 ≤ δ z ∧ δ z ≤ 1 / 4) ∧
      (∀ z, δ z = 0 ↔ z ∈ W_pts) ∧
      IsOpen D ∧ D ⊆ Λ ∧
      IsClosedDisc (closure D) ∧
      subBd D = closure D \ D ∧
      IsOArc (subBd D) ∧
      (∀ x ∈ closure D \ D, x ∈ closure (closure D)ᶜ) ∧
      subBd D ∩ subBd Λ = (fun z => (g z).1) '' W_pts ∧
      subBd D \ ((fun z => (g z).1) '' W_pts) ⊆ Λ ∧
      subBd D \ ((fun z => (g z).1) '' W_pts) ⊆ closure (Λ \ closure D) ∧
      Continuous cMap ∧
      Set.InjOn cMap {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} ∧
      (∀ z : Circle, cMap (0, z) = (g z).1) ∧
      cMap '' {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} = closure Λ \ D ∧
      cMap '' {p : ℝ × Circle | p.1 = δ p.2} = subBd D ∧
      cMap '' {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 < δ p.2} = closure Λ \ closure D := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hsubBd_eq : closure Λ \ Λ = subBd Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  obtain ⟨φ₀⟩ := hCD
  let f₀ : ClosedUnitDisc → S := fun x => (φ₀ x).1
  have hf₀_cont : Continuous f₀ := continuous_subtype_val.comp φ₀.continuous
  have hf₀_inj : Function.Injective f₀ := Subtype.val_injective.comp φ₀.injective
  have hf₀_emb : IsClosedEmbedding f₀ := hf₀_cont.isClosedEmbedding hf₀_inj
  have hf₀_range : range f₀ = closure Λ := by
    ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact (φ₀ x).2, fun hy => ⟨φ₀.symm ⟨y, hy⟩, by simp [f₀]⟩⟩
  have hf₀_bd : f₀ '' {x : ClosedUnitDisc | x.1 ∈ UnitCircle} = subBd Λ := by
    rw [← hdiscBd, disc_boundary (closure Λ) φ₀]
  have hCD_split : ∀ x : ClosedUnitDisc, x.1 ∈ OpenUnitDisc ↔ x.1 ∉ UnitCircle := by
    intro x
    have hx_le : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
    simp only [OpenUnitDisc, UnitCircle, Metric.mem_ball, Metric.mem_sphere, dist_zero_right]
    exact ⟨fun h => ne_of_lt h, fun h => lt_of_le_of_ne hx_le h⟩
  have hf₀_int : f₀ '' {x : ClosedUnitDisc | x.1 ∈ OpenUnitDisc} = Λ := by
    exact closed_disc_coordinates_map_interior (S := S) (Λ := Λ) hsubBd_eq φ₀ f₀ rfl hf₀_inj
      hf₀_range hf₀_bd hCD_split
  have hgz_cl : ∀ z : Circle, (g z).1 ∈ closure Λ := fun z => by
    have hmem : (g z).1 ∈ closure Λ \ Λ := by
      rw [hsubBd_eq]
      exact (g z).2
    exact hmem.1
  let α₀ : Circle → ClosedUnitDisc := fun z =>
    φ₀.symm ⟨(g z).1, hgz_cl z⟩
  let α : Circle → EuclideanPlane := fun z => (α₀ z).1
  have hf₀_α₀ : ∀ z : Circle, f₀ (α₀ z) = (g z).1 := fun z => by
    simp [f₀, α₀]
  have hα_cont : Continuous α :=
    continuous_subtype_val.comp (φ₀.symm.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp g.continuous) _))
  have hα_inj : Function.Injective α := by
    intro z₁ z₂ h
    have h₀ : α₀ z₁ = α₀ z₂ := Subtype.ext h
    have hg : (g z₁).1 = (g z₂).1 := by rw [← hf₀_α₀, h₀, hf₀_α₀]
    exact g.injective (Subtype.ext hg)
  have hα_unit : ∀ z : Circle, α z ∈ UnitCircle := by
    intro z
    have hmem : f₀ (α₀ z) ∈ f₀ '' {x : ClosedUnitDisc | x.1 ∈ UnitCircle} := by
      rw [hf₀_bd, hf₀_α₀]
      exact (g z).2
    rcases hmem with ⟨x, hx, h_eq⟩
    have hxx : α z = x.1 := congrArg Subtype.val (hf₀_inj h_eq.symm)
    exact hxx.symm ▸ hx
  have hα_norm : ∀ z : Circle, ‖α z‖ = 1 := fun z => by
    simpa [UnitCircle] using hα_unit z
  have hα_range : range α = UnitCircle := by
    exact boundary_coordinates_are_surjective (S := S) (Λ := Λ) g f₀ hf₀_inj hf₀_bd α₀ α rfl hf₀_α₀
      hα_unit
  let S_pts : Set EuclideanPlane := α '' W_pts
  have hS_cl : IsClosed S_pts := (hW_cl.isCompact.image hα_cont).isClosed
  have hS_ne : S_pts.Nonempty := hW_ne.image α
  have hS_sub : S_pts ⊆ UnitCircle := image_subset_iff.mpr fun z _ => hα_unit z
  have hS_mem : ∀ z : Circle, α z ∈ S_pts ↔ z ∈ W_pts := fun z => hα_inj.mem_set_image
  let δ : Circle → ℝ := fun z => 1 - pinchScale S_pts (α z)
  have hδ_cont : Continuous δ :=
    continuous_const.sub ((continuous_pinchScale S_pts).comp hα_cont)
  have hδ_bounds : ∀ z : Circle, 0 ≤ δ z ∧ δ z ≤ 1 / 4 := by
    intro z
    have hb := pinchScale_bounds S_pts (α z)
    dsimp [δ]
    constructor <;> linarith
  have hδ_zero : ∀ z : Circle, δ z = 0 ↔ z ∈ W_pts := by
    intro z
    dsimp [δ]
    rw [sub_eq_zero, eq_comm, pinchScale_eq_one_iff hS_cl hS_ne (α z), hS_mem z]
  let U_E : Set EuclideanPlane := pinchHomeo S_pts '' OpenUnitDisc
  let K_E : Set EuclideanPlane := pinchHomeo S_pts '' ClosedUnitDisc
  let C_E : Set EuclideanPlane := pinchHomeo S_pts '' UnitCircle
  let U_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' U_E
  let K_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' K_E
  let C_sub : Set ClosedUnitDisc := Subtype.val ⁻¹' C_E
  let D : Set S := f₀ '' U_sub
  have hU_E_sub_open : U_E ⊆ OpenUnitDisc := image_openUnitDisc_pinchHomeo_subset S_pts
  have hK_E_sub_cl : K_E ⊆ ClosedUnitDisc := image_closedUnitDisc_pinchHomeo_subset S_pts
  have hC_E_eq : K_E \ U_E = C_E := image_closedUnitDisc_sdiff_openUnitDisc_pinchHomeo S_pts
  have hC_sub_eq : K_sub \ U_sub = C_sub := by
    ext x
    change x.1 ∈ K_E \ U_E ↔ x.1 ∈ C_E
    rw [hC_E_eq]
  have hU_sub_open : IsOpen U_sub :=
    ((pinchHomeo S_pts).isOpenMap _ Metric.isOpen_ball).preimage continuous_subtype_val
  have hD_sub_Λ : D ⊆ Λ := by
    rw [← hf₀_int]
    refine image_mono ?_
    intro x hx
    exact hU_E_sub_open hx
  have hD_open : IsOpen D := by
    exact pinched_disc_image_is_open (S := S) (Λ := Λ) hΛ_open φ₀ f₀ rfl U_sub D rfl hU_sub_open
      hD_sub_Λ
  have hcl_U_sub : closure U_sub = K_sub := by
    exact closure_of_pinched_open_unit_disc S_pts U_E rfl U_sub rfl K_sub rfl hU_E_sub_open
  have hcl_D : closure D = f₀ '' K_sub := by
    rw [← hcl_U_sub]
    apply subset_antisymm
    · exact (hf₀_emb.isClosedMap _ isClosed_closure).closure_subset_iff.mpr
        (image_mono subset_closure)
    · exact image_closure_subset_closure_image hf₀_cont
  have hsubBd_D_eq : subBd D = closure D \ D := by
    rw [subBd_eq_frontier, hD_open.frontier_eq]
  have hsubBd_D_f₀ : subBd D = f₀ '' C_sub := by
    rw [hsubBd_D_eq, hcl_D, ← image_sdiff hf₀_inj, hC_sub_eq]
  have hCD_D : IsClosedDisc (closure D) := by
    exact pinched_closed_disc_image (S := S) f₀ hf₀_cont hf₀_inj S_pts K_E rfl K_sub rfl D
      hK_E_sub_cl hcl_D
  have hOArc_D : IsOArc (subBd D) := by
    exact pinched_disc_boundary_is_closed_curve (S := S) f₀ hf₀_cont hf₀_inj α hα_cont hα_inj
      hα_unit hα_range S_pts K_E rfl C_sub rfl D hK_E_sub_cl hsubBd_D_f₀
  have hsubBd_inter : subBd D ∩ subBd Λ = (fun z => (g z).1) '' W_pts := by
    exact pinched_boundary_meets_original_at_marks (S := S) (Λ := Λ) g (W_pts := W_pts) f₀ hf₀_inj
      hf₀_bd α₀ α rfl hf₀_α₀ S_pts rfl hS_cl hS_ne hS_sub C_sub rfl D hsubBd_D_f₀
  have hsubBd_sdiff_Λ : subBd D \ ((fun z => (g z).1) '' W_pts) ⊆ Λ := by
    intro y hy
    have hy_cl : y ∈ closure Λ := by
      have hy_clD : y ∈ closure D := (hsubBd_D_eq ▸ hy.1).1
      rw [hcl_D] at hy_clD
      rcases hy_clD with ⟨x, _, rfl⟩
      exact (φ₀ x).2
    have hy_not_bd : y ∉ subBd Λ := fun hy_bd => hy.2 (hsubBd_inter ▸ ⟨hy.1, hy_bd⟩)
    by_contra hy_not_Λ
    exact hy_not_bd (hsubBd_eq ▸ ⟨hy_cl, hy_not_Λ⟩)
  have hsubBd_sdiff_cl : subBd D \ ((fun z => (g z).1) '' W_pts) ⊆ closure (Λ \ closure D) := by
    exact pinched_boundary_off_marks_in_outer_closure (S := S) (Λ := Λ) g (W_pts := W_pts) f₀
      hf₀_cont hf₀_inj hf₀_int α₀ α rfl hf₀_α₀ S_pts rfl hS_cl hS_ne hS_sub K_E rfl K_sub rfl C_sub
        rfl
      D hcl_D hsubBd_D_f₀
  have hout_D : ∀ x ∈ closure D \ D, x ∈ closure (closure D)ᶜ := by
    intro x hx
    rw [← hsubBd_D_eq] at hx
    by_cases hxW : x ∈ (fun z => (g z).1) '' W_pts
    · have hx_bdΛ : x ∈ closure Λ \ Λ := by
        rw [hsubBd_eq]
        exact (hsubBd_inter ▸ hxW).2
      have hx_outΛ := hout x hx_bdΛ
      refine closure_mono (compl_subset_compl.mpr ?_) hx_outΛ
      exact closure_mono hD_sub_Λ
    · refine closure_mono ?_ (hsubBd_sdiff_cl ⟨hx, hxW⟩)
      intro y hy
      exact hy.2
  have hcMap_mem : ∀ p : ℝ × Circle, max 0 (min 1 (1 - p.1)) • α p.2 ∈ ClosedUnitDisc := by
    intro p
    have hr0 : 0 ≤ max 0 (min 1 (1 - p.1)) := le_max_left 0 _
    have hr1 : max 0 (min 1 (1 - p.1)) ≤ 1 := max_le zero_le_one (min_le_left 1 _)
    simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hr0, hα_norm p.2, mul_one]
    exact hr1
  let cMap : ℝ × Circle → S := fun p => f₀ ⟨max 0 (min 1 (1 - p.1)) • α p.2, hcMap_mem p⟩
  have hcMap_cont : Continuous cMap := by
    refine hf₀_cont.comp (Continuous.subtype_mk ?_ _)
    have hcont_r : Continuous (fun p : ℝ × Circle => max (0 : ℝ) (min 1 (1 - p.1))) :=
      continuous_const.max (continuous_const.min (continuous_const.sub continuous_fst))
    exact hcont_r.smul (hα_cont.comp continuous_snd)
  have hcMap_clamp : ∀ p : ℝ × Circle, 0 ≤ p.1 → p.1 ≤ δ p.2 →
      max 0 (min 1 (1 - p.1)) = 1 - p.1 := by
    intro p hp0 hpδ
    have hδ_le : δ p.2 ≤ 1 / 4 := (hδ_bounds p.2).2
    have h1 : 1 - p.1 ≤ 1 := by linarith
    have h0 : 0 ≤ 1 - p.1 := by linarith
    rw [min_eq_right h1, max_eq_right h0]
  have hcMap_inj : Set.InjOn cMap {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} := by
    exact radial_collar_map_injective (S := S) f₀ hf₀_inj α hα_inj hα_norm δ hδ_bounds
      hcMap_mem cMap rfl hcMap_clamp
  have hcMap_zero : ∀ z : Circle, cMap (0, z) = (g z).1 := by
    intro z
    dsimp [cMap]
    have hsub : (⟨max (0 : ℝ) (min 1 (1 - 0)) • α z, hcMap_mem (0, z)⟩ : ClosedUnitDisc) = α₀ z
      := by
      apply Subtype.ext
      simp [α]
    rw [hsub, hf₀_α₀]
  have hcMap_collar : cMap '' {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 ≤ δ p.2} = closure Λ \ D := by
    exact radial_collar_covers_disc_complement (S := S) (Λ := Λ) φ₀ f₀ rfl hf₀_inj hf₀_range α
      hα_unit hα_norm hα_range S_pts δ rfl hδ_bounds U_E rfl U_sub rfl D rfl hcMap_mem cMap rfl
      hcMap_clamp
  have hcMap_bd : cMap '' {p : ℝ × Circle | p.1 = δ p.2} = subBd D := by
    exact radial_collar_inner_edge_is_disc_boundary (S := S) f₀ α hα_unit hα_norm hα_range S_pts δ
      rfl hδ_bounds C_sub rfl D hsubBd_D_f₀ hcMap_mem cMap rfl hcMap_clamp
  have hcMap_open_collar : cMap '' {p : ℝ × Circle | 0 ≤ p.1 ∧ p.1 < δ p.2} = closure Λ \ closure D
    := by
    exact open_radial_collar_covers_closed_disc_complement (S := S) (Λ := Λ) φ₀ f₀ rfl hf₀_inj
      hf₀_range α hα_unit hα_norm hα_range S_pts δ rfl hδ_bounds K_E rfl K_sub rfl D hcl_D
      hcMap_mem cMap rfl hcMap_clamp
  exact ⟨δ, D, cMap, hδ_cont, hδ_bounds, hδ_zero, hD_open, hD_sub_Λ, hCD_D, hsubBd_D_eq,
    hOArc_D, hout_D, hsubBd_inter, hsubBd_sdiff_Λ, hsubBd_sdiff_cl, hcMap_cont, hcMap_inj,
    hcMap_zero, hcMap_collar, hcMap_bd, hcMap_open_collar⟩

/-! ## Gluing a Compact Space along its Boundary -/

/-- The gluing relation on `X ⊕ ULift.{w} Y` identifying `b z ∈ X` with `z.1 ∈ B ⊆ Y`. -/
def glueRel {X : Type w} {Y : Type} {B : Set Y} (b : ↥B → X)
    (a a' : X ⊕ ULift.{w} Y) : Prop :=
  a = a' ∨
    (∃ z : ↥B, a = .inl (b z) ∧ a' = .inr (ULift.up z.1)) ∨
    (∃ z : ↥B, a = .inr (ULift.up z.1) ∧ a' = .inl (b z))

/-- The equivalence relation `glueRel b` when `b` is injective. -/
def glueSetoid {X : Type w} {Y : Type} {B : Set Y} {b : ↥B → X}
    (hb : Function.Injective b) : Setoid (X ⊕ ULift.{w} Y) where
  r := glueRel b
  iseqv :=
    { refl := fun _ => .inl rfl
      symm := by
        rintro a a' (rfl | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩)
        · exact .inl rfl
        · exact .inr (.inr ⟨z, rfl, rfl⟩)
        · exact .inr (.inl ⟨z, rfl, rfl⟩)
      trans := by
        rintro a a' a'' (rfl | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩) h'
        · exact h'
        · obtain rfl | ⟨w, h1, rfl⟩ | ⟨w, h1, rfl⟩ := h'
          · exact .inr (.inl ⟨z, rfl, rfl⟩)
          · exact absurd h1 (by simp)
          · have hzw : z = w := Subtype.ext (ULift.up.inj (Sum.inr.inj h1))
            subst hzw
            exact .inl rfl
        · obtain rfl | ⟨w, h1, rfl⟩ | ⟨w, h1, rfl⟩ := h'
          · exact .inr (.inr ⟨z, rfl, rfl⟩)
          · have hzw : z = w := hb (Sum.inl.inj h1)
            subst hzw
            exact .inl rfl
          · exact absurd h1 (by simp) }

/-- The quotient space obtained by gluing `X` and `Y` along `b : ↥B → X`. -/
def GluedSpace {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) : Type w :=
  Quotient (glueSetoid hb)

instance {X : Type w} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    TopologicalSpace (GluedSpace hb) :=
  inferInstanceAs (TopologicalSpace (Quotient (glueSetoid hb)))

/-- Left inclusion `X → GluedSpace hb`. -/
def GluedSpace.inl {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) (x : X) : GluedSpace hb :=
  Quotient.mk (glueSetoid hb) (.inl x)

/-- Right inclusion `Y → GluedSpace hb`. -/
def GluedSpace.inr {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) (y : Y) : GluedSpace hb :=
  Quotient.mk (glueSetoid hb) (.inr (ULift.up y))

theorem GluedSpace.inl_injective {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    Function.Injective (GluedSpace.inl hb) := by
  intro x x' h
  obtain h1 | ⟨z, -, h1⟩ | ⟨z, h1, -⟩ := Quotient.exact h
  · exact Sum.inl.inj h1
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)

theorem GluedSpace.inr_injective {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    Function.Injective (GluedSpace.inr hb) := by
  intro y y' h
  obtain h1 | ⟨z, h1, -⟩ | ⟨z, -, h1⟩ := Quotient.exact h
  · exact ULift.up.inj (Sum.inr.inj h1)
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)

theorem GluedSpace.inl_eq_inr {X : Type w} {Y : Type}
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) {x : X} {y : Y} :
    GluedSpace.inl hb x = GluedSpace.inr hb y ↔ ∃ hy : y ∈ B, x = b ⟨y, hy⟩ := by
  constructor
  · intro h
    obtain h1 | ⟨z, h1, h2⟩ | ⟨z, h1, -⟩ := Quotient.exact h
    · exact absurd h1 (by simp)
    · have hyz : y = z.1 := ULift.up.inj (Sum.inr.inj h2)
      subst hyz
      exact ⟨z.2, Sum.inl.inj h1⟩
    · exact absurd h1 (by simp)
  · rintro ⟨hy, rfl⟩
    exact Quotient.sound (.inr (.inl ⟨⟨y, hy⟩, rfl, rfl⟩))

theorem GluedSpace.continuous_inl {X : Type w} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    Continuous (GluedSpace.inl hb) :=
  continuous_quotient_mk'.comp _root_.continuous_inl

theorem GluedSpace.continuous_inr {X : Type w} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y]
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    Continuous (GluedSpace.inr hb) :=
  continuous_quotient_mk'.comp (_root_.continuous_inr.comp continuous_uliftUp)

theorem GluedSpace.range_inl_union_range_inr {X : Type w}
    {Y : Type} {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    range (GluedSpace.inl hb) ∪ range (GluedSpace.inr hb) = univ := by
  rw [eq_univ_iff_forall]
  intro p
  obtain ⟨x | y, rfl⟩ := Quotient.exists_rep p
  · exact .inl ⟨x, rfl⟩
  · exact .inr ⟨y.down, rfl⟩

theorem GluedSpace.range_inl_inter_range_inr {X : Type w}
    {Y : Type} {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    range (GluedSpace.inl hb) ∩ range (GluedSpace.inr hb) = GluedSpace.inl hb '' range b := by
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, he⟩⟩
    obtain ⟨hy, rfl⟩ := (GluedSpace.inl_eq_inr hb).mp he.symm
    exact ⟨b ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨⟨b z, rfl⟩, ⟨z.1, ((GluedSpace.inl_eq_inr hb).mpr ⟨z.2, rfl⟩).symm⟩⟩

theorem GluedSpace.range_inl_inter_range_inr_eq_inr {X : Type w}
    {Y : Type} {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    range (GluedSpace.inl hb) ∩ range (GluedSpace.inr hb) = GluedSpace.inr hb '' B := by
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, he⟩⟩
    obtain ⟨hy, rfl⟩ := (GluedSpace.inl_eq_inr hb).mp he.symm
    exact ⟨y, hy, he⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨b ⟨y, hy⟩, (GluedSpace.inl_eq_inr hb).mpr ⟨hy, rfl⟩⟩, ⟨y, rfl⟩⟩

instance {X : Type w} [TopologicalSpace X] [CompactSpace X]
    {Y : Type} [TopologicalSpace Y] [CompactSpace Y]
    {B : Set Y} {b : ↥B → X} (hb : Function.Injective b) :
    CompactSpace (GluedSpace hb) :=
  inferInstanceAs (CompactSpace (Quotient (glueSetoid hb)))

theorem GluedSpace.t2Space {X : Type w} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {B : Set Y} (hB : IsClosed B) {b : ↥B → X}
    (hb_cont : Continuous b) (hb : Function.Injective b) :
    T2Space (GluedSpace hb) := by
  have : CompactSpace ↥B := isCompact_iff_compactSpace.mp hB.isCompact
  refine t2Space_quotient_of_isClosed (glueSetoid hb) ?_
  let f : ↥B → (X ⊕ ULift.{w} Y) × (X ⊕ ULift.{w} Y) :=
    fun z => (.inl (b z), .inr (ULift.up z.1))
  have hf_cont : Continuous f :=
    (_root_.continuous_inl.comp hb_cont).prodMk
      (_root_.continuous_inr.comp (continuous_uliftUp.comp continuous_subtype_val))
  have hG : IsCompact (range f) := isCompact_range hf_cont
  have hG' : IsCompact (Prod.swap '' range f) := hG.image continuous_swap
  have hrel : {p : (X ⊕ ULift.{w} Y) × (X ⊕ ULift.{w} Y) | (glueSetoid hb) p.1 p.2} =
      diagonal _ ∪ (range f ∪ Prod.swap '' range f) := by
    ext ⟨a, a'⟩
    constructor
    · rintro (h | ⟨z, h1, h2⟩ | ⟨z, h1, h2⟩)
      · exact .inl h
      · exact .inr (.inl ⟨z, Prod.ext h1.symm h2.symm⟩)
      · exact .inr (.inr ⟨f z, ⟨z, rfl⟩, Prod.ext h1.symm h2.symm⟩)
    · rintro (h | ⟨z, he⟩ | ⟨_, ⟨z, rfl⟩, he⟩)
      · exact .inl h
      · simp only [f, Prod.mk.injEq] at he
        exact .inr (.inl ⟨z, he.1.symm, he.2.symm⟩)
      · simp only [f, Prod.swap_prod_mk, Prod.mk.injEq] at he
        exact .inr (.inr ⟨z, he.1.symm, he.2.symm⟩)
  rw [hrel]
  exact isClosed_diagonal.union (hG.isClosed.union hG'.isClosed)

theorem GluedSpace.connectedSpace {X : Type w} [TopologicalSpace X] [ConnectedSpace X]
    {Y : Type} [TopologicalSpace Y] [ConnectedSpace Y]
    {B : Set Y} (hB_ne : B.Nonempty) {b : ↥B → X} (hb : Function.Injective b) :
    ConnectedSpace (GluedSpace hb) := by
  rw [connectedSpace_iff_univ, ← GluedSpace.range_inl_union_range_inr hb]
  refine (isConnected_range (GluedSpace.continuous_inl hb)).union ?_
    (isConnected_range (GluedSpace.continuous_inr hb))
  rw [GluedSpace.range_inl_inter_range_inr_eq_inr hb]
  exact hB_ne.image (GluedSpace.inr hb)

private theorem cylinder_boundary_image {S : Type w} [TopologicalSpace S] {D : Set S}
    (e : ClosedCylinder ≃ₜ D) (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2) :
    Subtype.val '' bd ↥D =
      range (fun w => (e (cylEnd 1 m1 w)).1) ∪ range (fun w => (e (cylEnd 2 m2 w)).1) := by
  rw [← image_bd_homeomorph e, ← image_comp, bd_cylinder, image_union, ← range_comp, ← range_comp]
  rfl

private theorem cylinder_coordinate_map_injective
    {S : Type w} [TopologicalSpace S] {D : Set S}
    (e : ClosedCylinder ≃ₜ D)
    (hmem : ∀ (p : Circle × unitInterval), (1 + (p.2 : ℝ), p.1) ∈ ClosedCylinder) :
    Function.Injective (fun p : Circle × unitInterval => (e ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1) := by
  rintro ⟨w, t⟩ ⟨w', t'⟩ he
  have h3 := e.injective (Subtype.ext he)
  have h4 := Prod.ext_iff.mp (congrArg Subtype.val h3)
  have h5 : (t : ℝ) = t' := by
    have := h4.1
    simp only at this
    linarith
  exact Prod.ext h4.2 (Subtype.ext h5)

private theorem cylinder_with_complement_covers
    {S : Type w} [TopologicalSpace S] (S₁ S₂ : Set S) (e : ClosedCylinder ≃ₜ S₂)
    (hu : S₁ ∪ S₂ = univ)
    (hmem : ∀ (p : Circle × unitInterval), (1 + (p.2 : ℝ), p.1) ∈ ClosedCylinder) :
    ∀ x : S, x ∈ range (Subtype.val : ↥S₁ → S) ∨ x ∈ range
      (fun p : Circle × unitInterval => (e ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1) := by
  intro x
  rcases (hu ▸ mem_univ x : x ∈ S₁ ∪ S₂) with h3 | h3
  · exact .inl ⟨⟨x, h3⟩, rfl⟩
  · right
    obtain ⟨⟨⟨r, w⟩, hr, hru⟩, he⟩ := e.surjective ⟨x, h3⟩
    have ht : r - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    let p : Circle × unitInterval := (w, ⟨r - 1, ht⟩)
    refine ⟨p, ?_⟩
    have h4 : (⟨(1 + (p.2 : ℝ), p.1), hmem p⟩ : ClosedCylinder) = ⟨(r, w), hr, hru⟩ :=
      Subtype.ext (Prod.ext (by simp [p]) rfl)
    change (e ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1 = x
    rw [h4, he]

private theorem cylinder_attaches_only_along_end_circles
    {S' : Type w} [TopologicalSpace S'] (S₁ S₂ : Set S')
    (e₂ : ClosedCylinder ≃ₜ S₂) (h2 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₂)
    (m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2) (m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2)
    (hmem : ∀ (p : Circle × unitInterval), (1 + (p.2 : ℝ), p.1) ∈ ClosedCylinder)
    (hbd₂ : Subtype.val '' bd ↥S₂ =
      range (fun w => (e₂ (cylEnd 1 m1 w)).1) ∪ range (fun w => (e₂ (cylEnd 2 m2 w)).1)) :
    ∀ (y : ↥S₁) (p : Circle × unitInterval), y.1 = (e₂ ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1 →
      ((p.2 : ℝ) = 0 ∧ y.1 ∈ range (fun w => (e₂ (cylEnd 1 m1 w)).1)) ∨
      ((p.2 : ℝ) = 1 ∧ y.1 ∈ range (fun w => (e₂ (cylEnd 2 m2 w)).1)) := by
  let f₁ : Circle → S' := fun w => (e₂ (cylEnd 1 m1 w)).1
  let f₂ : Circle → S' := fun w => (e₂ (cylEnd 2 m2 w)).1
  let c : Circle × unitInterval → S' := fun p => (e₂ ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1
  rintro y ⟨w, t⟩ he
  have h3 : y.1 ∈ S₁ ∩ S₂ := ⟨y.2, he ▸ (e₂ _).2⟩
  rw [h2, hbd₂] at h3
  rcases h3 with ⟨w', hw⟩ | ⟨w', hw⟩
  · left
    refine ⟨?_, ⟨w', hw⟩⟩
    have h4 : f₁ w' = c (w, t) := hw.trans he
    have h5 := e₂.injective (Subtype.ext h4)
    have h6 : (1 : ℝ) = 1 + t := congrArg (fun p : ClosedCylinder => p.1.1) h5
    simp only; linarith
  · right
    refine ⟨?_, ⟨w', hw⟩⟩
    have h4 : f₂ w' = c (w, t) := hw.trans he
    have h5 := e₂.injective (Subtype.ext h4)
    have h6 : (2 : ℝ) = 1 + t := congrArg (fun p : ClosedCylinder => p.1.1) h5
    simp only; linarith

/-- Gluing `ClosedCylinder` onto `↥(univ \ (Λ₁ ∪ Λ₂))` along a homeomorphism `b` between their
boundaries yields a closed connected surface `GluedSpace hb` obtained by adding a handle to `S`. -/
theorem isClosedSurface_of_handle_glue [ConnectedSpace S] (hS : IsClosedSurface S)
    {Λ₁ Λ₂ : Set S} (hΛ₁ : IsOpenDisc Λ₁) (hΛ₂ : IsOpenDisc Λ₂)
    (hd : Disjoint (closure Λ₁) (closure Λ₂))
    (hOArc₁ : IsOArc (subBd Λ₁)) (hOArc₂ : IsOArc (subBd Λ₂))
    (hout₁ : ∀ x ∈ closure Λ₁ \ Λ₁, x ∈ closure (closure Λ₁)ᶜ)
    (hout₂ : ∀ x ∈ closure Λ₂ \ Λ₂, x ∈ closure (closure Λ₂)ᶜ)
    {b : ↥(bd ↥ClosedCylinder) → ↥(univ \ (Λ₁ ∪ Λ₂) : Set S)}
    (hb_cont : Continuous b) (hb_inj : Function.Injective b)
    (hb_range : range b = bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S)) :
    IsClosedSurface (GluedSpace hb_inj) ∧
      ConnectedSpace (GluedSpace hb_inj) ∧
      IsObtainedByAddingHandle S (GluedSpace hb_inj) ∧
      IsSurface ↥(range (GluedSpace.inl hb_inj)) ∧
      IsSurface ↥(range (GluedSpace.inr hb_inj)) ∧
      range (GluedSpace.inl hb_inj) ∪ range (GluedSpace.inr hb_inj) = univ ∧
      range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj) =
        Subtype.val '' bd ↥(range (GluedSpace.inl hb_inj)) ∧
      range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj) =
        Subtype.val '' bd ↥(range (GluedSpace.inr hb_inj)) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hS_surf : IsSurface S := IsClosedSurface.isSurface hS
  have hbS : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS.2.2 x)
  obtain ⟨hX_surf, hX_conn, hX_bd⟩ :=
    compl_two_open_isSurface hS hΛ₁.1 hΛ₂.1 hOArc₁ hOArc₂ hout₁ hout₂ hd
  have : CompactSpace ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) := hX_surf.1
  obtain ⟨m_cyl⟩ := nonempty_cyl_homeo
  have hCyl_surf : IsSurface ↥ClosedCylinder :=
    isSurface_of_homeo m_cyl (isSurface_model 0 0 2).1
  have : CompactSpace ↥ClosedCylinder := hCyl_surf.1
  have : ConnectedSpace (SurfaceModel 0 0 2) := (isSurface_model 0 0 2).2
  have hCyl_conn : ConnectedSpace ↥ClosedCylinder :=
    m_cyl.surjective.connectedSpace m_cyl.continuous
  have : T2Space (GluedSpace hb_inj) := GluedSpace.t2Space (isClosed_bd ↥ClosedCylinder) hb_cont
    hb_inj
  have hbd_cyl_ne : (bd ↥ClosedCylinder).Nonempty := by
    rw [bd_cylinder]
    exact .inl ⟨cylEnd 1 (by norm_num) 1, 1, rfl⟩
  have hconn' : ConnectedSpace (GluedSpace hb_inj) :=
    @GluedSpace.connectedSpace _ _ hX_conn _ _ hCyl_conn _ hbd_cyl_ne _ hb_inj
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ (Λ₁ ∪ Λ₂) : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let e₂ : ↥ClosedCylinder ≃ₜ ↥S₂ := hinr_emb.isEmbedding.toHomeomorph
  have hS₁ : IsSurface ↥S₁ := isSurface_of_homeo e₁ hX_surf
  have hS₂ : IsSurface ↥S₂ := isSurface_of_homeo e₂ hCyl_surf
  have hu : S₁ ∪ S₂ = univ := GluedSpace.range_inl_union_range_inr hb_inj
  have h1 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₁ := by
    rw [← image_bd_homeomorph e₁, image_image]
    change S₁ ∩ S₂ = GluedSpace.inl hb_inj '' bd ↥(univ \ (Λ₁ ∪ Λ₂) : Set S)
    rw [← hb_range, GluedSpace.range_inl_inter_range_inr hb_inj]
  have h2 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₂ := by
    rw [← image_bd_homeomorph e₂, image_image]
    exact GluedSpace.range_inl_inter_range_inr_eq_inr hb_inj
  obtain ⟨a₀, b₀, c₀, ⟨e_S₀⟩⟩ := classification.{w} S hS_surf inferInstance
  obtain ⟨_, f₀, hf₀⟩ := presents_ew a₀ b₀ c₀
  have hc₀ : c₀ = 0 := by
    have h_cuffs : cuffs S = ∅ := by
      unfold cuffs
      rw [hbS]
      ext C
      simp [componentsIn]
    rw [← ncard_cuffs hf₀, ← ncard_cuffs_congr e_S₀, h_cuffs, ncard_empty]
  subst hc₀
  let e₁' : ↥(Λ₁ ∪ Λ₂)ᶜ ≃ₜ ↥S₁ := (Homeomorph.setCongr (compl_eq_univ_sdiff _)).trans e₁
  have hX : IsSurface ↥(Λ₁ ∪ Λ₂)ᶜ := isSurface_of_homeo e₁'.symm hS₁
  have hc₁ : CompactSpace ↥S₁ := hS₁.1
  have hval₂ : IsClosedEmbedding (Subtype.val : ↥S₂ → S') :=
    (isCompact_iff_compactSpace.mpr hS₂.1).isClosed.isClosedEmbedding_subtypeVal
  have hval₁ : IsClosedEmbedding (Subtype.val : ↥S₁ → S') :=
    (isCompact_iff_compactSpace.mpr hc₁).isClosed.isClosedEmbedding_subtypeVal
  have m1 : (1 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  have m2 : (2 : ℝ) ∈ Icc (1 : ℝ) 2 := by norm_num
  let f₁ : Circle → S' := fun w => (e₂ (cylEnd 1 m1 w)).1
  let f₂ : Circle → S' := fun w => (e₂ (cylEnd 2 m2 w)).1
  have hf₁ : IsEmbedding f₁ := hval₂.isEmbedding.comp (e₂.isEmbedding.comp
    (isEmbedding_cylEnd 1 m1))
  have hf₂ : IsEmbedding f₂ := hval₂.isEmbedding.comp (e₂.isEmbedding.comp
    (isEmbedding_cylEnd 2 m2))
  have hbd₂ : Subtype.val '' bd ↥S₂ = range f₁ ∪ range f₂ :=
    cylinder_boundary_image e₂ m1 m2
  have hs : Subtype.val '' bd ↥S₁ = range f₁ ∪ range f₂ := h1.symm.trans (h2.trans hbd₂)
  have hsub₁ : range f₁ ⊆ S₁ := fun x hx => (show x ∈ S₁ ∩ S₂ by rw [h2, hbd₂]; exact .inl hx).1
  have hsub₂ : range f₂ ⊆ S₁ := fun x hx => (show x ∈ S₁ ∩ S₂ by rw [h2, hbd₂]; exact .inr hx).1
  set J₁ : Set ↥S₁ := Subtype.val ⁻¹' range f₁ with hJ₁
  set J₂ : Set ↥S₁ := Subtype.val ⁻¹' range f₂ with hJ₂
  have hvJ₁ : Subtype.val '' J₁ = range f₁ := by
    rw [hJ₁, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hsub₁
  have hvJ₂ : Subtype.val '' J₂ = range f₂ := by
    rw [hJ₂, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hsub₂
  have hOJ₁ : IsOArc J₁ := isOArc_of_image hval₁.isEmbedding (hvJ₁ ▸ ⟨hf₁.toHomeomorph⟩)
  have hOJ₂ : IsOArc J₂ := isOArc_of_image hval₁.isEmbedding (hvJ₂ ▸ ⟨hf₂.toHomeomorph⟩)
  have hJu : J₁ ∪ J₂ = bd ↥S₁ := by
    rw [hJ₁, hJ₂, ← preimage_union, ← hs, preimage_image_eq _ Subtype.val_injective]
  have hrd : Disjoint (range f₁) (range f₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, rfl⟩ ⟨w', he⟩
    have h3 := e₂.injective (Subtype.ext he)
    have h4 : (2 : ℝ) = 1 := congrArg (fun p : ClosedCylinder => p.1.1) h3
    norm_num at h4
  have hJd : Disjoint J₁ J₂ := Set.disjoint_left.mpr fun x h3 h4 => Set.disjoint_left.mp hrd h3 h4
  let P₁ : Set ↥(Λ₁ ∪ Λ₂)ᶜ := e₁'.symm '' J₁
  let P₂ : Set ↥(Λ₁ ∪ Λ₂)ᶜ := e₁'.symm '' J₂
  have hOP₁ : IsOArc P₁ := isOArc_image e₁'.symm.isEmbedding hOJ₁
  have hOP₂ : IsOArc P₂ := isOArc_image e₁'.symm.isEmbedding hOJ₂
  have hPu : P₁ ∪ P₂ = bd ↥(Λ₁ ∪ Λ₂)ᶜ := by
    rw [← image_union, hJu, image_bd_homeomorph]
  have hPd : Disjoint P₁ P₂ := (disjoint_image_iff e₁'.symm.injective).mpr hJd
  have hbX : ∀ x : ↥(Λ₁ ∪ Λ₂)ᶜ, x ∈ bd ↥(Λ₁ ∪ Λ₂)ᶜ ↔ x.1 ∈ closure (Λ₁ ∪ Λ₂) := fun x => by
    have := bd_subset_iff hS.2.2 x
    rwa [compl_compl] at this
  have hne : ∀ {Λ Λ' : Set S}, IsOpenDisc Λ → IsOpenDisc Λ' → Disjoint (closure Λ) (closure Λ') →
    (closure Λ \ Λ).Nonempty := by
    intro Λ Λ' h3 h4 h5
    by_contra h6
    have h7 : closure Λ ⊆ Λ := fun z hz => by by_contra h8; exact h6 ⟨z, hz, h8⟩
    have h8 : IsClosed Λ := isClosed_of_closure_subset h7
    have h9 : Λ = univ := IsClopen.eq_univ ⟨h8, h3.1⟩ (IsOpenDisc.isPathConnected h3).nonempty
    obtain ⟨z, hz⟩ := (IsOpenDisc.isPathConnected h4).nonempty
    exact Set.disjoint_left.mp h5 (h9 ▸ subset_closure (mem_univ z)) (subset_closure hz)
  obtain ⟨a₁, b₁, ⟨e₃⟩, _⟩ : ∃ a₁ b₁, Nonempty (↥(Λ₁ ∪ Λ₂)ᶜ ≃ₜ SurfaceModel a₁ b₁ 2) ∧ 2 * a₁ + b₁
    = 2 * a₀ + b₀ := by
    rcases two_frontiers rfl hd (hne hΛ₁ hΛ₂ hd) (hne hΛ₂ hΛ₁ hd.symm) hbX hΛ₁.1 hΛ₂.1
      hOP₁.isPreconnected hOP₂.isPreconnected hPu with ⟨v1, v2⟩ | ⟨v1, v2⟩
    · exact handle_hole_model hS_surf hbS hΛ₁ hΛ₂ hd hX hOP₁ hOP₂ hPu hPd v1 v2 e_S₀
    · exact handle_hole_model hS_surf hbS hΛ₁ hΛ₂ hd hX hOP₂ hOP₁ ((union_comm _ _).trans hPu)
        hPd.symm v2 v1 e_S₀
  let e₄ : ↥S₁ ≃ₜ SurfaceModel a₁ b₁ 2 := e₁'.symm.trans e₃
  have hcJ₁ : J₁ ∈ cuffs ↥S₁ := cuff_of_split hOJ₁.isCompact.isClosed hOJ₂.isCompact.isClosed hJd
    hJu hOJ₁.isConnected'
  have hcJ₂ : J₂ ∈ cuffs ↥S₁ := cuff_of_split hOJ₂.isCompact.isClosed hOJ₁.isCompact.isClosed
    hJd.symm ((union_comm _ _).trans hJu) hOJ₂.isConnected'
  have hmem : ∀ p : Circle × unitInterval, (1 + (p.2 : ℝ), p.1) ∈ ClosedCylinder := fun p
    => ⟨⟨by linarith [p.2.2.1], by linarith [p.2.2.2]⟩, mem_univ _⟩
  let c : Circle × unitInterval → S' := fun p => (e₂ ⟨(1 + (p.2 : ℝ), p.1), hmem p⟩).1
  have hcc : Continuous c := by
    refine continuous_subtype_val.comp (e₂.continuous.comp (Continuous.subtype_mk ?_ _))
    fun_prop
  have hci : Function.Injective c := cylinder_coordinate_map_injective e₂ hmem
  have hc0 : ∀ w, c (w, 0) = f₁ w := fun w => by
    have : (⟨(1 + (((w, (0 : unitInterval)) : Circle × unitInterval).2 : ℝ), w), hmem
      (w, 0)⟩ : ClosedCylinder) = cylEnd 1 m1 w := Subtype.ext (Prod.ext (by simp [cylEnd]) rfl)
    simp only [c, this, f₁]
  have hc1 : ∀ w, c (w, 1) = f₂ w := fun w => by
    have : (⟨(1 + (((w, (1 : unitInterval)) : Circle × unitInterval).2 : ℝ), w), hmem
      (w, 1)⟩ : ClosedCylinder) = cylEnd 2 m2 w := Subtype.ext (Prod.ext
        (by simp [cylEnd]; norm_num) rfl)
    simp only [c, this, f₂]
  let j₁ : Circle → ↥S₁ := fun w => ⟨f₁ w, hsub₁ ⟨w, rfl⟩⟩
  have hj₁ : IsEmbedding j₁ := IsEmbedding.of_comp (hf₁.continuous.subtype_mk _)
    continuous_subtype_val hf₁
  have hr₁ : range j₁ = J₁ := by
    ext x
    exact ⟨by rintro ⟨w, rfl⟩; exact ⟨w, rfl⟩, by rintro ⟨w, he⟩; exact ⟨w, Subtype.ext he⟩⟩
  let φ₁ : Circle ≃ₜ J₁ := hj₁.toHomeomorph.trans (Homeomorph.setCongr hr₁)
  have hφ₁ : ∀ w, (φ₁ w).1.1 = f₁ w := fun w => rfl
  have hm' : ∀ (y : ↥S₁) (p : Circle × unitInterval), y.1 = c p → ((p.2 : ℝ) = 0 ∧ y ∈ J₁) ∨
    ((p.2 : ℝ) = 1 ∧ y ∈ J₂) := by
    exact cylinder_attaches_only_along_end_circles S₁ S₂ e₂ h2 m1 m2 hmem hbd₂
  have hcov : ∀ x : S', x ∈ range (Subtype.val : ↥S₁ → S') ∨ x ∈ range c :=
    cylinder_with_complement_covers S₁ S₂ e₂ hu hmem
  have h1' : Subtype.val '' J₂ = range fun w => c (w, 1) := by
    rw [hvJ₂]
    ext x
    simp only [mem_range, hc1]
  obtain ⟨ψ, hψ, b1, b2, hpre⟩ := handle_cut hS₁ continuous_subtype_val Subtype.val_injective hcc
    hci φ₁ hcJ₁ hOJ₂.isCompact.isClosed hJd (hJu ▸ subset_rfl)
    (fun w => (hφ₁ w).trans (hc0 w).symm) h1' hm' hcov
  obtain ⟨i, hi', j, hj, hij, φ, φ', g, hg, hs₁, hs₂⟩ := exists_two_holes e₄ hcJ₁ hcJ₂ (fun h => by
    obtain ⟨w, hw⟩ := hOJ₁.isConnected'.1
    exact Set.disjoint_left.mp hJd hw (show w ∈ J₂ by rw [← h]; exact hw))
  obtain ⟨hN, hLf⟩ := erase_erase_facts 2 i j
  obtain ⟨σ, g', hp⟩ := loop_two_aux hS₁ hψ hcJ₂ hOJ₁.isCompact.isClosed hOJ₂.isCompact.isClosed
    hJd hpre b1 b2 φ φ' hij hi' hj hLf hg hs₁ hs₂
  replace hp := hp.1
  have hn := nf_blkE (a := a₁) (b := b₁) (c := 2) hij hi' hj hN hLf σ
  have hlen := length_erase_erase hij hi' hj
  obtain ⟨a', b', ⟨e'⟩⟩ : ∃ a' b', Nonempty (S' ≃ₜ SurfaceModel a' b' 0) := by
    cases σ with
    | false =>
      obtain ⟨w, h5, h6⟩ := hn.1 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [hlen] at e'
      exact ⟨a₁ + 1, b₁, ⟨e'⟩⟩
    | true =>
      obtain ⟨w, h5, h6⟩ := hn.2 rfl
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [hlen] at e'
      exact ⟨a₁, b₁ + 2, ⟨e'⟩⟩
  have hS'_surf : IsSurface S' := isSurface_of_homeo e'.symm (isSurface_model a' b' 0).1
  obtain ⟨_, f_m, hf_m⟩ := presents_ew a' b' 0
  have hcuffs_zero : (cuffs S').ncard = 0 := (ncard_cuffs_congr e').trans (ncard_cuffs hf_m)
  have hcuffs_empty : cuffs S' = ∅ := (Set.ncard_eq_zero (cuff_statement.{w} S' hS'_surf).2.1).mp
    hcuffs_zero
  have hb' : bd S' = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
    have hmem : connectedComponentIn (bd S') x ∈ cuffs S' := ⟨x, hx, rfl⟩
    rw [hcuffs_empty] at hmem
    exact hmem
  have hS'_closed : IsClosedSurface S' :=
    ⟨hS'_surf.1, hS'_surf.2.1, fun x => by by_contra hx; exact (hb' ▸ hx : x ∈ (∅ : Set S'))⟩
  refine ⟨hS'_closed, hconn', ?_, hS₁, hS₂, hu, h1, h2⟩
  exact ⟨hS_surf, hS'_surf, hb', Λ₁, Λ₂, S₁, S₂, hΛ₁, hΛ₂, hd,
    by rw [hbS]; exact disjoint_empty _, by rw [hbS]; exact disjoint_empty _,
    hu, h1, h2, ⟨e₁⟩, ⟨e₂⟩⟩

/-- Gluing `MobiusBand` onto `↥(univ \ Λ)` along a homeomorphism `b` between their boundaries
yields a closed connected surface `GluedSpace hb` obtained by adding a crosscap to `S`. -/
theorem isClosedSurface_of_crosscap_glue [ConnectedSpace S] (hS : IsClosedSurface S)
    {Λ : Set S} (hΛ : IsOpenDisc Λ) (hOArc : IsOArc (subBd Λ))
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    {b : ↥(bd MobiusBand) → ↥(univ \ Λ : Set S)}
    (hb_cont : Continuous b) (hb_inj : Function.Injective b)
    (hb_range : range b = bd ↥(univ \ Λ : Set S)) :
    IsClosedSurface (GluedSpace hb_inj) ∧
      ConnectedSpace (GluedSpace hb_inj) ∧
      IsObtainedByAddingCrosscap S (GluedSpace hb_inj) ∧
      IsSurface ↥(range (GluedSpace.inl hb_inj)) ∧
      IsSurface ↥(range (GluedSpace.inr hb_inj)) ∧
      range (GluedSpace.inl hb_inj) ∪ range (GluedSpace.inr hb_inj) = univ ∧
      range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj) =
        Subtype.val '' bd ↥(range (GluedSpace.inl hb_inj)) ∧
      range (GluedSpace.inl hb_inj) ∩ range (GluedSpace.inr hb_inj) =
        Subtype.val '' bd ↥(range (GluedSpace.inr hb_inj)) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hS_surf : IsSurface S := IsClosedSurface.isSurface hS
  have hbS : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hS.2.2 x)
  obtain ⟨hX_surf, hX_conn, hX_bd, hOArc_bd⟩ :=
    compl_open_isSurface hS hΛ.1 hOArc hout
  have : CompactSpace ↥(univ \ Λ : Set S) := hX_surf.1
  obtain ⟨m_mob⟩ := nonempty_mob_homeo
  have hMob_surf : IsSurface MobiusBand :=
    isSurface_of_homeo m_mob (isSurface_model 0 1 1).1
  have : CompactSpace MobiusBand := hMob_surf.1
  have : ConnectedSpace (SurfaceModel 0 1 1) := (isSurface_model 0 1 1).2
  have hMob_conn : ConnectedSpace MobiusBand :=
    m_mob.surjective.connectedSpace m_mob.continuous
  have : T2Space (GluedSpace hb_inj) := GluedSpace.t2Space (isClosed_bd MobiusBand) hb_cont hb_inj
  have hbd_mob_oarc : IsOArc (bd MobiusBand) := isOArc_bd_one m_mob
  have hconn' : ConnectedSpace (GluedSpace hb_inj) :=
    @GluedSpace.connectedSpace _ _ hX_conn _ _ hMob_conn _ hbd_mob_oarc.isConnected'.1 _ hb_inj
  let S' := GluedSpace hb_inj
  let S₁ : Set S' := range (GluedSpace.inl hb_inj)
  let S₂ : Set S' := range (GluedSpace.inr hb_inj)
  have hinl_emb : IsClosedEmbedding (GluedSpace.inl hb_inj) :=
    (GluedSpace.continuous_inl hb_inj).isClosedEmbedding (GluedSpace.inl_injective hb_inj)
  have hinr_emb : IsClosedEmbedding (GluedSpace.inr hb_inj) :=
    (GluedSpace.continuous_inr hb_inj).isClosedEmbedding (GluedSpace.inr_injective hb_inj)
  let e₁ : ↥(univ \ Λ : Set S) ≃ₜ ↥S₁ := hinl_emb.isEmbedding.toHomeomorph
  let e₂ : MobiusBand ≃ₜ ↥S₂ := hinr_emb.isEmbedding.toHomeomorph
  have hS₁ : IsSurface ↥S₁ := isSurface_of_homeo e₁ hX_surf
  have hS₂ : IsSurface ↥S₂ := isSurface_of_homeo e₂ hMob_surf
  have hu : S₁ ∪ S₂ = univ := GluedSpace.range_inl_union_range_inr hb_inj
  have h1 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₁ := by
    rw [← image_bd_homeomorph e₁, image_image]
    change S₁ ∩ S₂ = GluedSpace.inl hb_inj '' bd ↥(univ \ Λ : Set S)
    rw [← hb_range, GluedSpace.range_inl_inter_range_inr hb_inj]
  have h2 : S₁ ∩ S₂ = Subtype.val '' bd ↥S₂ := by
    rw [← image_bd_homeomorph e₂, image_image]
    exact GluedSpace.range_inl_inter_range_inr_eq_inr hb_inj
  have hOb₁ : IsOArc (bd ↥S₁) := by
    rw [← image_bd_homeomorph e₁]
    exact isOArc_image e₁.isEmbedding hOArc_bd
  have hval₁ : IsClosedEmbedding (Subtype.val : ↥S₁ → S') :=
    (isCompact_iff_compactSpace.mpr hS₁.1).isClosed.isClosedEmbedding_subtypeVal
  have hOF : IsOArc (Subtype.val '' bd ↥S₁) := isOArc_image hval₁.isEmbedding hOb₁
  obtain ⟨a₁, b₁, c₁, ⟨e₃⟩⟩ := classification.{w} ↥(univ \ Λ : Set S) hX_surf hX_conn
  obtain ⟨_, f₁, hf₁⟩ := presents_ew a₁ b₁ c₁
  have hc₁ : c₁ = 1 := by
    rw [← ncard_cuffs hf₁, ← ncard_cuffs_congr e₃, cuffs_eq_of_isConnected hOArc_bd.isConnected',
      ncard_singleton]
  subst hc₁
  have hran₁ : range (Subtype.val : ↥S₁ → S') ∪ S₂ = univ := by
    rw [Subtype.range_coe]
    exact hu
  have hm₁ : range (Subtype.val : ↥S₁ → S') ∩ S₂ = Subtype.val '' bd ↥S₁ := by
    rw [Subtype.range_coe]
    exact h1
  have hBb : Subtype.val ⁻¹' (Subtype.val '' bd ↥S₁) ⊆ bd ↥S₂ := fun z hz => by
    have h3 : z.1 ∈ Subtype.val '' bd ↥S₂ := by
      rw [← h2, h1]
      exact hz
    obtain ⟨k, hk, he⟩ := h3
    exact Subtype.ext he ▸ hk
  obtain ⟨-, -, ⟨e₅⟩⟩ := glue_model hS₁ (isCuff_of_oArc hOb₁) hS₂ inferInstance hval₁
    hran₁ hm₁ hOF hBb (e₁.symm.trans e₃) (m_mob.trans e₂).symm
  have hS'_surf : IsSurface S' := isSurface_of_homeo e₅.symm (isSurface_model (0 + a₁) (1 + b₁) 0).1
  obtain ⟨_, f_m, hf_m⟩ := presents_ew (0 + a₁) (1 + b₁) 0
  have hcuffs_zero : (cuffs S').ncard = 0 := (ncard_cuffs_congr e₅).trans (ncard_cuffs hf_m)
  have hcuffs_empty : cuffs S' = ∅ := (Set.ncard_eq_zero (cuff_statement.{w} S' hS'_surf).2.1).mp
    hcuffs_zero
  have hb' : bd S' = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
    have hmem : connectedComponentIn (bd S') x ∈ cuffs S' := ⟨x, hx, rfl⟩
    rw [hcuffs_empty] at hmem
    exact hmem
  have hS'_closed : IsClosedSurface S' :=
    ⟨hS'_surf.1, hS'_surf.2.1, fun x => by by_contra hx; exact (hb' ▸ hx : x ∈ (∅ : Set S'))⟩
  refine ⟨hS'_closed, hconn', ?_, hS₁, hS₂, hu, h1, h2⟩
  exact ⟨hS_surf, hS'_surf, hb', Λ, S₁, S₂, hΛ, by rw [hbS]; exact disjoint_empty _,
    hu, h1, h2, ⟨e₁⟩, ⟨e₂⟩⟩

end GraphMinor.GM15
