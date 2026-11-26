/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.LoopSides
import LeanPool.GraphMinor.GM19.FragmentExtend
import LeanPool.GraphMinor.GM19.Section6a

/-!
# A good edge to cut along

This file proves (7.3). The proof follows the paper's induction on the number of edges. Where the
paper uses the `O`-arc `A_{r-1}(C)`,
which does not exist as printed (see the correction on page 238 in `corrections/GM07.md`), we take
the edge between a region in `Δ_{r-1}(C)` and a region outside it.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- A disc in a closed surface, or in the interior of a surface, inside a given open set. -/
theorem exists_disc_in_open {y : S} (hy : IsInteriorPoint y) {W : Set S}
  (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ D, IsClosedDisc D ∧ y ∈ discInt D ∧ D ⊆ W := by
  obtain ⟨U, h, g, c, hUW, hy'⟩ := hy.exists_ballChart hW hyW (R := 2) (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hconv := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) 1) (by
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall
  obtain ⟨h1, h2⟩ := c.image_disc hconv.1 hsub
  have hb : discBd (closedBall (0 : ℂ) 1) = sphere 0 1 := by
    rw [hconv.2, frontier_closedBall _ one_ne_zero]
  refine ⟨_, h1, ⟨⟨0, by simp, hy'⟩, ?_⟩, ?_⟩
  · rw [h2, hb]
    rintro ⟨z, hz, he⟩
    have h3 : z = 0 := by
      have h4 := congrArg h (he.trans hy'.symm)
      rw [c.hg (hsub (sphere_subset_closedBall hz)), c.hg (show (0 : ℂ) ∈ ball 0 2 by simp)] at h4
      exact h4
    rw [h3] at hz
    simp at hz
  · rintro _ ⟨z, hz, rfl⟩
    exact hUW (c.gm (hsub hz))

/-- A closed disc whose boundary lies in another closed disc lies in it, off the sphere. -/
theorem disc_subset_of_bd_subset (hT : IsSurface T) [ConnectedSpace T]
  (hns : ¬ IsSphere T) {Δ₀ Δ : Set T} (hΔ₀ : IsClosedDisc Δ₀)
    (hΔ : IsClosedDisc Δ) (hb : discBd Δ ⊆ Δ₀) : Δ ⊆ Δ₀ := by
  have hO := hΔ.isOArc_discBd
  obtain ⟨φ⟩ := id hO
  have hn : IsNullHomotopicOArcIn Δ₀ (discBd Δ) := ⟨φ, hΔ₀.isSimplyConnectedSet.2 _ (by
    rintro _ ⟨w, rfl⟩
    exact hb (φ w).2)⟩
  obtain ⟨Δ₃, hs, hd, hbd⟩ := nullHomotopicOArcIn_bounds_disc hT hO hb hn
  rwa [eq_of_discBd_eq hT hns hΔ hd hbd.symm]

variable [T1Space S] [T1Space T]

omit [T1Space S] [T1Space T] in
/-- A map from one cap to another, over the identity of `S`, is one to one. -/
theorem exists_cap_injective (hS : IsSurface S) {C : Set S} {T' : Type u} [TopologicalSpace T'] {j
  : S → T} {D : Set T} {j' : S → T'}
    {D' : Set T'} (hc : IsCappedCuff C T j D) (hc' : IsCappedCuff C T' j' D') :
    ∃ Ψ : T' → T, Continuous Ψ ∧ Injective Ψ ∧ ∀ y, Ψ (j' y) = j y := by
  have : CompactSpace S := hS.1
  have : T2Space T := hc.isSurface.2.1
  have : T2Space T' := hc'.isSurface.2.1
  have hne : C.Nonempty := by
    obtain ⟨y, hy, rfl⟩ := hc.cuff
    exact ⟨y, mem_connectedComponentIn hy⟩
  obtain ⟨Ψ, hΨc, hΨj, hΨm, hΨi, -, hΨo⟩ := exists_cap_map hc' hc continuous_id (bijOn_id C) hne
  simp only [id] at hΨj
  refine ⟨Ψ, hΨc, ?_, hΨj⟩
  have hcross : ∀ (a : T') (y : S), a ∈ D' → Ψ a = j y → a = j' y := by
    intro a y ha he
    by_cases hi : a ∈ discInt D'
    · have h1 := hΨo hi
      have h2 : j y ∈ range j ∩ D := ⟨mem_range_self y, he ▸ h1.1⟩
      rw [hc.inter_eq, ← hc.discBd_eq] at h2
      exact absurd h2 (he ▸ h1.2)
    · have hb : a ∈ discBd D' := by
        by_contra hn
        exact hi ⟨ha, hn⟩
      rw [hc'.discBd_eq] at hb
      obtain ⟨z, -, rfl⟩ := hb
      rw [hΨj] at he
      rw [hc.isEmbedding.injective he]
  intro a b he
  have hA : a ∈ range j' ∪ D' := hc'.union_eq ▸ mem_univ a
  have hB : b ∈ range j' ∪ D' := hc'.union_eq ▸ mem_univ b
  rcases hA with ⟨x, rfl⟩ | hA <;> rcases hB with ⟨y, rfl⟩ | hB
  · rw [hΨj, hΨj] at he
    rw [hc.isEmbedding.injective he]
  · exact (hcross b x hB (by rw [← he, hΨj])).symm
  · exact hcross a y hA (by rw [he, hΨj])
  · exact hΨi hA hB he

omit [T1Space S] [T1Space T] in
/-- A hole of `X` lies in a disc with boundary in `X` in each cap. -/
theorem IsInnerHole.in_cap (hS : IsSurface S) {C X K : Set S} (hh : IsInnerHole C X K) {j : S
  → T} {D : Set T}
    (hc : IsCappedCuff C T j D) : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ ⊆ j '' X ∧ j '' K ⊆ Δ := by
  obtain ⟨-, S', tS, j', D', Δ', hc', hΔ', hb, hk⟩ := hh
  have : T2Space T := hc.isSurface.2.1
  obtain ⟨Ψ, hΨc, hΨi, hΨj⟩ := exists_cap_injective hS hc hc'
  obtain ⟨h1, h2⟩ := isClosedDisc_image_of_injOn hΔ' hΨc hΨi.injOn
  refine ⟨Ψ '' Δ', h1, ?_, ?_⟩
  · rw [h2]
    rintro _ ⟨_, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hb hz
    exact ⟨y, hy, (hΨj y).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨j' y, hk (mem_image_of_mem j' hy), hΨj y⟩

omit [T1Space S] in
/-- A cuff is not planar. -/
theorem not_isPlanar_cuff (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3
  ≤ 3 * a + 3 * b + c)
    (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) {C : Set S} (hC : C ∈ cuffs S) : ¬ IsPlanar C := by
  intro hp
  have : T2Space S := hS.2.1
  have hO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
  obtain ⟨T, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : ConnectedSpace T := hc.connectedSpace hS
  have hnull := (isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hO).mp hp
  obtain ⟨Δ, hΔ, hbd⟩ := nullHomotopicOArc_bounds_disc hS hO hnull
  obtain ⟨h1, h2⟩ := isClosedDisc_image_of_injOn hΔ hc.isEmbedding.continuous
    hc.isEmbedding.injective.injOn
  have heq := eq_of_discBd_eq hT (not_isSphere_cap hS habc hm hc) h1 hc.isClosedDisc
    (by rw [h2, hbd, hc.discBd_eq])
  obtain ⟨hh, g, cc⟩ := hc.isClosedDisc.exists_isChart
  have hp0 : g 0 ∈ discInt D := by
    refine ⟨cc.gm (by simp), fun hb => ?_⟩
    have h2' : hh (g 0) ∈ Metric.sphere (0 : ℂ) 1 := cc.bd ▸ mem_image_of_mem hh hb
    rw [cc.hg (by simp)] at h2'
    simp at h2'
  have h3 : g 0 ∈ j '' Δ := heq ▸ hp0.1
  obtain ⟨y, -, hy⟩ := h3
  have h4 : g 0 ∈ range j ∩ D := ⟨⟨y, hy⟩, hp0.1⟩
  rw [hc.inter_eq, ← hc.discBd_eq] at h4
  exact hp0.2 h4

omit [T1Space S] in
/-- A cuff surrounds itself. -/
theorem isScriptASet_cuff (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3
  ≤ 3 * a + 3 * b + c)
    (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) {G : Drawing S} (hG : G.IsProper) {C : Set S}
      (hC : C ∈ cuffs S) {r : ℕ}
    (hr : (G.V ∩ C).ncard ≤ r) : IsScriptASet G r C C := by
  have hO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC
  have hsub : C ⊆ bd S := by
    obtain ⟨y, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  refine ⟨isSolid_of_isOArc hS hO, isConnected_of_isOArc hO, fun z hz => hG ⟨hsub hz.1, hz.2⟩,
    ⟨hC, ?_, not_isPlanar_cuff hS habc hm hC⟩, hr⟩
  refine isPlanarInCappedCuff_of_cap hS hc ⟨D, hc.isClosedDisc, ?_⟩
  rw [← hc.discBd_eq]
  exact Surface.discBd_subset _

omit [T1Space S] in
/-- The inside of a connected surface stays connected after removing finitely many points. -/
theorem isPreconnected_interior_sdiff_finite (hS : IsSurface S) [ConnectedSpace S] {P : Set S}
  (hP : P.Finite) :
    IsPreconnected ((bd S)ᶜ \ P) := by
  have ht2 : T2Space S := hS.2.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, hconn⟩ := exists_capAll S hS
  have : ConnectedSpace T := hconn inferInstance
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  obtain ⟨p, q, c, ⟨e⟩⟩ := classification.{u} T hT.isSurface inferInstance
  have hM : IsClosedSurface (SurfaceModel p q c) := by
    refine ⟨e.surjective.compactSpace e.continuous, e.symm.isEmbedding.t2Space, fun x => ?_⟩
    have h1 := (isInteriorPoint_homeomorph_iff e (e.symm x)).mpr (hT.2.2 _)
    simpa using h1
  have : T2Space (SurfaceModel p q c) := hM.2.1
  have : ConnectedSpace (SurfaceModel p q c) := e.surjective.connectedSpace e.continuous
  have hd : IsPreconnected (bd S)ᶜ := by
    rw [compl_eq_univ_sdiff]
    exact isPreconnected_diff_bd hS isOpen_univ isPreconnected_univ
  have hemb : IsEmbedding fun x => e (j x) := e.isEmbedding.comp hj.isEmbedding
  have him : (fun x => e (j x)) '' (bd S)ᶜ = e '' Kᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨j x, fun hk => hx ?_, rfl⟩
      have h1 : j x ∈ range j ∩ K := ⟨mem_range_self x, hk⟩
      rw [hi] at h1
      obtain ⟨z, hz, he⟩ := h1
      rwa [← hj.injective he]
    · rintro ⟨t, ht, rfl⟩
      have h1 : t ∈ range j := (hu.ge (mem_univ t)).resolve_right ht
      obtain ⟨x, rfl⟩ := h1
      refine ⟨x, fun hx => ht ?_, rfl⟩
      have h2 : j x ∈ range j ∩ K := by
        rw [hi]
        exact mem_image_of_mem j hx
      exact h2.2
  have hO : IsOpen (e '' Kᶜ) := e.isOpenMap _ hK.isOpen_compl
  have hOc : IsPreconnected (e '' Kᶜ) := by
    rw [← him]
    exact hd.image _ hemb.continuous.continuousOn
  have h1 := GM19.isPreconnected_sdiff_finite hM hO hOc (hP.image fun x => e (j x))
  have h2 : e '' Kᶜ \ (fun x => e (j x)) '' P = (fun x => e (j x)) '' ((bd S)ᶜ \ P) := by
    rw [← him]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      exact ⟨x, ⟨hx, fun hp => hn (mem_image_of_mem _ hp)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      refine ⟨mem_image_of_mem _ hx, ?_⟩
      rintro ⟨z, hz, he⟩
      exact hp (hemb.injective he ▸ hz)
  rw [h2] at h1
  exact hemb.isInducing.isPreconnected_image.mp h1

omit [T1Space S] in
/-- Two regions with a common point are equal. -/
theorem region_eq_of_mem {G : Drawing S} {ρ ρ' : Set S} (hρ : ρ ∈ G.R) (hρ' : ρ' ∈ G.R) {x : S}
  (hx : x ∈ ρ) (hx' : x ∈ ρ') : ρ = ρ' := by
  obtain ⟨a, -, rfl⟩ := hρ
  obtain ⟨b, -, rfl⟩ := hρ'
  rw [connectedComponentIn_eq hx, connectedComponentIn_eq hx']

omit [T1Space S] in
/-- A candidate for `α(G)` exists when `α(G) > 0`, and it gives the bound. -/
theorem exists_candidate_of_alpha_pos {G : Drawing S} (h : 0 < alpha G) : ∃ X, IsAlphaCandidate G X
  := by
  have hne : {n : ℕ | ∃ X : Set S, IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    have : alpha G = 0 := by
      rw [alpha, hn]
      exact Nat.sInf_empty
    omega
  obtain ⟨n, X, hX, -⟩ := hne
  exact ⟨X, hX⟩

omit [T1Space S] in
theorem alpha_le_of_candidate {G : Drawing S} {X : Set S} (hX : IsAlphaCandidate G X) : alpha G ≤
  (X ∩ G.V).ncard :=
  Nat.sInf_le ⟨X, hX, rfl⟩

section Fill

variable (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
  {G : Drawing S} (hG : G.IsProper) {r : ℕ}

include hS habc hm

omit [T1Space S] [T1Space T] in
/-- `Δ_r(C)` lies in the disc of (5.7). -/
theorem cuffInsideSet_image_subset {C : Set S} {j : S → T} {D Δ₀ : Set T}
  (hc : IsCappedCuff C T j D) (hΔ₀ : IsClosedDisc Δ₀)
    (hsub : j '' scriptA G r C ⊆ Δ₀) : j '' cuffInsideSet G r C ⊆ Δ₀ := by
  have hT := hc.isSurface
  have : ConnectedSpace T := hc.connectedSpace hS
  rintro _ ⟨y, ⟨Y, ⟨X, hX, hY⟩, hy⟩, rfl⟩
  rcases hY with rfl | hh
  · exact hsub (mem_image_of_mem j (show y ∈ scriptA G r C from ⟨Y, hX, hy⟩))
  · obtain ⟨Δ, hΔ, hb, hk⟩ := hh.in_cap hS hc
    have h1 : discBd Δ ⊆ Δ₀ := hb.trans ((image_mono fun x hx => show x ∈ scriptA G r C from ⟨X,
      hX, hx⟩).trans hsub)
    exact disc_subset_of_bd_subset hT (not_isSphere_cap hS habc hm hc) hΔ₀ hΔ h1 (hk
      (mem_image_of_mem j hy))

omit habc hm in
omit [T1Space S] in
/-- A region that meets `Δ_r(C)` lies in `𝒜_r(C)` or in a hole of a member of it. -/
theorem region_of_meets_fill {C ρ : Set S} (hρ : ρ ∈ G.R) (hm' : (ρ ∩ cuffInsideSet G r
  C).Nonempty) :
    ρ ⊆ scriptA G r C ∨ ∃ X K, IsScriptASet G r C X ∧ IsInnerHole C X K ∧ ρ ⊆ K := by
  obtain ⟨y, hyρ, Y, ⟨X, hX, hY⟩, hy⟩ := hm'
  by_cases hmeet : (ρ ∩ X).Nonempty
  · obtain ⟨z, hz, hzX⟩ := hmeet
    exact .inl (region_subset_scriptA hS hρ ⟨z, hz, X, hX, hzX⟩)
  · rcases hY with rfl | hh
    · exact absurd ⟨y, hyρ, hy⟩ hmeet
    · refine .inr ⟨X, Y, hX, hh, ?_⟩
      obtain ⟨w, hw, rfl⟩ := hh.1
      rw [connectedComponentIn_eq hy]
      refine (region_isPreconnected hρ).subset_connectedComponentIn hyρ fun z hz => ⟨mem_univ _,
        fun hzX => hmeet ⟨z, hz, hzX⟩⟩

omit habc hm in
omit [T1Space S] in
theorem subset_fill_of_region {C ρ : Set S} (hρ : ρ ∈ G.R) (hm' : (ρ ∩ cuffInsideSet G r
  C).Nonempty) :
    ρ ⊆ cuffInsideSet G r C := by
  rcases region_of_meets_fill hS hρ hm' with h | ⟨X, K, hX, hK, h⟩
  · rintro z hz
    obtain ⟨X, hX, hzX⟩ := h hz
    exact ⟨X, ⟨X, hX, .inl rfl⟩, hzX⟩
  · exact fun z hz => ⟨K, ⟨X, hX, .inr hK⟩, h hz⟩

include hG

omit [T1Space S] in
/-- There is a region in `Δ_r(C)`, and a region off it, with an edge in the closure of both. -/
theorem exists_frontier_edge (hr : 9 * (r + 1) ≤ 2 * alpha G) (hcuff : ∀ C ∈ cuffs S,
  (G.V ∩ C).ncard ≤ r) {C : Set S} (hC : C ∈ cuffs S) :
    ∃ f ∈ G.E, ∃ ρ ∈ G.R, ∃ ρ' ∈ G.R, ρ ⊆ cuffInsideSet G r C ∧ Disjoint ρ' (cuffInsideSet G r C)
      ∧ f ⊆ closure ρ ∧ f ⊆ closure ρ' := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcpt : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := hS.locallyConnected
  set Fill := cuffInsideSet G r C with hFill
  have hRfin : G.R.Finite := finite_regions_of_isProper hS hG
  have hsplit : ∀ ρ ∈ G.R, ρ ⊆ Fill ∨ Disjoint ρ Fill := fun ρ hρ => by
    by_cases h : (ρ ∩ Fill).Nonempty
    · exact .inl (subset_fill_of_region hS hρ h)
    · exact .inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h))
  let 𝓘 : Set (Set S) := {ρ ∈ G.R | ρ ⊆ Fill}
  let 𝓞 : Set (Set S) := {ρ ∈ G.R | Disjoint ρ Fill}
  have hS1 : IsScriptASet G r C C := isScriptASet_cuff hS habc hm hG hC (hcuff C hC)
  have hCFill : C ⊆ Fill := fun x hx => ⟨C, ⟨C, hS1, .inl rfl⟩, hx⟩
  have hbdC : C ⊆ bd S := by
    obtain ⟨y, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  -- A region in `Fill`.
  have hIne : 𝓘.Nonempty := by
    have hO : IsOArc C := (cuff_statement.{u} S hS).2.2 C hC
    obtain ⟨x, hx, hxV⟩ : ∃ x ∈ C, x ∉ G.V := by
      by_contra hn
      push Not at hn
      exact infinite_of_isOArc hO (G.finite_V.subset hn)
    have hxU : x ∉ G.U := fun h => hxV (hG ⟨hbdC hx, h⟩)
    let ρ := connectedComponentIn (univ \ G.U) x
    have hρ : ρ ∈ G.R := ⟨x, ⟨mem_univ _, hxU⟩, rfl⟩
    exact ⟨ρ, hρ, subset_fill_of_region hS hρ ⟨x, mem_connectedComponentIn ⟨mem_univ _, hxU⟩,
      hCFill hx⟩⟩
  -- A region off `Fill`: otherwise a candidate would be planar in the capped surface.
  have hOne : 𝓞.Nonempty := by
    by_contra hn
    have hall : ∀ ρ ∈ G.R, ρ ⊆ Fill := fun ρ hρ => (hsplit ρ hρ).resolve_right fun h
      => hn ⟨ρ, hρ, h⟩
    obtain ⟨T, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC
    have hpl := theorem_5_7_proof hS hm habc hG hC hr
    obtain ⟨Δ₀, hΔ₀, hsub⟩ := hpl.2.2 T j D hc
    have ht2' : T2Space T := hc.isSurface.2.1
    have hfs := cuffInsideSet_image_subset hS habc hm hc hΔ₀ hsub
    have hcl : IsClosed (j ⁻¹' Δ₀) := hΔ₀.isCompact.isClosed.preimage hc.isEmbedding.continuous
    have huniv : (univ : Set S) ⊆ j ⁻¹' Δ₀ := by
      rw [← closure_sUnion_regions_eq_univ hS hG]
      refine closure_minimal (sUnion_subset fun ρ hρ x hx => ?_) hcl
      exact hfs (mem_image_of_mem j (hall ρ hρ hx))
    obtain ⟨X, hX⟩ := exists_candidate_of_alpha_pos (G := G) (by omega)
    exact hX.2.2.2 (.inr ⟨C, hC, isPlanarInCappedCuff_of_cap hS hc ⟨Δ₀, hΔ₀, fun z ⟨y, _,
      hy⟩ => hy ▸ huniv (mem_univ y)⟩⟩)
  -- The inside of `S` off the vertices is connected, so the two closed sets meet there.
  let A : Set S := ⋃ ρ ∈ 𝓘, closure ρ
  let B : Set S := ⋃ ρ ∈ 𝓞, closure ρ
  have hAc : IsClosed A := (hRfin.subset (sep_subset _ _)).isClosed_biUnion fun _ _
    => isClosed_closure
  have hBc : IsClosed B := (hRfin.subset (sep_subset _ _)).isClosed_biUnion fun _ _
    => isClosed_closure
  have hcover : (univ : Set S) ⊆ A ∪ B := by
    rw [← closure_sUnion_regions_eq_univ hS hG]
    refine closure_minimal (sUnion_subset fun ρ hρ x hx => ?_) (hAc.union hBc)
    rcases hsplit ρ hρ with h | h
    · exact .inl (mem_biUnion (show ρ ∈ 𝓘 from ⟨hρ, h⟩) (subset_closure hx))
    · exact .inr (mem_biUnion (show ρ ∈ 𝓞 from ⟨hρ, h⟩) (subset_closure hx))
  let W : Set S := (bd S)ᶜ \ G.V
  have hW : IsPreconnected W := isPreconnected_interior_sdiff_finite hS G.finite_V
  have hpoint : ∀ ρ ∈ G.R, (W ∩ closure ρ).Nonempty := fun ρ hρ => by
    obtain ⟨x, hx⟩ := region_nonempty hρ
    obtain ⟨y, hy, hyb⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hS.2.2 x)) ρ
      (region_isOpen hρ) hx
    refine ⟨y, ⟨hyb, fun hV => ?_⟩, subset_closure hy⟩
    obtain ⟨w, -, hw⟩ := hρ
    have hyOutside : y ∈ univ \ G.U := connectedComponentIn_subset _ _ (hw ▸ hy)
    exact hyOutside.2 (G.V_subset_U hV)
  obtain ⟨ρ₁, hρ₁⟩ := hIne
  obtain ⟨ρ₂, hρ₂⟩ := hOne
  obtain ⟨x, hxW, hxA, hxB⟩ := isPreconnected_closed_iff.mp hW A B hAc hBc (fun x _ => hcover
    (mem_univ x))
    (by
      obtain ⟨x, h1, h2⟩ := hpoint ρ₁ hρ₁.1
      exact ⟨x, h1, mem_biUnion hρ₁ h2⟩)
    (by
      obtain ⟨x, h1, h2⟩ := hpoint ρ₂ hρ₂.1
      exact ⟨x, h1, mem_biUnion hρ₂ h2⟩)
  obtain ⟨ρ, hρ, hxρ⟩ := mem_iUnion₂.mp hxA
  obtain ⟨ρ', hρ', hxρ'⟩ := mem_iUnion₂.mp hxB
  have hne : ρ ≠ ρ' := by
    rintro rfl
    obtain ⟨y, hy⟩ := region_nonempty hρ.1
    exact disjoint_left.mp hρ'.2 hy (hρ.2 hy)
  have hxU : x ∈ G.U := by
    by_contra hn
    let ρ₃ := connectedComponentIn (univ \ G.U) x
    have hρ₃ : ρ₃ ∈ G.R := ⟨x, ⟨mem_univ _, hn⟩, rfl⟩
    have hxρ₃ : x ∈ ρ₃ := mem_connectedComponentIn ⟨mem_univ _, hn⟩
    obtain ⟨y, hy, hyρ⟩ := mem_closure_iff.mp hxρ _ (region_isOpen hρ₃) hxρ₃
    obtain ⟨y', hy', hyρ'⟩ := mem_closure_iff.mp hxρ' _ (region_isOpen hρ₃) hxρ₃
    exact hne ((region_eq_of_mem hρ.1 hρ₃ hyρ hy).trans (region_eq_of_mem hρ₃ hρ'.1 hy' hyρ'))
  rw [G.U_eq] at hxU
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp (hxU.resolve_left hxW.2)
  have hxf' : x ∈ f := by
    rw [← G.closure_diff_V hf]
    exact ⟨hxf, hxW.2⟩
  exact ⟨f, hf, ρ, hρ.1, ρ', hρ'.1, hρ.2, hρ'.2,
    subset_closure.trans (edge_closure_subset_closure_region hS hG hf hρ.1 hxf' hxρ),
    subset_closure.trans (edge_closure_subset_closure_region hS hG hf hρ'.1 hxf' hxρ')⟩

omit hG in
omit [T1Space S] hS [ConnectedSpace S] in
/-- The surface is not a cylinder. -/
theorem not_cylinder_of_model : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) := by
  rintro ⟨e'⟩
  obtain ⟨e₀⟩ := hm
  have hcrit := (modelCriterion.2 a b c 0 0 2).mp ⟨e₀.symm.trans e'⟩
  have hb0 : b = 0 := hcrit.2.2.mpr rfl
  omega

omit hG habc hm hS [ConnectedSpace S] in
omit [T1Space S] in
theorem isNormal_off_edge {G : Drawing S} {X f : Set S} (hX : G.IsNormal X) (hf : f ∈ G.E) {z : S}
  (hz : z ∈ f) : z ∉ X := fun hzX =>
  (hf.2.1 hz).2 (hX ⟨hzX, (hf.2.1 hz).1⟩)

omit hG habc hm [ConnectedSpace S] in
omit [T1Space S] in
theorem isOpen_of_mem_componentsIn {X K : Set S} (hX : IsClosed X) (hK : K ∈ componentsIn
  (univ \ X)) : IsOpen K := by
  have : LocallyConnectedSpace S := hS.locallyConnected
  obtain ⟨w, -, rfl⟩ := hK
  have h : IsOpen (univ \ X) := isOpen_univ.sdiff hX
  exact h.connectedComponentIn

omit [T1Space S] in
/-- The facts on an edge between a region in `Δ_r(C)` and a region off it. -/
theorem frontier_edge_good (hr : 9 * (r + 1) ≤ 2 * alpha G) (hr1 : 1 ≤ r)
  (hred : NoEdgeInSmallDisc G) {C : Set S} (hC : C ∈ cuffs S)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r) {f ρ ρ' : Set S} (hf : f ∈ G.E) (hρ : ρ ∈ G.R)
      (hρ' : ρ' ∈ G.R)
    (hin : ρ ⊆ cuffInsideSet G r C) (hout : Disjoint ρ' (cuffInsideSet G r C))
      (hfρ : f ⊆ closure ρ) (hfρ' : f ⊆ closure ρ') :
    (∀ z ∈ f, ∀ C' ∈ cuffs S, z ∉ cuffInsideSet G r C') ∧ Disjoint (closure f) (bd S) ∧
      (tilde f).ncard = 2 := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcpt : CompactSpace S := hS.1
  have hlc : LocallyConnectedSpace S := hS.locallyConnected
  have hcyl := not_cylinder_of_model habc hm
  have hdis : ∀ {r₁ r₂ : ℕ} {C₁ C₂ : Set S}, r₁ + r₂ < alpha G → C₁ ∈ cuffs S → C₂ ∈ cuffs S
    → C₁ ≠ C₂ →
      ∀ x, x ∈ scriptA G r₁ C₁ → x ∉ scriptA G r₂ C₂ := fun hlt h1 h2 hne x hx hx' => by
    have := theorem_5_3_proof hS hcyl G h1 h2 hne hlt
    exact (eq_empty_iff_forall_notMem.mp this x) ⟨hx, hx'⟩
  obtain ⟨z₀, hz₀⟩ := hf.2.2.1.nonempty
  have hclosρ : closure f ⊆ closure ρ := edge_closure_subset_closure_region hS hG hf hρ hz₀
    (hfρ hz₀)
  have hclosρ' : closure f ⊆ closure ρ' := edge_closure_subset_closure_region hS hG hf hρ' hz₀
    (hfρ' hz₀)
  -- `f` misses `Δ_r(C)`, since a hole is open and `ρ'` misses it.
  have hA : ∀ z ∈ f, z ∉ cuffInsideSet G r C := by
    rintro z hz ⟨Y, ⟨X, hX, hY⟩, hzY⟩
    rcases hY with rfl | hh
    · exact isNormal_off_edge hX.2.2.1 hf hz hzY
    · have hYo := isOpen_of_mem_componentsIn hS hX.1.2 hh.1
      obtain ⟨w, hwY, hwρ⟩ := mem_closure_iff.mp (hfρ' hz) Y hYo hzY
      exact disjoint_left.mp hout hwρ ⟨Y, ⟨X, hX, .inr hh⟩, hwY⟩
  -- `ρ` lies in `𝒜_r(C)`, since the frontier of a hole lies in `X`.
  have hB : ρ ⊆ scriptA G r C := by
    obtain ⟨y, hy⟩ := region_nonempty hρ
    rcases region_of_meets_fill hS hρ ⟨y, hy, hin hy⟩ with h | ⟨X, K, hX, hK, hsub⟩
    · exact h
    · exfalso
      have hzX : z₀ ∉ X := isNormal_off_edge hX.2.2.1 hf hz₀
      have hK₃ : connectedComponentIn (univ \ X) z₀ ∈ componentsIn (univ \ X)
        := ⟨z₀, ⟨mem_univ _, hzX⟩, rfl⟩
      have hopen := isOpen_of_mem_componentsIn hS hX.1.2 hK₃
      have hmem : z₀ ∈ connectedComponentIn (univ \ X) z₀ := mem_connectedComponentIn ⟨mem_univ _,
        hzX⟩
      obtain ⟨w, hw, hwρ⟩ := mem_closure_iff.mp (hfρ hz₀) _ hopen hmem
      have hwK := hsub hwρ
      obtain ⟨b', hb', rfl⟩ := hK.1
      rw [connectedComponentIn_eq hwK, ← connectedComponentIn_eq hw] at hK
      exact hA z₀ hz₀ ⟨_, ⟨X, hX, .inr hK⟩, hmem⟩
  have hbdC : ∀ {C' : Set S}, C' ∈ cuffs S → C' ⊆ bd S := fun {C'} hC' => by
    obtain ⟨y, -, rfl⟩ := hC'
    exact connectedComponentIn_subset _ _
  have hscript : ∀ {C' : Set S}, C' ∈ cuffs S → IsScriptASet G r C' C' := fun hC' =>
    isScriptASet_cuff hS habc hm hG hC' (hcuff _ hC')
  have hC1 : ∀ z ∈ f, ∀ C' ∈ cuffs S, z ∉ cuffInsideSet G r C' := by
    rintro z hz C' hC' ⟨Y, ⟨X', hX', hY⟩, hzY⟩
    by_cases hCC : C' = C
    · subst hCC
      exact hA z hz ⟨Y, ⟨X', hX', hY⟩, hzY⟩
    rcases hY with rfl | hh
    · exact isNormal_off_edge hX'.2.2.1 hf hz hzY
    · have hYo := isOpen_of_mem_componentsIn hS hX'.1.2 hh.1
      obtain ⟨y, hyY, hyρ⟩ := mem_closure_iff.mp (hfρ hz) Y hYo hzY
      obtain ⟨X, hX, hyX⟩ := hB hyρ
      have hX' : IsScriptASet G r C X := hX
      by_cases hmeet : (X ∩ X').Nonempty
      · obtain ⟨p, hp, hp'⟩ := hmeet
        exact hdis (by omega) hC hC' (Ne.symm hCC) p ⟨X, hX', hp⟩ ⟨X', ‹IsScriptASet G r C' X'›,
          hp'⟩
      · have hsub : X ⊆ Y := by
          obtain ⟨w, -, rfl⟩ := hh.1
          rw [connectedComponentIn_eq hyY]
          exact hX'.2.1.isPreconnected.subset_connectedComponentIn hyX fun q hq =>
            ⟨mem_univ _, fun hq' => hmeet ⟨q, hq, hq'⟩⟩
        obtain ⟨T, tT, j, D, hc, -⟩ := exists_cappedCuff hS hC'
        have : T2Space T := hc.isSurface.2.1
        obtain ⟨Δ, hΔ, -, hk⟩ := hh.in_cap hS hc
        have hpl : IsPlanarInCappedCuff C' X := isPlanarInCappedCuff_of_cap hS hc ⟨Δ, hΔ,
          (image_mono hsub).trans hk⟩
        have hs' : IsScriptASet G r C' X := ⟨hX'.1, hX'.2.1, hX'.2.2.1, ⟨hC', hpl,
          hX'.2.2.2.1.2.2⟩, hX'.2.2.2.2⟩
        exact hdis (by omega) hC hC' (Ne.symm hCC) y ⟨X, hX', hyX⟩ ⟨X, hs', hyX⟩
  -- `f` misses the boundary.
  have hC2 : Disjoint (closure f) (bd S) := by
    rw [disjoint_left]
    intro u hu hub
    have huU : u ∈ G.U := G.closure_subset_U hf hu
    have huV : u ∈ G.V := hG ⟨hub, huU⟩
    have hunorm : u ∈ (G.U \ G.V)ᶜ := fun h => h.2 huV
    have hC' : connectedComponentIn (bd S) u ∈ cuffs S := ⟨u, hub, rfl⟩
    have huC' : u ∈ connectedComponentIn (bd S) u := mem_connectedComponentIn hub
    set C' := connectedComponentIn (bd S) u with hC'def
    have hoffU : ∀ {ρ₀ : Set S}, ρ₀ ∈ G.R → ∀ q ∈ ρ₀, q ∉ G.U := fun {ρ₀} hρ₀ q hq hU => by
      obtain ⟨w, -, hw⟩ := hρ₀
      have hqOutside : q ∈ univ \ G.U := connectedComponentIn_subset _ _ (hw ▸ hq)
      exact hqOutside.2 hU
    by_cases hCC : C' = C
    · -- At an end on `C`, a line from `C` gives a member of `𝒜_r(C)` that meets `ρ'`.
      rw [hCC] at huC'
      obtain ⟨w, hwρ', hj⟩ := joinedIn_region_of_mem_closure hS hG hρ' (hclosρ' hu) hunorm
      have hwC : w ∉ C := fun h => disjoint_left.mp hout hwρ' ⟨C, ⟨C, hscript hC, .inl rfl⟩, h⟩
      have hCcl : IsClosed C := (isCompact_of_isOArc ((cuff_statement.{u} S hS).2.2 C hC)).isClosed
      obtain ⟨x, hx, L, hL, hl, hLX⟩ := exists_whisker_line hCcl huC' hwC hj
      have hLn : G.IsNormal L := by
        rintro q ⟨hq, hU⟩
        rcases hL hq with h | h
        · exact absurd hU (hoffU hρ' q h)
        · rw [show q = u from h]
          exact huV
      have hcount : G.V ∩ (C ∪ L) ⊆ G.V ∩ C := by
        rintro q ⟨hqV, hq | hq⟩
        · exact ⟨hqV, hq⟩
        · rcases hL hq with h | h
          · exact absurd (G.V_subset_U hqV) (hoffU hρ' q h)
          · exact ⟨hqV, (show q = u from h) ▸ huC'⟩
      have hs := IsScriptASet.whisker hS (r' := r) (hscript hC) hx hl hLX hLn
        ((ncard_le_ncard hcount (G.finite_V.subset inter_subset_left)).trans (hcuff C hC))
      have hwL : w ∈ L := by
        obtain ⟨g, -, h1⟩ := id hl
        rw [← h1]
        exact (g 1).2
      exact disjoint_left.mp hout hwρ' ⟨C ∪ L, ⟨C ∪ L, hs, .inl rfl⟩, .inr hwL⟩
    · -- At an end on another cuff, a line from `𝒜_r(C)` gives a point of both.
      obtain ⟨w, hwρ, hj⟩ := joinedIn_region_of_mem_closure hS hG hρ (hclosρ hu) hunorm
      obtain ⟨X, hX, hwX⟩ := hB hwρ
      have hX' : IsScriptASet G r C X := hX
      have hu' : u ∈ scriptA G r C' := ⟨C', hscript hC', huC'⟩
      by_cases huX : u ∈ X
      · exact hdis (by omega) hC hC' (Ne.symm hCC) u ⟨X, hX', huX⟩ hu'
      · obtain ⟨x, hx, L, hL, hl, hLX⟩ := exists_whisker_line hX'.1.2 hwX huX hj.symm
        have hLn : G.IsNormal L := by
          rintro q ⟨hq, hU⟩
          rcases hL hq with h | h
          · exact absurd hU (hoffU hρ q h)
          · rw [show q = u from h]
            exact huV
        have hcount : G.V ∩ (X ∪ L) ⊆ (G.V ∩ X) ∪ {u} := by
          rintro q ⟨hqV, hq | hq⟩
          · exact .inl ⟨hqV, hq⟩
          · rcases hL hq with h | h
            · exact absurd (G.V_subset_U hqV) (hoffU hρ q h)
            · exact .inr h
        have hc' : (G.V ∩ (X ∪ L)).ncard ≤ r + 1 := by
          refine (ncard_le_ncard hcount ((G.finite_V.subset inter_subset_left).union
            (finite_singleton u))).trans ?_
          refine (ncard_union_le _ _).trans ?_
          rw [ncard_singleton]
          exact Nat.add_le_add_right hX'.2.2.2.2 1
        have hs := IsScriptASet.whisker hS hX' hx hl hLX hLn hc'
        have huL : u ∈ L := by
          obtain ⟨g, -, h1⟩ := id hl
          rw [← h1]
          exact (g 1).2
        exact hdis (r₁ := r + 1) (by omega) hC hC' (Ne.symm hCC) u ⟨X ∪ L, hs, .inr huL⟩ hu'
  refine ⟨hC1, hC2, ?_⟩
  rw [GraphMinor.GM19.tilde_eq_inter_V G hf]
  rcases G.edge_cond f hf with ⟨u, v, huv, hcap, -⟩ | ⟨v, hcap, hO⟩
  · rw [hcap]
    exact ncard_pair huv
  · exfalso
    obtain ⟨K, h1, h2, h3, h4, h5, h6⟩ := exists_loop_sides hS hm (not_isSphere_of_model hm
      (by omega)) hf hcap hO hC2 hred
    have hcount : (K ∩ G.V).ncard ≤ 1 := by
      have : K ∩ G.V ⊆ {v} := fun x hx => h4 ⟨hx.2, hx.1⟩
      simpa using ncard_le_ncard this
    have hnear : IsNearPlanar K := by
      by_contra hn
      have := alpha_le_of_candidate (G := G) ⟨h1, h2, h3, hn⟩
      omega
    rcases hnear with hp | ⟨C'', hC'', hp⟩
    · exact h5 hp
    · have hs : IsScriptASet G r C'' K := ⟨h1, h2, h3, ⟨hC'', hp, h5⟩, by
        rw [inter_comm]
        omega⟩
      by_cases hCC : C'' = C
      · subst hCC
        obtain ⟨q, hqρ, hqK⟩ := h6 z₀ hz₀ ρ' hρ' (hfρ' hz₀)
        exact disjoint_left.mp hout hqρ ⟨K, ⟨K, hs, .inl rfl⟩, hqK⟩
      · obtain ⟨q, hqρ, hqK⟩ := h6 z₀ hz₀ ρ hρ (hfρ hz₀)
        exact hdis (by omega) hC hC'' (Ne.symm hCC) q (hB hqρ) ⟨K, hs, hqK⟩

end Fill

/-- With no edges and no cuffs, `α(G) = 0`: an isolated vertex lies in a small disc, and we push a
candidate out of it. -/
theorem alpha_eq_zero_of_no_edges (hS : IsSurface S) [ConnectedSpace S] (hns : ¬ IsSphere S)
  (hb : bd S = ∅) {G : Drawing S}
    (hE : G.E = ∅) {X₀ : Set S} (hX₀ : IsAlphaCandidate G X₀) : alpha G = 0 := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hVs : ∀ W : Set S, W ⊆ G.V → (G.span W ∅).V = W := fun W hW => by
    rw [Drawing.span_V, Drawing.spanV]
    simp [inter_eq_left.mpr hW]
  have hUs : ∀ W : Set S, W ⊆ G.V → (G.span W ∅).U = W := fun W hW => by
    rw [Drawing.span_U, Drawing.spanU, Drawing.spanV]
    simp [inter_eq_left.mpr hW]
  have key : ∀ W : Set S, W.Finite → W ⊆ G.V → ∃ X, IsAlphaCandidate (G.span W ∅) X ∧ X ∩ W = ∅
    := by
    intro W hW
    induction W, hW using Set.Finite.induction_on with
    | empty =>
      intro _
      refine ⟨X₀, ⟨hX₀.1, hX₀.2.1, ?_, hX₀.2.2.2⟩, inter_empty _⟩
      rw [Drawing.IsNormal, hUs ∅ (empty_subset _), inter_empty]
      exact empty_subset _
    | @insert v W hvW hfin ih =>
      intro hsub
      have hWsub : W ⊆ G.V := (subset_insert _ _).trans hsub
      obtain ⟨X', hX', hoff⟩ := ih hWsub
      have hint : IsInteriorPoint v := by
        by_contra hn
        have : v ∈ bd S := hn
        rw [hb] at this
        exact this
      obtain ⟨Δ, hΔ, hvΔ, hsubΔ⟩ := exists_disc_in_open hint hfin.isClosed.isOpen_compl hvW
      have hbdoff : ∀ z ∈ discBd Δ, z ∉ insert v W := by
        intro z hz hzi
        rcases hzi with rfl | hzW
        · exact hvΔ.2 hz
        · exact hsubΔ (Surface.discBd_subset _ hz) hzW
      obtain ⟨X, hX, hXs⟩ := exists_candidate_of_prune hS hns (G := G.span (insert v W) ∅) (G'
        := G.span W ∅) hΔ
        (by
          rintro z ⟨hz, hzU⟩
          rw [hUs _ hsub] at hzU
          exact absurd hzU (hbdoff z hz))
        (by
          rintro z ⟨hzV, hz⟩
          rw [hVs _ hsub] at hzV
          exact absurd hzV (hbdoff z hz))
        (by
          rw [hUs _ hsub, hUs _ hWsub]
          rintro z ⟨rfl | hz, hzi⟩
          · exact absurd hvΔ hzi
          · exact hz)
        (by
          rw [hVs _ hsub, hVs _ hWsub]
          exact subset_insert _ _) hX'
      refine ⟨X, hX, ?_⟩
      rw [eq_empty_iff_forall_notMem]
      rintro z ⟨hzX, hzi⟩
      have h1 := hXs ⟨hzX, by rw [hVs _ hsub]; exact hzi⟩
      rw [hVs _ hWsub] at h1
      exact (eq_empty_iff_forall_notMem.mp hoff z) h1
  obtain ⟨X, hX, hoff⟩ := key G.V G.finite_V subset_rfl
  have hc : IsAlphaCandidate G X := by
    refine ⟨hX.1, hX.2.1, fun z hz => ?_, hX.2.2.2⟩
    have h1 := hz.2
    rw [G.U_eq, hE] at h1
    simpa using h1
  have := alpha_le_of_candidate hc
  rw [hoff, ncard_empty] at this
  omega

section Reduced

variable (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
  {G : Drawing S} (hG : G.IsProper) {r : ℕ}

include hS habc hm hG

/-- (7.3) when no small disc holds an edge. -/
theorem exists_good_edge_reduced (hr : 9 * (r + 1) ≤ 2 * alpha G) (hr1 : 1 ≤ r)
  (hred : NoEdgeInSmallDisc G)
    (hcuff : ∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r) :
    ∃ e ∈ G.E, (tilde e).ncard = 2 ∧ Disjoint (closure e) (bd S) ∧ ¬ e ⊆ allCuffsInsideSet G r := by
  classical
  have ht2 : T2Space S := hS.2.1
  by_cases hne : (cuffs S).Nonempty
  · obtain ⟨C, hC⟩ := hne
    obtain ⟨f, hf, ρ, hρ, ρ', hρ', hin, hout, hfρ, hfρ'⟩ := exists_frontier_edge hS habc hm hG hr
      hcuff hC
    obtain ⟨h1, h2, h3⟩ := frontier_edge_good hS habc hm hG hr hr1 hred hC hcuff hf hρ hρ' hin hout
      hfρ hfρ'
    refine ⟨f, hf, h3, h2, fun hsub => ?_⟩
    obtain ⟨z, hz⟩ := hf.2.2.1.nonempty
    obtain ⟨C', ⟨hC', -⟩, hzC⟩ := mem_iUnion₂.mp (hsub hz)
    exact h1 z hz C' hC' hzC
  · have hcuffs : cuffs S = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hb : bd S = ∅ := by
      rw [← sUnion_cuffs, hcuffs, sUnion_empty]
    have hall : allCuffsInsideSet G r = ∅ := by
      simp [allCuffsInsideSet, hcuffs]
    have hns := not_isSphere_of_model hm (by omega)
    obtain ⟨X, hX⟩ := exists_candidate_of_alpha_pos (G := G) (by omega)
    have hE : G.E.Nonempty := by
      by_contra hn
      have := alpha_eq_zero_of_no_edges hS hns hb (not_nonempty_iff_eq_empty.mp hn) hX
      omega
    obtain ⟨f, hf⟩ := hE
    have hd : Disjoint (closure f) (bd S) := by rw [hb]; exact disjoint_empty _
    refine ⟨f, hf, ?_, hd, ?_⟩
    · rw [GraphMinor.GM19.tilde_eq_inter_V G hf]
      rcases G.edge_cond f hf with ⟨u, v, huv, hcap, -⟩ | ⟨v, hcap, hO⟩
      · rw [hcap]
        exact ncard_pair huv
      · exfalso
        obtain ⟨K, h1, h2, h3, h4, h5, -⟩ := exists_loop_sides hS hm hns hf hcap hO hd hred
        have hcount : (K ∩ G.V).ncard ≤ 1 := by
          have : K ∩ G.V ⊆ {v} := fun x hx => h4 ⟨hx.2, hx.1⟩
          simpa using ncard_le_ncard this
        have := alpha_le_of_candidate (G := G) ⟨h1, h2, h3, fun hn => by
          rcases hn with hp | ⟨C, hC, -⟩
          · exact h5 hp
          · exact hne ⟨C, hC⟩⟩
        omega
    · rw [hall]
      intro hs
      obtain ⟨z, hz⟩ := hf.2.2.1.nonempty
      exact hs hz

end Reduced

/-- What (7.3) asks of an edge, without the cut. -/
def IsGoodCutEdge (G : Drawing S) (r : ℕ) (e : Set S) : Prop :=
  e ∈ G.E ∧ (tilde e).ncard = 2 ∧ Disjoint (closure e) (bd S) ∧ ¬ e ⊆ allCuffsInsideSet G r ∧
    ¬ ∃ F : Set S, G.IsNormal F ∧ IsNullHomotopicOArc F ∧ (G.V ∩ F).ncard ≤ 1 ∧ IsInsideOArc e F

/-- `G` with the inside of `Δ` removed. -/
noncomputable def pruneDisc (G : Drawing S) (Δ : Set S) : Drawing S :=
  G.span (G.V \ discInt Δ) {e | Disjoint e (discInt Δ)}

theorem pruneDisc_V_subset (G : Drawing S) (Δ : Set S) : (pruneDisc G Δ).V ⊆ G.V
  := G.spanV_subset _ _

theorem pruneDisc_U_subset (G : Drawing S) (Δ : Set S) : (pruneDisc G Δ).U ⊆ G.U := by
  refine union_subset ((pruneDisc_V_subset G Δ).trans G.V_subset_U) ?_
  exact iUnion₂_subset fun e he => G.closure_subset_U he.2

theorem pruneDisc_inter_V (G : Drawing S) (Δ : Set S) {x : S} (hx : x ∈ (pruneDisc G Δ).U)
  (hV : x ∈ G.V) : x ∈ (pruneDisc G Δ).V := by
  rcases hx with hx | hx
  · exact hx
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact .inr (mem_iUnion₂.mpr ⟨e, he, hxe, hV⟩)

theorem pruneDisc_U_of_off (hman : ∀ x : S, IsManifoldPoint x) [T2Space S] {G : Drawing S} {Δ : Set
  S} (hΔ : IsClosedDisc Δ)
    (hF : G.IsNormal (discBd Δ)) : G.U \ discInt Δ ⊆ (pruneDisc G Δ).U := by
  rintro x ⟨hxU, hxi⟩
  rw [G.U_eq] at hxU
  rcases hxU with hV | hx
  · exact .inl (.inl ⟨⟨hV, hxi⟩, hV⟩)
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have hoff : Disjoint e (discBd Δ) := by
      rw [disjoint_left]
      exact fun z hz hb => (he.2.1 hz).2 (hF ⟨hb, (he.2.1 hz).1⟩)
    rcases hΔ.side hman he.2.2.1.isConnected.isPreconnected hoff with hin | hdj
    · have hxD : x ∈ Δ := closure_minimal (hin.trans (discInt_subset Δ)) hΔ.isCompact.isClosed hxe
      have hxb : x ∈ discBd Δ := by
        by_contra hn
        exact hxi ⟨hxD, hn⟩
      have hV : x ∈ G.V := hF ⟨hxb, G.closure_subset_U he hxe⟩
      exact .inl (.inl ⟨⟨hV, hxi⟩, hV⟩)
    · refine .inr (mem_iUnion₂.mpr ⟨e, ⟨?_, he⟩, hxe⟩)
      exact hdj.mono_right (discInt_subset Δ)

section Induction

variable (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c)
  (hm : Nonempty (S ≃ₜ SurfaceModel a b c))

include hS habc hm

/-- (7.3) without the cut, by induction on the number of edges. -/
theorem exists_good_edge {r : ℕ} (hr1 : 1 ≤ r) : ∀ (n : ℕ) (G : Drawing S), G.E.ncard = n
  → G.IsProper →
    9 * (r + 1) ≤ 2 * alpha G → (∀ C ∈ cuffs S, (G.V ∩ C).ncard ≤ r) → ∃ e, IsGoodCutEdge G r e
      := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  have hns := not_isSphere_of_model hm (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hG hr hcuff
  by_cases hred : NoEdgeInSmallDisc G
  · obtain ⟨e, he, h1, h2, h3⟩ := exists_good_edge_reduced hS habc hm hG hr hr1 hred hcuff
    exact ⟨e, he, h1, h2, h3, fun ⟨F, h4, h5, h6, h7⟩ => hred ⟨F, e, h4, h5, h6, he, h7⟩⟩
  -- A small disc holds an edge: remove the inside of the disc.
  obtain ⟨F, e, hFn, hnull, hcount, he, hins⟩ := not_not.mp hred
  obtain ⟨z, hz⟩ := he.2.2.1.nonempty
  have hO : IsOArc F := by
    obtain ⟨φ, -⟩ := hnull
    exact ⟨φ⟩
  obtain ⟨Δ, hΔ, hbd, hzΔ⟩ : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ z ∈ Δ := by
    rcases hins z hz with ⟨-, Δ, hΔ, hbd, hzΔ⟩ | ⟨C, -, -, hsur, -⟩
    · exact ⟨Δ, hΔ, hbd, hzΔ.1⟩
    · exact absurd ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS hO).mpr hnull) hsur.2.2
  subst hbd
  have hoff : Disjoint e (discBd Δ) := by
    rw [disjoint_left]
    exact fun w hw hb => (he.2.1 hw).2 (hFn ⟨hb, (he.2.1 hw).1⟩)
  have heI : e ⊆ discInt Δ := (hΔ.side hman he.2.2.1.isConnected.isPreconnected hoff).resolve_right
    fun h =>
    disjoint_left.mp h hz hzΔ
  set G' := pruneDisc G Δ with hG'
  have hVs := pruneDisc_V_subset G Δ
  have hUs := pruneDisc_U_subset G Δ
  have hnormal : ∀ {X : Set S}, G.IsNormal X → G'.IsNormal X := fun {X} hX x hx =>
    pruneDisc_inter_V G Δ hx.2 (hX ⟨hx.1, hUs hx.2⟩)
  have hcardle : ∀ X : Set S, (G'.V ∩ X).ncard ≤ (G.V ∩ X).ncard := fun X =>
    ncard_le_ncard (inter_subset_inter_left _ hVs) (G.finite_V.subset inter_subset_left)
  have hG'p : G'.IsProper := hnormal hG
  have hEs : G'.E = {e | Disjoint e (discInt Δ)} ∩ G.E := G.span_E _ _
  have hlt : G'.E.ncard < n := by
    rw [← hn]
    refine ncard_lt_ncard ?_ G.finite_edges
    refine ⟨fun f hf => (hEs ▸ hf : f ∈ _ ∩ G.E).2, fun hsub => ?_⟩
    have h1 : e ∈ G'.E := hsub he
    rw [hEs] at h1
    exact disjoint_left.mp h1.1 hz (heI hz)
  have hαpos : 0 < alpha G := by omega
  have hαle : alpha G ≤ alpha G' := by
    obtain ⟨X₀, hX₀⟩ := exists_candidate_of_alpha_pos hαpos
    have hne : {n : ℕ | ∃ X : Set S, IsAlphaCandidate G' X ∧ (X ∩ G'.V).ncard = n}.Nonempty :=
      ⟨_, X₀, ⟨hX₀.1, hX₀.2.1, hnormal hX₀.2.2.1, hX₀.2.2.2⟩, rfl⟩
    obtain ⟨X', hX', hcard⟩ := Nat.sInf_mem hne
    have hone : (G.V ∩ discBd Δ).Subsingleton := fun x hx y hy =>
      (ncard_le_one (G.finite_V.subset inter_subset_left)).mp hcount x hx y hy
    obtain ⟨X, hX, hXs⟩ := exists_candidate_of_prune hS hns hΔ hFn hone
      (pruneDisc_U_of_off hman hΔ hFn) hVs hX'
    calc alpha G ≤ (X ∩ G.V).ncard := alpha_le_of_candidate hX
      _ ≤ (X' ∩ G'.V).ncard := ncard_le_ncard hXs (G'.finite_V.subset inter_subset_right)
      _ = alpha G' := hcard
  obtain ⟨e', he', h1, h2, h3, h4⟩ := ih _ hlt G' rfl hG'p (by omega) fun C hC => (hcardle C).trans
    (hcuff C hC)
  have hscript : ∀ {C X : Set S}, IsScriptASet G r C X → IsScriptASet G' r C X := fun hX =>
    ⟨hX.1, hX.2.1, hnormal hX.2.2.1, hX.2.2.2.1, (hcardle _).trans hX.2.2.2.2⟩
  refine ⟨e', (hEs ▸ he' : e' ∈ _ ∩ G.E).2, h1, h2, fun hsub => h3 (hsub.trans ?_), ?_⟩
  · intro x hx
    obtain ⟨C, ⟨hC, y, X₁, hX₁, hy⟩, Y, ⟨X, hX, hY⟩, hxY⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨C, ⟨hC, y, X₁, hscript hX₁, hy⟩, Y, ⟨X, hscript hX, hY⟩, hxY⟩
  · rintro ⟨F', h5, h6, h7, h8⟩
    exact h4 ⟨F', hnormal h5, h6, (hcardle _).trans h7, h8⟩

end Induction

end GraphMinor.GM07
