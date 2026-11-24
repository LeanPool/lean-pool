/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffGrid
public import LeanPool.GraphMinor.GM07.RegionNest
public import LeanPool.GraphMinor.GM07.Section5b

/-!
# The layers around `A(C)`

Graph Minors VII, (5.9), page 234: the sets `Z_j` are closures of unions of regions of `G`, and
"there is a circuit $C_j$ of $G$ with $U(C_j) \subseteq Z_j$, such that $Z_j - U(C_j)$ is inside the
$O$-arc $U(C_j)$". These are the layers of regions of `RegionNest.lean`. There the surface is a
sphere. Here the layers lie in a disc of a closed surface, and we find the circuits by a chart of
a neighbourhood of the disc into a sphere (`exists_layer_circuit_in_disc`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

variable {W : Type} [TopologicalSpace W] [T2Space W]

/-- A point of the closed set of a family of regions that is off the boundary of the family is an
interior point of that set. -/
theorem mem_interior_of_off_boundary [ConnectedSpace W] (hS : IsClosedSurface W) {Γ : Drawing W} {Z
  : Set (Set W)} (hZ : Z ⊆ Γ.R) {x : W} (hx : x ∈ ⋃ r ∈ Z, closure r) (hxN : x ∉
    (boundaryDrawing Γ Z).U) :
    x ∈ interior (⋃ r ∈ Z, closure r) := by
  classical
  have hlc : LocallyConnectedSpace W := IsClosedSurface.locallyConnectedSpace hS
  have hfin : Γ.R.Finite := finite_R hS Γ
  obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx
  have hFc : IsClosed (⋃ r' ∈ Γ.R \ Z, closure r') := (hfin.subset sdiff_subset).isClosed_biUnion
    fun _ _ => isClosed_closure
  have hxF : x ∉ ⋃ r' ∈ Γ.R \ Z, closure r' := fun h => by
    obtain ⟨r', hr', hxr'⟩ := mem_iUnion₂.mp h
    by_cases hxV : x ∈ Γ.V
    · refine hxN ((boundaryDrawing Γ Z).V_subset_U ((mem_boundaryDrawing_V hS).mpr ⟨⟨r, hr, hxV,
        .inr (hZ hr), hxr⟩, r', hr', hxV, .inr hr'.1, hxr'⟩))
    by_cases hxU : x ∈ Γ.U
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      have hin : e ∈ (boundaryDrawing Γ Z).E := mem_boundaryDrawing_E.mpr ⟨⟨r, hr, he, hZ hr, x,
        hxe, hxr⟩, r', hr', he, hr'.1, x, hxe, hxr'⟩
      exact hxN ((boundaryDrawing Γ Z).closure_subset_U hin (subset_closure hxe))
    · have hx' : x ∈ connectedComponentIn (univ \ Γ.U) x := mem_connectedComponentIn ⟨mem_univ x,
        hxU⟩
      have hR : connectedComponentIn (univ \ Γ.U) x ∈ Γ.R := (mem_R_iff Γ).mpr ⟨x, hxU, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hxr _ (region_isOpen hR) hx'
      obtain ⟨y', hy1', hy2'⟩ := mem_closure_iff.mp hxr' _ (region_isOpen hR) hx'
      have e1 := region_eq_of_mem_atom hR (.inr (hZ hr)) hy1 hy2
      have e2 := region_eq_of_mem_atom hR (.inr hr'.1) hy1' hy2'
      exact hr'.2 (e2 ▸ e1.symm ▸ hr)
  refine mem_interior.mpr ⟨(⋃ r' ∈ Γ.R \ Z, closure r')ᶜ, fun y hy => ?_, hFc.isOpen_compl, hxF⟩
  have hprop : Γ.IsProper := fun z hz => absurd (hS.2.2 z) hz.1
  have hS' : IsSurface W := ⟨hS.1, hS.2.1, fun z => (hS.2.2 z).isManifoldPoint⟩
  have h1 : y ∈ closure (⋃₀ Γ.R) := (closure_sUnion_regions_eq_univ hS' hprop).symm ▸ mem_univ y
  rw [hfin.closure_sUnion] at h1
  obtain ⟨r', hr', hyr'⟩ := mem_iUnion₂.mp h1
  by_cases h2 : r' ∈ Z
  · exact mem_iUnion₂.mpr ⟨r', h2, hyr'⟩
  · exact absurd (mem_iUnion₂.mpr ⟨r', ⟨hr', h2⟩, hyr'⟩) hy

/-- The boundary of a family of regions lies in the closed set of the family. -/
theorem boundary_subset_regions (hS : IsClosedSurface W) {Γ : Drawing W} {Z :
  Set (Set W)} : (boundaryDrawing Γ Z).U ⊆ ⋃ r ∈ Z, closure r := fun x hx => by
  by_cases hv : x ∈ (boundaryDrawing Γ Z).V
  · obtain ⟨⟨r, hr, h1⟩, -⟩ := (mem_boundaryDrawing_V hS).mp hv
    exact mem_iUnion₂.mpr ⟨r, hr, h1.2.2⟩
  · obtain ⟨e, he, hxe⟩ := (boundaryDrawing Γ Z).exists_edge_of_mem hx hv
    obtain ⟨⟨r, hr, h1⟩, -⟩ := mem_boundaryDrawing_E.mp he
    exact mem_iUnion₂.mpr ⟨r, hr, closure_edge_subset hS h1.1 h1.2.1 h1.2.2 (subset_closure hxe)⟩

/-- **A circuit around a family of regions in a disc.** If the closed set of a family of regions
lies strictly inside a disc `Ω` of a closed surface, the boundary of the family holds a
circuit that bounds a disc in `Ω` around a given point of the family. -/
theorem exists_layer_circuit_in_disc [ConnectedSpace W] (hS : IsClosedSurface W) {Γ : Drawing W} {Z
  : Set (Set W)} (hZ : Z ⊆ Γ.R) {r₀ : Set W} (h₀ : r₀ ∈ Z) {p : W} (hp : p ∈ r₀) {Ω : Set W}
    (hΩ : IsClosedDisc Ω)
    (hsub : ⋃ r ∈ Z, closure r ⊆ discInt Ω) : ∃ (C : Drawing W) (D : Set W), C.IsCircuit
      ∧ C.IsSubdrawing (boundaryDrawing Γ Z) ∧ IsClosedDisc D ∧ discBd D = C.U ∧ p ∈ D ∧ D ⊆ Ω := by
  classical
  have hman : ∀ x : W, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hfin : Γ.R.Finite := finite_R hS Γ
  have : CompactSpace W := hS.1
  obtain ⟨E, hE, hΩE, -⟩ := Surface.exists_disc_around hman hΩ (fun x _ => hS.2.2 x) isOpen_univ
    (subset_univ _)
  obtain ⟨q⟩ := hΩ.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr', hcE, hcb, -⟩ := exists_disc_collar hΩ hE hΩE q
  obtain ⟨R, tR, ι, hR2, hRc, hRs, hιc, hιi⟩ := exists_sphere_chart
  have : CompactSpace R := hRc.1
  have : ConnectedSpace R := by
    obtain ⟨e⟩ := hRs
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have hRman : ∀ x : R, IsManifoldPoint x := fun x => (hRc.2.2 x).isManifoldPoint
  have hlcR : LocallyConnectedSpace R := IsClosedSurface.locallyConnectedSpace hRc
  let τ : W → R := ι ∘ c'
  have hτc : ContinuousOn τ E := hιc.comp_continuousOn hcc'
  have hτi : InjOn τ E := fun x hx y hy h => by
    have h1 : c' x = c' y := hιi h
    rw [← hr' hx, ← hr' hy, h1]
  have hΩE' : Ω ⊆ E := fun x hx => (hΩE hx).1
  set N := boundaryDrawing Γ Z with hN
  have hNs : N.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  set L₀ : Set W := ⋃ r ∈ Z, closure r with hL₀
  have hNL : N.U ⊆ L₀ := boundary_subset_regions hS
  have hL₀c : IsClosed L₀ := (hfin.subset hZ).isClosed_biUnion fun _ _ => isClosed_closure
  have hL₀Ω : L₀ ⊆ Ω := fun x hx => (hsub hx).1
  have hNE : N.U ⊆ E := (hNL.trans hL₀Ω).trans hΩE'
  have hne : E.Nonempty := ⟨p, hΩE' (hL₀Ω (mem_iUnion₂.mpr ⟨r₀, h₀, subset_closure hp⟩))⟩
  obtain ⟨M, hMU, hMV, hME⟩ := exists_transport hE.isCompact hne hτc hτi N hNE
  obtain ⟨ρ, hρc, hρl⟩ := Surface.exists_inv_of_compactOn hE.isCompact hτc hτi
  have hτρ : ∀ y ∈ τ '' E, τ (ρ y) = y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hρl hx]
  obtain ⟨hΩ', hΩb⟩ := isClosedDisc_image hΩ (hτc.mono hΩE') (hτi.mono hΩE')
  obtain ⟨hD₂, hD₂b⟩ := GM12.isClosedDisc_closure_compl_of_sphere hRc hRs hΩ'
  set Ω' := τ '' Ω with hΩ'def
  set D₂ := closure (univ \ Ω') with hD₂def
  have hoffD : ∀ {x}, x ∉ Ω' → x ∈ discInt D₂ := fun {x} hx => ⟨subset_closure ⟨mem_univ x, hx⟩,
    fun hb => hx (Surface.discBd_subset Ω' (hD₂b ▸ hb))⟩
  have hnotΩ : ∀ {x}, x ∈ discInt Ω' → x ∉ D₂ := fun {x} hx h => by
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h _ (hΩ'.isOpen_discInt hRman) hx
    exact hw2.2 hw1.1
  have hint₂ : ∀ {x}, x ∈ discInt D₂ → x ∉ Ω' := fun {x} hx h => by
    refine hnotΩ ⟨h, fun hb => hx.2 ?_⟩ hx.1
    rw [hD₂b]
    exact hb
  have hτint : ∀ {z}, z ∈ discInt Ω → τ z ∈ discInt Ω' := fun {z} hz => ⟨mem_image_of_mem τ hz.1,
    fun h => by
    rw [hΩb] at h
    obtain ⟨w, hw, he⟩ := h
    exact hz.2 ((hτi (hΩE' (Surface.discBd_subset _ hw)) (hΩE' hz.1) he) ▸ hw)⟩
  -- the points of the layers off `N` form an open set
  set L := τ '' L₀ with hL
  have hLc : IsClosed L := ((hL₀c.isCompact).image_of_continuousOn (hτc.mono
    (hL₀Ω.trans hΩE'))).isClosed
  have hLΩ : L ⊆ Ω' := image_mono hL₀Ω
  have hMoffL : ∀ {y}, y ∈ L₀ → y ∉ N.U → τ y ∉ M.U := fun {y} hy h1 h2 => by
    rw [hMU] at h2
    obtain ⟨w, hw, he⟩ := h2
    exact h1 (hτi (hNE hw) (hΩE' (hL₀Ω hy)) he ▸ hw)
  have hYo : IsOpen (L \ M.U) := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    obtain ⟨⟨y, hy, rfl⟩, hxM⟩ := hx
    have hyN : y ∉ N.U := fun h => hxM (hMU ▸ mem_image_of_mem τ h)
    have hyint := mem_interior_of_off_boundary hS hZ hy hyN
    have hO : IsOpen (ρ ⁻¹' (interior L₀) ∩ discInt Ω') := by
      have hρo : ContinuousOn ρ (discInt Ω') := hρc.mono fun z hz => image_mono hΩE' hz.1
      rw [inter_comm]
      exact hρo.isOpen_inter_preimage (hΩ'.isOpen_discInt hRman) isOpen_interior
    refine ⟨(ρ ⁻¹' (interior L₀) ∩ discInt Ω') ∩ M.Uᶜ, ?_, hO.inter M.isClosed_U.isOpen_compl,
      ⟨?_, hτint (hsub hy)⟩, hxM⟩
    · rintro z ⟨⟨hz1, hz2⟩, hz3⟩
      refine ⟨?_, hz3⟩
      obtain ⟨w, hw, rfl⟩ := hz2.1
      have h4 : ρ (τ w) = w := hρl (hΩE' hw)
      exact mem_image_of_mem τ (h4 ▸ interior_subset hz1 : w ∈ L₀)
    · change ρ (τ y) ∈ interior L₀
      rw [hρl (hΩE' (hL₀Ω hy))]
      exact hyint
  obtain ⟨a, ha⟩ := hD₂.nonempty_discInt
  have haΩ := hint₂ ha
  have hpL : p ∈ L₀ := mem_iUnion₂.mpr ⟨r₀, h₀, subset_closure hp⟩
  have hpU : p ∉ Γ.U := fun h => by
    obtain ⟨x, -, hx⟩ := (mem_R_iff Γ).mp (hZ h₀)
    exact (connectedComponentIn_subset _ _ (hx ▸ hp : p ∈ connectedComponentIn (univ \ Γ.U) x)).2 h
  have hpM : τ p ∉ M.U := hMoffL hpL fun h => hpU (hNs.U_subset h)
  have hUQ : M.U ⊆ ({τ p, a} : Set R)ᶜ := fun x hx h => by
    rcases h with rfl | rfl
    · exact hpM hx
    · refine haΩ ?_
      rw [hMU] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact mem_image_of_mem τ (hL₀Ω (hNL hw))
  have hnot : ¬ ∀ F, IsOArc F → F ⊆ M.U → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ ({τ p, a} : Set R)ᶜ ∧ discBd Δ
    = F := fun h => by
    obtain ⟨r, hr, har, hpr⟩ := same_region_of_discs (Q := ({τ p, a} : Set R)ᶜ) (a := a) (b
      := τ p) hRc hRs (by simp) (by simp) _ M rfl hUQ h
    have hrM : ∀ {x}, x ∈ r → x ∉ M.U := fun {x} hx h1 => by
      obtain ⟨y, -, hy⟩ := (mem_R_iff M).mp hr
      exact (connectedComponentIn_subset _ _ (hy ▸ hx : x ∈ connectedComponentIn
        (univ \ M.U) y)).2 h1
    have hsubY : r ⊆ L \ M.U := by
      refine IsPreconnected.subset_left_of_subset_union (v := (closure
        (L \ M.U))ᶜ) hYo isClosed_closure.isOpen_compl ?_ ?_ ?_ (region_isPreconnected hr)
      · exact disjoint_left.mpr fun x h1 h2 => h2 (subset_closure h1)
      · intro x hx
        by_cases hc : x ∈ closure (L \ M.U)
        · exact .inl ⟨closure_minimal sdiff_subset hLc hc, hrM hx⟩
        · exact .inr hc
      · exact ⟨τ p, hpr, mem_image_of_mem τ hpL, hpM⟩
    exact haΩ (hLΩ (hsubY har).1)
  push Not at hnot
  obtain ⟨F, hF, hFU, hno⟩ := hnot
  obtain ⟨C', hC', hC's, hC'U⟩ := exists_circuit_of_oArc hF hFU
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc R hRs F hF
  have hpF : τ p ∉ F := fun h => hUQ (hFU h) (.inl rfl)
  have haF : a ∉ F := fun h => hUQ (hFU h) (.inr rfl)
  have hhit : ∀ Δ, IsClosedDisc Δ → discBd Δ = F → τ p ∈ Δ ∨ a ∈ Δ := fun Δ h1 h2 => by
    by_contra hn
    push Not at hn
    refine hno Δ h1 (fun x hx h3 => ?_) h2
    rcases h3 with rfl | rfl
    · exact hn.1 hx
    · exact hn.2 hx
  have hex : ∃ D', IsClosedDisc D' ∧ discBd D' = F ∧ τ p ∈ D' ∧ a ∉ D' := by
    have hcovp : τ p ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ _
    by_cases h1 : τ p ∈ Δ₁
    · refine ⟨Δ₁, hΔ₁, hb₁, h1, fun h2 => ?_⟩
      rcases hhit Δ₂ hΔ₂ hb₂ with h3 | h3
      · exact hpF (hcap ▸ ⟨h1, h3⟩)
      · exact haF (hcap ▸ ⟨h2, h3⟩)
    · have h2 : τ p ∈ Δ₂ := hcovp.resolve_left h1
      have h3 : a ∈ Δ₁ := (hhit Δ₁ hΔ₁ hb₁).resolve_left h1
      exact ⟨Δ₂, hΔ₂, hb₂, h2, fun h4 => haF (hcap ▸ ⟨h3, h4⟩)⟩
  obtain ⟨D', hD', hD'b, hpD', haD'⟩ := hex
  have hD'Ω : D' ⊆ Ω' := fun x hx => by
    by_contra hn
    have hf : Disjoint (discInt D₂) (discBd D') := by
      rw [hD'b, disjoint_left]
      intro y hy1 hy2
      refine hint₂ hy1 ?_
      have := hFU hy2
      rw [hMU] at this
      obtain ⟨w, hw, rfl⟩ := this
      exact mem_image_of_mem τ (hL₀Ω (hNL hw))
    exact haD' (side_of_disc hRc hD₂ hD' hf (hoffD hn) ha hx)
  have hEsub : Ω' ⊆ τ '' E := image_mono hΩE'
  have hρcon : ContinuousOn ρ D' := hρc.mono (hD'Ω.trans hEsub)
  have hρinj : InjOn ρ D' := fun x hx y hy e => by
    rw [← hτρ x (hEsub (hD'Ω hx)), ← hτρ y (hEsub (hD'Ω hy)), e]
  obtain ⟨hD, hDb⟩ := isClosedDisc_image hD' hρcon hρinj
  have hF' : F ⊆ D' := hD'b ▸ Surface.discBd_subset D'
  have hC'Ub : C'.U ⊆ D' := hC'U ▸ hF'
  obtain ⟨C, hCU, hCV, hCE⟩ := exists_transport C'.isClosed_U.isCompact (isConnected_of_isOArc
    (hC'U ▸ hF)).nonempty (hρcon.mono hC'Ub) (hρinj.mono hC'Ub) C' subset_rfl
  have hρM : ∀ {x}, x ∈ N.U → ρ (τ x) = x := fun {x} hx => hρl (hNE hx)
  have hCsub : C.IsSubdrawing N := by
    refine ⟨?_, ?_⟩
    · rw [hCV]
      rintro _ ⟨y, hy, rfl⟩
      have h6 := hC's.1 hy
      rw [hMV] at h6
      obtain ⟨x, hx, rfl⟩ := h6
      rwa [hρM (N.V_subset_U hx)]
    · rw [hCE]
      rintro _ ⟨f, hf, rfl⟩
      have h6 := hC's.2 hf
      rw [hME] at h6
      obtain ⟨e, he, rfl⟩ := h6
      have hee : e ⊆ N.U := fun z hz => N.closure_subset_U he (subset_closure hz)
      have h7 : image ρ (image τ e) = e := by
        rw [image_image]
        exact (image_congr fun z hz => hρM (hee hz)).trans (image_id' e)
      rwa [h7]
  have hbd : discBd (ρ '' D') = C.U := by
    rw [hDb, hD'b, hCU, hC'U]
  have hO : IsOArc C.U := hbd ▸ hD.isOArc_discBd
  obtain ⟨X, h3, h4, h5⟩ := exists_circuit_of_oArc hO (hCsub.U_subset.trans hNs.U_subset)
  have hCΓ := hCsub.trans hNs
  have hV : X.V = C.V := subset_antisymm (fun x hx => mem_V_of_subdrawing hCΓ
    (h5 ▸ X.V_subset_U hx) (h4.1 hx)) fun x hx => mem_V_of_subdrawing h4
      (h5.symm ▸ C.V_subset_U hx) (hCΓ.1 hx)
  have hEq : X.E = C.E := by
    unfold Drawing.E
    rw [h5, hV]
  have hXC : X = C := Drawing.ext_of_V_E hV hEq
  refine ⟨C, ρ '' D', hXC ▸ h3, hCsub, hD, hbd, ⟨τ p, hpD', hρl (hΩE' (hL₀Ω hpL))⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hD'Ω hy
  rw [hρl (hΩE' hz)]
  exact hz

/-- In a sphere, a disc whose boundary lies inside another disc, with a point off both, lies in the
other disc. -/
theorem disc_subset_of_sphere {R : Type} [TopologicalSpace R] [T2Space R]
  (hS : IsClosedSurface R) (hsph : IsSphere R) {D D' : Set R} (hD : IsClosedDisc D)
    (hD' : IsClosedDisc D') {a : R} (ha : a ∉ D) (ha' : a ∉ D')
    (hb : discBd D ⊆ interior D') : D ⊆ D' := by
  have hfrD : frontier D = discBd D := IsClosedDisc.frontier_eq_discBd hS hD
  obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hD'
  have hcompl : discInt (closure (univ \ D')) = D'ᶜ := by
    ext x
    have hfx : x ∈ discBd D' ↔ x ∈ closure D' ∩ closure D'ᶜ := by
      rw [← IsClosedDisc.frontier_eq_discBd hS hD', frontier_eq_closure_inter_closure]
    rw [discInt, hbE, mem_sdiff, hfx, hD'.isClosed.closure_eq, ← compl_eq_univ_sdiff]
    constructor
    · rintro ⟨h1, h2⟩ h3
      exact h2 ⟨h3, h1⟩
    · intro h
      exact ⟨subset_closure h, fun h3 => h h3.1⟩
  have hX : IsPreconnected D'ᶜ := hcompl ▸ hE.isPreconnected_discInt
  have hdis2 : Disjoint D'ᶜ (frontier D) := by
    rw [hfrD]
    exact disjoint_left.mpr fun x h1 h2 => h1 (interior_subset (hb h2))
  rcases inside_or_outside hX hD.isClosed hdis2 with h | h
  · exact absurd (interior_subset (h ha')) ha
  · exact fun x hx => by
      by_contra hn
      exact h hn hx

/-- **Two discs in a disc.** If two discs lie in a disc `Ω`, and the boundary of the first lies
inside the second, then the first lies in the second. -/
theorem disc_subset_of_disc {X : Type*} [TopologicalSpace X] [T2Space X]
  (hman : ∀ x : X, IsManifoldPoint x) {Ω D D' : Set X} (hΩ : IsClosedDisc Ω)
    (hint : ∀ x ∈ discBd Ω, IsInteriorPoint x) (hD : IsClosedDisc D) (hD' : IsClosedDisc D')
      (hDΩ : D ⊆ Ω) (hD'Ω : D' ⊆ Ω)
    (hb : discBd D ⊆ discInt D') : D ⊆ D' := by
  obtain ⟨E, hE, hΩE, -⟩ := Surface.exists_disc_around hman hΩ hint isOpen_univ (subset_univ _)
  obtain ⟨q⟩ := hΩ.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr', hcE, hcb, -⟩ := exists_disc_collar hΩ hE hΩE q
  obtain ⟨R, tR, ι, hR2, hRc, hRs, hιc, hιi⟩ := exists_sphere_chart
  have : ConnectedSpace R := by
    obtain ⟨e⟩ := hRs
    exact e.symm.surjective.connectedSpace e.symm.continuous
  have hRman : ∀ x : R, IsManifoldPoint x := fun x => (hRc.2.2 x).isManifoldPoint
  let τ : X → R := ι ∘ c'
  have hτc : ContinuousOn τ E := hιc.comp_continuousOn hcc'
  have hτi : InjOn τ E := fun x hx y hy h => by
    have h1 : c' x = c' y := hιi h
    rw [← hr' hx, ← hr' hy, h1]
  have hΩE' : Ω ⊆ E := fun x hx => (hΩE hx).1
  obtain ⟨hΩ', -⟩ := isClosedDisc_image hΩ (hτc.mono hΩE') (hτi.mono hΩE')
  obtain ⟨hD₂, hD₂b⟩ := GM12.isClosedDisc_closure_compl_of_sphere hRc hRs hΩ'
  obtain ⟨a, ha⟩ := hD₂.nonempty_discInt
  have haΩ : a ∉ τ '' Ω := fun h => by
    have h1 : a ∈ discInt (τ '' Ω) := ⟨h, fun hb' => ha.2 (hD₂b ▸ hb')⟩
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp ha.1 _ (hΩ'.isOpen_discInt hRman) h1
    exact hw2.2 hw1.1
  obtain ⟨h1, h2⟩ := isClosedDisc_image hD (hτc.mono (hDΩ.trans hΩE')) (hτi.mono (hDΩ.trans hΩE'))
  obtain ⟨h3, h4⟩ := isClosedDisc_image hD' (hτc.mono (hD'Ω.trans hΩE')) (hτi.mono
    (hD'Ω.trans hΩE'))
  have hin : discBd (τ '' D) ⊆ interior (τ '' D') := by
    rw [h2]
    rintro _ ⟨y, hy, rfl⟩
    exact interior_maximal (discInt_subset _) (h3.isOpen_discInt hRman) (by
      refine ⟨mem_image_of_mem τ (hb hy).1, fun h5 => ?_⟩
      rw [h4] at h5
      obtain ⟨w, hw, he⟩ := h5
      exact (hb hy).2 ((hτi (hΩE' (hD'Ω (Surface.discBd_subset _ hw)))
        (hΩE' (hDΩ (Surface.discBd_subset _ hy))) he) ▸ hw))
  have hsub := disc_subset_of_sphere hRc hRs h1 h3 (fun h => haΩ (image_mono hDΩ h)) (fun h => haΩ
    (image_mono hD'Ω h)) hin
  intro x hx
  obtain ⟨y, hy, he⟩ := hsub (mem_image_of_mem τ hx)
  exact hτi (hΩE' (hD'Ω hy)) (hΩE' (hDΩ hx)) he ▸ hy

/-- **A disc with its boundary in a smaller disc.** If a disc `D` lies in a disc `Ω` of a closed
surface, and the boundary of `D` lies in a disc `Δ` strictly inside `Ω`, then `D` lies in `Δ`. The
reason is that `Ω` without `Δ` is connected, misses the boundary of `D`, and has a point off `D`. -/
theorem disc_subset_of_bd_in_disc {X : Type} [TopologicalSpace X] [T2Space X]
  (hS : IsClosedSurface X) {Ω Δ D : Set X} (hΩ : IsClosedDisc Ω) (hΔ : IsClosedDisc Δ)
    (hD : IsClosedDisc D) (hin : Δ ⊆ Ω \ discBd Ω) (hDΩ : D ⊆ Ω) (hb : discBd D ⊆ Δ) : D ⊆ Δ := by
  have hman : ∀ x : X, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨q⟩ := hΔ.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr', hcE, hcb, -⟩ := exists_disc_collar hΔ hΩ hin q
  -- the part of `Ω` off `Δ`
  let A : Set ℂ := Metric.closedBall 0 2 \ Metric.closedBall 0 1
  have hAc : IsPreconnected A := by
    have hs : IsPreconnected (Metric.sphere (0 : ℂ) 1) := isPreconnected_sphere (by
      rw [Complex.rank_real_complex]
      norm_num) 0 1
    have : A = (fun w : ℝ × ℂ => (w.1 : ℂ) * w.2) '' (Set.Ioc 1 2 ×ˢ Metric.sphere (0 : ℂ) 1) := by
      ext z
      simp only [A, mem_sdiff, Metric.mem_closedBall, dist_zero_right, mem_image, mem_prod,
        mem_Ioc, Prod.exists, not_le, mem_sphere_zero_iff_norm]
      constructor
      · rintro ⟨h1, h2⟩
        have h0 : (‖z‖ : ℂ) ≠ 0 := by
          exact_mod_cast (by linarith : ‖z‖ ≠ 0)
        refine ⟨‖z‖, z / ‖z‖, ⟨⟨h2, h1⟩, ?_⟩, by field_simp⟩
        rw [norm_div, Complex.norm_real, norm_norm, div_self (by linarith)]
      · rintro ⟨r, w, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
        simp only [norm_mul, h3, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by linarith)]
        exact ⟨h2, h1⟩
    rw [this]
    refine (isPreconnected_Ioc.prod hs).image _ ?_
    refine Continuous.continuousOn ?_
    fun_prop
  have hAs : A ⊆ Metric.closedBall 0 2 := sdiff_subset
  have hcA : ContinuousOn c A := hcc.mono hAs
  have hX : IsPreconnected (c '' A) := hAc.image c hcA
  have hA1 : ∀ x ∈ Δ, x ∈ c '' Metric.closedBall 0 1 := fun x hx => hcE ▸ hx
  have hoff : Disjoint (c '' A) Δ := disjoint_left.mpr fun x hx h1 => by
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', he⟩ := hA1 _ h1
    have hz'2 : z' ∈ Metric.closedBall (0 : ℂ) 2 := Metric.closedBall_subset_closedBall
      (by norm_num) hz'
    have : z' = z := by rw [← hl hz'2, he, hl hz.1]
    exact hz.2 (this ▸ hz')
  have hfr : frontier D = discBd D := IsClosedDisc.frontier_eq_discBd hS hD
  have hdis : Disjoint (c '' A) (frontier D) := by
    rw [hfr]
    exact hoff.mono_right hb
  -- a boundary point of `Ω` is off `D`
  have hne : (Metric.sphere (0 : ℂ) 2).Nonempty := ⟨2, by simp⟩
  obtain ⟨z₂, hz₂⟩ := hne
  have hyb : c z₂ ∈ discBd Ω := hcb ▸ mem_image_of_mem c hz₂
  have hyA : c z₂ ∈ c '' A := by
    refine ⟨z₂, ⟨Metric.sphere_subset_closedBall hz₂, fun h1 => ?_⟩, rfl⟩
    have h2 : ‖z₂‖ = 2 := by simpa using hz₂
    have h3 : ‖z₂‖ ≤ 1 := by simpa using h1
    linarith
  have hyD : c z₂ ∉ D := fun h1 => by
    by_cases h2 : c z₂ ∈ discBd D
    · exact disjoint_left.mp hdis hyA (hfr ▸ h2)
    · exact (discInt_mono hman hD hDΩ ⟨h1, h2⟩).2 hyb
  rcases inside_or_outside hX hD.isClosed hdis with h | h
  · exact absurd (interior_subset (h hyA)) hyD
  · intro x hx
    have hxΩ := hDΩ hx
    by_contra hxn
    have hc2 := hm' hxΩ
    have hne1 : c' x ∉ Metric.closedBall (0 : ℂ) 1 := fun h1 => hxn (hcE ▸ ⟨c' x, h1, hr' hxΩ⟩)
    exact h ⟨c' x, ⟨hc2, hne1⟩, hr' hxΩ⟩ hx

/-- **The nest of the layers in a disc.** If the first `s` layers around a region lie strictly
inside a disc of a closed surface, they give `s` disjoint nested circuits. -/
theorem exists_region_nest_in_disc [ConnectedSpace W] (hS : IsClosedSurface W) {Γ : Drawing W} {r₀
  : Set W} (h₀ : r₀ ∈ Γ.R) {p : W} (hp : p ∈ r₀) {Ω : Set W} (hΩ : IsClosedDisc Ω) {s : ℕ}
    (hsub : ∀ t < s, ⋃ r ∈ regLayer Γ r₀ t, closure r ⊆ discInt Ω) :
    ∃ (C : Fin s → Drawing W) (D : Fin s → Set W), (∀ t, (C t).IsCircuit ∧ (C t).IsSubdrawing
      (boundaryDrawing Γ (regLayer Γ r₀ t)) ∧ IsClosedDisc (D t) ∧ discBd (D t) = (C t).U ∧ p ∈ D t
        ∧ D t ⊆ Ω) ∧
      ∀ t t', t < t' → Disjoint (C t).V (C t').V ∧ D t ⊆ D t' := by
  classical
  have hman : ∀ x : W, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hex : ∀ t : Fin s, ∃ (C : Drawing W) (D : Set W), C.IsCircuit ∧ C.IsSubdrawing
    (boundaryDrawing Γ (regLayer Γ r₀ t)) ∧ IsClosedDisc D ∧ discBd D = C.U ∧ p ∈ D ∧ D ⊆ Ω
      := fun t =>
    exists_layer_circuit_in_disc hS (regLayer_subset h₀ t) (regLayer_mono
      (Nat.zero_le t) rfl) hp hΩ (hsub t t.2)
  choose C D hC hCs hD hb hpD hDΩ using hex
  refine ⟨C, D, fun t => ⟨hC t, hCs t, hD t, hb t, hpD t, hDΩ t⟩, fun t t' htt => ?_⟩
  have hin : ∀ {x}, x ∈ (C t).U → x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := fun {x} hx
    => boundary_subset_layer hS ((hCs t).U_subset hx)
  have hfr' : frontier (D t') = (C t').U := by
    rw [IsClosedDisc.frontier_eq_discBd hS (hD t'), hb t']
  have hoff : ∀ {x}, x ∈ (C t').U → x ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r → False := fun {x} hx h
    => boundary_off_layer hS h₀ (Fin.lt_def.mp htt) ((hCs t').U_subset hx) h
  refine ⟨disjoint_left.mpr fun x h1 h2 => hoff ((C t').V_subset_U h2) (hin
    ((C t).V_subset_U h1)), ?_⟩
  have hL := isPreconnected_layer h₀ t
  have hpL : p ∈ ⋃ r ∈ regLayer Γ r₀ t, closure r := mem_iUnion₂.mpr ⟨r₀, regLayer_mono
    (Nat.zero_le _) rfl, subset_closure hp⟩
  have hdis : Disjoint (⋃ r ∈ regLayer Γ r₀ t, closure r) (frontier (D t')) := by
    rw [hfr']
    exact disjoint_left.mpr fun x h1 h2 => hoff h2 h1
  have hint : (⋃ r ∈ regLayer Γ r₀ t, closure r) ⊆ interior (D t') := by
    rcases inside_or_outside hL (hD t').isClosed hdis with h | h
    · exact h
    · exact absurd (hpD t') (h hpL)
  refine disc_subset_of_disc hman hΩ (fun x _ => hS.2.2 x) (hD t) (hD t') (hDΩ t) (hDΩ t') fun x hx
    => ?_
  have h1 := hint (hin (hb t ▸ hx))
  refine ⟨interior_subset h1, fun h2 => ?_⟩
  rw [← IsClosedDisc.frontier_eq_discBd hS (hD t')] at h2
  exact h2.2 h1

end GraphMinor.GM07
