/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.DiscSide

/-!
# Graph Minors XIX, (5.3): the fifth condition of "fit"

Take an edge `e₁` of size three of `Γ₁`, a region `r₁`, and a component `f₁` of `e₁ ∩ rBar₁` whose
closure misses
`bd(Σ₁)`. The paper says that `f = ψ(f₁)` is a component of `rBar ∩ e` for a region `r` of `Γ`. This
needs that the
region next to a point of the boundary of the disc `ē` does not change along an arc, and that is
what we prove
first. The rest follows the paper.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


/-- A connected set in `Θ` minus the ends of an arc of `Θ`, that meets the arc, lies in the arc. -/
theorem subset_arcOf {Θ : Set S} (f : Circle ≃ₜ Θ) {a b : ℝ} (hab : a < b)
  (hub : b < a + 2 * Real.pi)
    {F : Set S} (hF : IsPreconnected F) (hFΘ : F ⊆ Θ) (ha : cuffPoint f a ∉ F)
      (hb : cuffPoint f b ∉ F)
    {y : S} (hyF : y ∈ F) (hyA : y ∈ arcOf f a b) : F ⊆ arcOf f a b := by
  have hpi := Real.pi_pos
  let T₁ : Set S := cuffPoint f '' Icc a b
  let T₂ : Set S := cuffPoint f '' Icc b (a + 2 * Real.pi)
  have hc : Continuous (cuffPoint f) := continuous_cuffPoint f
  have hT₁ : IsClosed T₁ := (isCompact_Icc.image hc).isClosed
  have hT₂ : IsClosed T₂ := (isCompact_Icc.image hc).isClosed
  have hcov : F ⊆ T₁ ∪ T₂ := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := exists_angle_in f a ⟨z, hFΘ hz⟩
    change cuffPoint f t = z at hzt
    rcases le_total t b with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, hzt⟩
    · exact Or.inr ⟨t, ⟨h, ht.2.le⟩, hzt⟩
  have hsubT : F ⊆ T₁ := by
    intro z hz
    by_contra hzn
    have hzT₂ := hcov hz |>.resolve_left hzn
    obtain ⟨w, hwF, ⟨t, ht, hwt⟩, ⟨t', ht', hwt'⟩⟩ := isPreconnected_closed_iff.mp hF T₁ T₂ hT₁ hT₂
      hcov
      ⟨y, hyF, (by obtain ⟨t, ht, h⟩ := hyA; exact ⟨t, ⟨ht.1.le, ht.2.le⟩, h⟩)⟩ ⟨z, hz, hzT₂⟩
    obtain ⟨m, hm⟩ := cuffPoint_eq f (hwt.trans hwt'.symm)
    have hm0 : (m : ℝ) * (2 * Real.pi) ≤ 0 := by linarith [ht.2, ht'.1]
    have hm1 : -(2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) := by linarith [ht.1, ht'.2]
    have h₁ : (m : ℝ) ≤ 0 := by nlinarith
    have h₂ : (-1 : ℝ) ≤ m := by nlinarith
    have h₁' : m ≤ 0 := by exact_mod_cast h₁
    have h₂' : -1 ≤ m := by exact_mod_cast h₂
    obtain rfl | rfl : m = 0 ∨ m = -1 := by omega
    · have ht1 : t = b := by
        push_cast at hm
        linarith [ht.2, ht'.1]
      exact hb (ht1 ▸ hwt ▸ hwF)
    · have ht1 : t = a := by
        push_cast at hm
        linarith [ht.1, ht'.2]
      exact ha (ht1 ▸ hwt ▸ hwF)
  intro z hz
  obtain ⟨t, ht, rfl⟩ := hsubT hz
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
  · rintro rfl
    exact ha hz
  · rintro rfl
    exact hb hz

namespace Painting

variable {Γ : Painting S}

omit [T2Space S] in
/-- A point of the closure of a region off the region lies in `U(Γ)`. -/
theorem mem_U_of_closure_region (hS : IsSurface S) {r : Set S} (hr : r ∈ Γ.regions) {z : S}
    (hz : z ∈ closure r) (hzr : z ∉ r) : z ∈ Γ.U := by
  have : LocallyConnectedSpace S := IsSurface.locallyConnected hS
  by_contra hzU
  obtain ⟨r₀, hr₀, rfl⟩ := id hr
  have hopen : IsOpen (connectedComponentIn Γ.Uᶜ z) :=
    Γ.isClosed_U.isOpen_compl.connectedComponentIn
  obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz _ hopen (mem_connectedComponentIn hzU)
  have h₁ := connectedComponentIn_eq hw₁
  have h₂ := connectedComponentIn_eq hw₂
  exact hzr (h₂.trans h₁.symm ▸ mem_connectedComponentIn hzU)

/-- Near a point `y` of the boundary of the disc of an edge `e` of size three, the outside of the
disc is connected
and misses `U(Γ)`. -/
theorem exists_side_nhds (hS : IsSurface S) {e : Set S} (he : e ∈ Γ.E) (h3 : (tilde e).ncard = 3)
    (hb : ¬ IsBorder e) {O : Set S} (hO : IsOpen O) (heO : e ⊆ O) {y : S} (hye : y ∈ e)
    (hyΘ : y ∈ discBd (closure e)) :
    ∃ W, IsOpen W ∧ y ∈ W ∧ ∃ B ⊆ Γ.Uᶜ ∩ O, IsPreconnected B ∧ (closure e)ᶜ ∩ W ⊆ B := by
  have hy : y ∉ bd S := fun h ↦ hb ⟨y, hye, h⟩
  let 𝓔 : Set (Set S) := closure '' {e' ∈ Γ.E | e' ≠ e}
  have hfin : 𝓔.Finite := (Γ.finite_edges.subset (sep_subset _ _)).image _
  let F : Set S := Γ.V ∪ ⋃₀ 𝓔
  have hFc : IsClosed F := Γ.finite_V.isClosed.union (hfin.isClosed_sUnion (by
    rintro _ ⟨c, -, rfl⟩
    exact isClosed_closure))
  have hyF : y ∉ F := by
    rintro (hv | ⟨_, ⟨c, ⟨hc, hne⟩, rfl⟩, hyc⟩)
    · exact Γ.disjoint_V he hye hv
    · rcases Γ.closure_subset hc hyc with h | h
      · exact hne (arcComp_eq_of_mem hc he h hye)
      · exact Γ.disjoint_V he hye h
  have hoff : ∀ x, x ∉ closure e → x ∉ F → x ∉ Γ.U := by
    intro x hxe hxF hxU
    have hxV : x ∉ Γ.V := fun h ↦ hxF (Or.inl h)
    obtain ⟨c, hc, hsub⟩ := exists_arcComp_superset (isPathConnected_singleton x) (F := Γ.U \ Γ.V)
      (singleton_subset_iff.mpr ⟨hxU, hxV⟩)
    have hxc : x ∈ c := hsub rfl
    refine hxF (Or.inr ⟨closure c, ⟨c, ⟨hc, fun h ↦ hxe (h ▸ subset_closure hxc)⟩, rfl⟩,
      subset_closure hxc⟩)
  obtain ⟨B, hBs, hBc, W', hW', hsub⟩ := (isConnectedNear_compl_disc hS
    (Γ.isDisc_of_three he h3).1 hyΘ hy).1
    (Fᶜ ∩ O) (hFc.isOpen_compl.inter hO |>.mem_nhds ⟨hyF, heO hye⟩)
  refine ⟨interior W', isOpen_interior, mem_interior_iff_mem_nhds.mpr hW', B, ?_, hBc, ?_⟩
  · intro x hx
    obtain ⟨h₁, h₂, h₃⟩ := hBs hx
    exact ⟨hoff x h₁ h₂, h₃⟩
  · exact fun x hx ↦ hsub ⟨hx.1, interior_subset hx.2⟩

omit [T2Space S] in
/-- A point of an edge of size three in the closure of a region is on the boundary of the disc. -/
theorem mem_discBd_of_closure_region (hS : IsSurface S) {e r : Set S} (he : e ∈ Γ.E)
    (h3 : (tilde e).ncard = 3) (hr : r ⊆ Γ.Uᶜ) {y : S} (hye : y ∈ closure e) (hyr : y ∈ closure r) :
    y ∈ discBd (closure e) := by
  by_contra hn
  have hop := (Γ.isDisc_of_three he h3).1.isOpen_discInt hS.2.2
  obtain ⟨x, hx₁, hx₂⟩ := mem_closure_iff.mp hyr _ hop ⟨hye, hn⟩
  exact hr hx₂ (Γ.closure_subset_U he hx₁.1)

end Painting

variable {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

namespace PullData

variable (d : PullData Γ K ψ)
include d

omit [T2Space S₁] in
/-- A connected part of `R \ U(Γ)` that meets the image of a region of `Γ₁` lies in that image. -/
theorem subset_image_region {r₁ B : Set _} (hr₁ : r₁ ∈ componentsIn (pullU Γ ψ)ᶜ)
    (hB : B ⊆ Γ.Uᶜ ∩ IsCuttingFragment.R ψ) (hBc : IsPreconnected B) (hne :
      (ψ '' r₁ ∩ B).Nonempty) :
    B ⊆ ψ '' r₁ := by
  obtain ⟨x₀, hx₀, rfl⟩ := id hr₁
  obtain ⟨_, ⟨z, hz, rfl⟩, hzB⟩ := hne
  have hB₁ : IsPreconnected (ψ ⁻¹' B) :=
    d.frag.isPreconnected_preimage d.isClosed_bd d.isOpen_R (fun x hx ↦ (hB hx).2) hBc
  have hsub : ψ ⁻¹' B ⊆ (pullU Γ ψ)ᶜ := by
    rintro x hx (hxU | hxb)
    · exact (hB hx).1 hxU
    · exact d.frag.mem_R_iff.mp (hB hx).2 hxb
  rw [connectedComponentIn_eq hz]
  have hin := hB₁.subset_connectedComponentIn hzB hsub
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (hB hy).2
  exact mem_image_of_mem ψ (hin hy)

omit [T2Space S₁] in
/-- The set `ψ(rBar₁)` is open in the boundary of the disc `ē`, inside `e`. This is the step the
paper leaves out:
the region next to a point of `e` does not change along the boundary of the disc. -/
theorem exists_nhds_image_closure (hS : IsSurface S) {e r₁ : Set _} (he : e ∈ Γ.E) (h3 :
  (tilde e).ncard = 3)
    (hb : ¬ Painting.IsBorder e) (hR : e ⊆ IsCuttingFragment.R ψ) (hr₁ : r₁ ∈ componentsIn
      (pullU Γ ψ)ᶜ)
    {y : S} (hye : y ∈ e) (hyΘ : y ∈ discBd (closure e)) (hy : y ∈ ψ '' closure r₁) :
    ∃ W, IsOpen W ∧ y ∈ W ∧ W ∩ e ∩ discBd (closure e) ⊆ ψ '' closure r₁ := by
  obtain ⟨W, hW, hyW, B, hBs, hBc, hsub⟩ := Γ.exists_side_nhds hS he h3 hb d.isOpen_R hR hye hyΘ
  obtain ⟨y₁, hy₁, rfl⟩ := hy
  have hc := d.frag.continuous_ψ
  obtain ⟨x₁, hx₁W, hx₁r⟩ := mem_closure_iff.mp hy₁ _ (hW.preimage hc) hyW
  have hrU : r₁ ⊆ (pullU Γ ψ)ᶜ := by
    obtain ⟨x₀, -, rfl⟩ := id hr₁
    exact connectedComponentIn_subset _ _
  have hxU : ψ x₁ ∉ Γ.U := fun h ↦ hrU hx₁r (Or.inl h)
  have hxB : ψ x₁ ∈ B := hsub ⟨fun h ↦ hxU (Γ.closure_subset_U he h), hx₁W⟩
  have hBsub := d.subset_image_region hr₁ hBs hBc ⟨_, mem_image_of_mem ψ hx₁r, hxB⟩
  refine ⟨W, hW, hyW, fun y' hy' ↦ ?_⟩
  have hy'b : y' ∉ bd S := fun h ↦ hb ⟨y', hy'.1.2, h⟩
  have hcl := (isConnectedNear_compl_disc hS (Γ.isDisc_of_three he h3).1 hy'.2 hy'b).2
  have hcl' := hW.inter_closure ⟨hy'.1.1, hcl⟩
  have hsub' : W ∩ (closure e)ᶜ ⊆ ψ '' r₁ := fun x hx ↦ hBsub (hsub ⟨hx.2, hx.1⟩)
  have h := closure_mono hsub' hcl'
  rwa [d.frag.isClosedMap.closure_image_eq_of_continuous hc] at h

omit [T2Space S₁] in
/-- The core of the fifth condition. Let `r₁` be a region of `Γ₁`, and let `y₀` be a point of `e₁ ∩
rBar₁` whose component
in `e₁ ∩ rBar₁` has its closure off `bd(Σ₁)`. The arc of the boundary of `ē` through `ψ(y₀)` lies in
`ψ(rBar₁)`, and its ends
`v, v'` lie off `bd(Σ)` and off `U(K)`. The component of `ē ∩ rBar` through `ψ(y₀)` lies in this
arc, for the region `r` of
`Γ` that holds `ψ(r₁)`. So the fifth condition for `Γ` gives `rBar ∩ V(Γ) = {v, v'}`. Each component
of `K` has a vertex
of `Γ`, and so `U(K)` misses `rBar`. Thus each point of `rBar₁ ∩ V₁` lies over `v` or `v'`, in the
interior of `Σ₁`. -/
theorem ncard_closure_region_le (hS : IsSurface S) (hfive : ∀ e ∈ Γ.E, (tilde e).ncard = 3
  → ∀ r ∈ Γ.regions,
      3 ≤ (closure r ∩ Γ.V).ncard → ∀ f ∈ componentsIn (e ∩ closure r), (closure f ∩ bd S).Nonempty)
    (hA : IsAnchored Γ K) {e r₁ : Set _} (he : e ∈ Γ.E) (h3 : (tilde e).ncard = 3)
    (hb : ¬ Painting.IsBorder e) (hR : e ⊆ IsCuttingFragment.R ψ) (hr₁ : r₁ ∈ componentsIn
      (pullU Γ ψ)ᶜ)
    {y₀ : S₁} (hy₀ : y₀ ∈ ψ ⁻¹' e ∩ closure r₁)
    (hno : ¬ (closure (connectedComponentIn (ψ ⁻¹' e ∩ closure r₁) y₀) ∩ bd S₁).Nonempty) :
    (closure r₁ ∩ pullV Γ K ψ).ncard ≤ 2 := by
  have hc := d.frag.continuous_ψ
  have hcl := d.frag.isClosedMap
  have hinjR : ∀ {x x' : S₁}, ψ x ∈ IsCuttingFragment.R ψ → ψ x = ψ x' → x = x'
    := fun {x x'} h hxx ↦
    d.frag.injOn_interior (d.frag.mem_R_iff.mp h) (d.frag.mem_R_iff.mp (hxx ▸ h)) hxx
  -- the region `r`
  obtain ⟨x₀, hx₀, hr₁eq⟩ := id hr₁
  let r : Set S := connectedComponentIn Γ.Uᶜ (ψ x₀)
  have hrU₁ : r₁ ⊆ (pullU Γ ψ)ᶜ := hr₁eq ▸ connectedComponentIn_subset _ _
  have hx₀U : ψ x₀ ∈ Γ.Uᶜ := fun h ↦ hx₀ (Or.inl h)
  have hrmem : r ∈ Γ.regions := ⟨ψ x₀, hx₀U, rfl⟩
  have hrU : r ⊆ Γ.Uᶜ := connectedComponentIn_subset _ _
  have hsubr : ψ '' r₁ ⊆ r := by
    have hpc : IsPreconnected (ψ '' r₁) :=
      (hr₁eq ▸ isPreconnected_connectedComponentIn : IsPreconnected r₁).image _ hc.continuousOn
    refine hpc.subset_connectedComponentIn ⟨x₀, hr₁eq ▸ mem_connectedComponentIn hx₀, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩ h
    exact hrU₁ hx (Or.inl h)
  have hClr : ψ '' closure r₁ ⊆ closure r :=
    (image_closure_subset_closure_image hc).trans (closure_mono hsubr)
  -- the arc
  let Δ := closure e
  obtain ⟨hdisc, hTΘ, hTf⟩ := Γ.isDisc_of_three he h3
  let y := ψ y₀
  have hye : y ∈ e := hy₀.1
  have hyCl : y ∈ ψ '' closure r₁ := mem_image_of_mem ψ hy₀.2
  have hyΘ : y ∈ discBd Δ :=
    Γ.mem_discBd_of_closure_region hS he h3 hrU (subset_closure hye) (hClr hyCl)
  have hyT : y ∉ tilde e := fun h ↦ h.2 hye
  obtain ⟨φ⟩ := hdisc.isOArc_discBd
  obtain ⟨p, q, w, hpq, -, -, hT⟩ := Set.ncard_eq_three.mp h3
  have hpT : p ∈ tilde e := hT ▸ mem_insert _ _
  have hqT : q ∈ tilde e := hT ▸ mem_insert_of_mem _ (mem_insert _ _)
  obtain ⟨a, b, hab, hub, hyA, hdisj, haT, hbT⟩ := exists_arc_of_two φ hTf ⟨hpT, hTΘ hpT⟩ ⟨hqT, hTΘ
    hqT⟩ hpq
    ⟨hyΘ, hyT⟩
  let A := arcOf φ a b
  let v := cuffPoint φ a
  let v' := cuffPoint φ b
  have hvne : v ≠ v' := (GM20.line_facts (isLine_arcOf φ hab hub)).1
  have hAΘ : A ⊆ discBd Δ := arcOf_subset φ a b
  have hAe : A ⊆ e := fun x hx ↦ by
    by_contra hxe
    exact disjoint_left.mp hdisj hx ⟨discBd_subset _ (hAΘ hx), hxe⟩
  -- `A` lies in `ψ(rBar₁)`
  have hAc : IsPreconnected A := by
    rw [show A = cuffPoint φ '' Ioo a b from rfl]
    exact isPreconnected_Ioo.image _ (continuous_cuffPoint φ).continuousOn
  have hClc : IsClosed (ψ '' closure r₁) := hcl _ isClosed_closure
  have hACl : A ⊆ ψ '' closure r₁ := by
    intro x hxA
    by_contra hxn
    have hex : ∀ y' : ↥(A ∩ ψ '' closure r₁), ∃ W, IsOpen W ∧ y'.1 ∈ W ∧
        W ∩ e ∩ discBd (closure e) ⊆ ψ '' closure r₁ := fun y' ↦
      d.exists_nhds_image_closure hS he h3 hb hR hr₁ (hAe y'.2.1) (hAΘ y'.2.1) y'.2.2
    choose W hWo hyW hWs using hex
    obtain ⟨z, hzA, hzO, hzC⟩ := hAc (⋃ y', W y') (ψ '' closure r₁)ᶜ (isOpen_iUnion hWo)
      hClc.isOpen_compl
      (fun z hz ↦ by
        by_cases hzC : z ∈ ψ '' closure r₁
        · exact Or.inl (mem_iUnion.mpr ⟨⟨z, hz, hzC⟩, hyW _⟩)
        · exact Or.inr hzC)
      ⟨y, hyA, mem_iUnion.mpr ⟨⟨y, hyA, hyCl⟩, hyW _⟩⟩ ⟨x, hxA, hxn⟩
    obtain ⟨y', hzW⟩ := mem_iUnion.mp hzO
    exact hzC (hWs y' ⟨⟨hzW, hAe hzA⟩, hAΘ hzA⟩)
  -- lifts of the ends
  have hAR : A ⊆ IsCuttingFragment.R ψ := hAe.trans hR
  have hA₁c : IsPreconnected (ψ ⁻¹' A) := d.frag.isPreconnected_preimage d.isClosed_bd d.isOpen_R
    hAR hAc
  have hA₁sub : ψ ⁻¹' A ⊆ ψ ⁻¹' e ∩ closure r₁ := by
    intro x hx
    obtain ⟨x', hx', hxx⟩ := hACl hx
    exact ⟨hAe hx, (hinjR (hAR hx) hxx.symm) ▸ hx'⟩
  have hA₁f := hA₁c.subset_connectedComponentIn (show y₀ ∈ ψ ⁻¹' A from hyA) hA₁sub
  have hclA : closure A = cuffPoint φ '' Icc a b := closure_arcOf φ hab
  have hAimg : A = ψ '' (ψ ⁻¹' A) := by
    refine (image_preimage_eq_of_subset ?_).symm
    exact fun x hx ↦ image_subset_range _ _ (hAR hx)
  have hclsub : closure A ⊆ ψ '' closure (connectedComponentIn (ψ ⁻¹' e ∩ closure r₁) y₀) := by
    conv_lhs => rw [hAimg]
    rw [hcl.closure_image_eq_of_continuous hc]
    exact image_mono (closure_mono hA₁f)
  have hvA : v ∈ closure A := by rw [hclA]; exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
  have hvA' : v' ∈ closure A := by rw [hclA]; exact ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩
  have hoff : ∀ {u}, u ∈ closure A → u ∉ bd S ∪ K.U := by
    intro u hu hub
    obtain ⟨u₁, hu₁, rfl⟩ := hclsub hu
    exact hno ⟨u₁, hu₁, d.mem_bd_of_notMem_R hub⟩
  have hArcl : closure A ⊆ closure r := closure_minimal (hACl.trans hClr) isClosed_closure
  have hvV : v ∈ closure r ∩ Γ.V := ⟨hArcl hvA, Γ.tilde_subset_V he haT⟩
  have hvV' : v' ∈ closure r ∩ Γ.V := ⟨hArcl hvA', Γ.tilde_subset_V he hbT⟩
  -- the fifth condition for `Γ`
  have hlt : ¬ 3 ≤ (closure r ∩ Γ.V).ncard := by
    intro hcard
    have hf : connectedComponentIn (e ∩ closure r) y ∈ componentsIn (e ∩ closure r) :=
      ⟨y, ⟨hye, hClr hyCl⟩, rfl⟩
    have hfsub : connectedComponentIn (e ∩ closure r) y ⊆ e ∩ closure r
      := connectedComponentIn_subset _ _
    have hFΘ : connectedComponentIn (e ∩ closure r) y ⊆ discBd Δ := fun x hx ↦
      Γ.mem_discBd_of_closure_region hS he h3 hrU (subset_closure (hfsub hx).1) (hfsub hx).2
    have hsubA := subset_arcOf φ hab hub isPreconnected_connectedComponentIn hFΘ
      (fun h ↦ (hfsub h).1 |> fun hin ↦ haT.2 hin) (fun h ↦ (hfsub h).1 |> fun hin ↦ hbT.2 hin)
      (mem_connectedComponentIn ⟨hye, hClr hyCl⟩) hyA
    obtain ⟨z, hz, hzb⟩ := hfive e he h3 r hrmem hcard _ hf
    exact hoff (closure_mono hsubA hz) (Or.inl hzb)
  have hsubvv : closure r ∩ Γ.V ⊆ {v, v'} := by
    rintro w₀ hw₀
    by_contra hw
    have hw₁ : v ≠ w₀ := fun h ↦ hw (h ▸ mem_insert _ _)
    have hw₂ : v' ≠ w₀ := fun h ↦ hw (h ▸ mem_insert_of_mem _ rfl)
    have h3' : ({v, v', w₀} : Set S).ncard = 3 := Set.ncard_eq_three.mpr ⟨v, v', w₀, hvne, hw₁,
      hw₂, rfl⟩
    refine hlt (h3' ▸ Set.ncard_le_ncard ?_ (Γ.finite_V.subset inter_subset_right))
    rintro _ (rfl | rfl | rfl)
    · exact hvV
    · exact hvV'
    · exact hw₀
  have hvvK : ∀ {u}, u ∈ closure r ∩ Γ.V → u ∉ bd S ∪ K.U := by
    intro u hu
    rcases hsubvv hu with rfl | rfl
    · exact hoff hvA
    · exact hoff hvA'
  -- `U(K)` misses `rBar`
  have hrK : ∀ x ∈ closure r, x ∉ K.U := by
    intro x hxr hxK
    have hxv : x ≠ v := fun h ↦ hoff hvA (Or.inr (h ▸ hxK))
    obtain ⟨C, hCs, hxC, hCc, g, hgC, hgV⟩ := hA v x hxK hxv
    by_cases hgr : g ∈ closure r
    · exact hvvK ⟨hgr, hgV⟩ (Or.inr (hCs hgC).1)
    · obtain ⟨z, hzC, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hCc (closure r) (closure
      (closure r)ᶜ)
        isClosed_closure isClosed_closure (fun z _ ↦ by
          by_cases hzr : z ∈ closure r
          · exact Or.inl hzr
          · exact Or.inr (subset_closure hzr)) ⟨x, hxC, hxr⟩ ⟨g, hgC, subset_closure hgr⟩
      have hrop : IsOpen r := by
        have : LocallyConnectedSpace S := IsSurface.locallyConnected hS
        exact Γ.isClosed_U.isOpen_compl.connectedComponentIn
      have hzr : z ∉ r := fun h ↦ by
        obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hz₂ _ hrop h
        exact hw₂ (subset_closure hw₁)
      have hzU := Painting.mem_U_of_closure_region hS hrmem hz₁ hzr
      have hzV : z ∈ Γ.V := (d.inter ⟨hzU, (hCs hzC).1⟩).1
      exact hvvK ⟨hz₁, hzV⟩ (Or.inr (hCs hzC).1)
  -- count
  have hmap : MapsTo ψ (closure r₁ ∩ pullV Γ K ψ) {v, v'} := by
    rintro x ⟨hxr, hxV | hxV⟩
    · exact hsubvv ⟨hClr (mem_image_of_mem ψ hxr), hxV⟩
    · exact absurd (K.V_subset_U hxV) (hrK _ (hClr (mem_image_of_mem ψ hxr)))
  have hint : closure r₁ ∩ pullV Γ K ψ ⊆ (bd S₁)ᶜ := by
    intro x hx hxb
    have hv : ψ x ∈ closure r ∩ Γ.V := by
      obtain ⟨hxr, hxV | hxV⟩ := hx
      · exact ⟨hClr (mem_image_of_mem ψ hxr), hxV⟩
      · exact absurd (K.V_subset_U hxV) (hrK _ (hClr (mem_image_of_mem ψ hxr)))
    exact hvvK hv (d.frag.maps_bd (mem_image_of_mem ψ hxb))
  have hle := Set.ncard_le_ncard_of_injOn ψ hmap (d.frag.injOn_interior.mono hint)
    (toFinite _ |>.subset fun _ h ↦ h)
  rwa [Set.ncard_pair hvne] at hle

/-- **The fifth condition in the definition of "fit", for the pull-back** (Graph Minors XIX, (5.3)).
-/
theorem size_three_region [Nonempty S₁] (hS : IsSurface S) (γb : Set S₁ → List S₁)
    (hγ₁ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), (γb p).Nodup)
    (hγ₂ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), {v | v ∈ γb p} = tilde p)
    (hfive : ∀ e ∈ Γ.E, (tilde e).ncard = 3 → ∀ r ∈ Γ.regions,
      3 ≤ (closure r ∩ Γ.V).ncard → ∀ f ∈ componentsIn (e ∩ closure r), (closure f ∩ bd S).Nonempty)
    (hA : IsAnchored Γ K) :
    ∀ e₁ ∈ (pullPainting d γb hγ₁ hγ₂).E, (tilde e₁).ncard = 3 → ∀ r₁ ∈
      (pullPainting d γb hγ₁ hγ₂).regions,
      3 ≤ (closure r₁ ∩ (pullPainting d γb hγ₁ hγ₂).V).ncard → ∀ f₁ ∈ componentsIn
        (e₁ ∩ closure r₁),
        (closure f₁ ∩ bd S₁).Nonempty := by
  intro e₁ he₁ h3 r₁ hr₁ hcard f₁ hf₁
  by_contra hne
  have he₁' : e₁ ∈ arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ) := he₁
  rw [d.arcComponentsIn_eq] at he₁'
  rcases he₁' with hp | ⟨e, he, hb, hne', rfl⟩
  · obtain ⟨u, v, huv, ht, -⟩ := d.exists_ends hp
    rw [ht, Set.ncard_pair huv] at h3
    omega
  · have hsub := d.subset_R he hb hne'
    obtain ⟨y₀, hy₀, rfl⟩ := id hf₁
    have hle := d.ncard_closure_region_le hS hfive hA he (by rwa [d.ncard_tilde he hsub] at h3) hb
      hsub hr₁ hy₀ hne
    change 3 ≤ (closure r₁ ∩ pullV Γ K ψ).ncard at hcard
    omega

end PullData

end GraphMinor.GM19
