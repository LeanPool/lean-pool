/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5d

/-!
# Graph Minors XIX, (5.3): how a fragment looks near its boundary

Let `x` be a boundary point of a fragment such that the boundary near `x` maps into `bd(Σ)`. The
fragment near
`x` then fills all of `Σ` near `ψ(x)`. From this we get what the paper leaves out: distinct points
of the boundary
over `bd(Σ)` have distinct images, and an end of an edge of `K` is not such a point `ψ(x)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace S₁] [T2Space S₁]


namespace IsCuttingFragment

variable {K : Drawing S} {ψ : S₁ → S} (h : IsCuttingFragment S K S₁ ψ)
include h

/-- The image of the part of a neighbourhood of a boundary point `x` off the boundary contains all
of `Σ \ bd(Σ)`
near `ψ(x)`, if the neighbourhood meets `bd(Σ₁)` only over `bd(Σ)` and meets the fibre of `ψ(x)`
only in `x`.
The image of an open set is open. It is also closed in a small connected piece of `Σ \ bd(Σ)` at
`ψ(x)`, since a
limit point comes from the closure of the open set and by assumption not from its frontier or
`bd(Σ₁)`. -/
theorem local_fill (hS : IsSurface S) {x : S₁} (hx : x ∈ bd S₁) (hxb : ψ x ∈ bd S) {W₁ : Set S₁}
    (hW₁ : W₁ ∈ 𝓝 x) (hbd : ∀ z ∈ W₁, z ∈ bd S₁ → ψ z ∈ bd S) (hfib : ∀ z ∈ W₁, ψ z = ψ x → z = x) :
    ∃ N ∈ 𝓝 (ψ x), (bd S)ᶜ ∩ N ⊆ ψ '' (W₁ \ bd S₁) := by
  have hS₁ : IsSurface S₁ := h.isSurface
  have : CompactSpace S₁ := hS₁.1
  have hclosed : IsClosedMap ψ := h.isClosedMap
  have hc : Continuous ψ := h.continuous_ψ
  have hbS₁ : IsClosed (bd S₁) := (cuff_statement S₁ hS₁).1
  obtain ⟨W₂, hW₂, hW₂c, hW₂s⟩ := exists_mem_nhds_isClosed_subset hW₁
  let W' := interior W₂
  have hW'o : IsOpen W' := isOpen_interior
  have hxW' : x ∈ W' := mem_interior_iff_mem_nhds.mpr hW₂
  have hclW' : closure W' ⊆ W₂ := closure_minimal interior_subset hW₂c
  have hfrC : IsClosed (ψ '' frontier W') := hclosed _ isClosed_frontier
  have hxfr : ψ x ∉ ψ '' frontier W' := by
    rintro ⟨z, hz, hzx⟩
    have hzW : z ∈ W₁ := hW₂s (hclW' hz.1)
    rw [hfib z hzW hzx] at hz
    exact hz.2 (by rw [hW'o.interior_eq]; exact hxW')
  obtain ⟨B, hBsub, hBc, N, hN, hNB⟩ := (isConnectedNear_compl_bd (hS.2.2 (ψ x)) hxb).1 _
    (hfrC.isOpen_compl.mem_nhds hxfr)
  have hO : IsOpen (ψ '' (W' ∩ (bd S₁)ᶜ)) :=
    h.isOpen_image (h.isOpen_R hS K.isClosed_U) inter_subset_right (hW'o.inter hbS₁.isOpen_compl)
  have hsub : B ⊆ ψ '' (W' ∩ (bd S₁)ᶜ) ∪ (closure (ψ '' (W' ∩ (bd S₁)ᶜ)))ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure (ψ '' (W' ∩ (bd S₁)ᶜ))
    · refine Or.inl ?_
      rw [hclosed.closure_image_eq_of_continuous hc] at hyc
      obtain ⟨z, hz, rfl⟩ := hyc
      have hzcl : z ∈ closure W' := closure_mono inter_subset_left hz
      have hzW : z ∈ W' := by
        by_contra hzn
        exact (hBsub hy).2 ⟨z, ⟨hzcl, by rwa [hW'o.interior_eq]⟩, rfl⟩
      refine ⟨z, ⟨hzW, fun hzb ↦ ?_⟩, rfl⟩
      exact (hBsub hy).1 (hbd z (hW₂s (interior_subset hzW)) hzb)
    · exact Or.inr hyc
  have hne : (B ∩ ψ '' (W' ∩ (bd S₁)ᶜ)).Nonempty := by
    have hnb := Filter.inter_mem (hW'o.mem_nhds hxW') (hc.continuousAt.preimage_mem_nhds hN)
    obtain ⟨z, hzn, hzb⟩ := mem_closure_iff_nhds.mp (isConnectedNear_compl_bd
      (hS₁.2.2 x) hx).2 _ hnb
    have hzo : ψ z ∉ bd S ∪ K.U := disjoint_left.mp h.maps_interior_disjoint
      (mem_image_of_mem ψ hzb)
    exact ⟨ψ z, hNB ⟨fun hb ↦ hzo (Or.inl hb), hzn.2⟩, mem_image_of_mem ψ ⟨hzn.1, hzb⟩⟩
  have hBO := hBc.subset_left_of_subset_union hO isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun _ hy hy' ↦ hy' (subset_closure hy)) hsub hne
  refine ⟨N, hN, fun y hy ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hBO (hNB hy)
  exact ⟨z, ⟨hW₂s (interior_subset hz.1), hz.2⟩, rfl⟩

omit [T2Space S] in
/-- Shrink a neighbourhood so that it meets the fibre of `ψ(x)` only in `x`. -/
theorem exists_nhds_fibre (x : S₁) {W : Set S₁} (hW : W ∈ 𝓝 x) :
    ∃ W' ∈ 𝓝 x, W' ⊆ W ∧ ∀ z ∈ W', ψ z = ψ x → z = x := by
  have hfin : ((ψ ⁻¹' {ψ x}) \ {x}).Finite := (h.finite_fibres (ψ x)).subset sdiff_subset
  refine ⟨W ∩ ((ψ ⁻¹' {ψ x}) \ {x})ᶜ, Filter.inter_mem hW (hfin.isClosed.isOpen_compl.mem_nhds
    fun hx ↦ hx.2 rfl), inter_subset_left, fun z hz hzx ↦ ?_⟩
  by_contra hne
  exact hz.2 ⟨hzx, hne⟩

/-- Two points of `bd(Σ₁)` that lie over the same point, near which `bd(Σ₁)` maps into `bd(Σ)`, are
equal. Each
fills `Σ` near the point, and `ψ` is one-to-one off the boundary. -/
theorem eq_of_image_eq (hS : IsSurface S) {x₁ x₂ : S₁} (hx₁ : x₁ ∈ bd S₁) (hx₂ : x₂ ∈ bd S₁)
    (hb : ψ x₁ ∈ bd S) {W₁ W₂ : Set S₁} (hW₁ : W₁ ∈ 𝓝 x₁) (hW₂ : W₂ ∈ 𝓝 x₂)
    (hb₁ : ∀ z ∈ W₁, z ∈ bd S₁ → ψ z ∈ bd S) (hb₂ : ∀ z ∈ W₂, z ∈ bd S₁ → ψ z ∈ bd S) (heq : ψ x₁
      = ψ x₂) :
    x₁ = x₂ := by
  by_contra hne
  obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hne
  obtain ⟨A₁, hA₁, hA₁s, hf₁⟩ := h.exists_nhds_fibre x₁ (Filter.inter_mem hW₁ (hu.mem_nhds hxu))
  obtain ⟨A₂, hA₂, hA₂s, hf₂⟩ := h.exists_nhds_fibre x₂ (Filter.inter_mem hW₂ (hv.mem_nhds hxv))
  obtain ⟨N₁, hN₁, hs₁⟩ := h.local_fill hS hx₁ hb hA₁ (fun z hz ↦ hb₁ z (hA₁s hz).1) hf₁
  obtain ⟨N₂, hN₂, hs₂⟩ := h.local_fill hS hx₂ (heq ▸ hb) hA₂ (fun z hz ↦ hb₂ z (hA₂s hz).1) hf₂
  rw [← heq] at hN₂
  obtain ⟨w, hwN, hwb⟩ := mem_closure_iff_nhds.mp (isConnectedNear_compl_bd (hS.2.2 (ψ x₁)) hb).2 _
    (Filter.inter_mem hN₁ hN₂)
  obtain ⟨z₁, hz₁, rfl⟩ := hs₁ ⟨hwb, hwN.1⟩
  obtain ⟨z₂, hz₂, hzz⟩ := hs₂ ⟨hwb, hwN.2⟩
  have hzeq : z₂ = z₁ := h.injOn_interior hz₂.2 hz₁.2 hzz
  exact disjoint_left.mp huv (hA₁s hz₁.1).2 (hzeq ▸ (hA₂s hz₂.1).2)

/-- If `bd(Σ₁)` near `x` maps into `bd(Σ)` then `ψ(x)` is not a limit of a set in `U(K)` off
`bd(Σ)`. -/
theorem notMem_closure_of_fill (hS : IsSurface S) {x : S₁} (hx : x ∈ bd S₁)
  (hxb : ψ x ∈ bd S) {W : Set S₁}
    (hW : W ∈ 𝓝 x) (hb : ∀ z ∈ W, z ∈ bd S₁ → ψ z ∈ bd S) {e : Set S} (he : e ⊆ K.U)
    (hed : Disjoint e (bd S)) : ψ x ∉ closure e := by
  intro hcl
  obtain ⟨A, hA, hAs, hf⟩ := h.exists_nhds_fibre x hW
  obtain ⟨N, hN, hs⟩ := h.local_fill hS hx hxb hA (fun z hz ↦ hb z (hAs hz)) hf
  obtain ⟨y, hyN, hye⟩ := mem_closure_iff_nhds.mp hcl N hN
  obtain ⟨z, hz, rfl⟩ := hs ⟨fun hyb ↦ disjoint_left.mp hed hye hyb, hyN⟩
  exact disjoint_left.mp h.maps_interior_disjoint (mem_image_of_mem ψ hz.2) (Or.inr (he hye))

end IsCuttingFragment

/-- Near a boundary point `x`, the boundary consists of `x` and points of arcs that have `x` in
their closure.
There are finitely many arcs, so the arcs with `x` outside their closure stay away from `x`. -/
theorem exists_nhds_arcs (hS : IsSurface S₁) {N : Set S₁} (hN : N.Finite)
    (h2 : ∀ C : cuffs S₁, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) (x : S₁) :
    ∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ bd S₁ → z = x ∨ ∃ R ∈ arcComponentsIn (bd S₁ \ N), z ∈ R
      ∧ x ∈ closure R := by
  have hfin := finite_arcComponentsIn_bd hS hN h2
  let F : Set S₁ := (N \ {x}) ∪ ⋃₀ (closure '' {R ∈ arcComponentsIn (bd S₁ \ N) | x ∉ closure R})
  have hFc : IsClosed F := by
    refine ((hN.subset sdiff_subset).isClosed).union (Set.Finite.isClosed_sUnion
      ((hfin.subset (sep_subset _ _)).image _) ?_)
    rintro _ ⟨R, -, rfl⟩
    exact isClosed_closure
  have hxF : x ∉ F := by
    rintro (hx | ⟨_, ⟨R, hR, rfl⟩, hx⟩)
    · exact hx.2 rfl
    · exact hR.2 hx
  refine ⟨Fᶜ, hFc.isOpen_compl.mem_nhds hxF, fun z hz hzb ↦ ?_⟩
  by_cases hzx : z = x
  · exact Or.inl hzx
  refine Or.inr ?_
  have hzN : z ∉ N := fun hn ↦ hz (Or.inl ⟨hn, hzx⟩)
  obtain ⟨R, hR, hsub⟩ := exists_arcComp_superset (isPathConnected_singleton z) (F := bd S₁ \ N)
    (singleton_subset_iff.mpr ⟨hzb, hzN⟩)
  have hzR : z ∈ R := hsub rfl
  refine ⟨R, hR, hzR, ?_⟩
  by_contra hxR
  exact hz (Or.inr ⟨_, ⟨R, ⟨hR, hxR⟩, rfl⟩, subset_closure hzR⟩)

/-- The ends of an arc of `bd(Σ₁) \ N` lie in `N`, so a point of its closure off `N` is on the arc.
-/
theorem mem_of_mem_closure_arc (hS : IsSurface S₁) {N : Set S₁} (hN : N.Finite)
    (h2 : ∀ C : cuffs S₁, ∃ p ∈ N ∩ C.1, ∃ q ∈ N ∩ C.1, p ≠ q) {R : Set S₁}
    (hR : R ∈ arcComponentsIn (bd S₁ \ N)) {x : S₁} (hx : x ∈ closure R) (hxN : x ∉ N) : x ∈ R := by
  by_contra hxR
  obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ := exists_arc_of_mem hS (cuffPar hS) hN h2 hR
  have ht : x ∈ tilde (arcOf (cuffPar hS C) a b) := ⟨hx, hxR⟩
  rw [tilde_arcOf _ hab hub] at ht
  rcases ht with rfl | rfl
  · exact hxN ha
  · exact hxN hb

/-- A line has a homeomorphism to `[0, 1]` with one end first. -/
theorem Frame.exists_line {T : Type} [TopologicalSpace T] [T2Space T] (Φ : Frame T) {s : Set T}
    (hs : s ∈ arcComponentsIn (bd T \ Φ.V)) {v : T} (hv : v ∈ tilde s) :
    ∃ w, v ≠ w ∧ tilde s = {v, w} ∧ IsLineWithEnds (closure s) v w := by
  obtain ⟨hn, -, ⟨f⟩, he⟩ := Φ.side_shape s hs
  have hL : IsLineWithEnds (closure s) (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
  have ht : tilde s = {(f 0).1, (f 1).1} := by rw [← he]; exact (GM20.line_facts hL).2.2.2
  have hne := (GM20.line_facts hL).1
  rw [ht] at hv
  rcases hv with rfl | rfl
  · exact ⟨_, hne, ht, hL⟩
  · exact ⟨_, hne.symm, by rw [ht, pair_comm], hL.symm⟩

namespace FrameData

variable {Φ : Frame S} {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S} (D : FrameData Φ Γ K ψ)
include D

omit [T2Space S] in
/-- Points of a side of the fragment map to `bd(Σ)` if the side lies over a side of `Φ`, and near a
point of such
a side the boundary is the side. -/
theorem exists_nhds_of_mem {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ))
    {s : Set S} (hs : s ∈ Φ.sides) (hsub : ψ '' R ⊆ s) {x : S₁} (hx : x ∈ R) :
    ∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ bd S₁ → ψ z ∈ bd S := by
  have hS₁ := D.pull.frag.isSurface
  obtain ⟨W, hW, hWs⟩ := exists_nhds_arcs hS₁ D.finite_pullFrameV D.two x
  have hbd : ∀ {z}, z ∈ R → ψ z ∈ bd S := fun hz ↦ (hs.2.1 (hsub (mem_image_of_mem ψ hz))).1
  refine ⟨W, hW, fun z hz hzb ↦ ?_⟩
  rcases hWs z hz hzb with rfl | ⟨R', hR', hzR', hxc⟩
  · exact hbd hx
  · have hxR' := mem_of_mem_closure_arc hS₁ D.finite_pullFrameV D.two hR' hxc (hR.2.1 hx).2
    rw [arcComp_eq_of_mem hR' hR hxR' hx] at hzR'
    exact hbd hzR'

/-- `ψ` is one-to-one on a side of the fragment over a side of `Φ`. -/
theorem injOn_side {R₁ R₂ : Set S₁} (hR₁ : R₁ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ))
    (hR₂ : R₂ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) {s₁ s₂ : Set S} (hs₁ : s₁ ∈ Φ.sides)
    (hs₂ : s₂ ∈ Φ.sides) (hsub₁ : ψ '' R₁ ⊆ s₁) (hsub₂ : ψ '' R₂ ⊆ s₂) {x₁ x₂ : S₁} (hx₁ : x₁ ∈ R₁)
    (hx₂ : x₂ ∈ R₂) (heq : ψ x₁ = ψ x₂) : x₁ = x₂ := by
  obtain ⟨W₁, hW₁, hb₁⟩ := D.exists_nhds_of_mem hR₁ hs₁ hsub₁ hx₁
  obtain ⟨W₂, hW₂, hb₂⟩ := D.exists_nhds_of_mem hR₂ hs₂ hsub₂ hx₂
  exact D.pull.frag.eq_of_image_eq D.pull.surface (hR₁.2.1 hx₁).1 (hR₂.2.1 hx₂).1
    (hs₁.2.1 (hsub₁ (mem_image_of_mem ψ hx₁))).1 hW₁ hW₂ hb₁ hb₂ heq

omit [T2Space S] in
/-- A short check that every side has both ends in `pullFrameV`. -/
theorem tilde_subset {R : Set S₁} (hR : R ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ)) :
    tilde R ⊆ pullFrameV Φ K ψ := by
  obtain ⟨C, a, b, hab, hub, rfl, -, ha, hb⟩ :=
    exists_arc_of_mem D.pull.frag.isSurface (cuffPar D.pull.frag.isSurface) D.finite_pullFrameV
      D.two hR
  rw [tilde_arcOf _ hab hub]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

/-- **No two long sides of the frame of a fragment have a common end** (Graph Minors XIX, (5.3)).
Suppose two long
sides end at `p`. The boundary near `p` is those sides and `p`, so it maps into `bd(Σ)`. Hence
`ψ(p)` is no end of an
edge of `K`, and so is no vertex of `K`, since `K` has no isolated vertex. So `ψ(p)` is an end of
both sides of
`Φ`. They are one side `s`, since no two long sides of `Φ` have a common end. Both sides of the
fragment map one-to-one
into `s` near the same end, so they meet, and this is impossible. -/
theorem long_disjoint (hF : IsFeature Φ K) :
    ∀ s₁ ∈ arcComponentsIn (bd S₁ \ pullFrameV Φ K ψ), ∀ s₂ ∈ arcComponentsIn
      (bd S₁ \ pullFrameV Φ K ψ),
      s₁ ≠ s₂ → (∃ s ∈ Φ.longSides, ψ '' s₁ ⊆ s) → (∃ s ∈ Φ.longSides, ψ '' s₂ ⊆ s) →
      Disjoint (tilde s₁) (tilde s₂) := by
  intro R₁ hR₁ R₂ hR₂ hne ⟨s₁, hs₁, hsub₁⟩ ⟨s₂, hs₂, hsub₂⟩
  refine disjoint_left.mpr fun p hp₁ hp₂ ↦ ?_
  have hS₁ := D.pull.frag.isSurface
  have hS := D.pull.surface
  have hbd : IsClosed (bd S) := (cuff_statement S hS).1
  have hc := D.pull.frag.continuous_ψ
  have hps : ∀ {R s : Set _}, s ∈ Φ.sides → ψ '' R ⊆ s → p ∈ tilde R → ψ p ∈ closure s
    := fun hs hsub hp ↦
    image_closure_subset_closure_image hc ⟨p, hp.1, rfl⟩ |> closure_mono hsub
  have hpc₁ := hps hs₁.1 hsub₁ hp₁
  have hpc₂ := hps hs₂.1 hsub₂ hp₂
  have hsb : ∀ {s : Set S}, s ∈ Φ.sides → closure s ⊆ bd S := fun hs ↦
    closure_minimal (fun z hz ↦ (hs.2.1 hz).1) hbd
  have hpb := hsb hs₁.1 hpc₁
  have hpb' : p ∈ bd S₁ := by
    have := (D.pullFrameV_subset_bd (D.tilde_subset hR₁ hp₁))
    exact this
  -- the boundary near `p`
  obtain ⟨W, hW, hWs⟩ := exists_nhds_arcs hS₁ D.finite_pullFrameV D.two p
  have hnear : ∀ z ∈ W, z ∈ bd S₁ → ψ z ∈ bd S := by
    intro z hz hzb
    rcases hWs z hz hzb with rfl | ⟨R, hR, hzR, hpc⟩
    · exact hpb
    · have hpN : p ∉ R := fun h ↦ (hR.2.1 h).2 (D.tilde_subset hR₁ hp₁)
      rcases eq_or_eq_of_mem_tilde hS₁ D.finite_pullFrameV D.two hR₁ hR₂ hR hne hp₁ hp₂ ⟨hpc, hpN⟩
        with rfl | rfl
      · exact (hs₁.1.2.1 (hsub₁ (mem_image_of_mem ψ hzR))).1
      · exact (hs₂.1.2.1 (hsub₂ (mem_image_of_mem ψ hzR))).1
  have hpK : ψ p ∉ K.V := by
    intro hv
    obtain ⟨e, he, hve⟩ := hF.no_isolated_vertices _ hv
    exact D.pull.frag.notMem_closure_of_fill hS hpb' hpb hW hnear (fun z hz ↦ (he.2.1 hz).1)
      (hF.no_border_edges e he) hve.1
  have hpV : ψ p ∈ Φ.V := (D.tilde_subset hR₁ hp₁).resolve_right hpK
  have ht : ∀ {s : Set S}, s ∈ Φ.sides → ψ p ∈ closure s → ψ p ∈ tilde s := fun hs hp ↦
    ⟨hp, fun hin ↦ (hs.2.1 hin).2 hpV⟩
  have hss : s₁ = s₂ := by
    by_contra hssne
    exact disjoint_left.mp (Φ.long_disjoint s₁ hs₁.1 s₂ hs₂.1 hssne hs₁.2 hs₂.2) (ht hs₁.1 hpc₁)
      (ht hs₂.1 hpc₂)
  subst hss
  obtain ⟨w, -, -, hL⟩ := Φ.exists_line hs₁.1 (ht hs₁.1 hpc₁)
  have hneV : ∀ {R : Set S₁}, ψ '' R ⊆ s₁ → ψ '' R ⊆ closure s₁ \ {ψ p} := fun hsub _ hy ↦
    ⟨subset_closure (hsub hy), fun h ↦ (hs₁.1.2.1 (hsub hy)).2 (h ▸ hpV)⟩
  obtain ⟨_, ⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hxe⟩⟩ := nonempty_inter_of_end hL (hneV hsub₁) (hneV hsub₂)
    (hR₁.2.2.1.isConnected.isPreconnected.image _ hc.continuousOn)
    (hR₂.2.2.1.isConnected.isPreconnected.image _ hc.continuousOn)
    (image_closure_subset_closure_image hc ⟨p, hp₁.1, rfl⟩)
    (image_closure_subset_closure_image hc ⟨p, hp₂.1, rfl⟩)
    (hR₁.1.image ψ) (hR₂.1.image ψ)
  have hxx : x₂ = x₁ := D.injOn_side hR₂ hR₁ hs₁.1 hs₁.1 hsub₂ hsub₁ hx₂ hx₁ hxe
  exact hne (arcComp_eq_of_mem hR₁ hR₂ hx₁ (hxx ▸ hx₂))

end FrameData

end GraphMinor.GM19
