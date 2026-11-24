/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidAccess
public import LeanPool.GraphMinor.GM14.RigidExtension
public import LeanPool.GraphMinor.GM14.RigidPoints
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.Surface.Schoenflies
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Redrawing a rigid drawing along a 3-segregation

This file proves the first step of the proof of Graph Minors XIV, (6.5). Let `H` be a rigid drawing
in a closed
disc `Δ`, and let `α` be an arrangement in `Δ` of a 3-segregation. We redraw `H` so that the part of
`H` in
each society lies in the disc of this society, with the vertices in `ΩBar` at their places
(`union_drawing_65`).

We work one society at a time. In a sphere, the part of `H` in a society lies in a closed disc with
the vertices
in `ΩBar` on its boundary (`exists_disc_of_part`). We map this disc onto the disc of the society,
with
these vertices going to their places (`exists_part_map`). These maps agree on common points, since
the
societies share only vertices in `ΩBar`. Gluing them gives a map on all of `U(H)`.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Metric Graph GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- **One part of `H`.** Let `P₀` be a subdrawing of a rigid drawing `H` in `Δ`, and let `X₀` be at
most three
vertices of `P₀`. Suppose that all other vertices of `P₀` are off `bd(Δ)` and have all their edges
in `P₀`.
Then `P₀` can be mapped into any closed disc `A ⊆ Δ`, with `X₀` going to given points of `bd(A)`,
and with
only `X₀` going to `bd(A)`. -/
theorem exists_part_map {H P₀ : Drawing S} {Δ A : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ
  = discBd Δ)
    (hHΔ : H.U ⊆ Δ) (hHbd : H.U ∩ subBd Δ ⊆ H.V) (hrigid : IsRigidIn H Δ) (hP₀ : P₀.IsSubdrawing H)
    {X₀ : Set S} (hXV : X₀ ⊆ P₀.V) (hc : X₀.ncard ≤ 3)
    (hout : ∀ v ∈ P₀.V, v ∉ X₀ → v ∉ subBd Δ ∧ ∀ e ∈ H.E, v ∈ closure e → e ∈ P₀.E)
    (hA : IsClosedDisc A) (hAΔ : A ⊆ Δ) {g : S → S} (hg : InjOn g X₀) (hgA : MapsTo g X₀
      (subBd A)) :
    ∃ ψ ψ', PH P₀.U (ψ '' P₀.U) ψ ψ' ∧ MapsTo ψ P₀.U A ∧ (∀ z ∈ P₀.U, ψ z ∈ subBd A → z ∈ X₀) ∧
      ∀ x ∈ X₀, ψ x = g x := by
  classical
  let T := OnePoint EuclideanPlane
  have hsph : IsSphere T := ⟨Homeomorph.refl _⟩
  obtain ⟨hS, hconn⟩ := IsSphere.isClosedSurface hsph
  have hO : IsOArc (sph '' sphere (0 : ℂ) 1) :=
    isOArc_image isOpenEmbedding_sph.isEmbedding oArc_sphere
  obtain ⟨D₁, D₂, -, hd₁, hd₂, hb₁, hb₂, hcov, hcap, -, -⟩ := sphere_disc T hsph _ hO
  generalize sph '' sphere (0 : ℂ) 1 = C at hO hb₁ hb₂ hcap
  obtain ⟨f, f', hP, hf₁, hf₂⟩ := exists_disc_map hΔ hd₁
  have hAc : IsCompact Δ := hΔ.isCompact
  have hBc : IsCompact D₁ := hd₁.isCompact
  have hsbD : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hbd : f '' subBd Δ ⊆ subBd D₁ := by
    rw [hbdΔ, IsClosedDisc.subBd_eq_discBd hS hd₁]
    exact hf₁
  have hbd' : f' '' subBd D₁ ⊆ subBd Δ := by
    rw [hbdΔ, IsClosedDisc.subBd_eq_discBd hS hd₁]
    exact hf₂
  have hU₀ : P₀.U ⊆ Δ := hP₀.U_subset.trans hHΔ
  have hVΔ : H.V ⊆ Δ := H.V_subset_U.trans hHΔ
  let M := mapD hP hAc H hHΔ
  let Γ := mapD hP hAc P₀ hU₀
  have hMU : M.U ⊆ D₁ := hP.image_sub hHΔ
  have hMn : M.U ∩ C ⊆ M.V := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have h₁ : f' (f x) ∈ subBd Δ := hbd' (mem_image_of_mem f' (hsbD.symm ▸ hxC))
    rw [hP.left (hHΔ hx)] at h₁
    exact mem_image_of_mem f (hHbd ⟨hx, h₁⟩)
  have hMr : IsRigidIn M D₁ := isRigidIn_mapD hP hAc hBc hbd hbd' H hHΔ hrigid
  have hΓ : Γ.IsSubdrawing M := by
    refine ⟨image_mono hP₀.1, ?_⟩
    change (mapD hP hAc P₀ hU₀).E ⊆ (mapD hP hAc H hHΔ).E
    rw [mapD_E, mapD_E]
    exact image_mono hP₀.2
  have hX'f : (f '' X₀).Finite := (P₀.finite_V.subset hXV).image f
  have hX'c : (f '' X₀).ncard ≤ 3 := (ncard_image_le (P₀.finite_V.subset hXV)).trans hc
  have hout' : ∀ v ∈ Γ.V, v ∉ f '' X₀ → v ∉ C ∧ ∀ e ∈ M.E, v ∈ closure e → e ∈ Γ.E := by
    rintro _ ⟨v, hv, rfl⟩ hvn
    obtain ⟨h₁, h₂⟩ := hout v hv fun h => hvn (mem_image_of_mem f h)
    have hvH : v ∈ H.V := hP₀.1 hv
    refine ⟨fun hC => h₁ ?_, fun e' he' hin => ?_⟩
    · have h₃ := hbd' (mem_image_of_mem f' (hsbD.symm ▸ hC))
      rwa [hP.left (hVΔ hvH)] at h₃
    · change e' ∈ (mapD hP hAc H hHΔ).E at he'
      rw [mapD_E] at he'
      obtain ⟨e, he, rfl⟩ := he'
      have heΔ : e ⊆ Δ := subset_closure.trans ((H.closure_subset_U he).trans hHΔ)
      have hm : f v ∈ closure (f '' e) ∩ f '' H.V := ⟨hin, mem_image_of_mem f hvH⟩
      rw [cap_image_eq hP hAc heΔ hVΔ] at hm
      obtain ⟨w, ⟨hw, hwV⟩, hfw⟩ := hm
      have hwv : w = v := hP.injOn (hVΔ hwV) (hVΔ hvH) hfw
      change f '' e ∈ (mapD hP hAc P₀ hU₀).E
      rw [mapD_E]
      exact ⟨e, h₂ e he (hwv ▸ hw), rfl⟩
  obtain ⟨E, hE, hKE, hbE⟩ := exists_disc_of_part hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap hMU hMn hMr hΓ
    (image_mono hXV) hX'c hout'
  have hAd : IsClosedDisc (f '' A) := hP.disc_image hAΔ hA
  have hAsb : subBd (f '' A) = discBd (f '' A) := IsClosedDisc.subBd_eq_discBd hS hAd
  have hsub_img : f '' subBd A ⊆ subBd (f '' A) := subBd_image hP hbd hAΔ hA.isClosed
  have hgΔ : ∀ {x : S}, x ∈ X₀ → g x ∈ Δ := fun hx => hAΔ (subBd_subset_of subset_rfl hA.isClosed
    (hgA hx))
  have hX₀Δ : X₀ ⊆ Δ := hXV.trans (P₀.V_subset_U.trans hU₀)
  let g' : T → T := fun y => f (g (f' y))
  have hg'e : ∀ {x : S}, x ∈ X₀ → g' (f x) = f (g x) := fun {x} hx => by
    change f (g (f' (f x))) = _
    rw [hP.left (hX₀Δ hx)]
  have hg'i : InjOn g' (f '' X₀) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    rw [hg'e hx, hg'e hy] at h
    rw [hg (hx) hy (hP.injOn (hgΔ hx) (hgΔ hy) h)]
  have hg'm : MapsTo g' (f '' X₀) (discBd (f '' A)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hg'e hx, ← hAsb]
    exact hsub_img (mem_image_of_mem f (hgA hx))
  obtain ⟨p, p', hp, hpg, -, hpb'⟩ := exists_disc_points hE hAd hX'f
    (fun y hy => (hbE.symm ▸ hy : y ∈ discBd E ∩ Γ.U).1) hX'c hg'i hg'm
  have hsub₃ : p '' (f '' P₀.U) ⊆ D₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hP.image_sub hAΔ (hp.1 (hKE hy))
  have hch := ((hP.restrict' hU₀).comp (hp.restrict' hKE)).comp (hP.symm.restrict' hsub₃)
  have hch' := hch
  rw [← hch.image_eq] at hch'
  refine ⟨_, _, hch', ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, h₁⟩ := hp.1 (hKE (mem_image_of_mem f hz))
    change f' (p (f z)) ∈ A
    rw [← h₁, hP.left (hAΔ ha)]
    exact ha
  · intro z hz hzb
    change f' (p (f z)) ∈ subBd A at hzb
    have hin : p (f z) ∈ D₁ := hsub₃ (mem_image_of_mem p (mem_image_of_mem f hz))
    have h₁ := hsub_img (mem_image_of_mem f hzb)
    rw [hP.right hin, hAsb] at h₁
    have h₂ := hpb' h₁
    rw [hp.left (hKE (mem_image_of_mem f hz))] at h₂
    have h₃ : f z ∈ discBd E ∩ Γ.U := ⟨h₂, mem_image_of_mem f hz⟩
    rw [hbE] at h₃
    obtain ⟨x, hx, hxz⟩ := h₃
    exact hP.injOn (hX₀Δ hx) (hU₀ hz) hxz ▸ hx
  · intro x hx
    change f' (p (f x)) = g x
    rw [hpg _ (mem_image_of_mem f hx), hg'e hx, hP.left (hgΔ hx)]

/-- The vertices of `H` that go into `ΩBar` of a society. -/
abbrev barPart {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    (S₀ : Society α β) : Set S := {v | v ∈ H.V ∧ η.vMap v ∈ S₀.Ω.bar}

omit [T2Space S] in
theorem seg_edge {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    {S_seg : Set (Society α β)} (hseg : IsThreeSegregation G S_seg) {e : Set S} (he : e ∈ H.E) :
    ∃ S₀ ∈ S_seg, η.eMap e ∈ E(S₀.G) := by
  have hPle : ∀ P ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, P ≤ G := by
    rintro _ ⟨S₀, hS₀, rfl⟩
    exact hseg.1.le S₀ hS₀
  have h₁ : η.eMap e ∈ E(G) := η.imageGraph_le.edgeSet_mono (η.bijOn_e.mapsTo he)
  have hEu := congrArg Graph.edgeSet hseg.1.union_eq
  rw [edgeSet_subgraphSUnion hPle] at hEu
  rw [← hEu] at h₁
  obtain ⟨_, ⟨S₀, hS₀, rfl⟩, h₂⟩ := mem_iUnion₂.mp h₁
  exact ⟨S₀, hS₀, h₂⟩

omit [T2Space S] in
theorem seg_vertex {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S} (η : SpanEmbedding H G)
    {S_seg : Set (Society α β)} (hseg : IsThreeSegregation G S_seg) {v : S} (hv : v ∈ H.V) :
    ∃ S₀ ∈ S_seg, η.vMap v ∈ V(S₀.G) := by
  have h₁ : η.vMap v ∈ V(G) := η.imageGraph_le.vertexSet_mono (η.bijOn_v.mapsTo hv)
  have hVu : (⋃ P ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, V(P)) = V(G) :=
    congrArg Graph.vertexSet hseg.1.union_eq
  rw [← hVu] at h₁
  obtain ⟨_, ⟨S₀, hS₀, rfl⟩, h₂⟩ := mem_iUnion₂.mp h₁
  exact ⟨S₀, hS₀, h₂⟩

/-- For each society, the part of `H` in it, with a map into the disc of the society. -/
theorem exists_society_maps {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ) (hHΔ : H.U ⊆ Δ) (hHbd : H.U ∩ subBd Δ ⊆ H.V)
    (hrigid : IsRigidIn H Δ) (η : SpanEmbedding H G) {S_seg : Set (Society α β)}
    (hseg : IsThreeSegregation G S_seg)
    (hbd_in_seg : ∀ v ∈ H.V ∩ subBd Δ, η.vMap v ∈ segregationVertices S_seg)
    {α_disc : Society α β → Set S} {α_pt : α → S} (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (harr_Δ : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Δ) :
    ∃ (Pd : Society α β → Drawing S) (ψ ψ' : S_seg → S → S),
      (∀ S₀, (Pd S₀).IsSubdrawing H) ∧
      (∀ S₀, (Pd S₀).E = {e | e ∈ H.E ∧ η.eMap e ∈ E(S₀.G)}) ∧
      (∀ S₀ ∈ S_seg, (Pd S₀).V = {v | v ∈ H.V ∧ η.vMap v ∈ V(S₀.G)}) ∧
      ∀ i : S_seg, PH (Pd i.1).U (ψ i '' (Pd i.1).U) (ψ i) (ψ' i) ∧
        MapsTo (ψ i) (Pd i.1).U (α_disc i.1) ∧
        (∀ z ∈ (Pd i.1).U, ψ i z ∈ subBd (α_disc i.1) → z ∈ barPart η i.1) ∧
        ∀ x ∈ barPart η i.1, ψ i x = α_pt (η.vMap x) := by
  classical
  have hηv : InjOn η.vMap H.V := η.bijOn_v.injOn
  have hle : ∀ S₀ ∈ S_seg, S₀.G ≤ G := hseg.1.le
  have hIncG : ∀ e ∈ H.E, ∀ v ∈ H.V, v ∈ closure e → G.Inc (η.eMap e) (η.vMap v) := by
    intro e he v hv hve
    obtain ⟨y, hy⟩ := (η.inc_iff e he v hv).mpr hve
    exact ⟨y, hy.mono η.imageGraph_le⟩
  have hsoc_v : ∀ S₀ ∈ S_seg, ∀ e ∈ H.E, η.eMap e ∈ E(S₀.G) → ∀ v ∈ H.V, v ∈ closure e →
      η.vMap v ∈ V(S₀.G) := by
    intro S₀ hS₀ e he hη v hv hve
    obtain ⟨y, hy⟩ := hIncG e he v hv hve
    exact (((hle S₀ hS₀).isLink_iff hη).mpr hy).left_mem
  have hsegv : ∀ {S₀ x}, S₀ ∈ S_seg → x ∈ S₀.Ω.bar → x ∈ segregationVertices S_seg :=
    fun hS₀ hx => mem_iUnion₂.mpr ⟨_, hS₀, hx⟩
  have hbar : ∀ S₀ : Society α β, S₀.Ω.bar.Finite := fun S₀ => S₀.finite_V.subset S₀.bar_subset
  let Vs : Society α β → Set S := fun S₀ => {v | v ∈ H.V ∧ η.vMap v ∈ V(S₀.G)}
  let Es : Society α β → Set (Set S) := fun S₀ => {e | e ∈ H.E ∧ η.eMap e ∈ E(S₀.G)}
  let Pd : Society α β → Drawing S := fun S₀ => H.span (Vs S₀) (Es S₀)
  have hPs : ∀ S₀, (Pd S₀).IsSubdrawing H := fun S₀ => H.span_isSubdrawing _ _
  have hPE : ∀ S₀, (Pd S₀).E = Es S₀ := fun S₀ => by
    change (H.span (Vs S₀) (Es S₀)).E = _
    rw [H.span_E]
    exact inter_eq_left.mpr fun e he => he.1
  have hPV : ∀ S₀ ∈ S_seg, (Pd S₀).V = Vs S₀ := by
    intro S₀ hS₀
    apply subset_antisymm
    · rintro v (⟨hv, -⟩ | hv)
      · exact hv
      · obtain ⟨e, ⟨he, -⟩, hve, hvV⟩ := mem_iUnion₂.mp hv
        exact ⟨hvV, hsoc_v S₀ hS₀ e he.1 he.2 v hvV hve⟩
    · intro v hv
      exact Or.inl ⟨hv, hv.1⟩
  have hPXs : ∀ S₀ ∈ S_seg, barPart η S₀ ⊆ (Pd S₀).V := fun S₀ hS₀ => by
    rw [hPV S₀ hS₀]
    exact fun v hv => ⟨hv.1, S₀.bar_subset hv.2⟩
  have hXc : ∀ S₀ ∈ S_seg, (barPart η S₀).ncard ≤ 3 := by
    intro S₀ hS₀
    have hinj : InjOn η.vMap (barPart η S₀) := hηv.mono fun v hv => hv.1
    rw [← hinj.ncard_image]
    refine (ncard_le_ncard ?_ (hbar S₀)).trans (hseg.2 S₀ hS₀)
    rintro _ ⟨v, hv, rfl⟩
    exact hv.2
  have hout : ∀ S₀ ∈ S_seg, ∀ v ∈ (Pd S₀).V, v ∉ barPart η S₀ →
      v ∉ subBd Δ ∧ ∀ e ∈ H.E, v ∈ closure e → e ∈ (Pd S₀).E := by
    intro S₀ hS₀ v hv hvX
    rw [hPV S₀ hS₀] at hv
    have hoth : ∀ S₁ ∈ S_seg, η.vMap v ∈ V(S₁.G) → S₁ = S₀ := by
      intro S₁ hS₁ h₁
      by_contra hne
      exact hvX ⟨hv.1, (hseg.1.vertex_inter_subset S₀ hS₀ S₁ hS₁ (Ne.symm hne) ⟨hv.2, h₁⟩).1⟩
    refine ⟨fun hb => ?_, fun e he hve => ?_⟩
    · obtain ⟨S₁, hS₁, h₁⟩ := mem_iUnion₂.mp (hbd_in_seg v ⟨hv.1, hb⟩)
      have h₂ := hoth S₁ hS₁ (S₁.bar_subset h₁)
      subst h₂
      exact hvX ⟨hv.1, h₁⟩
    · obtain ⟨S₁, hS₁, h₁⟩ := seg_edge η hseg he
      have h₂ := hoth S₁ hS₁ (hsoc_v S₁ hS₁ e he h₁ v hv.1 hve)
      subst h₂
      rw [hPE]
      exact ⟨he, h₁⟩
  have hdisc : ∀ S₀ ∈ S_seg, IsClosedDisc (α_disc S₀) := fun S₀ hS₀ => (harr.isClosedDisc S₀ hS₀).1
  have hparts : ∀ i : S_seg, ∃ ψ ψ', PH (Pd i.1).U (ψ '' (Pd i.1).U) ψ ψ' ∧
      MapsTo ψ (Pd i.1).U (α_disc i.1) ∧ (∀ z ∈ (Pd i.1).U, ψ z ∈ subBd (α_disc i.1)
        → z ∈ barPart η i.1) ∧
      ∀ x ∈ barPart η i.1, ψ x = α_pt (η.vMap x) := by
    rintro ⟨S₀, hS₀⟩
    refine exists_part_map (g := fun x => α_pt (η.vMap x)) hΔ hbdΔ hHΔ hHbd hrigid (hPs S₀)
      (hPXs S₀ hS₀) (hXc S₀ hS₀) (hout S₀ hS₀) (hdisc S₀ hS₀) (harr_Δ S₀ hS₀) ?_ ?_
    · intro x hx y hy h
      exact hηv hx.1 hy.1 (harr.injOn_pts (hsegv hS₀ hx.2) (hsegv hS₀ hy.2) h)
    · intro x hx
      exact (harr.isClosedDisc S₀ hS₀).2 _ hx.2
  choose ψ ψ' h using hparts
  exact ⟨Pd, ψ, ψ', hPs, hPE, hPV, h⟩

/-- **The first step of the proof of (6.5).** See the module docstring. -/
theorem union_drawing_65 {α : Type v} {β : Type w} {G : Graph α β} {H : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ) (hHΔ : H.U ⊆ Δ) (hHbd : H.U ∩ subBd Δ ⊆ H.V)
    (hrigid : ∀ F, F ⊆ Δ → IsOArc F → F ∩ H.U ⊆ H.V → (F ∩ H.V).ncard ≤ 2 →
      ∃ Δ', Δ' ⊆ Δ ∧ IsDial H F Δ')
    (η : SpanEmbedding H G) {S_seg : Set (Society α β)} (hseg : IsThreeSegregation G S_seg)
    (hbd_in_seg : ∀ v ∈ H.V ∩ subBd Δ, η.vMap v ∈ segregationVertices S_seg)
    {α_disc : Society α β → Set S} {α_pt : α → S} (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    (harr_Δ : ∀ S₀ ∈ S_seg, α_disc S₀ ⊆ Δ) (hα_id : ∀ v ∈ H.V ∩ subBd Δ, α_pt (η.vMap v) = v)
    (hα_bd : ∀ v ∈ H.V, η.vMap v ∈ segregationVertices S_seg → α_pt (η.vMap v) ∈ subBd Δ
      → v ∈ subBd Δ) :
    ∃ (H' : Drawing S) (φ : Iso H.toGraph H'.toGraph),
      H'.U ⊆ Δ ∧ H'.U ∩ subBd Δ ⊆ H'.V ∧ H.V ∩ subBd Δ = H'.V ∩ subBd Δ ∧
      (∀ v : V(H.toGraph), η.vMap v.1 ∈ segregationVertices S_seg →
        α_pt (η.vMap v.1) = (φ.vertexEquiv v).1) ∧
      (∀ S₀ ∈ S_seg,
        H'.U ∩ subBd (α_disc S₀) = {w | ∃ v : V(H.toGraph), (φ.vertexEquiv v).1 = w
          ∧ η.vMap v.1 ∈ S₀.Ω.bar} ∧
        (∀ v, (φ.vertexEquiv v).1 ∈ α_disc S₀ ↔ η.vMap v.1 ∈ V(S₀.G)) ∧
        (∀ e, (φ.edgeEquiv e).1 ⊆ α_disc S₀ ↔ η.eMap e.1 ∈ E(S₀.G))) := by
  classical
  obtain ⟨Pd, ψ, ψ', hPs, hPE, hPV, hparts⟩ := exists_society_maps hΔ hbdΔ hHΔ hHbd hrigid η hseg
    hbd_in_seg harr harr_Δ
  have h₁ := fun i => (hparts i).1
  have h₂ := fun i => (hparts i).2.1
  have h₃ := fun i => (hparts i).2.2.1
  have h₄ := fun i => (hparts i).2.2.2
  clear hparts
  have hηv : InjOn η.vMap H.V := η.bijOn_v.injOn
  have hsegv : ∀ {S₀ x}, S₀ ∈ S_seg → x ∈ S₀.Ω.bar → x ∈ segregationVertices S_seg :=
    fun hS₀ hx => mem_iUnion₂.mpr ⟨_, hS₀, hx⟩
  have hdisc : ∀ S₀ ∈ S_seg, IsClosedDisc (α_disc S₀) := fun S₀ hS₀ => (harr.isClosedDisc S₀ hS₀).1
  have hPXs : ∀ S₀ ∈ S_seg, barPart η S₀ ⊆ (Pd S₀).V := fun S₀ hS₀ => by
    rw [hPV S₀ hS₀]
    exact fun v hv => ⟨hv.1, S₀.bar_subset hv.2⟩
  have hPU_V : ∀ S₀ ∈ S_seg, ∀ z ∈ (Pd S₀).U, z ∈ H.V → z ∈ {v | v ∈ H.V ∧ η.vMap v ∈ V(S₀.G)} := by
    intro S₀ hS₀ z hz hzV
    rw [← hPV S₀ hS₀]
    by_contra hn
    obtain ⟨e, he, hze⟩ := (Pd S₀).exists_edge_of_mem hz hn
    exact edge_notMem_V ((hPs S₀).2 he) hze hzV
  -- A point of one part that goes into the disc of another society is a shared vertex.
  have hcross : ∀ i j : S_seg, i ≠ j → ∀ z ∈ (Pd i.1).U, ψ i z ∈ α_disc j.1 →
      z ∈ barPart η i.1 ∧ η.vMap z ∈ j.1.Ω.bar := by
    intro i j hij z hz hzj
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    obtain ⟨q, ⟨hqi, hqj⟩, hq⟩ := harr.inter_discs i.1 i.2 j.1 j.2 hne ⟨h₂ i hz, hzj⟩
    have hb : ψ i z ∈ subBd (α_disc i.1) := by
      rw [← hq]
      exact (harr.isClosedDisc i.1 i.2).2 q hqi
    have hzX := h₃ i z hz hb
    refine ⟨hzX, ?_⟩
    have he : α_pt (η.vMap z) = α_pt q := by rw [← h₄ i z hzX, hq]
    rw [harr.injOn_pts (hsegv i.2 hzX.2) (hsegv i.2 hqi) he]
    exact hqj
  have hclosedB : ∀ i : S_seg, IsClosed (ψ i '' (Pd i.1).U) := by
    intro i
    have hc : IsCompact (Pd i.1).U :=
      hΔ.isCompact.of_isClosed_subset (Pd i.1).isClosed_U ((hPs i.1).U_subset.trans hHΔ)
    exact (h₁ i).image_isClosed hc subset_rfl (Pd i.1).isClosed_U
  have hfin : Finite S_seg := hseg.1.1.to_subtype
  have hnS : Nonempty S := hΔ.isPathConnected.nonempty.to_type
  obtain ⟨Φ, Φ', hΦ, hEq, -⟩ := exists_glue (A := fun i : S_seg => (Pd i.1).U)
    (B := fun i : S_seg => ψ i '' (Pd i.1).U) (f := ψ) (f' := ψ') (fun i => (Pd i.1).isClosed_U)
    hclosedB h₁
    (by
      intro i j x hxi hxj
      by_cases hij : i = j
      · rw [hij]
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hxV : x ∈ H.V := by
        by_contra hn
        obtain ⟨e, he, hxe⟩ := (Pd i.1).exists_edge_of_mem hxi fun h => hn ((hPs i.1).1 h)
        obtain ⟨f, hf, hxf⟩ := (Pd j.1).exists_edge_of_mem hxj fun h => hn ((hPs j.1).1 h)
        have heq := H.edge_eq_of_mem ((hPs i.1).2 he) ((hPs j.1).2 hf) hxe hxf
        rw [hPE] at he hf
        subst heq
        exact disjoint_left.mp (hseg.1.edge_disjoint i.1 i.2 j.1 j.2 hne) he.2 hf.2
      have hi := hPU_V i.1 i.2 x hxi hxV
      have hj := hPU_V j.1 j.2 x hxj hxV
      obtain ⟨h₅, h₆⟩ := hseg.1.vertex_inter_subset i.1 i.2 j.1 j.2 hne ⟨hi.2, hj.2⟩
      rw [h₄ i x ⟨hxV, h₅⟩, h₄ j x ⟨hxV, h₆⟩])
    (by
      rintro i j y ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
      by_cases hij : i = j
      · subst hij
        rfl
      have hiz : ψ i z ∈ α_disc j.1 := hzz ▸ h₂ j hz'
      have hjz : ψ j z' ∈ α_disc i.1 := hzz.symm ▸ h₂ i hz
      obtain ⟨hX, hb⟩ := hcross i j hij z hz hiz
      obtain ⟨hX', hb'⟩ := hcross j i (Ne.symm hij) z' hz' hjz
      have h₅ : α_pt (η.vMap z) = α_pt (η.vMap z') := by
        rw [← h₄ i z hX, ← h₄ j z' hX', hzz]
      have h₆ := harr.injOn_pts (hsegv i.2 hX.2) (hsegv j.2 hX'.2) h₅
      have h₇ := hηv hX.1 hX'.1 h₆
      rw [(h₁ i).left hz, ← hzz, (h₁ j).left hz']
      exact h₇)
  have hcover : (⋃ i : S_seg, (Pd i.1).U) = H.U := by
    apply subset_antisymm (iUnion_subset fun i : S_seg => (hPs i.1).U_subset)
    intro z hz
    by_cases hzV : z ∈ H.V
    · obtain ⟨S₀, hS₀, h⟩ := seg_vertex η hseg hzV
      refine mem_iUnion.mpr ⟨⟨S₀, hS₀⟩, (Pd S₀).V_subset_U ?_⟩
      rw [hPV S₀ hS₀]
      exact ⟨hzV, h⟩
    · obtain ⟨e, he, hze⟩ := H.exists_edge_of_mem hz hzV
      obtain ⟨S₀, hS₀, h⟩ := seg_edge η hseg he
      have heP : e ∈ (Pd S₀).E := by
        rw [hPE]
        exact ⟨he, h⟩
      exact mem_iUnion.mpr ⟨⟨S₀, hS₀⟩, (Pd S₀).closure_subset_U heP (subset_closure hze)⟩
  rw [hcover] at hΦ
  have hHc : IsCompact H.U := hΔ.isCompact.of_isClosed_subset H.isClosed_U hHΔ
  let H' := mapD hΦ hHc H subset_rfl
  let φ := mapIso hΦ hHc H subset_rfl
  have hφv : ∀ v : V(H.toGraph), (φ.vertexEquiv v).1 = Φ v.1 := fun v => mapIso_vertex hΦ hHc H _ v
  have hφe : ∀ e : E(H.toGraph), (φ.edgeEquiv e).1 = Φ '' e.1 := fun e => mapIso_edge hΦ hHc H _ e
  have hΦi : ∀ (i : S_seg) {z}, z ∈ (Pd i.1).U → Φ z = ψ i z := fun i {z} hz => hEq i hz
  have hsome : ∀ z ∈ H.U, ∃ i : S_seg, z ∈ (Pd i.1).U := fun z hz =>
    mem_iUnion.mp (hcover.symm ▸ hz)
  have hΦX : ∀ S₀ ∈ S_seg, ∀ v ∈ barPart η S₀, Φ v = α_pt (η.vMap v) := by
    intro S₀ hS₀ v hv
    have h₅ : v ∈ (Pd S₀).U := (Pd S₀).V_subset_U (hPXs S₀ hS₀ hv)
    rw [hΦi ⟨S₀, hS₀⟩ h₅]
    exact h₄ ⟨S₀, hS₀⟩ v hv
  have hbdα : ∀ {i : S_seg} {w}, w ∈ α_disc i.1 → w ∈ subBd Δ → w ∈ subBd (α_disc i.1) :=
    fun {i w} h₅ h₆ => ⟨subset_closure h₅, closure_mono (show univ \ Δ ⊆ univ \ α_disc i.1 from
      fun y hy => ⟨hy.1, fun h => hy.2 (harr_Δ i.1 i.2 h)⟩) h₆.2⟩
  have hbdV : ∀ z ∈ H.U, Φ z ∈ subBd Δ → ∃ S₀ ∈ S_seg, z ∈ barPart η S₀ := by
    intro z hz hb
    obtain ⟨i, hi⟩ := hsome z hz
    have h₅ : ψ i z ∈ α_disc i.1 := h₂ i hi
    rw [hΦi i hi] at hb
    exact ⟨i.1, i.2, h₃ i z hi (hbdα h₅ hb)⟩
  refine ⟨H', φ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := hsome z hz
    rw [hΦi i hi]
    exact harr_Δ i.1 i.2 (h₂ i hi)
  · rintro _ ⟨⟨z, hz, rfl⟩, hb⟩
    obtain ⟨S₀, -, hzX⟩ := hbdV z hz hb
    exact mem_image_of_mem Φ hzX.1
  · apply subset_antisymm
    · rintro v ⟨hv, hb⟩
      obtain ⟨S₁, hS₁, h₅⟩ := mem_iUnion₂.mp (hbd_in_seg v ⟨hv, hb⟩)
      have h₆ := hΦX S₁ hS₁ v ⟨hv, h₅⟩
      rw [hα_id v ⟨hv, hb⟩] at h₆
      exact ⟨⟨v, hv, h₆⟩, hb⟩
    · rintro _ ⟨⟨v, hv, rfl⟩, hb⟩
      have hvU : v ∈ H.U := H.V_subset_U hv
      obtain ⟨S₀, hS₀, hvX⟩ := hbdV v hvU hb
      have h₅ := hΦX S₀ hS₀ v hvX
      have hseg₀ := hsegv hS₀ hvX.2
      have hvb := hα_bd v hv hseg₀ (h₅ ▸ hb)
      rw [h₅, hα_id v ⟨hv, hvb⟩]
      exact ⟨hv, hvb⟩
  · intro v hv
    obtain ⟨S₁, hS₁, h₅⟩ := mem_iUnion₂.mp hv
    rw [hφv, hΦX S₁ hS₁ v.1 ⟨v.2, h₅⟩]
  · intro S₀ hS₀
    let i₀ : S_seg := ⟨S₀, hS₀⟩
    have hdiskSub : subBd (α_disc S₀) ⊆ α_disc S₀ := subBd_subset_of subset_rfl
      (hdisc S₀ hS₀).isClosed
    refine ⟨?_, fun v => ?_, fun e => ?_⟩
    · apply subset_antisymm
      · rintro _ ⟨⟨z, hz, rfl⟩, hb⟩
        obtain ⟨i, hi⟩ := hsome z hz
        have hzb : ψ i z ∈ subBd (α_disc S₀) := hΦi i hi ▸ hb
        have hzX : z ∈ H.V ∧ η.vMap z ∈ S₀.Ω.bar := by
          by_cases hii : i = i₀
          · have hs : i.1 = S₀ := congrArg Subtype.val hii
            exact hs ▸ h₃ i z hi (hs.symm ▸ hzb)
          · obtain ⟨h₅, h₆⟩ := hcross i i₀ hii z hi (hdiskSub hzb)
            exact ⟨h₅.1, h₆⟩
        exact ⟨⟨z, hzX.1⟩, hφv _, hzX.2⟩
      · rintro _ ⟨v, rfl, hv⟩
        rw [hφv, hΦX S₀ hS₀ v.1 ⟨v.2, hv⟩]
        refine ⟨?_, (harr.isClosedDisc S₀ hS₀).2 _ hv⟩
        rw [← hΦX S₀ hS₀ v.1 ⟨v.2, hv⟩]
        exact mem_image_of_mem Φ (H.V_subset_U v.2)
    · rw [hφv]
      have hvU : v.1 ∈ H.U := H.V_subset_U v.2
      constructor
      · intro h₅
        obtain ⟨i, hi⟩ := hsome v.1 hvU
        by_cases hii : i = i₀
        · have hs : i.1 = S₀ := congrArg Subtype.val hii
          have hi' : v.1 ∈ (Pd S₀).U := hs ▸ hi
          exact (hPU_V S₀ hS₀ v.1 hi' v.2).2
        · have h₆ : ψ i v.1 ∈ α_disc i₀.1 := hΦi i hi ▸ h₅
          exact S₀.bar_subset (hcross i i₀ hii v.1 hi h₆).2
      · intro h₅
        have h₆ : v.1 ∈ (Pd S₀).U := (Pd S₀).V_subset_U (by
          rw [hPV S₀ hS₀]
          exact ⟨v.2, h₅⟩)
        rw [hΦi i₀ h₆]
        exact h₂ i₀ h₆
    · rw [hφe]
      have heH : e.1 ∈ H.E := e.2
      obtain ⟨z, hz⟩ := heH.1
      constructor
      · intro h₅
        obtain ⟨S₁, hS₁, h₆⟩ := seg_edge η hseg heH
        by_cases hii : S₁ = S₀
        · exact hii ▸ h₆
        · have heP : e.1 ∈ (Pd S₁).E := by
            rw [hPE]
            exact ⟨heH, h₆⟩
          have hzU : z ∈ (Pd S₁).U := (Pd S₁).closure_subset_U heP (subset_closure hz)
          have h₇ : ψ ⟨S₁, hS₁⟩ z ∈ α_disc S₀ := hΦi ⟨S₁, hS₁⟩ hzU ▸ h₅ (mem_image_of_mem Φ hz)
          have h₈ := hcross ⟨S₁, hS₁⟩ i₀ (fun h => hii (congrArg Subtype.val h)) z hzU h₇
          exact absurd h₈.1.1 (edge_notMem_V heH hz)
      · rintro h₅ _ ⟨y, hy, rfl⟩
        have heP : e.1 ∈ (Pd S₀).E := by
          rw [hPE]
          exact ⟨heH, h₅⟩
        have hyU : y ∈ (Pd S₀).U := (Pd S₀).closure_subset_U heP (subset_closure hy)
        rw [hΦi i₀ hyU]
        exact h₂ i₀ hyU

end GraphMinor.GM14.Whitney
