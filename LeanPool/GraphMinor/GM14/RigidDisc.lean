/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.RigidClaims
public import LeanPool.GraphMinor.GM14.RigidAccess
public import LeanPool.GraphMinor.GM14.RigidSegregation
public import LeanPool.GraphMinor.GM14.GraphTransport
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.Schoenflies
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Two facts about a drawing that is rigid in a closed disc

Let `H` be a drawing that is rigid in a closed disc `Δ`. A circuit of `H` has three disjoint paths
to
`V(H) ∩ bd(Δ)` (`three_paths_of_rigid`). This is Claim (1) of (6.5), page 34, for a disc in any
surface. A vertex of `H` off `bd(Δ)` does not lie on just one edge (`two_edges_of_rigid`). Claim (2)
of (8.4) needs this second fact.

Both facts are first proved in a sphere, with the wheel of `exists_frame` on the other side of
`bd(Δ)`. Then we move `H` to a disc in the sphere by `mapD`.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
open GraphMinor.GM14.Whitney

universe u

section Sphere

variable {T : Type u} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

/-- A vertex off the boundary circle lies on at least two edges. -/
theorem two_edges_sphere (hS : IsClosedSurface T) (hsph : IsSphere T)
    {D₁ D₂ C : Set T} (hd₁ : IsClosedDisc D₁) (hd₂ : IsClosedDisc D₂) (hb₁ : discBd D₁ = C)
    (hb₂ : discBd D₂ = C) (hcov : D₁ ∪ D₂ = univ) (hcap : D₁ ∩ D₂ = C) {H : Drawing T}
    (hU : H.U ⊆ D₁) (hn : H.U ∩ C ⊆ H.V) (hr : IsRigidIn H D₁) {v : T} (hv : v ∈ H.V)
    (hvC : v ∉ C) {e : Set T} (he : H.toGraph.Inc e v) :
    ∃ e', e' ≠ e ∧ H.toGraph.Inc e' v := by
  classical
  obtain ⟨W, a, Γ', hm, hw, hf, hrr, -, -, haD₁, -, hhub⟩ :=
    exists_frame hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap hU hn hr
  have hu : IsUnion H W (H.glue W hm) := isUnion_glue hm
  have hsb : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  generalize hJ : H.glue W hm = J at hu hf hrr
  have hHJ : H.IsSubdrawing J := ⟨hf.Vsub, hf.Esub⟩
  have hWJ : W.IsSubdrawing J := ⟨hu.hV ▸ subset_union_right, hu.hE ▸ subset_union_right⟩
  have heE : e ∈ H.E := he.edge_mem
  by_contra hno
  push Not at hno
  -- All edges of `J` at `v` are edges of `H`, as `v` is off the circle.
  have hJH : ∀ g, J.toGraph.Inc g v → g = e := by
    rintro g ⟨y, hl⟩
    have hgJ : g ∈ J.E := hl.edge_mem
    have hgH : g ∈ H.E := by
      by_contra hgH
      have hgW : g ∈ W.E := (show g ∈ H.E ∪ W.E from hu.hE ▸ hgJ).resolve_left hgH
      have h₁ : v ∈ closure g ∩ J.V := hl.2.2.2 ▸ mem_insert _ _
      rw [← hWJ.closure_inter_V hgW] at h₁
      exact hvC (hcap ▸ ⟨hU (H.V_subset_U hv), hw.Usub (W.V_subset_U h₁.2)⟩)
    by_contra hge
    have hc : closure g ∩ J.V = {v, y} := hl.2.2.2
    rw [← hHJ.closure_inter_V hgH] at hc
    have hy : y ∈ H.V := (show y ∈ closure g ∩ H.V from hc ▸ mem_insert_of_mem _ rfl).2
    exact hno g hge ⟨y, hgH, hv, hy, hc⟩
  obtain ⟨y, hl⟩ := he
  have hlJ : J.toGraph.IsLink e v y := by
    refine ⟨hHJ.2 heE, hHJ.1 hv, hHJ.1 hl.2.2.1, ?_⟩
    rw [← hHJ.closure_inter_V heE]
    exact hl.2.2.2
  have hb : Whitney.bdry J.toGraph {e} ⊆ {y} \ {v} := by
    rintro z ⟨⟨_, (rfl : _ = e), hz⟩, ⟨g, ⟨hgE, hge⟩, hzg⟩⟩
    have hzv : z ≠ v := by
      rintro rfl
      exact hge (hJH g hzg)
    obtain ⟨w, hw'⟩ := hz
    rcases J.toGraph.eq_or_eq_of_isLink_of_isLink hw' hlJ with h | h
    · exact absurd h hzv
    · exact ⟨h, hzv⟩
  have hsub : Whitney.bdry J.toGraph {e} ⊆ {y} := hb.trans sdiff_subset
  have hfin : (Whitney.bdry J.toGraph {e}).Finite := (finite_singleton y).subset hsub
  have hcard : (Whitney.bdry J.toGraph {e}).ncard ≤ 2 := by
    have := ncard_le_ncard hsub (finite_singleton y)
    rw [ncard_singleton] at this
    omega
  obtain ⟨x, y', -, hxy, hbd, -⟩ := exists_thread hf hrr hS hsph (singleton_subset_iff.mpr heE)
    hcard hfin (singleton_nonempty e)
  have h₁ : x ∈ ({y} : Set T) := hsub (hbd ▸ mem_insert _ _)
  have h₂ : y' ∈ ({y} : Set T) := hsub (hbd ▸ mem_insert_of_mem _ rfl)
  exact hxy (h₁.trans h₂.symm)

/-- Claim (1) of (6.5), with the wheel built in. -/
theorem three_paths_sphere (hS : IsClosedSurface T) (hsph : IsSphere T)
    {D₁ D₂ C : Set T} (hd₁ : IsClosedDisc D₁) (hd₂ : IsClosedDisc D₂) (hb₁ : discBd D₁ = C)
    (hb₂ : discBd D₂ = C) (hcov : D₁ ∪ D₂ = univ) (hcap : D₁ ∩ D₂ = C) {H : Drawing T}
    (hU : H.U ⊆ D₁) (hn : H.U ∩ C ⊆ H.V) (hr : IsRigidIn H D₁) {R : Drawing T}
    (hR : R.IsCircuit) (hRH : R.IsSubdrawing H) :
    ∃ Q : Fin 3 → Graph T (Set T), Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i, IsFromToPath H.toGraph (Q i) R.V (H.V ∩ C) := by
  classical
  obtain ⟨W, a, Γ', hm, hw, hf, hrr, -, -, haD₁, -, hhub⟩ :=
    exists_frame hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap hU hn hr
  have hu : IsUnion H W (H.glue W hm) := isUnion_glue hm
  have hsb : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hgood := good_of_wheel hf hrr hw hu
    (fun v hv hvW => ⟨hv, by
      have : v ∈ D₁ ∩ D₂ := ⟨hU (H.V_subset_U hv), hw.Usub (W.V_subset_U hvW)⟩
      rwa [hcap] at this⟩) hm hS hsph
  obtain ⟨G₀, Q₀, hsd⟩ := exists_subData (good_sub hgood)
  generalize hJ : H.glue W hm = J at hu hf hrr hgood hsd
  have hWJ : W.IsSubdrawing J := ⟨hu.hV ▸ subset_union_right, hu.hE ▸ subset_union_right⟩
  have hB' : ∀ v ∈ H.V, ∀ g ∈ J.E, g ∉ H.E → v ∈ closure g → v ∈ subBd D₁ := by
    intro v hv g hg hgH hvg
    have hgW : g ∈ W.E := (show g ∈ H.E ∪ W.E from hu.hE ▸ hg).resolve_left hgH
    have h₂ : v ∈ closure g ∩ J.V := ⟨hvg, hf.Vsub hv⟩
    rw [← hWJ.closure_inter_V hgW] at h₂
    rw [hsb]
    exact hcap ▸ ⟨hU (H.V_subset_U hv), hw.Usub (W.V_subset_U h₂.2)⟩
  have := claim_1_three_paths hf hrr hS hsph hsd hB' hR hRH
  rwa [hsb] at this

end Sphere

section Move

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The image of a drawing has the same graph. -/
theorem gmap_mapD {T : Type*} [TopologicalSpace T] [T2Space T] {A : Set S} {B : Set T} {f : S → T}
    {f' : T → S} (hP : PH A B f f') (hA : IsCompact A) (H : Drawing S) (hU : H.U ⊆ A) :
    GMap H.toGraph (mapD hP hA H hU).toGraph f (image f) := by
  have hVA : H.V ⊆ A := H.V_subset_U.trans hU
  have heA : ∀ {e}, e ∈ H.E → e ⊆ A := fun he => subset_closure.trans
    ((H.closure_subset_U he).trans hU)
  refine ⟨⟨fun x hx => mem_image_of_mem f hx, hP.injOn.mono hVA, fun y hy => hy⟩,
    ⟨fun e he => ?_, ?_, ?_⟩, ?_⟩
  · change image f e ∈ (mapD hP hA H hU).E
    rw [mapD_E]
    exact mem_image_of_mem _ he
  · intro e he e' he' h
    have h₁ := hP.back (heA he)
    have h₂ := hP.back (heA he')
    change f '' e = f '' e' at h
    rw [← h₁, ← h₂, h]
  · intro e' he'
    change e' ∈ (mapD hP hA H hU).E at he'
    rw [mapD_E] at he'
    exact he'
  · intro e x y he hx hy
    have hcap : closure (f '' e) ∩ f '' H.V = f '' (closure e ∩ H.V) := cap_image_eq hP hA
      (heA he) hVA
    have hcl : closure e ⊆ A := closure_minimal (heA he) hA.isClosed
    change (e ∈ H.E ∧ x ∈ H.V ∧ y ∈ H.V ∧ closure e ∩ H.V = {x, y}) ↔
      (image f e ∈ (mapD hP hA H hU).E ∧ f x ∈ f '' H.V ∧ f y ∈ f '' H.V ∧
        closure (f '' e) ∩ f '' H.V = {f x, f y})
    rw [hcap, ← image_pair]
    constructor
    · rintro ⟨-, -, -, h⟩
      refine ⟨?_, mem_image_of_mem f hx, mem_image_of_mem f hy, by rw [h]⟩
      rw [mapD_E]
      exact mem_image_of_mem _ he
    · rintro ⟨-, -, -, h⟩
      refine ⟨he, hx, hy, ?_⟩
      have hi : InjOn f A := hP.injOn
      refine (hi.image_eq_image_iff ?_ ?_).mp h
      · exact inter_subset_left.trans hcl
      · rintro z (rfl | rfl)
        · exact hVA hx
        · exact hVA hy

variable {α : Type*} {β : Type*} {α' : Type*} {β' : Type*}

theorem GMap.symm_image {G : Graph α β} {G' : Graph α' β'} {f : α → α'} {g : β → β'}
    [Nonempty α] (m : GMap G G' f g) {Z : Set α} (hZ : Z ⊆ V(G)) :
    Function.invFunOn f V(G) '' (f '' Z) = Z := by
  rw [image_image]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change Function.invFunOn f V(G) (f z) ∈ Z
    rw [m.bijV.invOn_invFunOn.1 (hZ hz)]
    exact hz
  · intro hx
    exact ⟨x, hx, m.bijV.invOn_invFunOn.1 (hZ hx)⟩

omit [T2Space S] in
/-- A closed disc of `S`, as a closed disc of a sphere. -/
theorem exists_sphere_model {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ) :
    ∃ (D₁ D₂ C : Set (OnePoint EuclideanPlane)) (f : S → OnePoint EuclideanPlane)
      (f' : OnePoint EuclideanPlane → S), IsClosedDisc D₁ ∧ IsClosedDisc D₂ ∧ discBd D₁ = C ∧
      discBd D₂ = C ∧ D₁ ∪ D₂ = univ ∧ D₁ ∩ D₂ = C ∧ PH Δ D₁ f f' ∧ subBd D₁ = C ∧
      (∀ x ∈ Δ, f x ∈ C ↔ x ∈ subBd Δ) ∧ f '' subBd Δ ⊆ subBd D₁ ∧ f' '' subBd D₁ ⊆ subBd Δ := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨hS, hconn⟩ := GraphMinor.GM11.IsSphere.isClosedSurface hsph
  have hO : IsOArc (sph '' Metric.sphere (0 : ℂ) 1) :=
    isOArc_image isOpenEmbedding_sph.isEmbedding oArc_sphere
  obtain ⟨D₁, D₂, -, hd₁, hd₂, hb₁, hb₂, hcov, hcap, -, -⟩ := sphere_disc _ hsph _ hO
  generalize sph '' Metric.sphere (0 : ℂ) 1 = C at hO hb₁ hb₂ hcap
  obtain ⟨f, f', hP, hf₁, hf₂⟩ := exists_disc_map hΔ hd₁
  have hsbD : subBd D₁ = C := (IsClosedDisc.subBd_eq_discBd hS hd₁).trans hb₁
  have hbd : f '' subBd Δ ⊆ subBd D₁ := by
    rw [hbdΔ, IsClosedDisc.subBd_eq_discBd hS hd₁]
    exact hf₁
  have hbd' : f' '' subBd D₁ ⊆ subBd Δ := by
    rw [hbdΔ, IsClosedDisc.subBd_eq_discBd hS hd₁]
    exact hf₂
  refine ⟨D₁, D₂, C, f, f', hd₁, hd₂, hb₁, hb₂, hcov, hcap, hP, hsbD, fun x hx => ⟨fun h => ?_,
    fun h => hsbD ▸ hbd (mem_image_of_mem f h)⟩, hbd, hbd'⟩
  have h₁ := hbd' (mem_image_of_mem f' (hsbD.symm ▸ h))
  rwa [hP.left hx] at h₁

variable {Δ : Set S} {H : Drawing S}

/-- **Claim (1) of (6.5).** A circuit of a drawing that is rigid in a closed disc has three disjoint
paths to the boundary. -/
theorem three_paths_of_rigid (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ) (hHΔ : H.U ⊆ Δ)
    (hHbd : H.U ∩ subBd Δ ⊆ H.V) (hrigid : IsRigidIn H Δ) {R : Drawing S} (hR : R.IsCircuit)
    (hRH : R.IsSubdrawing H) :
    ∃ Q : Fin 3 → Graph S (Set S), Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i, IsFromToPath H.toGraph (Q i) R.V (H.V ∩ subBd Δ) := by
  classical
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨hS, hconn⟩ := GraphMinor.GM11.IsSphere.isClosedSurface hsph
  obtain ⟨D₁, D₂, C, f, f', hd₁, hd₂, hb₁, hb₂, hcov, hcap, hP, hsbD, hiff, hbd, hbd'⟩ :=
    exists_sphere_model hΔ hbdΔ
  have hAc : IsCompact Δ := hΔ.isCompact
  have hBc : IsCompact D₁ := hd₁.isCompact
  have hRU : R.U ⊆ Δ := hRH.U_subset.trans hHΔ
  let M := mapD hP hAc H hHΔ
  let R' := mapD hP hAc R hRU
  have hVΔ : H.V ⊆ Δ := H.V_subset_U.trans hHΔ
  have hMn : M.U ∩ C ⊆ M.V := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    exact mem_image_of_mem f (hHbd ⟨hx, (hiff x (hHΔ hx)).mp hxC⟩)
  have hMr : IsRigidIn M D₁ := isRigidIn_mapD hP hAc hbd hbd' H hHΔ hrigid
  have hR'M : R'.IsSubdrawing M := by
    refine ⟨image_mono hRH.1, ?_⟩
    change (mapD hP hAc R hRU).E ⊆ (mapD hP hAc H hHΔ).E
    rw [mapD_E, mapD_E]
    exact image_mono hRH.2
  have hR' : R'.IsCircuit := by
    obtain ⟨u, W, ⟨hs, hd⟩, hlen, hV, hE⟩ := hR
    have mR := gmap_mapD hP hAc R hRU
    obtain ⟨W', h₁, h₂⟩ := exists_walk_image
      (fun {e x y} h => (mR.link h.edge_mem h.left_mem h.right_mem).mp h)
      (fun x hx => mR.bijV.mapsTo hx) W
    refine ⟨f u, W', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [h₁, ← List.map_tail]
      refine hs.map_on fun x hx y hy hxy => ?_
      exact mR.bijV.injOn (mem_of_mem_walk W (List.mem_of_mem_tail hx))
        (mem_of_mem_walk W (List.mem_of_mem_tail hy)) hxy
    · rw [h₂]
      refine hd.map_on fun x hx y hy hxy => ?_
      exact mR.bijE.injOn (hE ▸ hx : x ∈ R.E) (hE ▸ hy : y ∈ R.E) hxy
    · change 0 < W'.edges.length
      rw [h₂, List.length_map]
      exact hlen
    · change f '' R.V = _
      rw [hV, h₁]
      ext z
      simp
    · change (mapD hP hAc R hRU).E = _
      rw [mapD_E, hE, h₂]
      ext z
      simp
  obtain ⟨Q', hdis, hQ'⟩ := three_paths_sphere hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap
    (hP.image_sub hHΔ) hMn hMr hR' hR'M
  obtain ⟨u, -, -, -, -, -⟩ := id hR
  have : Nonempty S := ⟨u⟩
  have m := gmap_mapD hP hAc H hHΔ
  have ms := m.symm
  have hRV : R.V ⊆ H.V := hRH.1
  have hcapV : M.V ∩ C = f '' (H.V ∩ subBd Δ) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxC⟩
      exact ⟨x, ⟨hx, (hiff x (hVΔ hx)).mp hxC⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxb⟩, rfl⟩
      exact ⟨mem_image_of_mem f hx, (hiff x (hVΔ hx)).mpr hxb⟩
  refine ⟨fun i => ms.sub (Q' i), ?_, fun i => ?_⟩
  · intro i j hij
    obtain ⟨_, _, hPi⟩ := hQ' i
    obtain ⟨_, _, hPj⟩ := hQ' j
    change Disjoint (Function.invFunOn f H.V '' V(Q' i)) (Function.invFunOn f H.V '' V(Q' j))
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' := ms.bijV.injOn (hPj.1.1.vertexSet_mono hb) (hPi.1.1.vertexSet_mono ha) hab
    exact disjoint_left.mp (hdis hij) ha (hab' ▸ hb)
  · obtain ⟨a, b, hPi⟩ := hQ' i
    have h := ms.fromTo (image_mono hRH.1) (inter_subset_left.trans (Subset.rfl)) hPi
    have e₁ : Function.invFunOn f H.V '' (f '' R.V) = R.V := m.symm_image hRV
    have e₂ : Function.invFunOn f H.V '' (M.V ∩ C) = H.V ∩ subBd Δ := by
      rw [hcapV]
      exact m.symm_image inter_subset_left
    change IsFromToPathWithEnds H.toGraph _ (Function.invFunOn f H.V '' (f '' R.V))
      (Function.invFunOn f H.V '' (M.V ∩ C)) _ _ at h
    rw [e₁, e₂] at h
    exact ⟨_, _, h⟩

/-- A vertex off the boundary of a closed disc does not lie on just one edge, if the drawing is
rigid
in the disc. -/
theorem two_edges_of_rigid (hΔ : IsClosedDisc Δ) (hbdΔ : subBd Δ = discBd Δ) (hHΔ : H.U ⊆ Δ)
    (hHbd : H.U ∩ subBd Δ ⊆ H.V) (hrigid : IsRigidIn H Δ) {v : S} (hv : v ∈ H.V)
    (hvb : v ∉ subBd Δ) {e : Set S} (he : H.toGraph.Inc e v) :
    ∃ e', e' ≠ e ∧ H.toGraph.Inc e' v := by
  classical
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  obtain ⟨hS, hconn⟩ := GraphMinor.GM11.IsSphere.isClosedSurface hsph
  obtain ⟨D₁, D₂, C, f, f', hd₁, hd₂, hb₁, hb₂, hcov, hcap, hP, hsbD, hiff, hbd, hbd'⟩ :=
    exists_sphere_model hΔ hbdΔ
  have hAc : IsCompact Δ := hΔ.isCompact
  have hBc : IsCompact D₁ := hd₁.isCompact
  let M := mapD hP hAc H hHΔ
  have hVΔ : H.V ⊆ Δ := H.V_subset_U.trans hHΔ
  have hMn : M.U ∩ C ⊆ M.V := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    exact mem_image_of_mem f (hHbd ⟨hx, (hiff x (hHΔ hx)).mp hxC⟩)
  have hMr : IsRigidIn M D₁ := isRigidIn_mapD hP hAc hbd hbd' H hHΔ hrigid
  have m := gmap_mapD hP hAc H hHΔ
  obtain ⟨y, hl⟩ := he
  have hl' := (m.link hl.edge_mem hl.left_mem hl.right_mem).mp hl
  obtain ⟨g, hge, z, hg⟩ := two_edges_sphere hS hsph hd₁ hd₂ hb₁ hb₂ hcov hcap
    (hP.image_sub hHΔ) hMn hMr (mem_image_of_mem f hv)
    (fun h => hvb ((hiff v (hVΔ hv)).mp h)) ⟨_, hl'⟩
  obtain ⟨e', he', rfl⟩ := m.bijE.surjOn hg.edge_mem
  obtain ⟨z', hz', rfl⟩ := m.bijV.surjOn hg.right_mem
  refine ⟨e', fun h => hge (h ▸ rfl), z', ?_⟩
  exact (m.link he' hv hz').mpr hg

end Move

end GraphMinor.GM14
