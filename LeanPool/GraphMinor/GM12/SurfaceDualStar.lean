/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.SurfaceDualSplit

/-!
# Stars around vertices

Let `K` be a radial drawing of `D`, and let `H = D ∪ K`. Suppose that the vertices of `D` split into
a
set `V₀` and the rest, so that each edge of `D` has one end in each part. Let `N` be the part of `K`
that
misses `V₀`, on the vertices `V(K) \ V₀` (`IsSideSplit`).

The *star* of `v ∈ V₀` is `v` with the edges and the regions of `H` at `v`. Here we prove that the
stars
are open and disjoint, and that they cover the complement of `U(N)`. The file `SurfaceDualFan.lean`
proves that each star is an open disc. So the stars are the regions of `N`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {D K N : Drawing S}
  {V₀ : Set S}

/-- See the module docstring. -/
def star (H : Drawing S) (v : S) : Set S :=
  {v} ∪ (⋃ g ∈ {g ∈ H.E | v ∈ closure g}, g) ∪ ⋃ p ∈ {p ∈ H.R | v ∈ closure p}, p

omit [T2Space S] [ConnectedSpace S] in
theorem mem_star_self (H : Drawing S) (v : S) : v ∈ star H v := Or.inl (Or.inl rfl)

omit [T2Space S] [ConnectedSpace S] in
theorem edge_subset_star {H : Drawing S} {v : S} {g : Set S} (hg : g ∈ H.E) (hv : v ∈ closure g) :
    g ⊆ star H v :=
  fun _ hx => Or.inl (Or.inr (mem_biUnion (show g ∈ {g ∈ H.E | v ∈ closure g} from ⟨hg, hv⟩) hx))

omit [T2Space S] [ConnectedSpace S] in
theorem face_subset_star {H : Drawing S} {v : S} {p : Set S} (hp : p ∈ H.R) (hv : v ∈ closure p) :
    p ⊆ star H v :=
  fun _ hx => Or.inr (mem_biUnion (show p ∈ {p ∈ H.R | v ∈ closure p} from ⟨hp, hv⟩) hx)

omit [T2Space S] [ConnectedSpace S] in
theorem mem_star {H : Drawing S} {v x : S} (hx : x ∈ star H v) :
    x = v ∨ (∃ g ∈ H.E, v ∈ closure g ∧ x ∈ g) ∨ ∃ p ∈ H.R, v ∈ closure p ∧ x ∈ p := by
  rcases hx with (hx | hx) | hx
  · exact Or.inl hx
  · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
    exact Or.inr (Or.inl ⟨g, hg.1, hg.2, hxg⟩)
  · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    exact Or.inr (Or.inr ⟨p, hp.1, hp.2, hxp⟩)

/-- See the module docstring. -/
structure IsSideSplit (D K N : Drawing S) (V₀ : Set S) : Prop where
  sub_V : V₀ ⊆ D.V
  V_eq : N.V = K.V \ V₀
  E_sub : N.E ⊆ K.E
  D_ends : ∀ g ∈ D.E, ∃ u ∈ V₀, ∃ w ∈ D.V \ V₀, closure g ∩ D.V = {u, w}
  K_ends : ∀ g ∈ K.E, g ∉ N.E → ∃ u ∈ V₀, u ∈ closure g
  N_ends : ∀ g ∈ N.E, Disjoint (closure g) V₀

namespace IsSideSplit

variable (hX : IsSideSplit D K N V₀) (hrad : PreRad (PaintingOrDrawing.drawing D) K)

include hX

omit [T2Space S] [ConnectedSpace S] in
theorem V_sub {v : S} (hv : v ∈ V₀) : v ∈ (radialUnion hrad).V := by
  rw [radialUnion_V]
  exact radial_V hrad (hX.sub_V hv)

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of `H` at `v ∈ V₀` has its other end off `V₀`, in `N`. -/
theorem arm {g : Set S} (hg : g ∈ (radialUnion hrad).E) {v : S} (hv : v ∈ V₀)
  (hvg : v ∈ closure g) :
    ∃ w, w ≠ v ∧ w ∉ V₀ ∧ w ∈ N.V ∧ closure g ∩ (radialUnion hrad).V = {v, w} ∧ g ∉ N.E ∧
      (g ∈ D.E → w ∈ D.V) ∧ (g ∈ K.E → w ∉ D.V) := by
  have hvD := hX.sub_V hv
  rw [radialUnion_E] at hg
  rw [radialUnion_V]
  have hnotN : g ∉ N.E := fun h' => disjoint_left.mp (hX.N_ends g h') hvg hv
  rcases hg with hg | hg
  · obtain ⟨u, hu, w, hw, hcap⟩ := hX.D_ends g hg
    have hcap' : closure g ∩ K.V = {u, w} := by
      rw [← hcap]
      ext z
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, radial_inter hrad ▸ ⟨D.closure_subset_U hg h₁, K.V_subset_U h₂⟩⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, radial_V hrad h₂⟩
    have hvm : v ∈ closure g ∩ D.V := ⟨hvg, hvD⟩
    rw [hcap] at hvm
    rcases hvm with rfl | hvm
    · have hwV : w ∈ closure g ∩ D.V := by rw [hcap]; simp
      refine ⟨w, fun h' => hw.2 (h' ▸ hu), hw.2, hX.V_eq ▸ ⟨radial_V hrad hw.1, hw.2⟩, hcap', hnotN,
        fun _ => hw.1, fun hgK => ?_⟩
      exact absurd hg fun h' => edge_not_both hrad h' hgK
    · exact absurd (hvm ▸ hv) hw.2
  · obtain ⟨u, hu, w, hw, hcap⟩ := hrad.2.2.2.2.2.1 g hg
    have hvm : v ∈ closure g ∩ K.V := ⟨hvg, radial_V hrad hvD⟩
    rw [hcap] at hvm
    rcases hvm with rfl | hvm
    · exact ⟨w, fun h' => hw.2 (h' ▸ hvD), fun h' => hw.2 (hX.sub_V h'),
        hX.V_eq ▸ ⟨hw.1, fun h' => hw.2 (hX.sub_V h')⟩, hcap, hnotN,
        fun hgD => absurd hg fun h' => edge_not_both hrad hgD h', fun _ => hw.2⟩
    · exact absurd (hvm ▸ hvD) hw.2

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of `H` has at most one end in `V₀`. -/
theorem arm_unique {g : Set S} (hg : g ∈ (radialUnion hrad).E) {v v' : S} (hv : v ∈ V₀)
  (hv' : v' ∈ V₀)
    (hvg : v ∈ closure g) (hvg' : v' ∈ closure g) : v = v' := by
  obtain ⟨w, -, hw, -, hcap, -⟩ := hX.arm hrad hg hv hvg
  have : v' ∈ closure g ∩ (radialUnion hrad).V := ⟨hvg', hX.V_sub hrad hv'⟩
  rw [hcap] at this
  rcases this with h' | h'
  · exact h'.symm
  · exact absurd (h' ▸ hv') hw

omit [T2Space S] [ConnectedSpace S] in
theorem N_E_sub {g : Set S} (hg : g ∈ N.E) : g ∈ (radialUnion hrad).E := by
  rw [radialUnion_E]
  exact Or.inr (hX.E_sub hg)

omit [T2Space S] [ConnectedSpace S] in
theorem N_V_sub {z : S} (hz : z ∈ N.V) : z ∈ (radialUnion hrad).V := by
  rw [radialUnion_V]
  rw [hX.V_eq] at hz
  exact hz.1

omit [T2Space S] [ConnectedSpace S] in
theorem N_U_sub {z : S} (hz : z ∈ N.U) : z ∈ (radialUnion hrad).U := by
  by_cases hzV : z ∈ N.V
  · exact (radialUnion hrad).V_subset_U (hX.N_V_sub hrad hzV)
  · obtain ⟨g, hg, hzg⟩ := N.exists_edge_of_mem hz hzV
    exact (radialUnion hrad).closure_subset_U (hX.N_E_sub hrad hg) (subset_closure hzg)

omit [T2Space S] [ConnectedSpace S] in
/-- A point of `V₀` is off `N`. -/
theorem V₀_off {v : S} (hv : v ∈ V₀) : v ∉ N.U := by
  intro hz
  by_cases hzV : v ∈ N.V
  · rw [hX.V_eq] at hzV
    exact hzV.2 hv
  · obtain ⟨g, hg, hzg⟩ := N.exists_edge_of_mem hz hzV
    exact disjoint_left.mp (hX.N_ends g hg) (subset_closure hzg) hv

omit [T2Space S] [ConnectedSpace S] in
/-- An edge of `H` that is not in `N` is off `N`. -/
theorem edge_off {g : Set S} (hg : g ∈ (radialUnion hrad).E) (hgN : g ∉ N.E) : Disjoint g N.U := by
  refine disjoint_left.mpr fun z hzg hz => ?_
  by_cases hzV : z ∈ N.V
  · exact edge_notMem_V hg hzg (hX.N_V_sub hrad hzV)
  · obtain ⟨g', hg', hzg'⟩ := N.exists_edge_of_mem hz hzV
    exact hgN ((radialUnion hrad).edge_eq_of_mem hg (hX.N_E_sub hrad hg') hzg hzg' ▸ hg')

omit [T2Space S] [ConnectedSpace S] in
/-- A star is off `N`. -/
theorem star_off {v : S} (hv : v ∈ V₀) : Disjoint (star (radialUnion hrad) v) N.U := by
  refine disjoint_left.mpr fun z hz hzN => ?_
  rcases mem_star hz with rfl | ⟨g, hg, hvg, hzg⟩ | ⟨p, hp, -, hzp⟩
  · exact hX.V₀_off hv hzN
  · obtain ⟨w, -, -, -, -, hgN, -⟩ := hX.arm hrad hg hv hvg
    exact disjoint_left.mp (hX.edge_off hrad hg hgN) hzg hzN
  · exact region_subset hp hzp (hX.N_U_sub hrad hzN)

variable (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing D) K)
  (hE : D.E.Nonempty)

include hS hmax hE

/-- Each region of `H` has a point of `V₀` on its frontier: an end of its edge of `D`. -/
theorem exists_face_vertex {p : Set S} (hp : p ∈ (radialUnion hrad).R) :
    ∃ v ∈ V₀, v ∈ closure p := by
  obtain ⟨e, he, hep, -, -⟩ := face_edge hrad hS hmax hE hp
  obtain ⟨u, hu, w, -, hcap⟩ := hX.D_ends e he
  have : u ∈ closure e ∩ D.V := by rw [hcap]; simp
  exact ⟨u, hu, closure_minimal hep isClosed_closure this.1⟩

/-- Each region of `H` has just one point of `V₀` on its frontier. -/
theorem face_vertex_unique {p : Set S} (hp : p ∈ (radialUnion hrad).R) {v v' : S} (hv : v ∈ V₀)
    (hv' : v' ∈ V₀) (hvp : v ∈ closure p) (hvp' : v' ∈ closure p) : v = v' := by
  obtain ⟨e, he, -, -, hall⟩ := face_edge hrad hS hmax hE hp
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he
  exact hX.arm_unique hrad heH hv hv' (hall v (hX.sub_V hv) hvp) (hall v' (hX.sub_V hv') hvp')

/-- Stars at different points of `V₀` are disjoint. -/
theorem star_eq {v v' x : S} (hv : v ∈ V₀) (hv' : v' ∈ V₀) (hx : x ∈ star (radialUnion hrad) v)
    (hx' : x ∈ star (radialUnion hrad) v') : v = v' := by
  have hVU : ∀ {z}, z ∈ V₀ → z ∈ (radialUnion hrad).U := fun hz =>
    (radialUnion hrad).V_subset_U (hX.V_sub hrad hz)
  rcases mem_star hx with rfl | ⟨g, hg, hvg, hxg⟩ | ⟨p, hp, hvp, hxp⟩ <;>
    rcases mem_star hx' with h₁ | ⟨g', hg', hvg', hxg'⟩ | ⟨p', hp', hvp', hxp'⟩
  · exact h₁
  · exact absurd (hX.V_sub hrad hv) (edge_notMem_V hg' hxg')
  · exact absurd (hVU hv) (region_subset hp' hxp')
  · exact absurd (hX.V_sub hrad hv') (edge_notMem_V hg (h₁ ▸ hxg))
  · obtain rfl := (radialUnion hrad).edge_eq_of_mem hg hg' hxg hxg'
    exact hX.arm_unique hrad hg hv hv' hvg hvg'
  · exact absurd ((radialUnion hrad).closure_subset_U hg (subset_closure hxg))
      (region_subset hp' hxp')
  · exact absurd (hVU hv') (region_subset hp (h₁ ▸ hxp))
  · exact absurd ((radialUnion hrad).closure_subset_U hg' (subset_closure hxg'))
      (region_subset hp hxp)
  · obtain rfl := region_eq_of_mem hp hp' hxp hxp'
    exact hX.face_vertex_unique hrad hS hmax hE hp hv hv' hvp hvp'

/-- The stars cover the complement of `N`. -/
theorem exists_star {x : S} (hx : x ∉ N.U) : ∃ v ∈ V₀, x ∈ star (radialUnion hrad) v := by
  by_cases hxU : x ∈ (radialUnion hrad).U
  · by_cases hxV : x ∈ (radialUnion hrad).V
    · rw [radialUnion_V] at hxV
      have hxV₀ : x ∈ V₀ := by
        by_contra hn
        exact hx (N.V_subset_U (hX.V_eq ▸ ⟨hxV, hn⟩))
      exact ⟨x, hxV₀, mem_star_self _ _⟩
    · obtain ⟨g, hg, hxg⟩ := (radialUnion hrad).exists_edge_of_mem hxU hxV
      have hu : ∃ u ∈ V₀, u ∈ closure g := by
        have hg' := hg
        rw [radialUnion_E] at hg'
        rcases hg' with hg' | hg'
        · obtain ⟨u, hu, w, -, hcap⟩ := hX.D_ends g hg'
          have : u ∈ closure g ∩ D.V := by rw [hcap]; simp
          exact ⟨u, hu, this.1⟩
        · refine hX.K_ends g hg' fun h' => hx ?_
          exact N.closure_subset_U h' (subset_closure hxg)
      obtain ⟨u, hu, hug⟩ := hu
      exact ⟨u, hu, edge_subset_star hg hug hxg⟩
  · obtain ⟨p, hp, hxp⟩ := exists_region_of_notMem hxU
    obtain ⟨v, hv, hvp⟩ := hX.exists_face_vertex hrad hS hmax hE hp
    exact ⟨v, hv, face_subset_star hp hvp hxp⟩

/-- A star is open. Near `v` this follows from the sectors at `v`, once we remove the closed set
made of
the edges away from `v` and the other vertices. Near a point of an edge, it follows from the two
sides of the edge. -/
theorem star_isOpen {v : S} (hv : v ∈ V₀) : IsOpen (star (radialUnion hrad) v) := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let H := radialUnion hrad
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  rcases mem_star hx with rfl | ⟨g, hg, hvg, hxg⟩ | ⟨p, hp, hvp, hxp⟩
  · obtain ⟨y₀⟩ : Nonempty S := inferInstance
    obtain ⟨γ, hγ⟩ := exists_edgePar H
    obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS H hγ (hX.V_sub hrad hv)
      (two_half_edges hrad hS hmax hE hγ (hX.sub_V hv))
    let Z : Set S := (⋃ g ∈ {g ∈ H.E | x ∉ closure g}, closure g) ∪ (H.V \ {x})
    have hZ : IsClosed Z := by
      refine IsClosed.union ?_ ?_
      · exact (H.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure
      · exact (H.finite_V.subset sdiff_subset).isClosed
    have hxZ : x ∉ Z := by
      rintro (h' | h')
      · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h'
        exact hg.2 hxg
      · exact h'.2 rfl
    refine ⟨W \ Z, ?_, (IsSectors.isOpen hsec).sdiff hZ, IsSectors.mem hsec, hxZ⟩
    rintro y ⟨hyW, hyZ⟩
    by_cases hyU : y ∈ H.U
    · by_cases hyV : y ∈ H.V
      · have : y = x := by
          by_contra hn
          exact hyZ (Or.inr ⟨hyV, hn⟩)
        exact this ▸ mem_star_self _ _
      · obtain ⟨g, hg, hyg⟩ := H.exists_edge_of_mem hyU hyV
        have hxg : x ∈ closure g := by
          by_contra hn
          exact hyZ (Or.inl (mem_biUnion (show g ∈ {g ∈ H.E | x ∉ closure g} from ⟨hg, hn⟩)
            (subset_closure hyg)))
        exact edge_subset_star hg hxg hyg
    · obtain ⟨k, hk⟩ := mem_iUnion.mp (IsSectors.cover hsec ⟨hyW, hyU⟩)
      have hcor := IsSectors.corners hsec
      exact face_subset_star (IsCorners.region hcor k) (IsCorners.closure_v hcor k)
        (IsSectors.sub hsec k hk)
  · obtain ⟨W, A₁, A₂, hW, hxW, hWU, hcov, hc₁, hc₂, hd₁, hd₂, hcl₁, hcl₂⟩ :=
      exists_edge_sides hS H hg hxg
    refine ⟨W, ?_, hW, hxW⟩
    have hside : ∀ {A : Set S}, IsPreconnected A → Disjoint A H.U → g ∩ W ⊆ closure A →
        ∀ y ∈ A, y ∈ star H v := by
      intro A hA hd hcl y hy
      obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (disjoint_left.mp hd hy)
      have hAr : A ⊆ r := subset_region hr hA hd hy hyr
      have hxr : x ∈ closure r := closure_mono hAr (hcl ⟨hxg, hxW⟩)
      have hgr : g ⊆ closure r := edge_subset_closure_of_incident hS hg hr ⟨x, hxg, hxr⟩
      exact face_subset_star hr (closure_minimal hgr isClosed_closure hvg) hyr
    intro y hy
    by_cases hyU : y ∈ H.U
    · exact edge_subset_star hg hvg (hWU ⟨hy, hyU⟩)
    · rcases hcov ⟨hy, hyU⟩ with h₁ | h₁
      · exact hside hc₁ hd₁ hcl₁ y h₁
      · exact hside hc₂ hd₂ hcl₂ y h₁
  · exact ⟨p, face_subset_star hp hvp, region_isOpen hp, hxp⟩

variable {γ : Set S → I → S} {v : S}
  {next : halfEdges (radialUnion hrad) γ v → halfEdges (radialUnion hrad) γ v}
  {ρ P Q : halfEdges (radialUnion hrad) γ v → Set S} {W : Set S}
  {τ : halfEdges (radialUnion hrad) γ v → I}

omit hS hmax hE in
omit [ConnectedSpace S] in
/-- An edge at `v` has just one half-edge at `v`, since it is not a loop. -/
theorem half_inj (hγ : EdgePar (radialUnion hrad) γ) (hv : v ∈ V₀)
    {k k' : halfEdges (radialUnion hrad) γ v} (h' : k.1.1 = k'.1.1) : k = k' := by
  have hg := k.2.1
  have hvg : v ∈ closure k.1.1 := by
    have := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at this
  obtain ⟨w, hwv, -, -, hcap, -⟩ := hX.arm hrad hg hv hvg
  have hw : w ∈ closure k.1.1 ∩ (radialUnion hrad).V := by rw [hcap]; simp
  obtain ⟨b, hb⟩ := exists_end_eq hγ hg hw.2 hw.1
  refine Subtype.ext (Prod.ext h' ?_)
  by_contra hne
  have h₁ := k.2.2
  have h₂ := k'.2.2
  rw [← h'] at h₂
  have hbc : b = k.1.2 ∨ b = k'.1.2 := by
    revert hne
    cases b <;> cases k.1.2 <;> cases k'.1.2 <;> simp
  rcases hbc with hb' | hb'
  · rw [hb'] at hb
    exact hwv (hb.symm.trans h₁)
  · rw [hb'] at hb
    exact hwv (hb.symm.trans h₂)

/-- The corners at `v` lie in different regions of `H`. Each corner has a half-edge of `D` beside
it, by
`corner_alternates`. Two corners in one region have the same one, since a region has one edge of
`D`.
So they are the two corners beside this half-edge. But an edge of `D` has two different regions
beside
it, by `exists_two_faces`. -/
theorem corner_inj (hγ : EdgePar (radialUnion hrad) γ) (hv : v ∈ V₀)
    (hsec : IsSectors (radialUnion hrad) γ v next ρ P W Q τ)
    {k k' : halfEdges (radialUnion hrad) γ v} (h' : ρ k = ρ k') : k = k' := by
  have hcor := IsSectors.corners hsec
  have hvD := hX.sub_V hv
  have hbes : ∀ c : halfEdges (radialUnion hrad) γ v,
      ∃ j, (j = c ∨ j = next c) ∧ j.1.1 ∈ D.E ∧ j.1.1 ⊆ closure (ρ c) := by
    intro c
    obtain ⟨c', hc'⟩ := next_surjective hcor c
    have hl : c.1.1 ⊆ closure (ρ c) := by
      have := IsCorners.right hcor c'
      rwa [hc'] at this
    rcases corner_alternates hrad hS hmax hE hγ hvD hsec c with h₁ | h₁
    · exact ⟨next c, Or.inr rfl, h₁.2, IsCorners.left hcor c⟩
    · exact ⟨c, Or.inl rfl, h₁.1, hl⟩
  obtain ⟨j, hj, hjD, hjc⟩ := hbes k
  obtain ⟨j', hj', hjD', hjc'⟩ := hbes k'
  have hjj : j = j' := by
    obtain ⟨e, he, -, heu, -⟩ := face_edge hrad hS hmax hE (IsCorners.region hcor k)
    exact hX.half_inj hrad hγ hv
      ((heu _ hjD hjc).trans (heu _ hjD' (h'.symm ▸ hjc')).symm)
  subst hjj
  have hne : ∀ c : halfEdges (radialUnion hrad) γ v, (next c).1.1 ∈ D.E → ρ c ≠ ρ (next c) := by
    intro c hc heq
    obtain ⟨p, hp, q, hq, hpq, hep, heq', -⟩ := exists_two_faces hrad hS hmax hE hc
    have h₁ := IsCorners.sides hcor c p hp hep
    have h₂ := IsCorners.sides hcor c q hq heq'
    refine hpq ?_
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact h₁.trans h₂.symm
    · exact h₁.trans (heq.trans h₂.symm)
    · exact h₁.trans (heq.symm.trans h₂.symm)
    · exact h₁.trans h₂.symm
  rcases hj with hj | hj <;> rcases hj' with hj' | hj'
  · exact hj.symm.trans hj'
  · have hρ : ρ (next k') = ρ k := congrArg ρ (hj'.symm.trans hj)
    exact absurd (h'.symm.trans hρ.symm) (hne k' (hj' ▸ hjD))
  · have hρ : ρ (next k) = ρ k' := congrArg ρ (hj.symm.trans hj')
    exact absurd (h'.trans hρ.symm) (hne k (hj ▸ hjD))
  · exact IsCorners.inj hcor (hj.symm.trans hj')

end IsSideSplit

end GraphMinor.GM12
