/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.WhitneyPeripheral
public import LeanPool.GraphMinor.GM14.Section6a
import LeanPool.GraphMinor.GM11.SphereRegion
import LeanPool.GraphMinor.GM11.GlueFaces
import LeanPool.GraphMinor.GM11.RadialExists
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# Curves that a rigid drawing forces around a separation

Let `H` be a drawing that is rigid in a closed disc `Δ` in a sphere, and let `J` be a drawing with
`H`
inside `Δ` and with extra pieces outside. We show two things.

First, `J` is 2-cell (`Frame.twoCell`), since rigidity gives a disc inside any region. So `J` has a
radial drawing, whose circuits meet `J` only in vertices.

Second, this is the place where Graph Minors XIV uses "a form of Menger's theorem for planar
graphs". Let
`E` be a set of edges of `H`, and take the regions of the radial drawing that contain an edge of
`E`.
The boundary of their union meets `J` only in vertices that meet both `E` and another edge. If at
most
two vertices do so, then rigidity gives a dial for each `O`-arc in that boundary. A region outside
all
the dials cannot be both inside and outside the union, so each edge of `E` lies in a dial. As the
arc
meets an edge inside the disc, the disc must hold a path of `H`. This is `exists_dial_of_edge`.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- If `Z` is a set of regions of `Γ'`, then a region of `N(Z)` does not hold both a point of a
member
of `Z` and a point outside the closures of the members of `Z`. -/
theorem not_same_side [ConnectedSpace S] (hS : IsClosedSurface S) {Γ' : Drawing S} {Z : Set (Set S)}
    (hZ : Z ⊆ Γ'.R) {s : Set S} (hs : s ∈ Z) {p a : S} (hp : p ∈ s)
    (ha : a ∉ ⋃ t ∈ Z, closure t) :
    ¬ ∃ r ∈ (boundaryDrawing Γ' Z).R, a ∈ r ∧ p ∈ r := by
  classical
  rintro ⟨r, hr, har, hpr⟩
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin : Γ'.R.Finite := finite_R hS Γ'
  set N := boundaryDrawing Γ' Z with hN
  let Y := ⋃ t ∈ Z, closure t
  let Y' := ⋃ t ∈ Γ'.R \ Z, closure t
  have hYc : IsClosed Y := (hfin.subset hZ).isClosed_biUnion fun _ _ => isClosed_closure
  have hYc' : IsClosed Y' := (hfin.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have hcov : (univ : Set S) ⊆ Y ∪ Y' := by
    intro x _
    have hdense : x ∈ closure (⋃₀ Γ'.R) := by
      refine mem_closure_iff.mpr fun O hO hxO => ?_
      obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := Γ') hS hO ⟨x, hxO⟩
      obtain ⟨t, ht, hyt⟩ := exists_region_of_notMem hyU
      exact ⟨y, hyO, t, ht, hyt⟩
    rw [hfin.closure_sUnion] at hdense
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hdense
    by_cases htZ : t ∈ Z
    · exact Or.inl (mem_iUnion₂.mpr ⟨t, htZ, hxt⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, htZ⟩, hxt⟩)
  have hcap : Y ∩ Y' ⊆ N.U := by
    rintro x ⟨hx, hx'⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨t', ht', hxt'⟩ := mem_iUnion₂.mp hx'
    have htR := hZ ht
    have hne : t ≠ t' := fun h' => ht'.2 (h' ▸ ht)
    have hxU : x ∈ Γ'.U := by
      rcases closure_region_subset htR hxt with h₁ | h₁
      · exfalso
        obtain ⟨y, hy, hyt'⟩ := mem_closure_iff.mp hxt' t (region_isOpen htR) h₁
        exact hne (region_eq_of_mem htR ht'.1 hy hyt')
      · exact h₁
    by_cases hxV : x ∈ Γ'.V
    · exact N.V_subset_U ((mem_boundaryDrawing_V hS).mpr
        ⟨⟨t, ht, hxV, Or.inr htR, hxt⟩, t', ht', hxV, Or.inr ht'.1, hxt'⟩)
    · obtain ⟨e, he, hxe⟩ := Γ'.exists_edge_of_mem hxU hxV
      have hN' : e ∈ N.E := mem_boundaryDrawing_E.mpr
        ⟨⟨t, ht, he, htR, x, hxe, hxt⟩, t', ht', he, ht'.1, x, hxe, hxt'⟩
      exact N.closure_subset_U hN' (subset_closure hxe)
  have hpY : p ∈ Y := mem_iUnion₂.mpr ⟨s, hs, subset_closure hp⟩
  have haY' : a ∈ Y' := (hcov (mem_univ a)).resolve_left ha
  obtain ⟨z, hzr, hz, hz'⟩ := isPreconnected_closed_iff.mp (region_isPreconnected hr) Y Y' hYc hYc'
    (fun x _ => hcov (mem_univ x)) ⟨p, hpr, hpY⟩ ⟨a, har, haY'⟩
  exact region_subset hr hzr (hcap ⟨hz, hz'⟩)

/-- What we use about a drawing `H` in a closed disc `Δ` and a drawing `J` that extends it. -/
structure Frame (H J : Drawing S) (Δ : Set S) (a : S) : Prop where
  disc : IsClosedDisc Δ
  bd : subBd Δ ⊆ J.U
  Usub : H.U ⊆ Δ
  normal : H.U ∩ subBd Δ ⊆ H.V
  Vsub : H.V ⊆ J.V
  Esub : H.E ⊆ J.E
  rest : J.U ∩ (Δ \ subBd Δ) ⊆ H.U
  conn : IsPreconnected (Δ ∪ J.U)
  outside : a ∉ Δ
  outer : IsPreconnected Δᶜ
  rigid : IsRigidIn H Δ

variable {H J Γ' : Drawing S} {Δ : Set S} {a : S}

theorem Frame.U_subset (f : Frame H J Δ a) : H.U ⊆ J.U := by
  intro x hx
  rw [Drawing.U_eq] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (f.Vsub hx)
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨e, f.Esub he, hxe⟩)

omit [T2Space S] in
/-- A point of an edge of `J` is not a vertex of `J`. -/
theorem edge_notMem_V {e : Set S} (he : e ∈ J.E) {x : S} (hx : x ∈ e) : x ∉ J.V := he.2.1 hx |>.2

theorem Frame.U_inter_V (f : Frame H J Δ a) {x : S} (hx : x ∈ H.U) (hxV : x ∈ J.V) : x ∈ H.V := by
  by_contra hn
  obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hx hn
  exact edge_notMem_V (f.Esub he) hxe hxV

omit [T2Space S] in
/-- A closed disc with boundary in the interior of `Δ`, and inside `Δ`, misses the boundary of `Δ`.
-/
theorem disc_misses_bd (_hS : IsClosedSurface S) {D : Set S} (hD : subBd D ⊆ Δ \ subBd Δ)
    (_hclosed : IsClosed D) (hDΔ : D ⊆ Δ) : Disjoint D (subBd Δ) := by
  refine disjoint_left.mpr fun x hxD hxb => ?_
  have hxfr : x ∉ frontier D := by
    rw [← subBd_eq_frontier]
    exact fun h' => (hD h').2 hxb
  have hxi : x ∈ interior D := by
    by_contra hn
    exact hxfr ⟨subset_closure hxD, hn⟩
  have : x ∈ interior Δ := interior_mono hDΔ hxi
  rw [subBd_eq_frontier] at hxb
  exact hxb.2 this

/-- **`J` is 2-cell.** -/
theorem Frame.twoCell [ConnectedSpace S] (f : Frame H J Δ a) (hS : IsClosedSurface S)
  (hsph : IsSphere S) :
    (PaintingOrDrawing.drawing J).IsTwoCell := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine ⟨inferInstance, fun r hr => ?_⟩
  have hr' : r ∈ J.R := hr
  have hpre := region_isPreconnected hr'
  have hne : r.Nonempty := region_nonempty hr'
  have hfr : Disjoint r (subBd Δ) :=
    disjoint_left.mpr fun x hx hxb => region_subset hr' hx (f.bd hxb)
  have hbdne : (subBd Δ).Nonempty := by
    rw [subBd_eq_frontier]
    exact nonempty_frontier_iff.mpr ⟨f.disc.isPathConnected.nonempty,
      fun h' => f.outside (h' ▸ mem_univ a)⟩
  refine isOpenDisc_of_bound hS (region_isOpen hr') ⟨hne, hpre⟩ ?_ fun F hFr hF => ?_
  · obtain ⟨x, hx⟩ := hbdne
    exact fun h' => region_subset hr' (h' ▸ mem_univ x) (f.bd hx)
  have hFU : Disjoint F J.U := disjoint_left.mpr fun x hx hxU => region_subset hr' (hFr hx) hxU
  have hdisc := subset_or_disjoint_of_frontier f.disc.isClosed hpre
    (by rwa [← subBd_eq_frontier])
  rcases hdisc with hrΔ | hrΔ
  · have hFH : F ∩ H.U = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      exact disjoint_left.mp hFU hx.1 (f.U_subset hx.2)
    have hFV : F ∩ H.V = ∅ := eq_empty_of_subset (inter_subset_inter_right F H.V_subset_U) hFH
    obtain ⟨D, hDΔ, hd, hbd, hcases⟩ :=
      f.rigid F (hFr.trans hrΔ) hF (by rw [hFH]; exact empty_subset _)
      (by rw [hFV, ncard_empty]; omega)
    have hDH : D ∩ H.U ⊆ F := by
      rcases hcases with h₁ | ⟨u, v, huv, hc, -⟩
      · exact h₁
      · have h₁ : (F ∩ H.V).ncard = 2 := by rw [hc, ncard_pair huv]
        rw [hFV, ncard_empty] at h₁
        omega
    have hbdin : subBd D ⊆ Δ \ subBd Δ := fun x hx => by
      have hxF : x ∈ F := hbd ▸ hx
      exact ⟨hrΔ (hFr hxF), disjoint_left.mp hfr (hFr hxF)⟩
    have hDb := disc_misses_bd hS hbdin hd.isClosed hDΔ
    have hDJ : Disjoint D J.U := by
      refine disjoint_left.mpr fun x hxD hxU => ?_
      have hxH : x ∈ H.U := f.rest ⟨hxU, hDΔ hxD, disjoint_left.mp hDb hxD⟩
      exact disjoint_left.mp hFU (hDH ⟨hxD, hxH⟩) hxU
    have hbdF : discBd D = F := (IsClosedDisc.subBd_eq_discBd hS hd).symm.trans hbd
    obtain ⟨x, hx⟩ := id hF |> fun ⟨φ⟩ => (⟨(φ 1).1, (φ 1).2⟩ : ∃ x, x ∈ F)
    have hxD : x ∈ D := Surface.discBd_subset D (hbdF.symm ▸ hx)
    exact ⟨D, subset_region hr' hd.isPathConnected.isConnected.isPreconnected hDJ hxD (hFr hx), hd,
      hbdF⟩
  · have hT : Disjoint (Δ ∪ J.U) F := by
      refine disjoint_left.mpr ?_
      rintro x (hx | hx) hxF
      · exact disjoint_left.mp hrΔ (hFr hxF) hx
      · exact disjoint_left.mp hFU hxF hx
    obtain ⟨D, hd, hbdF, hdis⟩ := exists_disc_missing hS hsph hF f.conn hT
    have hDJ : Disjoint D J.U := hdis.mono_right subset_union_right
    obtain ⟨x, hx⟩ := id hF |> fun ⟨φ⟩ => (⟨(φ 1).1, (φ 1).2⟩ : ∃ x, x ∈ F)
    have hxD : x ∈ D := Surface.discBd_subset D (hbdF.symm ▸ hx)
    exact ⟨D, subset_region hr' hd.isPathConnected.isConnected.isPreconnected hDJ hxD (hFr hx), hd,
      hbdF⟩

/-- The facts on a radial drawing `Γ'` of `J` that we use. -/
structure Rad (J Γ' : Drawing S) : Prop where
  cap : J.U ∩ Γ'.U = J.V
  vsub : J.V ⊆ Γ'.V
  facts : RegionFacts (PaintingOrDrawing.drawing J) Γ'

/-- The regions of `Γ'` that hold an edge of `A`. -/
def tiles (Γ' : Drawing S) (A : Set (Set S)) : Set (Set S) := {s | s ∈ Γ'.R ∧ ∃ e ∈ A, e ⊆ s}

omit [T2Space S] in
theorem tiles_subset (A : Set (Set S)) : tiles Γ' A ⊆ Γ'.R := fun _ h => h.1

omit [T2Space S] in
theorem Rad.edge_off (r : Rad J Γ') {e : Set S} (he : e ∈ J.E) : Disjoint e Γ'.U := by
  refine disjoint_left.mpr fun x hx hxU => ?_
  have : x ∈ J.U ∩ Γ'.U := ⟨J.closure_subset_U he (subset_closure hx), hxU⟩
  rw [r.cap] at this
  exact edge_notMem_V he hx this

omit [T2Space S] in
/-- A point of `J` in a region of `Γ'` lies on the edge of that region. -/
theorem Rad.mem_edge (r : Rad J Γ') {e s : Set S} (he : e ∈ J.E) (hs : s ∈ Γ'.R) (hes : e ⊆ s)
    {x : S} (hx : x ∈ s) (hxU : x ∈ J.U) : x ∈ e := by
  have hxV : x ∉ J.V := fun h' => region_subset hs hx (Γ'.V_subset_U (r.vsub h'))
  obtain ⟨g, hg, hxg⟩ := J.exists_edge_of_mem hxU hxV
  have hgs : g ⊆ s := subset_region hs hg.2.2.1.isConnected.isPreconnected (r.edge_off hg) hxg hx
  have := r.facts.2.1 s hs g hg e he hgs hes
  exact this ▸ hxg

omit [T2Space S] in
/-- Each edge of `J` lies in a region of `Γ'`. -/
theorem Rad.exists_tile (r : Rad J Γ') {e : Set S} (he : e ∈ J.E) : ∃ s ∈ Γ'.R, e ⊆ s := by
  obtain ⟨p, hp⟩ := he.1
  have hpU : p ∉ Γ'.U := disjoint_left.mp (r.edge_off he) hp
  obtain ⟨s, hs, hps⟩ := exists_region_of_notMem hpU
  exact ⟨s, hs, subset_region hs he.2.2.1.isConnected.isPreconnected (r.edge_off he) hp hps⟩

/-- An edge of `J` with a point in the interior of `Δ` is an edge of `H`. -/
theorem Frame.mem_E (f : Frame H J Δ a) {g : Set S} (hg : g ∈ J.E) {q : S} (hq : q ∈ g)
    (hqΔ : q ∈ Δ) (hqb : q ∉ subBd Δ) : g ∈ H.E := by
  have hqU : q ∈ J.U := J.closure_subset_U hg (subset_closure hq)
  have hqH : q ∈ H.U := f.rest ⟨hqU, hqΔ, hqb⟩
  have hqV : q ∉ H.V := fun h' => edge_notMem_V hg hq (f.Vsub h')
  obtain ⟨g', hg', hqg'⟩ := H.exists_edge_of_mem hqH hqV
  rw [J.edge_eq_of_mem hg (f.Esub hg') hq hqg']
  exact hg'

/-- The closure of a region of `Γ'` that holds an edge of `H` lies in `Δ`. -/
theorem Frame.tile_sub (f : Frame H J Δ a) (r : Rad J Γ') {e s : Set S} (he : e ∈ H.E)
    (hs : s ∈ Γ'.R) (hes : e ⊆ s) : closure s ⊆ Δ := by
  have hd : Disjoint s (frontier Δ) := by
    rw [← subBd_eq_frontier]
    refine disjoint_left.mpr fun x hx hxb => ?_
    have hxe := r.mem_edge (f.Esub he) hs hes hx (f.bd hxb)
    have hxH : x ∈ H.U := H.closure_subset_U he (subset_closure hxe)
    exact edge_notMem_V he hxe (f.normal ⟨hxH, hxb⟩)
  have hsp : IsPreconnected s := region_isPreconnected hs
  rcases subset_or_disjoint_of_frontier f.disc.isClosed hsp hd with h₁ | h₁
  · exact closure_minimal h₁ f.disc.isClosed
  · obtain ⟨p, hp⟩ := he.1
    exact absurd (f.Usub (H.closure_subset_U he (subset_closure hp))) (disjoint_left.mp h₁ (hes hp))

/-- A vertex of `J` on `N(Z)` meets an edge of `A` and an edge outside `A`. -/
theorem Rad.mem_bdry (r : Rad J Γ') (hS : IsClosedSurface S) {A : Set (Set S)} {v : S}
    (hvJ : v ∈ J.V) (hv : v ∈ (boundaryDrawing Γ' (tiles Γ' A)).V) (hA : A ⊆ J.E) :
    v ∈ Whitney.bdry J.toGraph A := by
  obtain ⟨⟨t, ht, -, -, hvt⟩, t', ht', -, -, hvt'⟩ := (mem_boundaryDrawing_V hS).mp hv
  obtain ⟨htR, e, heA, het⟩ := ht
  obtain ⟨g, hg, hgt⟩ := r.facts.1 t' ht'.1
  have hgA : g ∉ A := fun h' => ht'.2 ⟨ht'.1, g, h', hgt⟩
  exact ⟨⟨e, heA, inc_of_mem_closure (hA heA)
      (r.facts.2.2 t htR e (hA heA) het v hvJ hvt) hvJ⟩,
    ⟨g, ⟨hg, hgA⟩, inc_of_mem_closure hg (r.facts.2.2 t' ht'.1 g hg hgt v hvJ hvt') hvJ⟩⟩

/-- An `O`-arc in `N(Z)`, for `Z` the regions of a set of edges, is normal for `H`, and its vertices
are in the boundary of the set. -/
theorem Frame.normal_arc (f : Frame H J Δ a) (r : Rad J Γ') (hS : IsClosedSurface S)
    {A : Set (Set S)} (hA : A ⊆ H.E) {F : Set S}
    (hFN : F ⊆ (boundaryDrawing Γ' (tiles Γ' A)).U) :
    F ∩ H.U ⊆ H.V ∧ F ∩ H.V ⊆ Whitney.bdry J.toGraph A := by
  have hNs : (boundaryDrawing Γ' (tiles Γ' A)).IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  have hJV : ∀ x ∈ F, x ∈ H.U → x ∈ J.V := fun x hx hxU => by
    have : x ∈ J.U ∩ Γ'.U := ⟨f.U_subset hxU, hNs.U_subset (hFN hx)⟩
    rwa [r.cap] at this
  refine ⟨fun x hx => f.U_inter_V hx.2 (hJV x hx.1 hx.2), fun x hx => ?_⟩
  have hxJ := f.Vsub hx.2
  have hxN : x ∈ (boundaryDrawing Γ' (tiles Γ' A)).V := by
    rcases hFN hx.1 with h₁ | h₁
    · exact h₁
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h₁
      exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, r.vsub hxJ⟩)
  exact r.mem_bdry hS hxJ hxN (hA.trans f.Esub)

/-- The boundary of the regions of edges of `H` lies in `Δ`. -/
theorem Frame.N_sub (f : Frame H J Δ a) (r : Rad J Γ') (hS : IsClosedSurface S)
    {A : Set (Set S)} (hA : A ⊆ H.E) : (boundaryDrawing Γ' (tiles Γ' A)).U ⊆ Δ := by
  intro x hx
  rw [Drawing.U_eq] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨t, ⟨htR, e, he, het⟩, -, -, hxt⟩, -⟩ := (mem_boundaryDrawing_V hS).mp hx
    exact f.tile_sub r (hA he) htR het hxt
  · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
    obtain ⟨⟨t, ⟨htR, e, he, het⟩, hinc⟩, -⟩ := mem_boundaryDrawing_E.mp hg
    have hgc := edge_subset_closure_of_incident hS hinc.1 hinc.2.1 hinc.2.2
    exact f.tile_sub r (hA he) htR het (closure_minimal hgc isClosed_closure hxg)

/-- **Each edge of a small set lies in a dial that holds a path.** Here the set `A` of edges of `H`
has
at most two vertices that meet both `A` and another edge of `J`. -/
theorem exists_dial_of_edge [ConnectedSpace S] (f : Frame H J Δ a) (r : Rad J Γ')
    (hS : IsClosedSurface S) (hsph : IsSphere S) {A : Set (Set S)} (hA : A ⊆ H.E)
    (hb : (Whitney.bdry J.toGraph A).ncard ≤ 2) (hfin : (Whitney.bdry J.toGraph A).Finite)
    {e : Set S} (he : e ∈ A) :
    ∃ F D x y, IsOArc F ∧ F ⊆ (boundaryDrawing Γ' (tiles Γ' A)).U ∧ D ⊆ Δ ∧ IsClosedDisc D ∧
      discBd D = F ∧ e ⊆ D ∧ x ≠ y ∧ F ∩ H.V = {x, y} ∧ (H.interSet D).IsPathBetween x y ∧
      F ∩ H.U ⊆ H.V ∧ F ∩ H.V ⊆ Whitney.bdry J.toGraph A := by
  classical
  set N := boundaryDrawing Γ' (tiles Γ' A) with hN
  have hNΔ : N.U ⊆ Δ := f.N_sub r hS hA
  have hdial : ∀ F, IsOArc F → F ⊆ N.U → ∃ D, D ⊆ Δ ∧ IsDial H F D := by
    intro F hF hFN
    obtain ⟨h₁, h₂⟩ := f.normal_arc r hS hA hFN
    exact f.rigid F (hFN.trans hNΔ) hF h₁ ((ncard_le_ncard h₂ hfin).trans hb)
  let Q : Set S := N.U ∪ ⋃₀ {D | D ⊆ Δ ∧ ∃ F, IsOArc F ∧ F ⊆ N.U ∧ IsDial H F D}
  have hQΔ : Q ⊆ Δ := union_subset hNΔ (sUnion_subset fun _ h => h.1)
  obtain ⟨p, hp⟩ := (hA he).1
  have heJ := f.Esub (hA he)
  have hpΓ : p ∉ Γ'.U := disjoint_left.mp (r.edge_off heJ) hp
  obtain ⟨s, hs, hes⟩ := r.exists_tile heJ
  have hsZ : s ∈ tiles Γ' A := ⟨hs, e, he, hes⟩
  have hNs : N.IsSubdrawing Γ' := Drawing.span_isSubdrawing Γ' _ _
  have hpN : p ∉ N.U := fun h' => hpΓ (hNs.U_subset h')
  have hpQ : p ∈ Q := by
    by_contra hpQ
    have hreg := same_region_of_discs hS hsph (fun h' => f.outside (hQΔ h')) hpQ _ N rfl
      subset_union_left (fun F hF hFN => by
        obtain ⟨D, hDΔ, hd⟩ := hdial F hF hFN
        exact ⟨D, hd.1, fun y hy => Or.inr ⟨D, ⟨hDΔ, F, hF, hFN, hd⟩, hy⟩,
          (IsClosedDisc.subBd_eq_discBd hS hd.1).symm.trans hd.2.1⟩)
    obtain ⟨t, ht, hat, hpt⟩ := hreg
    refine not_same_side hS (tiles_subset A) hsZ (hes hp) (fun hh => ?_) ⟨t, ht, hat, hpt⟩
    obtain ⟨t', ⟨htR, e', he', het⟩, hat'⟩ := mem_iUnion₂.mp hh
    exact f.outside (f.tile_sub r (hA he') htR het hat')
  rcases hpQ with hpQ | ⟨D, ⟨hDΔ, F, hF, hFN, hd⟩, hpD⟩
  · exact absurd hpQ hpN
  obtain ⟨hdisc, hbd, hcases⟩ := hd
  obtain ⟨h₁, h₂⟩ := f.normal_arc r hS hA hFN
  have heF : Disjoint e F := disjoint_left.mpr fun x hx hxF =>
    edge_notMem_V (hA he) hx (h₁ ⟨hxF, H.closure_subset_U (hA he) (subset_closure hx)⟩)
  have hfr : frontier D = F := by rw [← subBd_eq_frontier, hbd]
  have heD : e ⊆ D := by
    rcases subset_or_disjoint_of_frontier hdisc.isClosed (hA he).2.2.1.isConnected.isPreconnected
      (by rwa [hfr]) with h₃ | h₃
    · exact h₃
    · exact absurd hpD (disjoint_left.mp h₃ hp)
  rcases hcases with h₃ | ⟨x, y, hxy, hc, hpath⟩
  · exact absurd (h₃ ⟨hpD, H.closure_subset_U (hA he) (subset_closure hp)⟩)
      (disjoint_left.mp heF hp)
  · exact ⟨F, D, x, y, hF, hFN, hDΔ, hdisc, (IsClosedDisc.subBd_eq_discBd hS hdisc).symm.trans hbd,
      heD, hxy, hc, hpath, h₁, h₂⟩

end GraphMinor.GM14.Whitney
