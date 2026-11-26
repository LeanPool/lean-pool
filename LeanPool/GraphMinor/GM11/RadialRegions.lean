/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialCap

/-!
# The regions of a radial drawing

Let `Γ'` be a radial drawing of a 2-cell drawing `Γ` with an edge. Graph Minors XI (Section 3,
page 75) states without proof that every region of `Γ'` contains a unique edge of `Γ`. This file and
`RadialCorners.lean` prove it. We work in the union `H` of `Γ` and `Γ'`.

This file has the first steps: each vertex of `Γ` is an end of an edge of `Γ` (`exists_edge_at`),
and
it is joined by an edge of `Γ'` to the vertex `v_r` of every region `r` at it (`exists_spoke_at`).
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ Γ' : Drawing S} {e : Set S}

theorem radial_inter (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') :
    Γ.U ∩ Γ'.U = Γ.V := hrad.2.1

theorem radial_V (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') : Γ.V ⊆ Γ'.V :=
  hrad.2.2.1

theorem radial_meet (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') :
    Γ.U ∩ Γ'.U ⊆ Γ.V ∩ Γ'.V := by
  rw [radial_inter hrad]
  exact fun x hx => ⟨hx, radial_V hrad hx⟩

/-- The union `H` of a drawing and a radial drawing of it. -/
def radialUnion (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') : Drawing S :=
  Γ.glue Γ' (radial_meet hrad)

variable (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')

include hrad

theorem radialUnion_U : (radialUnion hrad).U = Γ.U ∪ Γ'.U := rfl

theorem radialUnion_V : (radialUnion hrad).V = Γ'.V := union_eq_right.mpr (radial_V hrad)

theorem radialUnion_E : (radialUnion hrad).E = Γ.E ∪ Γ'.E := Drawing.glue_E _

/-- An edge of `Γ` misses `U(Γ')`. -/
theorem edge_disjoint (he : e ∈ Γ.E) : Disjoint e Γ'.U := by
  refine disjoint_left.mpr fun x hx hx' => ?_
  have : x ∈ Γ.V := radial_inter hrad ▸ ⟨Γ.closure_subset_U he (subset_closure hx), hx'⟩
  exact edge_notMem_V he hx this

/-- An edge of `Γ'` misses `U(Γ)`. -/
theorem spoke_disjoint (he : e ∈ Γ'.E) : Disjoint e Γ.U := by
  refine disjoint_left.mpr fun x hx hx' => ?_
  have : x ∈ Γ.V := radial_inter hrad ▸ ⟨hx', Γ'.closure_subset_U he (subset_closure hx)⟩
  exact edge_notMem_V he hx (radial_V hrad this)

/-- The two ends of an edge of `Γ'`, and the region of `Γ` that contains the edge. -/
theorem spoke_ends (hS : IsClosedSurface S) (he : e ∈ Γ'.E) :
    ∃ v ∈ Γ.V, ∃ r ∈ Γ.R, ∃ w, w ∈ r ∧ w ∈ Γ'.V ∧ closure e ∩ Γ'.V = {v, w} ∧ e ⊆ r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨v, hv, w, ⟨hwV, hwn⟩, hcap⟩ := hrad.2.2.2.2.2.1 e he
  obtain ⟨r, hr, hwr⟩ := hrad.2.2.2.2.1 w ⟨hwV, hwn⟩
  have hwe : w ∈ closure e := by
    have : w ∈ closure e ∩ Γ'.V := by rw [hcap]; simp
    exact this.1
  have hrΓ : r ∈ Γ.R := hr
  obtain ⟨y, hyr, hye⟩ := mem_closure_iff.mp hwe r (region_isOpen hrΓ) hwr
  refine ⟨v, hv, r, hr, w, hwr, hwV, hcap, ?_⟩
  exact subset_region hrΓ he.2.2.1.isConnected.isPreconnected (spoke_disjoint hrad he) hye hyr

/-- The vertex of `Γ'` in a region of `Γ` is unique. -/
theorem hub_unique {r : Set S} (hr : r ∈ Γ.R) {c w : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (hw : w ∈ r)
    (hwV : w ∈ Γ'.V) : w = c :=
  (hrad.2.2.2.1 r hr).unique ⟨hw, hwV⟩ ⟨hc, hcV⟩

omit hrad in
/-- A vertex of `Γ'` in a region of `Γ` is not a vertex of `Γ`. -/
theorem notMem_V_of_mem_region {r : Set S} (hr : r ∈ Γ.R) {c : S} (hc : c ∈ r) : c ∉ Γ.V :=
  fun h => region_subset hr hc (Γ.V_subset_U h)

/-- **Every vertex of `Γ` is an end of an edge of `Γ`.** A vertex with no edge has a small closed
disc `D` around it, with `D` minus the vertex in a region `r`. The boundary of `D` bounds a closed
disc
in the open disc `r`. These two discs cover the surface, so `U(Γ)` is one point, against `E(Γ) ≠ ∅`.
This is why the paper excludes the case "`|V(Γ)| = 1` and `E(Γ) = ∅`". -/
theorem exists_edge_at [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    {x : S} (hx : x ∈ Γ.V) : ∃ e ∈ Γ.E, x ∈ closure e := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_contra hno
  push Not at hno
  let Bad : Set S := (Γ.V \ {x}) ∪ ⋃ e ∈ Γ.E, closure e
  have hBad : IsClosed Bad := (Γ.finite_V.subset sdiff_subset).isClosed.union
    (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
  have hxBad : x ∉ Bad := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h
      exact hno e he hxe
  obtain ⟨D, D', hD, hD', hxD', hD'D, hDO, hbdD⟩ :=
    exists_closedDisc_nbhd hS hBad.isOpen_compl hxBad
  have hbdU : Disjoint (discBd D) Γ.U := by
    refine disjoint_left.mpr fun y hy hyU => ?_
    have hyD : y ∈ D := discBd_subset D hy
    have hyx : y ≠ x := fun h => (hbdD ▸ hy).2 (h ▸ hxD')
    rw [Γ.U_eq] at hyU
    refine hDO hyD ?_
    rcases hyU with hyV | hyE
    · exact Or.inl ⟨hyV, hyx⟩
    · exact Or.inr hyE
  have hF := hD.isOArc_discBd
  have hbdne : (discBd D).Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨_, (φ 1).2⟩
  have hbdconn : IsPreconnected (discBd D) := by
    obtain ⟨φ⟩ := hF
    have : discBd D = range fun z => (φ z).1 := by
      ext y
      exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, by rintro ⟨z, rfl⟩; exact (φ z).2⟩
    rw [this]
    exact isPreconnected_range (by fun_prop)
  obtain ⟨y, hy⟩ := hbdne
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (disjoint_left.mp hbdU hy)
  have hsub : discBd D ⊆ r := subset_region hr hbdconn hbdU hy hyr
  obtain ⟨Δ, hΔr, hΔ, hb⟩ := exists_disc_in_openDisc (hrad.1.2 r hr) hF hsub
  have hxΔ : x ∉ Δ := fun h => region_subset hr (hΔr h) (Γ.V_subset_U hx)
  have hcov := cover_of_discBd_eq hS hD hΔ hb.symm fun h => hxΔ (h ▸ hD'D hxD')
  obtain ⟨e, he⟩ := hE
  obtain ⟨z, hz⟩ := he.1
  have hzU : z ∈ Γ.U := Γ.closure_subset_U he (subset_closure hz)
  rcases (hcov ▸ mem_univ z : z ∈ D ∪ Δ) with h | h
  · exact hDO h (Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hz⟩))
  · exact region_subset hr (hΔr h) hzU

variable [T2Space S]

omit [T2Space S] in
/-- A region of `H` lies in a region of `Γ`. -/
theorem exists_region_of_sub {p : Set S} (hp : p ∈ (radialUnion hrad).R) :
    ∃ r ∈ Γ.R, p ⊆ r := by
  obtain ⟨y, hy⟩ := region_nonempty hp
  have hyU : y ∉ Γ.U := fun h => region_subset hp hy (Or.inl h)
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
  refine ⟨r, hr, subset_region hr (region_isPreconnected hp) ?_ hy hyr⟩
  exact disjoint_left.mpr fun z hz h => region_subset hp hz (Or.inl h)

/-- If `x` is in the closure of a region of `Γ`, then it is in the closure of a region of `H` inside
that region. -/
theorem exists_sub_closure [ConnectedSpace S] (hS : IsClosedSurface S) {r : Set S} (hr : r ∈ Γ.R)
    {x : S} (hx : x ∈ closure r) :
    ∃ p ∈ (radialUnion hrad).R, p ⊆ r ∧ x ∈ closure p := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin := finite_R hS (radialUnion hrad)
  by_contra hno
  push Not at hno
  let Y : Set S := ⋃ p ∈ {p ∈ (radialUnion hrad).R | p ⊆ r}, closure p
  have hRfinite : {p ∈ (radialUnion hrad).R | p ⊆ r}.Finite := hfin.subset fun _ h => h.1
  have hY : IsClosed Y := hRfinite.isClosed_biUnion fun _ _ => isClosed_closure
  have hxY : x ∉ Y := by
    intro h
    obtain ⟨p, ⟨hp, hpr⟩, hxp⟩ := mem_iUnion₂.mp h
    exact hno p hp hpr hxp
  obtain ⟨y, hyW, hyr⟩ := mem_closure_iff.mp hx _ hY.isOpen_compl hxY
  obtain ⟨z, ⟨hzW, hzr⟩, hzU⟩ := exists_notMem_U (Γ := radialUnion hrad) hS
    (hY.isOpen_compl.inter (region_isOpen hr)) ⟨y, hyW, hyr⟩
  obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
  have hpr : p ⊆ r := by
    refine subset_region hr (region_isPreconnected hp) ?_ hzp hzr
    exact disjoint_left.mpr fun w hw h => region_subset hp hw (Or.inl h)
  exact hzW (mem_iUnion₂.mpr ⟨p, ⟨hp, hpr⟩, subset_closure hzp⟩)

omit [T2Space S] in
/-- The vertex of `Γ'` in `r` is in the closure of each region of `H` inside `r`. -/
theorem hub_mem_closure (hS : IsClosedSurface S) {r p : Set S} (hr : r ∈ Γ.R)
    (hp : p ∈ (radialUnion hrad).R) (hpr : p ⊆ r) {c : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) :
    c ∈ closure p := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  -- The set `p` is open in `r`, and not all of it, so `r` has a point in the frontier of `p`.
  have hpo : IsOpen p := region_isOpen hp
  have hcH : c ∈ (radialUnion hrad).U := Or.inr (Γ'.V_subset_U hcV)
  have hcp : c ∉ p := fun h => region_subset hp h hcH
  obtain ⟨q, hqr, hqcl, hqp⟩ : ∃ q ∈ r, q ∈ closure p ∧ q ∉ p := by
    by_contra hno
    push Not at hno
    have hclopen : r ⊆ p ∪ (closure p)ᶜ := fun y hy => by
      by_cases h : y ∈ closure p
      · exact Or.inl (hno y hy h)
      · exact Or.inr h
    obtain ⟨y, hy⟩ := region_nonempty hp
    have := (region_isPreconnected hr).subset_left_of_subset_union hpo isClosed_closure.isOpen_compl
      (disjoint_compl_right_iff_subset.mpr subset_closure) hclopen ⟨y, hpr hy, hy⟩
    exact hcp (this hc)
  have hqU : q ∈ (radialUnion hrad).U := by
    by_contra hqn
    obtain ⟨p', hp', hqp'⟩ := exists_region_of_notMem hqn
    obtain ⟨z, hz', hz⟩ := mem_closure_iff.mp hqcl p' (region_isOpen hp') hqp'
    exact hqp (region_eq_of_mem hp' hp hz' hz ▸ hqp')
  rcases hqU with hq | hq
  · exact (region_subset hr hqr hq).elim
  rw [Γ'.U_eq] at hq
  rcases hq with hqV | hqE
  · rw [← hub_unique hrad hr hc hcV hqr hqV]
    exact hqcl
  by_cases hqV : q ∈ Γ'.V
  · rw [← hub_unique hrad hr hc hcV hqr hqV]
    exact hqcl
  obtain ⟨e, he, hqe'⟩ := mem_iUnion₂.mp hqE
  have hqe : q ∈ e := Γ'.closure_diff_V he ▸ ⟨hqe', hqV⟩
  have heH : e ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inr he
  have hsub := edge_subset_closure_of_incident hS heH hp ⟨q, hqe, hqcl⟩
  obtain ⟨v, hv, r', hr', w, hwr, hwV, hcap, hsubr⟩ := spoke_ends hrad hS he
  have hr'r : r' = r := region_eq_of_mem hr' hr (hsubr hqe) hqr
  subst hr'r
  have hwe : w ∈ closure e := by
    have : w ∈ closure e ∩ Γ'.V := by rw [hcap]; simp
    exact this.1
  rw [← hub_unique hrad hr hc hcV hwr hwV]
  exact closure_minimal hsub isClosed_closure hwe

/-- Condition (v) of a radial drawing, for a chord of `r` from `c` to a vertex `x` of `Γ`. -/
theorem parallel_of_line (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) {r K : Set S} (hr : r ∈ Γ.R)
    {c x : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (hx : x ∈ Γ.V) (hK : IsLineWithEnds K c x) (hcx : c ≠ x)
    (hKr : K \ {c, x} ⊆ r) (hKU : Disjoint (K \ {c, x}) Γ'.U) :
    ∃ h ∈ Γ'.E, closure h ∩ Γ'.V = {x, c} ∧ ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ r ∪ {x} ∧
      subBd Δ = closure h ∪ K := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine exists_parallel_spoke (Γ := PaintingOrDrawing.drawing Γ) hrad.2 hmax hr hc hcV hx hK hcx
    hKr hKU
    (disjoint_left.mpr fun y hy => region_subset hr hy) ?_
  intro r₁ r₂ h₁ h₂ y hy hy'
  exact region_eq_of_mem h₁ h₂ hy hy'

/-- **Each vertex of `Γ` at a region `r` is joined by an edge of `Γ'` to the vertex of `r`.** -/
theorem exists_spoke_at (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') [ConnectedSpace S]
    (hS : IsClosedSurface S) (hE : Γ.E.Nonempty) {r : Set S}
    (hr : r ∈ Γ.R) {c x : S} (hc : c ∈ r) (hcV : c ∈ Γ'.V) (hx : x ∈ Γ.V) (hxr : x ∈ closure r) :
    ∃ h ∈ Γ'.E, closure h ∩ Γ'.V = {x, c} := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hne : Nonempty S := ⟨c⟩
  have hxU : x ∉ r := fun h => region_subset hr h (Γ.V_subset_U hx)
  have hcx : c ≠ x := fun h => hxU (h ▸ hc)
  have hcxU : x ≠ c := hcx.symm
  obtain ⟨e₀, he₀, hxe₀⟩ := exists_edge_at hrad hS hE hx
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  have he₀H : e₀ ∈ (radialUnion hrad).E := by
    rw [radialUnion_E]
    exact Or.inl he₀
  have hxH : x ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact radial_V hrad hx
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  obtain ⟨b, hb⟩ := exists_end_eq hγ he₀H hxH hxe₀
  have hhalf : (halfEdges (radialUnion hrad) γ x).Nonempty := ⟨(e₀, b), he₀H, hb⟩
  have hrpath : IsPathConnected r :=
    isPathConnected_of_isOpen hS (region_isOpen hr) (region_isPreconnected hr) ⟨c, hc⟩
  by_cases hchalf : (halfEdges (radialUnion hrad) γ c).Nonempty
  · obtain ⟨p, hp, hpr, hxp⟩ := exists_sub_closure hrad hS hr hxr
    have hcp := hub_mem_closure hrad hS hr hp hpr hc hcV
    obtain ⟨g₁, hg₁, h₁0, h₁⟩ := exists_access hS _ hγ hxH hhalf hp hxp
    obtain ⟨g₂, hg₂, h₂0, h₂⟩ := exists_access hS _ hγ hcH hchalf hp hcp
    obtain ⟨y, hy⟩ := region_nonempty hp
    have hppath : IsPathConnected p :=
      isPathConnected_of_isOpen hS (region_isOpen hp) (region_isPreconnected hp) ⟨y, hy⟩
    obtain ⟨u, hu, hui, hu0, hu1, hup, -⟩ :=
      exists_chord hppath hcxU (fun h => hxU (hpr h)) hg₁ hg₂ h₁0 h₂0 h₁ h₂
    have hline : IsLineWithEnds (range u) c x := by
      have := isLine_range hu hui
      rw [hu0, hu1] at this
      exact GraphMinor.GM11.IsLineWithEnds.symm this
    have hsubp : range u \ {c, x} ⊆ p := by
      rintro _ ⟨⟨t, rfl⟩, hn⟩
      exact hup t (fun h => hn (Or.inr (by rw [h, hu0]; rfl))) fun h => hn (Or.inl (by rw [h, hu1]))
    obtain ⟨h, hh, hcap, -⟩ := parallel_of_line hrad hmax hS hr hc hcV hx hline hcx
      (hsubp.trans hpr)
      (disjoint_left.mpr fun z hz hzU => region_subset hp (hsubp hz) (Or.inr hzU))
    exact ⟨h, hh, hcap⟩
  · -- There is no edge of `Γ'` at `c`, so `U(Γ')` meets `r` only in `c`.
    have hrU : ∀ y ∈ r, y ∈ Γ'.U → y = c := by
      intro y hy hyU
      by_cases hyV : y ∈ Γ'.V
      · exact hub_unique hrad hr hc hcV hy hyV
      rw [Γ'.U_eq] at hyU
      rcases hyU with h | hyE
      · exact (hyV h).elim
      obtain ⟨g, hg, hyg'⟩ := mem_iUnion₂.mp hyE
      have hyg : y ∈ g := Γ'.closure_diff_V hg ▸ ⟨hyg', hyV⟩
      obtain ⟨v, -, r', hr', w, hwr, hwV, hcap, hsubr⟩ := spoke_ends hrad hS hg
      have hr'r : r' = r := region_eq_of_mem hr' hr (hsubr hyg) hy
      subst hr'r
      have hwc : w = c := hub_unique hrad hr hc hcV hwr hwV
      have hcg : c ∈ closure g := by
        have : w ∈ closure g ∩ Γ'.V := by rw [hcap]; simp
        exact hwc ▸ this.1
      have hgH : g ∈ (radialUnion hrad).E := by
        rw [radialUnion_E]
        exact Or.inr hg
      obtain ⟨b', hb'⟩ := exists_end_eq hγ hgH hcH hcg
      exact (hchalf ⟨(g, b'), hgH, hb'⟩).elim
    obtain ⟨γ₀, hγ₀⟩ := exists_edgePar Γ
    obtain ⟨b₀, hb₀⟩ := exists_end_eq hγ₀ he₀ hx hxe₀
    obtain ⟨g₁, hg₁, h₁0, h₁⟩ := exists_access hS Γ hγ₀ hx ⟨(e₀, b₀), he₀, hb₀⟩ hr hxr
    obtain ⟨u, hu, hui, hu0, hu1, hup, -⟩ := exists_chord_to_point hrpath hxU hc hg₁ h₁0 h₁
    have hline : IsLineWithEnds (range u) c x := by
      have := isLine_range hu hui
      rw [hu0, hu1] at this
      exact GraphMinor.GM11.IsLineWithEnds.symm this
    have hsubp : range u \ {c, x} ⊆ r := by
      rintro _ ⟨⟨t, rfl⟩, hn⟩
      exact hup t fun h => hn (Or.inr (by rw [h, hu0]; rfl))
    obtain ⟨h, hh, hcap, -⟩ := parallel_of_line hrad hmax hS hr hc hcV hx hline hcx hsubp
      (disjoint_left.mpr fun z hz hzU => hz.2 (Or.inl (hrU z (hsubp hz) hzU)))
    exact ⟨h, hh, hcap⟩

omit hrad [T2Space S] in
/-- A region of a 2-cell drawing with an edge has a vertex in its closure. -/
theorem exists_vertex_at_region [ConnectedSpace S] (hS : IsClosedSurface S) (hE : Γ.E.Nonempty)
    {r : Set S} (hr : r ∈ Γ.R) : ∃ x ∈ Γ.V, x ∈ closure r := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hT2 : T2Space S := hS.2.1
  obtain ⟨e, he⟩ := hE
  obtain ⟨z, hz⟩ := he.1
  have hzU : z ∈ Γ.U := Γ.closure_subset_U he (subset_closure hz)
  have hro := region_isOpen hr
  have hrne := region_nonempty hr
  obtain ⟨q, hq⟩ : (frontier r).Nonempty := by
    by_contra hn
    have hempty := not_nonempty_iff_eq_empty.mp hn
    have hcl : IsClopen r := isClopen_iff_frontier_eq_empty.mpr hempty
    have huniv := hcl.eq_univ hrne
    exact region_subset hr (huniv ▸ mem_univ z) hzU
  have hqcl : q ∈ closure r := frontier_subset_closure hq
  have hqr : q ∉ r := fun h => by
    rw [hro.frontier_eq] at hq
    exact hq.2 h
  have hqU : q ∈ Γ.U := by
    by_contra hqn
    obtain ⟨r', hr', hqr'⟩ := exists_region_of_notMem hqn
    obtain ⟨y, hy', hy⟩ := mem_closure_iff.mp hqcl r' (region_isOpen hr') hqr'
    exact hqr (region_eq_of_mem hr' hr hy' hy ▸ hqr')
  by_cases hqV : q ∈ Γ.V
  · exact ⟨q, hqV, hqcl⟩
  rw [Γ.U_eq] at hqU
  rcases hqU with h | hqE
  · exact (hqV h).elim
  obtain ⟨g, hg, hqg'⟩ := mem_iUnion₂.mp hqE
  have hqg : q ∈ g := Γ.closure_diff_V hg ▸ ⟨hqg', hqV⟩
  have hsub := edge_subset_closure_of_incident hS hg hr ⟨q, hqg, hqcl⟩
  have hne : Nonempty S := ⟨q⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  exact ⟨_, end_mem_V hγ hg false, closure_minimal hsub isClosed_closure
    (end_mem_closure hγ hg false)⟩

end GraphMinor.GM11
