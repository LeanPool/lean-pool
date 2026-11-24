/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12c

/-!
# Graph Minors XIX, Section 12: the ring around a hub

We want a circuit of `Γ*` around the hub `H`, whose vertices of `Γ` are about `ρ` steps from `H`.
The paper builds it by
`½ρ` applications of Theorem 5.2 of XIV, along circuits of `sk(Γ)`. We use one application, to the
*ring*: the drawing
of the edges of `Γ*` from a vertex of `Γ` that is `ρ`-near `H` to a vertex of `R*` that is not `(ρ -
1)`-near `H`.

Write `ρ = k + 3`. The *zone* holds the vertices of `Γ` that are `(k + 1)`-near `H`, and the regions
of `Γ` whose centres
are `(k + 2)`-near. Theorem 5.2 needs that each region of the ring whose closure meets the zone lies
in the disc `Λ` of
(7.1). To see this, call a region of `Γ*` *good* if it has a centre that is `(k + 2)`-near as a
corner. Then a region of
`Γ*` that is good and a region that is not cannot share a point off the ring, by the corner lemma.
So the good regions
fill the region of the ring.

The caller may add a closed set `Y` to the zone. In (12.4) this `Y` holds an inside of a circuit
round a pole, whose cuff
may be far from `H` in steps of `Γ*`. The main result is `TangleDatum.ring_region_subset`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable (D : TangleDatum cap χ) (H : Drawing Shat) (k : ℕ) (Y : Set Shat)

/-- The zone: the vertices of `Γ` that are `(k + 1)`-near `H`, and the regions of `Γ` with a `(k +
2)`-near centre. -/
noncomputable def nearZone : Set Shat :=
  {x | x ∈ D.P.Γ.hatV cap ∧ D.IsNear H (k + 1) x} ∪
    ⋃ w ∈ {w | w ∈ D.rad.Rstar ∧ D.IsNear H (k + 2) w}, D.rad.regionOf w

/-- A region of `Γ*` is good if it lies in `Y` or has a `(k + 2)`-near centre as a corner. -/
def IsGood (q : Set Shat) : Prop :=
  q ⊆ Y ∨ ∃ w ∈ D.rad.Rstar, D.IsNear H (k + 2) w ∧ (q ∩ D.rad.regionOf w).Nonempty

/-- The edges of the ring. -/
def ringEdges : Set (Set Shat) :=
  {g | g ∈ D.rad.G.E ∧ ∃ v ∈ D.P.Γ.V, ∃ t ∈ D.rad.Rstar, closure g ∩ D.rad.G.V = {cap.emb v, t} ∧
    D.IsNear H (k + 3) (cap.emb v) ∧ ¬ D.IsNear H (k + 2) t ∧ ¬ g ⊆ Y}

/-- The ring: the subdrawing of `Γ*` formed by the edges of the ring. -/
noncomputable def ring : Drawing Shat := D.rad.G.span ∅ (ringEdges D H k Y)

/-- The conditions on the set `Y`. Each point of its frontier is in the zone, and a region of `Γ*`
that meets `Y` lies
in `Y`. The last condition handles the disc edges of `Γ` with a vertex on `bd(Σ)`, to which the
fifth condition of "fit"
says nothing: if such an edge has a near corner, then its region lies in `Y` or all its ends are
near. -/
structure IsZoneSet : Prop where
  closed : IsClosed Y
  meet : ∀ q ∈ D.rad.G.R, (q ∩ Y).Nonempty → q ⊆ Y
  frontier_sub : frontier Y ⊆ nearZone D H k
  cuff : ∀ q ∈ D.rad.G.R, ∀ e ∈ D.P.Γ.E, cap.emb '' e ⊆ q → (tilde e).ncard = 3 →
    (closure e ∩ bd S).Nonempty →
    ∀ w ∈ D.rad.Rstar, D.IsNear H (k + 2) w → (q ∩ D.rad.regionOf w).Nonempty →
      q ⊆ Y ∨ ∀ v ∈ tilde e, D.IsNear H (k + 3) (cap.emb v)

variable {D H k Y}

omit [T2Space S] in
theorem mem_ring_U {x : Shat} : x ∈ (ring D H k Y).U ↔ ∃ g ∈ ringEdges D H k Y, x ∈ closure g := by
  change x ∈ D.rad.G.spanU ∅ (ringEdges D H k Y) ↔ _
  constructor
  · rintro ((h | h) | h)
    · exact absurd h.1 (notMem_empty x)
    · obtain ⟨g, hg, hx⟩ := mem_iUnion₂.mp h
      exact ⟨g, hg.1, hx.1⟩
    · obtain ⟨g, hg, hx⟩ := mem_iUnion₂.mp h
      exact ⟨g, hg.1, hx⟩
  · rintro ⟨g, hg, hx⟩
    exact .inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hg.1⟩, hx⟩)

omit [T2Space Shat] in
/-- A point of the zone on an edge of `Γ*` lies in the region of the near centre of this edge. -/
theorem near_of_mem_edge {g : Set Shat} (hg : g ∈ D.rad.G.E) {t : Shat} {v : Shat}
  (ht : t ∈ D.rad.Rstar)
    (hv : v ∈ D.P.Γ.hatV cap) (hcap : closure g ∩ D.rad.G.V = {v, t}) {p : Shat} (hpg : p ∈ g)
    (hp : p ∈ nearZone D H k) : D.IsNear H (k + 2) t := by
  rcases hp with ⟨hpV, -⟩ | hp
  · exact absurd (D.rad.isPreRadial.2.1 hpV) (hg.2.1 hpg).2
  · obtain ⟨w, ⟨hw, hN⟩, hpw⟩ := mem_iUnion₂.mp hp
    have hc := D.rad.center_mem_closure χ.isSurface hg (D.rad.regionOf_mem hw).1 ⟨p, hpg, hpw⟩
      (D.rad.regionOf_mem hw).2 hw.1
    have hm : w ∈ closure g ∩ D.rad.G.V := ⟨hc, hw.1⟩
    rw [hcap] at hm
    rcases hm with rfl | rfl
    · exact absurd hv hw.2
    · exact hN

omit [T2Space Shat] in
/-- An edge of `Γ*` with an end in `R*` that is not near, and not in `Y`, misses `Y`. -/
theorem IsZoneSet.disjoint_edge (hY : IsZoneSet D H k Y) {g : Set Shat}
  (hg : g ∈ D.rad.G.E) {t v : Shat}
    (ht : t ∈ D.rad.Rstar) (hv : v ∈ D.P.Γ.hatV cap) (hcap : closure g ∩ D.rad.G.V = {v, t})
    (hnot : ¬ D.IsNear H (k + 2) t) (hgY : ¬ g ⊆ Y) : Disjoint g Y := by
  have hfr : ∀ x ∈ g, x ∉ frontier Y := fun x hx hfr ↦ hnot (near_of_mem_edge hg ht hv hcap hx
    (hY.frontier_sub hfr))
  rw [disjoint_left]
  intro x hx hxY
  have hint : ∀ y ∈ g, y ∈ Y → y ∈ interior Y := fun y hy hyY ↦ by
    by_contra hn
    exact hfr y hy ⟨subset_closure hyY, hn⟩
  apply hgY
  have hsub : g ⊆ interior Y := IsPreconnected.subset_left_of_subset_union isOpen_interior
    hY.closed.isOpen_compl
    (disjoint_left.mpr fun y hy hn ↦ hn (interior_subset hy))
    (fun y hy ↦ by
      by_cases h : y ∈ Y
      · exact .inl (hint y hy h)
      · exact .inr h) ⟨x, hx, hint x hx hxY⟩ hg.2.2.1.isConnected.isPreconnected
  exact hsub.trans interior_subset

/-- **A good region and one that is not good share no point off the ring and off `V(Γ*)`.** -/
theorem IsZoneSet.not_clash (hY : IsZoneSet D H k Y) (hH : H.IsSubdrawing D.rad.G) {q₁ q₂ : Set
  Shat} {p : Shat}
    (hq₁ : q₁ ∈ D.rad.G.R) (hq₂ : q₂ ∈ D.rad.G.R) (hg₁ : IsGood D H k Y q₁)
      (hg₂ : ¬ IsGood D H k Y q₂)
    (hp₁ : p ∈ closure q₁) (hp₂ : p ∈ closure q₂) (hpV : p ∉ D.rad.G.V) (hpr : p ∉
      (ring D H k Y).U) : False := by
  have hT := cap.isClosedSurface
  have hS := χ.isSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨hf₁, -, hf₃⟩ := D.rad.region_facts hS D.P.fits.internally_three_connected
  have hpq₁ : p ∉ q₁ := fun h ↦ by
    obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hp₂ q₁ (region_isOpen hq₁) h
    obtain rfl := region_eq_of_mem hq₁ hq₂ hy₁ hy₂
    exact hg₂ hg₁
  have hpU : p ∈ D.rad.G.U := (closure_region_subset hq₁ hp₁).resolve_left hpq₁
  obtain ⟨g, hg, hpg⟩ := D.rad.G.exists_edge_of_mem hpU hpV
  obtain ⟨_, ⟨v, hv, rfl⟩, t, ht, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  have hgq₁ : g ⊆ closure q₁ := edge_subset_closure_of_incident hT hg hq₁ ⟨p, hpg, hp₁⟩
  have htcl : t ∈ closure g := by
    have : t ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    exact this.1
  have hgt : g ⊆ D.rad.regionOf t := edge_subset_regionOf D ht hg htcl
  have hnot : ¬ D.IsNear H (k + 2) t := fun hN ↦ by
    obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hp₂ _ (isOpen_regionOf D ht) (hgt hpg)
    exact hg₂ (.inr ⟨t, ht, hN, y, hy₂, hy₁⟩)
  have hvimg : cap.emb v ∈ D.P.Γ.hatV cap := mem_image_of_mem _ hv
  by_cases hgY : g ⊆ Y
  · have hq₂Y : ¬ q₂ ⊆ Y := fun h ↦ hg₂ (.inl h)
    have hdis : ¬ (q₂ ∩ Y).Nonempty := fun h ↦ hq₂Y (hY.meet q₂ hq₂ h)
    have hfr : p ∈ frontier Y := by
      refine ⟨subset_closure (hgY hpg), fun hint ↦ hdis ?_⟩
      obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hp₂ _ isOpen_interior hint
      exact ⟨y, hy₂, interior_subset hy₁⟩
    exact hnot (near_of_mem_edge hg ht hvimg hcap hpg (hY.frontier_sub hfr))
  have hdis := hY.disjoint_edge hg ht hvimg hcap hnot hgY
  have hv3 : ¬ D.IsNear H (k + 3) (cap.emb v) := fun hN ↦ hpr (mem_ring_U.mpr
    ⟨g, ⟨hg, v, hv, t, ht, hcap, hN, hnot, hgY⟩, subset_closure hpg⟩)
  have hqY : ¬ q₁ ⊆ Y := fun h ↦ disjoint_left.mp hdis hpg (closure_minimal h hY.closed hp₁)
  rcases hg₁ with h | ⟨w, hw, hN, hm⟩
  · exact hqY h
  obtain ⟨e, he, heq⟩ := hf₁ q₁ hq₁
  have hvcl : cap.emb v ∈ closure q₁ := by
    have hve : cap.emb v ∈ closure g ∩ D.rad.G.V := by
      rw [hcap]
      exact .inl rfl
    exact closure_minimal hgq₁ isClosed_closure hve.1
  have hve : v ∈ tilde e := ⟨hf₃ q₁ hq₁ e he heq v hv hvcl, fun h ↦ D.P.Γ.disjoint_V he h hv⟩
  by_cases hc : (tilde e).ncard = 3 ∧ (closure e ∩ bd S).Nonempty
  · rcases hY.cuff q₁ hq₁ e he heq hc.1 hc.2 w hw hN hm with h | h
    · exact hqY h
    · exact hv3 (h v hve)
  · refine hv3 (hN.of_corner hH hq₁ he heq hw hm (fun h3 ↦ ?_) hve)
    exact not_nonempty_iff_eq_empty.mp fun h ↦ hc ⟨h3, h⟩

omit [T2Space S] [T2Space Shat] in
/-- Each point of `Σ̂` lies in an atom. -/
theorem exists_atom_mem (D : TangleDatum cap χ) (x : Shat) : ∃ a ∈ D.P.Γ.atoms cap, x ∈ a := by
  by_cases hx : x ∈ D.P.Γ.hatU cap
  · obtain ⟨y, hy, rfl⟩ := hx
    by_cases hyV : y ∈ D.P.Γ.V
    · exact ⟨_, Or.inl (Or.inl ⟨y, hyV, rfl⟩), rfl⟩
    · obtain ⟨c, hc, hyc⟩ := exists_arcComp_superset (F := D.P.Γ.U \ D.P.Γ.V)
        (isPathConnected_singleton y) (singleton_subset_iff.2 ⟨hy, hyV⟩)
      exact ⟨_, Or.inl (Or.inr ⟨c, hc, rfl⟩), mem_image_of_mem _ (hyc rfl)⟩
  · exact ⟨_, Or.inr ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩

/-- A walk of `Γ*` bounds the metric. The walk there and back is a closed walk through both ends. -/
theorem dist_atomOf_le_of_walk (D : TangleDatum cap χ) {x y : Shat} (W : GraphWalk D.rad.G.toGraph
  x y)
    (hlt : W.length < D.rep) : D.dist (D.rad.atomOf x) (D.rad.atomOf y) ≤ W.length := by
  have hlen : (W.append W.reverse).length = 2 * W.length := by
    rw [GraphWalk.length_append, GraphWalk.length_reverse]
    omega
  obtain ⟨T, hT, hl⟩ := D.exists_closedWalkIns (W.append W.reverse) (by omega)
  have hsub : ∀ z ∈ W.support, z ∈ T.ins := fun z hz ↦ by
    rw [hT]
    refine .inl ((walkDrawing D.rad.G _).V_subset_U ?_)
    rw [walkDrawing_V]
    exact (GraphWalk.mem_support_append _ _).mpr (.inl hz)
  have hxG : x ∈ D.rad.G.V := W.mem_vertexSet_of_mem_support W.start_mem_support
  have hyG : y ∈ D.rad.G.V := W.mem_vertexSet_of_mem_support W.end_mem_support
  have := D.dist_le T ⟨x, D.mem_atomOf hxG, hsub x W.start_mem_support⟩ ⟨y, D.mem_atomOf hyG, hsub
    y W.end_mem_support⟩
  omega

/-- The closure of a region of `Γ*` is within three steps of each of its corners. -/
theorem dist_closure_region_le (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {q ρ a : Set Shat}
  (hq : q ∈ D.rad.G.R)
    (hm : (q ∩ ρ).Nonempty) (ha : (a ∩ closure q).Nonempty) : D.dist ρ a ≤ 3 := by
  obtain ⟨e, he, heq⟩ := (D.rad.region_facts χ.isSurface D.P.fits.internally_three_connected).1 q hq
  obtain ⟨X, hX, hl, hsX⟩ := exists_tie D hrep hq
  obtain ⟨T, hTX, hTl⟩ := exists_walk_of_restraint D (by omega) hX
  obtain ⟨y, hy₁, hy₂⟩ := hm
  obtain ⟨b, hb₁, hb₂⟩ := ha
  have := D.dist_le T (a := ρ) (b := a) ⟨y, hy₂, hTX ▸ hsX (subset_closure hy₁)⟩ ⟨b, hb₁, hTX ▸ hsX
    hb₂⟩
  omega

/-- The goodness of a region of `Γ*` puts its closure into `Λ`. -/
theorem IsGood.closure_subset (D : TangleDatum cap χ) (hrep : 4 ≤ D.rep) {Y Λ z : Set Shat} {b : ℕ}
  (hY : IsClosed Y)
    (hYΛ : Y ⊆ Λ) (hΛ : ∀ x ∈ D.P.Γ.atoms cap, D.dist z x ≤ b + 3 → x ⊆ Λ)
    (hnear : ∀ w ∈ D.rad.Rstar, D.IsNear H (k + 2) w → D.dist z (D.rad.regionOf w) ≤ b)
    {q : Set Shat} (hq : q ∈ D.rad.G.R) (hg : IsGood D H k Y q) : closure q ⊆ Λ := by
  rcases hg with h | ⟨w, hw, hN, hm⟩
  · exact (closure_minimal h hY).trans hYΛ
  intro y hy
  obtain ⟨a, ha, hya⟩ := exists_atom_mem D y
  have h₁ := hnear w hw hN
  have h₂ := dist_closure_region_le D hrep hq hm (a := a) ⟨y, hya, hy⟩
  have h₃ := D.dist_triangle hrep (a := z) (c := a) (Or.inr (D.rad.regionOf_mem hw).1)
  exact hΛ a ha (by omega) hya

/-- A vertex of `Γ` has an edge of `Γ*`. -/
theorem exists_spoke_at (D : TangleDatum cap χ) {v : S} (hv : v ∈ D.P.Γ.V) :
    ∃ g ∈ D.rad.G.E, ∃ t ∈ D.rad.Rstar, closure g ∩ D.rad.G.V = {cap.emb v, t} := by
  have hTs := cap.isClosedSurface
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 D.rad hv
  obtain ⟨f, hf, hvf⟩ := D.P.Γ.exists_sk_at hc ⟨hvc, fun h ↦ D.P.Γ.disjoint_V hc h hv⟩
  have hfr : ∃ r ∈ D.P.Γ.hatRegions cap, cap.emb '' f ⊆ closure r := by
    rcases D.P.Γ.size_cases hc with h2 | h3'
    · have hfE : cap.emb '' f ∈ Sk.E := (hSk.edge_iff hS).mpr ⟨f, hf.mem, rfl⟩
      obtain ⟨r, hr, hsub⟩ := exists_region_incident hTs hfE
      rcases hSk.region_cases hS hr with hhat | ⟨c', hc', h3c, hsubr⟩
      · exact ⟨r, hhat, hsub⟩
      · exfalso
        have hfc : f = c := by
          rcases hf.2 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · omega
        subst hfc
        obtain ⟨x, hx⟩ := hc.1
        have hcl : IsClosed (cap.emb '' closure c') := (cap.isClosedEmbedding hS).isClosedMap _
          isClosed_closure
        obtain ⟨x', hx', hxx⟩ := closure_minimal hsubr hcl (hsub (mem_image_of_mem _ hx))
        obtain rfl := cap.isEmbedding.injective hxx
        have hxc' : x' ∈ c' := by
          rcases D.P.Γ.closure_subset hc' hx' with h | h
          · exact h
          · exact absurd h (D.P.Γ.disjoint_V hc hx)
        obtain rfl := arcComp_eq_of_mem hc hc' hx hxc'
        omega
    · exact hSk.exists_hatRegion_side hS hf h3'
  obtain ⟨r, hr, hsub⟩ := hfr
  have hvr : cap.emb v ∈ closure r := closure_minimal hsub isClosed_closure
    (image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hvf.1))
  obtain ⟨w, ⟨hwr, hwG⟩, -⟩ := D.rad.isPreRadial.2.2.1 r hr
  have hwV : w ∉ D.P.Γ.hatV cap := fun hV ↦ by
    obtain ⟨y, hy, rfl⟩ := id hr
    exact (connectedComponentIn_subset _ _ hwr) (image_mono D.P.Γ.V_subset hV)
  have hw : w ∈ D.rad.Rstar := ⟨hwG, hwV⟩
  have hreg : D.rad.regionOf w = r := by
    obtain ⟨y, hy, rfl⟩ := id hr
    exact (connectedComponentIn_eq hwr).symm
  obtain ⟨e, he, hcap⟩ := D.rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hw hv
    (hreg ▸ hvr)
  exact ⟨e, he, w, hw, hcap⟩

/-- **The regions of the ring.** Let `Λ'` include the closure of each good region. Then `Λ'`
includes each region of the
ring whose closure meets the zone or `Y`. -/
theorem IsZoneSet.ring_region_subset (hY : IsZoneSet D H k Y) (hH : H.IsSubdrawing D.rad.G) {Λ' :
  Set Shat}
    (hgood : ∀ q ∈ D.rad.G.R, IsGood D H k Y q → closure q ⊆ Λ') {r : Set Shat} (hr : r ∈
      (ring D H k Y).R)
    (hz : (closure r ∩ (nearZone D H k ∪ Y)).Nonempty) : r ⊆ Λ' := by
  have hTs := cap.isClosedSurface
  have hS := χ.isSurface
  have : ConnectedSpace Shat := cap.connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hTs
  set G := D.rad.G with hGdef
  have hrO : IsOpen r := region_isOpen hr
  have hrU : ∀ x ∈ r, x ∉ (ring D H k Y).U := fun x hx ↦ region_subset hr hx
  have hRfin : G.R.Finite := finite_R hTs G
  -- A good region meets `r`.
  have hreg : ∀ w ∈ D.rad.Rstar, D.IsNear H (k + 2) w → (r ∩ D.rad.regionOf w).Nonempty →
      ∃ q ∈ G.R, IsGood D H k Y q ∧ (q ∩ r).Nonempty := by
    rintro w hw hN ⟨y, hyr, hyw⟩
    have hO : IsOpen (r ∩ D.rad.regionOf w) := hrO.inter (isOpen_regionOf D hw)
    obtain ⟨q, hq, -, u, huq, hur, huw⟩ := exists_region_near hTs G hO (subset_closure ⟨hyr, hyw⟩)
    exact ⟨q, hq, .inr ⟨w, hw, hN, u, huq, huw⟩, u, huq, hur⟩
  have hzone : (closure r ∩ nearZone D H k).Nonempty → ∃ q ∈ G.R, IsGood D H k Y q ∧
    (q ∩ r).Nonempty := by
    rintro ⟨z₀, hz₀, ⟨hzV, hzN⟩ | hzR⟩
    · obtain ⟨v, hv, rfl⟩ := hzV
      have hnotU : cap.emb v ∉ (ring D H k Y).U := fun h ↦ by
        obtain ⟨g, ⟨hg, v', hv', t, ht, hcap, -, hnot, -⟩, hx⟩ := mem_ring_U.mp h
        have hm : cap.emb v ∈ closure g ∩ G.V := ⟨hx, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv)⟩
        rw [hcap] at hm
        rcases hm with hm | hm
        · obtain rfl := cap.isEmbedding.injective hm
          have hcap' : closure g ∩ G.V = {t, cap.emb v} := by rw [hcap, pair_comm]
          exact hnot (hzN.step ⟨hg, ht.1, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv'), hcap'⟩)
        · exact ht.2 (hm ▸ mem_image_of_mem _ hv)
      have hvr : cap.emb v ∈ r := (closure_region_subset hr hz₀).resolve_right hnotU
      obtain ⟨g, hg, t, ht, hcap⟩ := exists_spoke_at D hv
      have hmem : ∀ {x}, x ∈ ({cap.emb v, t} : Set Shat) → x ∈ closure g := fun {x} hx ↦ by
        have : x ∈ closure g ∩ G.V := hcap ▸ hx
        exact this.1
      have hcap' : closure g ∩ G.V = {t, cap.emb v} := by rw [hcap, pair_comm]
      have hN : D.IsNear H (k + 2) t :=
        hzN.step ⟨hg, ht.1, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv), hcap'⟩
      obtain ⟨y, hyr, hyg⟩ := mem_closure_iff.mp (hmem (mem_insert _ _)) r hrO hvr
      exact hreg t ht hN ⟨y, hyr, edge_subset_regionOf D ht hg (hmem (mem_insert_of_mem _ rfl)) hyg⟩
    · obtain ⟨w, ⟨hw, hN⟩, hzw⟩ := mem_iUnion₂.mp hzR
      obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hz₀ _ (isOpen_regionOf D hw) hzw
      exact hreg w hw hN ⟨y, hy₂, hy₁⟩
  have hkey : ∃ q ∈ G.R, IsGood D H k Y q ∧ (q ∩ r).Nonempty := by
    obtain ⟨z₀, hz₀, hzz⟩ := hz
    rcases hzz with hzz | hzY
    · exact hzone ⟨z₀, hz₀, hzz⟩
    by_cases hfr : z₀ ∈ frontier Y
    · exact hzone ⟨z₀, hz₀, hY.frontier_sub hfr⟩
    have hint : z₀ ∈ interior Y := by
      by_contra hn
      exact hfr ⟨subset_closure hzY, hn⟩
    obtain ⟨q, hq, hzq, u, huq, hur⟩ := exists_region_near hTs G hrO hz₀
    obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hzq _ isOpen_interior hint
    exact ⟨q, hq, .inl (hY.meet q hq ⟨y, hy₂, interior_subset hy₁⟩), u, huq, hur⟩
  -- the two closed sets
  let T : Set Shat := r \ G.V
  have hTc : IsPreconnected T := GM11.isPreconnected_sdiff_finite hTs hrO
    (region_isPreconnected hr) G.finite_V
  let 𝒜 : Set (Set Shat) := {q | q ∈ G.R ∧ IsGood D H k Y q}
  let ℬ : Set (Set Shat) := {q | q ∈ G.R ∧ ¬ IsGood D H k Y q}
  let A : Set Shat := ⋃ q ∈ 𝒜, closure q
  let B : Set Shat := ⋃ q ∈ ℬ, closure q
  have h𝒜fin : 𝒜.Finite := hRfin.subset fun _ h => h.1
  have hℬfin : ℬ.Finite := hRfin.subset fun _ h => h.1
  have hAc : IsClosed A := h𝒜fin.isClosed_biUnion fun _ _ => isClosed_closure
  have hBc : IsClosed B := hℬfin.isClosed_biUnion fun _ _ => isClosed_closure
  have hcover : ∀ x, x ∈ A ∪ B := fun x ↦ by
    obtain ⟨q, hq, hx, -⟩ := exists_region_near hTs G isOpen_univ (x := x) (by simp)
    by_cases hg : IsGood D H k Y q
    · exact .inl (mem_iUnion₂.mpr ⟨q, ⟨hq, hg⟩, hx⟩)
    · exact .inr (mem_iUnion₂.mpr ⟨q, ⟨hq, hg⟩, hx⟩)
  obtain ⟨q₀, hq₀, hg₀, y₀, hy₀q, hy₀r⟩ := hkey
  have hTA : (T ∩ A).Nonempty :=
    ⟨y₀, ⟨hy₀r, fun h ↦ region_subset hq₀ hy₀q (G.V_subset_U h)⟩, mem_iUnion₂.mpr ⟨q₀, ⟨hq₀, hg₀⟩,
      subset_closure hy₀q⟩⟩
  have hnoB : ¬ (T ∩ B).Nonempty := fun hTB ↦ by
    obtain ⟨p, hpT, hpA, hpB⟩ := isPreconnected_closed_iff.mp hTc A B hAc hBc
      (fun x _ ↦ hcover x) hTA hTB
    obtain ⟨q₁, ⟨h₁, h₁g⟩, hp₁⟩ := mem_iUnion₂.mp hpA
    obtain ⟨q₂, ⟨h₂, h₂g⟩, hp₂⟩ := mem_iUnion₂.mp hpB
    exact hY.not_clash hH h₁ h₂ h₁g h₂g hp₁ hp₂ hpT.2 (hrU p hpT.1)
  intro p hp
  obtain ⟨q, hq, hpq, y, hyq, hyr⟩ := exists_region_near hTs G hrO (subset_closure hp)
  have hyT : y ∈ T := ⟨hyr, fun h ↦ region_subset hq hyq (G.V_subset_U h)⟩
  have hqg : IsGood D H k Y q := by
    rcases hcover y with hyA | hyB
    · obtain ⟨q₁, ⟨h₁, h₁g⟩, hy₁⟩ := mem_iUnion₂.mp hyA
      obtain ⟨u, hu₁, hu₂⟩ := mem_closure_iff.mp hy₁ q (region_isOpen hq) hyq
      obtain rfl := region_eq_of_mem hq h₁ hu₁ hu₂
      exact h₁g
    · exact absurd ⟨y, hyT, hyB⟩ hnoB
  exact hgood q hq hqg hpq

end TangleDatum

end GraphMinor.GM19
