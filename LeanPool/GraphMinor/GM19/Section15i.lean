/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15h
public import LeanPool.GraphMinor.GM19.Section12g
public import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# Graph Minors XIX, (15.2): the metric of the tangle on the skeleton

The proof of (15.2) applies (3.2) of Graph Minors XII to the tangle `𝒯'` in `sk(Γ)`. That theorem
asks that certain regions of
`sk(Γ)` are far apart in the metric of `𝒯'`. The proof of (15.2) gets from (1) that they are far
apart in the metric of `𝒯`. So we
compare the two metrics.

A closed walk `W` of the radial drawing of `sk(Γ)` may pass through the centre of a cell, so it is
not a walk of `Γ*`. We do not
replace it by a walk of `Γ*`. Instead we give each vertex of the radial drawing an atom of `Γ`
(`SkData.exists_anchor`), and neighbours
get atoms at distance at most three. So all of `W` lies within `3|W|` of any one of its vertices. If
a region of `sk(Γ)` lies inside `W`,
then a separation of `𝒯` has its boundary on `W`, and `TangleDatum.exists_inside_cover` shows that
the region is close to `W`.
The result used later is `TangleDatum.dist_le_of_skMetric`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β} {D : TangleDatum cap χ} {H G₃
    : Drawing Shat}

/-- A tangle cannot hold both a separation and one with the same two vertex sets the other way
round. The two can differ only in edges
with all ends in the middle, so `(A ∪ A', B ∩ B')` is a separation of small order. It is not in `𝒯`
by the third axiom, and its reverse breaks
the second axiom. -/
theorem not_mem_of_swapped_vertexSets {α β' : Type*} {G : Hypergraph α β'} {θ : ℕ} {T : Set
  (Hypergraph α β' × Hypergraph α β')} (hT : IsTangle G θ T) {A B A' B' : Hypergraph α β'}
    (h : (A, B) ∈ T) (h' : (A', B') ∈ T) (hA : A.vertexSet = B'.vertexSet) (hB : B.vertexSet
      = A'.vertexSet) : False := by
  have h₁ := hT.isSeparation h
  have h₂ := hT.isSeparation h'
  have hsep := h₁.union_inter h₂
  have hle : ((A ∪ A') ∩ (B ∩ B')).vertexSet ⊆ (A ∩ B).vertexSet := fun x hx => by
    obtain ⟨-, hxB, hxB'⟩ := hx
    exact ⟨hA ▸ hxB', hxB⟩
  have hord : separationOrder (A ∪ A') (B ∩ B') < θ :=
    lt_of_le_of_lt (ncard_le_ncard hle (A ∩ B).vertexSet_finite) (hT.order_lt h)
  rcases hT.axiom1 hsep hord with h₃ | h₃
  · refine hT.axiom3 h₃ ?_
    rw [← h₁.vertexSet_union, hB]
    rfl
  · exact hT.axiom2 h h' h₃ hsep.union_eq

namespace TangleDatum.SkData

omit [T2Space Shat] in
omit [T2Space S] in
/-- A centre of a region of `Γ` in the radial drawing of `sk(Γ)` is a vertex of `Γ*`. -/
theorem hub_mem (hd : D.SkData H G₃) {r : Set Shat} (hr : r ∈ D.P.Γ.hatRegions cap) {c : Shat}
  (hc : c ∈ r) (hcV : c ∈ G₃.V) : c ∈ D.rad.G.V := by
  have hrR := hd.sk.hatRegion_mem_R χ.isSurface hr
  obtain ⟨w, -, huniq⟩ := hd.pre.2.2.2.1 r hrR
  obtain ⟨w', ⟨hw'r, hw'V⟩, -⟩ := D.rad.isPreRadial.2.2.1 r hr
  have e : c = w' := (huniq c ⟨hc, hcV⟩).trans (huniq w' ⟨hw'r, hd.sub.1 hw'V⟩).symm
  exact e ▸ hw'V

/-- Each vertex of the radial drawing of `sk(Γ)` has an atom of `Γ`: itself if it is a vertex of
`Γ`, and the region or the edge of its
region otherwise. The atom is close to the corners of the region. -/
theorem exists_anchor (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {x : Shat} (hx : x ∈ G₃.V) :
    ∃ α ∈ D.P.Γ.atoms cap, (∀ v ∈ D.P.Γ.V, x = cap.emb v → α = {x}) ∧ ∀ r ∈ H.R, x ∈ r
      → ∀ v ∈ D.P.Γ.V, cap.emb v ∈ closure r → D.dist α {cap.emb v} ≤ 3 := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have h3 := D.P.fits.internally_three_connected
  by_cases hxH : x ∈ H.V
  · have hxH' := hxH
    rw [hd.sk.hV] at hxH'
    obtain ⟨v, hv, rfl⟩ := hxH'
    refine ⟨_, Or.inl (Or.inl ⟨v, hv, rfl⟩), fun _ _ _ => rfl, fun r hr hxr => ?_⟩
    exact absurd (H.V_subset_U hxH) (region_subset hr hxr)
  obtain ⟨r, hr, hxr⟩ := hd.pre.2.2.2.2.1 x ⟨hx, hxH⟩
  have hrU : ∀ r' ∈ H.R, x ∈ r' → r' = r := fun r' hr' hxr' => by
    obtain ⟨y, -, rfl⟩ := (mem_R_iff H).mp hr
    obtain ⟨y', -, rfl⟩ := (mem_R_iff H).mp hr'
    rw [connectedComponentIn_eq hxr, connectedComponentIn_eq hxr']
  have hne : ∀ v ∈ D.P.Γ.V, x ≠ cap.emb v := fun v hv h => hxH (hd.sk.hV ▸ h ▸ mem_image_of_mem _
    hv)
  rcases hd.sk.region_cases hS hr with hh | ⟨c, hc, h3', hrc⟩
  · have hxG := hd.hub_mem hh hxr hx
    have hxR : x ∈ D.rad.Rstar := ⟨hxG, fun h => hxH (hd.sk.hV ▸ h)⟩
    have hreg : D.rad.regionOf x = r := by
      obtain ⟨y, hy, rfl⟩ := id hh
      exact (connectedComponentIn_eq hxr).symm
    refine ⟨r, Or.inr ?_, fun v hv h => absurd h (hne v hv), fun r' hr' hxr' v hv hcl => ?_⟩
    · exact hh
    rw [hrU r' hr' hxr'] at hcl
    obtain ⟨e, he, hcap⟩ := D.rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hxR hv
      (hreg ▸ hcl)
    have hvG : cap.emb v ∈ D.rad.G.V := D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv)
    have hl : D.rad.G.toGraph.IsLink e x (cap.emb v) := ⟨he, hxG, hvG, by rw [hcap, pair_comm]⟩
    have hlen : (GraphWalk.cons hl (GraphWalk.nil hvG)).length = 1 := by
      simp [GraphWalk.length, GraphWalk.edges]
    have h₁ := D.dist_atomOf_le_of_walk (GraphWalk.cons hl (GraphWalk.nil hvG)) (by omega)
    have h₂ : D.rad.atomOf x = r := by
      unfold RadialDrawing.atomOf
      rw [ite_eq_right hxR.2, hreg]
    have h₃ : D.rad.atomOf (cap.emb v) = {cap.emb v} := D.atomOf_emb hv
    rw [h₂, h₃, hlen] at h₁
    omega
  · refine ⟨cap.emb '' c, Or.inl (Or.inr ⟨c, hc, rfl⟩), fun v hv h => absurd h (hne v hv),
      fun r' hr' hxr' v hv hcl => ?_⟩
    rw [hrU r' hr' hxr'] at hcl
    have hcld : IsClosed (cap.emb '' closure c) := (cap.isClosedEmbedding χ.isSurface).isClosedMap
      _ isClosed_closure
    obtain ⟨y, hy, hyv⟩ := closure_minimal hrc hcld hcl
    obtain rfl := cap.isEmbedding.injective hyv
    have h₁ := D.edgeVertDist_self_le hrep hc ⟨hy, fun h => D.P.Γ.disjoint_V hc h hv⟩ hv
    have h₃ : D.rad.atomOf (cap.emb y) = {cap.emb y} := D.atomOf_emb hv
    unfold edgeVertDist at h₁
    rwa [h₃] at h₁

/-- A choice of atoms for the vertices of the radial drawing of `sk(Γ)`, with neighbours close. -/
structure IsAnchors (D : TangleDatum cap χ) (H G₃ : Drawing Shat) (A : Shat → Set Shat) : Prop where
  atom : ∀ x ∈ G₃.V, A x ∈ D.P.Γ.atoms cap
  vertex : ∀ v ∈ D.P.Γ.V, A (cap.emb v) = {cap.emb v}
  corner : ∀ r ∈ H.R, ∀ x ∈ r, x ∈ G₃.V → ∀ v ∈ D.P.Γ.V, cap.emb v ∈ closure r → D.dist
    (A x) {cap.emb v} ≤ 3

theorem exists_isAnchors (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) : ∃ A, IsAnchors D H G₃ A := by
  classical
  have hex : ∀ x, x ∈ G₃.V → _ := fun x (hx : x ∈ G₃.V) => hd.exists_anchor hrep hx
  choose! A hA₁ hA₂ hA₃ using hex
  refine ⟨A, hA₁, fun v hv => ?_, fun r hr x hxr hx v hv hcl => hA₃ x hx r hr hxr v hv hcl⟩
  have hG : cap.emb v ∈ G₃.V := hd.sub.1 (D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv))
  exact hA₂ _ hG v hv rfl

omit [T2Space S] in
/-- Neighbours in the radial drawing of `sk(Γ)` have close atoms. -/
theorem IsAnchors.step (hd : D.SkData H G₃) {A : Shat → Set Shat} (hA : IsAnchors D H G₃ A) {e :
  Set Shat} {a b : Shat} (hl : G₃.toGraph.IsLink e a b) :
    D.dist (A a) (A b) ≤ 3 := by
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨v, hv, w, ⟨hwG, hwH⟩, hcap⟩ := hd.pre.2.2.2.2.2.1 e hl.1
  have heq : ({a, b} : Set Shat) = {v, w} := hl.2.2.2.symm.trans hcap
  obtain ⟨r, hr, hwr⟩ := hd.pre.2.2.2.2.1 w ⟨hwG, hwH⟩
  have hwc : w ∈ closure e := by
    have : w ∈ closure e ∩ G₃.V := hcap ▸ .inr rfl
    exact this.1
  have hvc : v ∈ closure e := by
    have : v ∈ closure e ∩ G₃.V := hcap ▸ .inl rfl
    exact this.1
  obtain ⟨y, hyr, hye⟩ := mem_closure_iff.mp hwc r (region_isOpen hr) hwr
  have hdis : Disjoint e H.U := disjoint_left.mpr fun z hz hzU => by
    have hzG : z ∈ G₃.U := (hl.1.2.1 hz).1
    have : z ∈ H.U ∩ G₃.U := ⟨hzU, hzG⟩
    rw [show H.U ∩ G₃.U = H.V from hd.pre.2.1] at this
    exact (hl.1.2.1 hz).2 (hd.pre.2.2.1 this)
  have her : e ⊆ r := subset_region hr hl.1.2.2.1.isConnected.isPreconnected hdis hye hyr
  have hv' := hv
  change v ∈ H.V at hv'
  rw [hd.sk.hV] at hv'
  obtain ⟨v₀, hv₀, rfl⟩ := hv'
  have h₁ := hA.corner r hr w hwr hwG v₀ hv₀ (closure_mono her hvc)
  rw [← hA.vertex v₀ hv₀] at h₁
  rcases Set.pair_eq_pair_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rwa [D.dist_comm]
  · exact h₁

/-- All of a walk of the radial drawing of `sk(Γ)` is close to its start. -/
theorem IsAnchors.dist_le_of_walk (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {A : Shat → Set Shat}
  (hA : IsAnchors D H G₃ A) {a b : Shat} (W : GraphWalk G₃.toGraph a b) :
    ∀ x ∈ W.support, D.dist (A a) (A x) ≤ 3 * W.length := by
  induction W with
  | nil hv =>
    intro x hx
    simp only [GraphWalk.support, List.mem_singleton] at hx
    rw [hx, D.dist_self]
    exact Nat.zero_le _
  | @cons u v w e hl rest ih =>
    intro x hx
    simp only [GraphWalk.support, List.mem_cons] at hx
    have hlen : (GraphWalk.cons hl rest).length = rest.length + 1 := by
      simp [GraphWalk.length, GraphWalk.edges]
    rw [hlen]
    rcases hx with rfl | hx
    · rw [D.dist_self]
      exact Nat.zero_le _
    · have h₁ := D.dist_triangle hrep (a := A u) (c := A x) (hA.atom v hl.2.2.1)
      have h₂ := hA.step hd hl
      have h₃ := ih x hx
      omega

/-- The two atoms of two vertices of a closed walk are close. -/
theorem IsAnchors.dist_le_of_closed_walk (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {A : Shat
  → Set Shat} (hA : IsAnchors D H G₃ A) {u : Shat} (W : GraphWalk G₃.toGraph u u) {x y : Shat}
    (hx : x ∈ W.support) (hy : y ∈ W.support) : D.dist (A x) (A y) ≤ 6 * W.length := by
  have h₁ := hA.dist_le_of_walk hd hrep W x hx
  have h₂ := hA.dist_le_of_walk hd hrep W y hy
  have h₃ := D.dist_triangle hrep (a := A x) (c := A y) (hA.atom u (W.mem_vertexSet_of_mem_support
    W.start_mem_support))
  rw [D.dist_comm (A x) (A u)] at h₃
  omega

omit [T2Space S] in
/-- A side of an edge lies in the closure of the edge. -/
theorem _root_.GraphMinor.GM19.Painting.IsSkEdgeIn.subset_closure {Γ : Painting S} {f c : Set S}
  (hf : Γ.IsSkEdgeIn f c) : f ⊆ closure c := by
  rcases hf.2 with ⟨-, rfl⟩ | ⟨h3, hfb⟩
  · exact _root_.subset_closure
  · exact hfb.2.1.trans (sdiff_subset.trans (Surface.discBd_subset _))

/-- **An atom on a region inside a walk is close to the walk.** Let `W` be a closed walk of the
radial drawing of `sk(Γ)` that has the
centre of a region inside it, and let `c` be an edge of `Γ` with a side on the boundary of the
region. If the region is off `W`, then
the separation of `𝒯'` at a circuit of `W` around it comes from a separation of `𝒯`, and
`TangleDatum.exists_inside_cover` applies. -/
theorem exists_near_walk (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {A : Shat → Set Shat}
  (hA : IsAnchors D H G₃ A) {m : ℕ} (hmr : m ≤ D.rep) (hm : 1 ≤ m) (h3m : 3 * m < 2 * D.ord + 3)
    {ins : Drawing Shat → Set Shat} (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m
      (D.skTangle H m) ins) {u : Shat} (W : GraphWalk G₃.toGraph u u) (hl : W.length < 2 * m)
    {r : Set Shat} (hr : r ∈ H.R) {h : Shat} (hh : h ∈ r) (hhV : h ∈ G₃.V)
      (hin : h ∈ insWalk ins G₃ W) {f c : Set S} (hf : D.P.Γ.IsSkEdgeIn f c)
        (hfr : cap.emb '' f ⊆ closure r) :
    ∃ x ∈ W.support, D.dist (cap.emb '' c) (A x) ≤ W.length + 6 := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hTg := D.isTangle_skTangle hd.sk hm h3m
  have hsl : IsSlope G₃ (2 * m) ins := GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H)
    hT hTg.isPretangle hd.pre.2.1 hins
  have hc := hf.1
  obtain ⟨p, q, -, ht, htV, -⟩ := D.P.Γ.sk_line hf.mem
  have hp : p ∈ tilde f := ht ▸ .inl rfl
  have hpV : p ∈ D.P.Γ.V := htV hp
  have hpc : p ∈ tilde c := ⟨closure_minimal hf.subset_closure isClosed_closure hp.1, fun h'
    => D.P.Γ.disjoint_V hc h' hpV⟩
  have hpr : cap.emb p ∈ closure r := closure_minimal hfr isClosed_closure (by
    rw [(cap.isClosedEmbedding hS).closure_image_eq f]
    exact mem_image_of_mem _ hp.1)
  have hcp : D.dist (cap.emb '' c) {cap.emb p} ≤ 3 := by
    have := D.edgeVertDist_self_le hrep hc hpc hpV
    unfold edgeVertDist at this
    rwa [D.atomOf_emb hpV] at this
  have hsingle : ({cap.emb p} : Set Shat) ∈ D.P.Γ.atoms cap := Or.inl (Or.inl ⟨p, hpV, rfl⟩)
  rcases hin with hU | hC
  · have hsup : h ∈ W.support := by
      have := mem_V_of_mem_U_sub (walkDrawing_isSubdrawing G₃ W) hU hhV
      rwa [walkDrawing_V] at this
    refine ⟨h, hsup, ?_⟩
    have h₁ := hA.corner r hr h hh hhV p hpV hpr
    have h₂ := D.dist_triangle hrep (a := cap.emb '' c) (c := A h) hsingle
    rw [D.dist_comm {cap.emb p} (A h)] at h₂
    omega
  obtain ⟨C, ⟨hC, hCs⟩, hiC⟩ := mem_iUnion₂.mp hC
  have hCG : C.IsSubdrawing G₃ := hCs.trans (walkDrawing_isSubdrawing G₃ W)
  have hCU : C.U ⊆ (walkDrawing G₃ W).U := hCs.U_subset
  by_cases hhU : h ∈ C.U
  · have hsup : h ∈ W.support := by
      have := mem_V_of_mem_U_sub (walkDrawing_isSubdrawing G₃ W) (hCU hhU) hhV
      rwa [walkDrawing_V] at this
    refine ⟨h, hsup, ?_⟩
    have h₁ := hA.corner r hr h hh hhV p hpV hpr
    have h₂ := D.dist_triangle hrep (a := cap.emb '' c) (c := A h) hsingle
    rw [D.dist_comm {cap.emb p} (A h)] at h₂
    omega
  have hCE : C.E.ncard ≤ W.length := by
    have hsub : C.E ⊆ {e | e ∈ W.edges} := by
      have := hCs.2
      rwa [walkDrawing_E] at this
    calc C.E.ncard ≤ {e | e ∈ W.edges}.ncard := ncard_le_ncard hsub (List.finite_toSet _)
      _ ≤ W.edges.length := by
        have e : {e | e ∈ W.edges} = (↑W.edges.toFinset : Set (Set Shat)) := by
          ext x
          simp
        rw [e, ncard_coe_finset]
        exact List.toFinset_card_le _
  have hCl : C.length < 2 * m := lt_of_le_of_lt hCE hl
  have hdis : Disjoint r C.U := disjoint_region_U hT hd.pre.2 hr hh hhV hCG hhU
  have hcl : closure r ⊆ ins C := closure_subset_ins hsl hC hCG hCl (region_isPreconnected hr) hh
    hiC hdis
  obtain ⟨hdisc, hsub, hmem⟩ := hins C hC hCG hCl
  have hfr' : frontier (ins C) = C.U := by rw [← subBd_eq_frontier, hsub]
  obtain ⟨-, -, q₀, hq, e₁, e₂⟩ := hmem
  simp only at e₁ e₂
  have hinj := cap.isEmbedding.injective
  have hqsep := D.isTangle.isSeparation (A := q₀.1) (B := q₀.2) hq
  have hsep₀ : ∀ v, cap.emb v ∈ ((PaintingOrDrawing.drawing H).inter (ins C)).vertexSet
    → cap.emb v ∈ ((PaintingOrDrawing.drawing H).interOutside (ins C)).vertexSet → cap.emb v ∈ C.V
      := fun v h₁ h₂ => by
    have := inter_outside_subset (Γ := PaintingOrDrawing.drawing H) (Δ := ins C) (x
      := cap.emb v) ⟨h₁, h₂⟩
    rw [hfr'] at this
    exact mem_V_of_mem_U_sub (Drawing.IsSubdrawing.refl C) this.1 (mem_V_of_mem_U_sub hCG this.1
      (hd.pre.2.2.1 this.2))
  have hcard := (GM12.circuit_length_eq_two_mul_ncard hd.pre.2 hC hCG).1
  have hsepV : ∀ v, v ∈ (q₀.1 ∩ q₀.2).vertexSet → cap.emb v ∈ C.V := fun v hv =>
    hsep₀ v (e₁ ▸ mem_image_of_mem _ hv.1) (e₂ ▸ mem_image_of_mem _ hv.2)
  have hqVV : ∀ v, v ∈ (q₀.1 ∩ q₀.2).vertexSet → v ∈ D.P.Γ.V := fun v hv
    => hqsep.left_le.vertexSet_subset hv.1
  have hord : (q₀.1 ∩ q₀.2).vertexSet.ncard ≤ (C.V ∩ H.V).ncard := by
    rw [← ncard_image_of_injective _ hinj]
    refine ncard_le_ncard ?_ (C.finite_V.subset inter_subset_left)
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨hsepV v hv, hd.sk.hV ▸ mem_image_of_mem _ (hqVV v hv)⟩
  have hordrep : separationOrder q₀.1 q₀.2 < D.rep := by
    change (q₀.1 ∩ q₀.2).vertexSet.ncard < D.rep
    change C.E.ncard = _ at hcard
    omega
  have hpA : p ∈ q₀.1.vertexSet := by
    have : cap.emb p ∈ ((PaintingOrDrawing.drawing H).inter (ins C)).vertexSet
      := ⟨(hd.sk.hV ▸ mem_image_of_mem _ hpV : cap.emb p ∈ H.V), hcl hpr⟩
    rw [← e₁] at this
    obtain ⟨y, hy, hye⟩ := this
    exact hinj hye ▸ hy
  rcases edge_cases hqsep hc with ⟨hcA, -⟩ | ⟨-, hcB⟩
  · obtain ⟨N, hNG, hshort, hNV, hcov⟩ := D.exists_inside_cover (A := q₀.1) (B := q₀.2) hq hordrep
    obtain ⟨F, hF, hFN, hin'⟩ := hcov c hcA
    have hFG : F.IsSubdrawing D.rad.G := hFN.trans hNG
    obtain ⟨hFc, ⟨y, hyF, hyH⟩⟩ := GM12.circuit_length_eq_two_mul_ncard hd.pre.2 hF
      (hFG.trans hd.sub)
    have hyH' := hyH
    rw [hd.sk.hV] at hyH'
    have hle : (F.V ∩ H.V).ncard ≤ (q₀.1 ∩ q₀.2).vertexSet.ncard := by
      rw [← ncard_image_of_injective _ hinj]
      refine ncard_le_ncard ?_ ((q₀.1 ∩ q₀.2).vertexSet_finite.image _)
      rintro z ⟨hzF, hzH⟩
      rw [hd.sk.hV] at hzH
      obtain ⟨z₀, hz₀, rfl⟩ := hzH
      exact mem_image_of_mem _ (hNV z₀ hz₀ (hFN.1 hzF))
    obtain ⟨y₀, hy₀, rfl⟩ := hyH'
    have hy₀q := hNV y₀ hy₀ (hFN.1 hyF)
    have hyC := hsepV y₀ hy₀q
    have hsup : cap.emb y₀ ∈ W.support := by
      have := hCs.1 hyC
      rwa [walkDrawing_V] at this
    refine ⟨cap.emb y₀, hsup, ?_⟩
    rw [hA.vertex y₀ hy₀]
    change F.E.ncard = _ at hFc
    change C.E.ncard = _ at hcard
    have hFlt : F.E.ncard < 2 * D.rep := hshort F hF hFN
    obtain ⟨x, hx⟩ := hc.1
    have := D.dist_le_of_circuit (by omega) (F := F) ⟨hFG, hF⟩ hFlt (a := cap.emb '' c) (b
      := {cap.emb y₀}) ⟨_, mem_image_of_mem _ hx, hin' (mem_image_of_mem _ hx)⟩
      ⟨_, rfl, D.U_subset_ins ⟨hFG, hF⟩ hFlt (F.V_subset_U hyF)⟩
    omega
  · have hpB : p ∈ q₀.2.vertexSet := by
      have h₁ : p ∈ D.P.Γ.toHypergraph.ends c := ⟨hc, hpV, hpc⟩
      rw [hqsep.right_le.ends_eq c hcB] at h₁
      exact q₀.2.vertex_mem_of_inc h₁
    have hsup : cap.emb p ∈ W.support := by
      have := hCs.1 (hsepV p ⟨hpA, hpB⟩)
      rwa [walkDrawing_V] at this
    refine ⟨cap.emb p, hsup, ?_⟩
    rw [hA.vertex p hpV]
    omega

omit [T2Space Shat] in
/-- The atom of the radial drawing that corresponds to a region is its centre. -/
theorem exists_hub_of_corresponding {r x' : Set Shat} (hr : r ∈ H.R) (hx : IsCorrespondingAtom H G₃
  r x') : ∃ v ∈ G₃.V ∩ r, x' = {v} := by
  rcases hx.2.2 with ⟨v, hv, rfl, -⟩ | ⟨hE, -⟩ | ⟨-, v, hv, e⟩
  · exact absurd (H.V_subset_U hv) (region_subset hr rfl)
  · obtain ⟨y, hy⟩ := hE.1
    exact absurd (hE.2.1 hy).1 (region_subset hr hy)
  · exact ⟨v, hv, e⟩

/-- **Comparing the metrics.** If two regions of `sk(Γ)` are close in the metric of `𝒯'`, then edges
of `Γ` with sides on their boundaries
are close in the metric of `𝒯`. -/
theorem dist_le_of_skMetric (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {m : ℕ} (hmr : m ≤ D.rep)
  (hm : 1 ≤ m) (h3m : 3 * m < 2 * D.ord + 3)
    {ins : Drawing Shat → Set Shat} (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m
      (D.skTangle H m) ins) {r₁ r₂ : Set Shat} (hr₁ : r₁ ∈ H.R) (hr₂ : r₂ ∈ H.R) (hne : r₁ ≠ r₂)
    (hlt : GM14.tangleMetric H G₃ ins m r₁ r₂ < m) {f₁ c₁ f₂ c₂ : Set S}
      (hf₁ : D.P.Γ.IsSkEdgeIn f₁ c₁) (hfr₁ : cap.emb '' f₁ ⊆ closure r₁)
        (hf₂ : D.P.Γ.IsSkEdgeIn f₂ c₂)
    (hfr₂ : cap.emb '' f₂ ⊆ closure r₂) : D.dist (cap.emb '' c₁) (cap.emb '' c₂)
      ≤ 16 * GM14.tangleMetric H G₃ ins m r₁ r₂ + 12 := by
  obtain ⟨A, hA⟩ := hd.exists_isAnchors hrep
  rcases GM11.tangleMetric_cases hd.pre.2 hne (ins := ins) (θ := m) with h | ⟨-, hw⟩
  · omega
  obtain ⟨u, W, x', y', hx, hy, hl, hlen, hxi, hyi⟩ := hw
  obtain ⟨h₁, ⟨h₁V, h₁r⟩, rfl⟩ := exists_hub_of_corresponding hr₁ hx
  obtain ⟨h₂, ⟨h₂V, h₂r⟩, rfl⟩ := exists_hub_of_corresponding hr₂ hy
  obtain ⟨a, ha, hda⟩ := exists_near_walk hd hrep hA hmr hm h3m hins W hl hr₁ h₁r h₁V
    (hxi rfl) hf₁ hfr₁
  obtain ⟨b, hb, hdb⟩ := exists_near_walk hd hrep hA hmr hm h3m hins W hl hr₂ h₂r h₂V
    (hyi rfl) hf₂ hfr₂
  have hab := hA.dist_le_of_closed_walk hd hrep W ha hb
  have h₃ := D.dist_triangle hrep (a := cap.emb '' c₁) (c := cap.emb '' c₂) (hA.atom a
    (W.mem_vertexSet_of_mem_support ha))
  have h₄ := D.dist_triangle hrep (a := A a) (c := cap.emb '' c₂) (hA.atom b
    (W.mem_vertexSet_of_mem_support hb))
  rw [D.dist_comm (A b) (cap.emb '' c₂)] at h₄
  omega

omit [T2Space S] in
/-- **The slopes agree.** The slope `ins` of `𝒯'` and the slope `D.ins` of `𝒯` agree on short
circuits of `Γ*`. If not, the surface is a sphere and they
give two opposite discs. That gives two separations of `𝒯` with the same vertex sets the other way
round. -/
theorem ins_eq_of_derived (hd : D.SkData H G₃) {m : ℕ} (hmr : m ≤ D.rep)
    {ins : Drawing Shat → Set Shat} (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m
      (D.skTangle H m) ins) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
        (hlt : F.E.ncard < 2 * m) :
    ins F = D.ins F := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hinj := cap.isEmbedding.injective
  have hi := D.ins_spec hF (by omega)
  have hFG : F.IsSubdrawing G₃ := hF.1.trans hd.sub
  obtain ⟨hdisc, hsub, hmem⟩ := hins F hF.2 hFG hlt
  have hbd₁ : discBd (ins F) = F.U := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hT hdisc, ← subBd_eq_frontier, hsub]
  have hbd₂ : discBd (D.ins F) = F.U := hi.2.2.2.1
  by_contra hne
  have hsph : IsSphere Shat := by
    by_contra hns
    exact hne (eq_of_discBd_eq hT.isSurface hns hdisc hi.2.2.1 (hbd₁.trans hbd₂.symm))
  obtain ⟨Δ₁, Δ₂, -, -, -, -, -, hun, hcap, -, huniq⟩ := sphere_disc Shat hsph F.U
    (IsCircuit.isOArc_U hF.2)
  have hun' : ins F ∪ D.ins F = univ ∧ ins F ∩ D.ins F = F.U := by
    rcases huniq _ hdisc hbd₁ with e₁ | e₁ <;> rcases huniq _ hi.2.2.1 hbd₂ with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) hne
    · rw [e₁, e₂]
      exact ⟨hun, hcap⟩
    · rw [e₁, e₂, Set.union_comm, Set.inter_comm]
      exact ⟨hun, hcap⟩
    · exact absurd (e₁.trans e₂.symm) hne
  obtain ⟨hU, hI⟩ := hun'
  have hfr₁ : frontier (ins F) = F.U := by rw [← subBd_eq_frontier, hsub]
  have hfr₂ : frontier (D.ins F) = F.U := by
    rw [GM11.IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hbd₂]
  have key : ∀ {X Y : Set Shat}, IsClosed Y → X ∪ Y = univ → X ∩ Y = F.U → frontier X = F.U
    → ∀ z, z ∈ closure Xᶜ ↔ z ∈ Y := fun {X Y} hY hXY hXY' hfr z => by
    refine ⟨fun h => closure_minimal (fun w hw => ?_) hY h, fun h => ?_⟩
    · exact (hXY.symm ▸ mem_univ w : w ∈ X ∪ Y).resolve_left hw
    · by_cases hz : z ∈ X
      · have : z ∈ frontier X := by rw [hfr, ← hXY']; exact ⟨hz, h⟩
        rw [closure_compl]
        exact this.2
      · exact subset_closure hz
  obtain ⟨-, -, q₀, hq, e₁, e₂⟩ := hmem
  simp only at e₁ e₂
  have hcl : ∀ X : Set Shat, closure (univ \ X) = closure Xᶜ := fun X => by rw [compl_eq_univ_sdiff]
  have hV₁ : q₀.1.vertexSet = (D.P.Γ.restrict (cap.emb ⁻¹' closure (D.ins F)ᶜ)).vertexSet := by
    ext v
    have hvi : v ∈ q₀.1.vertexSet ↔ cap.emb v ∈ cap.emb '' q₀.1.vertexSet :=
      (hinj.mem_set_image).symm
    rw [hvi, e₁]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hvH : cap.emb v ∈ H.V := h.1
      rw [hd.sk.hV] at hvH
      have hv : v ∈ D.P.Γ.V := hinj.mem_set_image.mp hvH
      exact ⟨hv, (key hdisc.isClosed (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) hfr₂
        _).mpr h.2⟩
    · exact ⟨(hd.sk.hV ▸ mem_image_of_mem _ h.1 : cap.emb v ∈ H.V),
        (key hdisc.isClosed (by rwa [Set.union_comm]) (by rwa [Set.inter_comm]) hfr₂ _).mp h.2⟩
  have hV₂ : q₀.2.vertexSet = (D.P.Γ.restrict (cap.emb ⁻¹' D.ins F)).vertexSet := by
    ext v
    have hvi : v ∈ q₀.2.vertexSet ↔ cap.emb v ∈ cap.emb '' q₀.2.vertexSet :=
      (hinj.mem_set_image).symm
    rw [hvi, e₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hvH : cap.emb v ∈ H.V := h.1
      rw [hd.sk.hV] at hvH
      have hv : v ∈ D.P.Γ.V := hinj.mem_set_image.mp hvH
      refine ⟨hv, (key hi.2.2.1.isClosed hU hI hfr₁ _).mp ?_⟩
      have := h.2
      rwa [hcl] at this
    · refine ⟨(hd.sk.hV ▸ mem_image_of_mem _ h.1 : cap.emb v ∈ H.V), ?_⟩
      rw [hcl]
      exact (key hi.2.2.1.isClosed hU hI hfr₁ _).mpr h.2
  exact not_mem_of_swapped_vertexSets D.isTangle hi.2.2.2.2 hq hV₂.symm hV₁.symm

/-- **The free sets of (15.2).** Let `X` be a small set of vertices of `sk(Γ)` on the closure of a
region. If a separation of `𝒯'` has `X` on its left and
has order less than `|X|`, then (15.1) gives a circuit of `Γ*` that holds the centre of the region
and more than half its length of `X`.
This is the step from (4) to (5) in the proof of (15.2), done without moving a circuit of the radial
drawing of `sk(Γ)`. -/
theorem exists_circuit_of_not_free (hd : D.SkData H G₃) {m : ℕ} (hmr : m
  ≤ D.rep) (hm : 1 ≤ m) (h3m : 3 * m < 2 * D.ord + 3)
    {ins : Drawing Shat → Set Shat} (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m
      (D.skTangle H m) ins) {r : Set Shat} (hr : r ∈ H.R) {w : Shat} (hw : w ∈ r) (hwV : w ∈ G₃.V)
    {X : Set Shat} (hXV : X ⊆ H.V) (hXr : X ⊆ closure r) (hXm : X.ncard
      ≤ m) {A' B' : Hypergraph Shat (Set Shat)} (hmem : (A', B') ∈ D.skTangle H m)
        (hXA : X ⊆ A'.vertexSet)
    (hord : separationOrder A' B' < X.ncard) : ∃ F : Drawing Shat, F.IsCircuitOf D.rad.G
      ∧ F.E.ncard < 2 * m ∧ F.E.ncard < 2 * (X ∩ D.ins F).ncard ∧ w ∈ D.ins F := by
  classical
  have hS := χ.isSurface
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have h3 := D.P.fits.internally_three_connected
  have hinj := cap.isEmbedding.injective
  have hTg := D.isTangle_skTangle hd.sk hm h3m
  have hsl : IsSlope G₃ (2 * m) ins := GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H)
    hT hTg.isPretangle hd.pre.2.1 hins
  obtain ⟨-, -, q₀, hq, e₁, e₂⟩ := hmem
  simp only at e₁ e₂
  obtain ⟨A, B⟩ := q₀
  simp only at e₁ e₂ hq
  have hsep := D.isTangle.isSeparation hq
  set Z : Set Shat := cap.emb '' (A ∩ B).vertexSet with hZ
  have hZe : Z = (A' ∩ B').vertexSet := by
    change _ = A'.vertexSet ∩ B'.vertexSet
    rw [← e₁, ← e₂, hZ]
    exact image_inter hinj
  have hordq : separationOrder A B < X.ncard := by
    have : Z.ncard = separationOrder A B := ncard_image_of_injective _ hinj
    change (A' ∩ B').vertexSet.ncard < _ at hord
    rw [← hZe] at hord
    omega
  obtain ⟨N, hNG, -, hNV, hcov⟩ := D.exists_inside_cover hq (by omega)
  have hZfin : Z.Finite := (A ∩ B).vertexSet_finite.image _
  have hGZ : ∀ v ∈ N.V, v ∈ H.V → v ∈ Z := fun v hv hvH => by
    rw [hd.sk.hV] at hvH
    obtain ⟨y, hy, rfl⟩ := hvH
    exact mem_image_of_mem _ (hNV y hy hv)
  have hZX : Z.ncard < X.ncard := by
    rw [hZ, ncard_image_of_injective _ hinj]
    exact hordq
  have hshort : ∀ F : Drawing Shat, F.IsCircuit → F.IsSubdrawing N → F.E.ncard < 2 * m
    := fun F hF hFN => by
    have hFc := (GM12.circuit_length_eq_two_mul_ncard hd.pre.2 hF (hFN.trans (hNG.trans hd.sub))).1
    change F.E.ncard = _ at hFc
    have : (F.V ∩ H.V).ncard ≤ Z.ncard := ncard_le_ncard (fun z hz => hGZ z (hFN.1 hz.1) hz.2) hZfin
    omega
  have hagree : ∀ F : Drawing Shat, F.IsCircuit → F.IsSubdrawing N → ins F = D.ins F
    := fun F hF hFN =>
    hd.ins_eq_of_derived hmr hins ⟨hFN.trans hNG, hF⟩ (hshort F hF hFN)
  have hcov' : ∀ x ∈ X, x ∉ Z → ∃ F : Drawing Shat, F.IsCircuit ∧ F.IsSubdrawing N ∧ x ∈ ins F
    := fun x hx hxZ => by
    have hxH := hXV hx
    rw [hd.sk.hV] at hxH
    obtain ⟨v, hv, rfl⟩ := hxH
    have hvA : v ∈ A.vertexSet := by
      have := hXA hx
      rw [← e₁] at this
      exact hinj.mem_set_image.mp this
    have hvB : v ∉ B.vertexSet := fun h => hxZ (mem_image_of_mem _ ⟨hvA, h⟩)
    obtain ⟨c, hc, hvc⟩ := exists_edge_incident hS h3 D.rad hv
    have hvt : v ∈ tilde c := ⟨hvc, fun h => D.P.Γ.disjoint_V hc h hv⟩
    have hcA : c ∈ A.edgeSet := by
      rcases edge_cases hsep hc with h | ⟨-, hcB⟩
      · exact h.1
      · have h₁ : v ∈ D.P.Γ.toHypergraph.ends c := ⟨hc, hv, hvt⟩
        rw [hsep.right_le.ends_eq c hcB] at h₁
        exact absurd (B.vertex_mem_of_inc h₁) hvB
    obtain ⟨F, hF, hFN, hin⟩ := hcov c hcA
    refine ⟨F, hF, hFN, ?_⟩
    rw [hagree F hF hFN]
    have hcl : IsClosed (D.ins F) :=
      (D.ins_spec ⟨hFN.trans hNG, hF⟩ (by have := hshort F hF hFN; omega)).2.2.1.isClosed
    have : cap.emb v ∈ closure (cap.emb '' c) := by
      rw [(cap.isClosedEmbedding hS).closure_image_eq c]
      exact mem_image_of_mem _ hvc
    exact closure_minimal hin hcl this
  obtain ⟨C, hC, hCN, hl, hlX, hwC⟩ := exists_circuit_of_confined_in hT hd.pre.2 hsl hr hw hwV hXV
    hXr hXm (hNG.trans hd.sub) hZfin hGZ hZX hcov'
  rw [hagree C hC hCN] at hlX hwC
  exact ⟨C, ⟨hCN.trans hNG, hC⟩, hl, hlX, hwC⟩

end TangleDatum.SkData

end GraphMinor.GM19
