/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section75Case2Lift
public import LeanPool.GraphMinor.GM12.Section73Tangle
public import LeanPool.GraphMinor.GM11.Theorem65
public import LeanPool.GraphMinor.GM11.Theorem66

/-!
# The step of (6.6) at order 2 in Case 2 of XII (7.5)

At `θ = 3`, Case 2 of (7.5) passes from the tangle `T₂` of order 2 in `Γ₂ = Γ₁ \ v` to a tangle of
order 2
in `Γ₃`, by (6.6). But (6.6) fails at order 2 for a drawing with loops, and `Γ₃` may have loops. We
use
that `T₂` comes from a tangle `T₁` of order 3 in `Γ₁`.

Let `T₃` be the pretangle in `Γ₃` induced by the slope of `T₂`. By X (2.7) we need that a loop `e`
of `Γ₃`
has a small side. Suppose not. Then `Γ₃ \ e` is small. Let `s` be the region of `J` containing `e`,
and
`g` the edge of `Γ₂` in `s`. Every other region of `J` lies in the disc of a short circuit in
`N(Z)`, and
`N(Z)` lies in `sBar`, so the vertex of `Γ₂` on that circuit is an end of `g`. By (6.3) these discs
give
two members of `T₂`, one for each end of `g`, whose left sides and `g` make up `Γ₂`. This
contradicts
`false_of_cover_of_edge`.
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

private theorem vertex_side_join_contains_selected_insides
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {J : Drawing S}
    {ins : Drawing S → Set S}
    (H : Drawing S)
    (hJ₂ : (PaintingOrDrawing.drawing H).IsRadialDrawing J)
    (hE₂ : H.E.Nonempty)
    (T₂ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (hresp : (PaintingOrDrawing.drawing H).IsRespectful 2 T₂)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) J 2 T₂ ins)
    (hp₂ : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph 2 T₂)
    (Cs : Set (Drawing S))
    (hCJ : ∀ C ∈ Cs, C.IsCircuit ∧ C.IsSubdrawing J ∧ C.length < 2 * 2)
    (pair : Drawing S → Hypergraph S (Set S) × Hypergraph S (Set S))
    (hPairEdges : ∀ C, (pair C).1.edgeSet ⊆ {f | f ⊆ ins C})
    (P : S → Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (hP : ∀ h, P h = pair '' {C ∈ Cs | C.V ∩ H.V ⊆ {h}})
    (hPs : ∀ (h : S), ∀ p ∈ P h, H.toHypergraph.IsSeparation p.1 p.2)
    (hPm : ∀ (h : S), ∀ p ∈ P h, (p.1 ∩ p.2).vertexSet ⊆ {h})
:
    ∀ (h : S) (hh : h ∈ H.toHypergraph.vertexSet), (joinLeft H.toHypergraph (P h) h (hPs h) hh,
      joinRight H.toHypergraph (P h) h (hPs h) hh (hPm h)) ∈ T₂ := by
  intro h hh
  have ht := theorem_6_3_proof S hS inferInstance (PaintingOrDrawing.drawing H) J 2 T₂ ins hJ₂.1
    hE₂ hp₂
    hresp hJ₂ hins
  have hsepj := join_isSeparation (hPs h) hh (hPm h)
  have hmj := join_inter_subset (hPs h) hh (hPm h)
  have hordj : separationOrder (joinLeft H.toHypergraph (P h) h (hPs h) hh)
      (joinRight H.toHypergraph (P h) h (hPs h) hh (hPm h)) < 2 := by
    unfold separationOrder
    rw [hmj, ncard_singleton]
    omega
  refine (ht.1 _ _ hsepj hordj).mpr ?_
  set A := joinLeft H.toHypergraph (P h) h (hPs h) hh with hA
  have hex : ∀ f : A.edgeSet, ∃ C, (C ∈ Cs ∧ C.V ∩ H.V ⊆ {h}) ∧ f.1 ⊆ ins C := by
    rintro ⟨f, hf⟩
    obtain ⟨p, hp, hf'⟩ := mem_iUnion₂.mp hf
    rw [hP] at hp
    obtain ⟨C, hC, rfl⟩ := hp
    exact ⟨C, hC, hPairEdges C hf'⟩
  choose C' hC' using hex
  have : Fintype A.edgeSet := A.edgeSet_finite.fintype
  refine ⟨Fintype.card A.edgeSet, fun i => C' ((Fintype.equivFin _).symm i), fun i => ?_, ?_⟩
  · obtain ⟨hc, hs'⟩ := (hC' ((Fintype.equivFin _).symm i)).1
    refine ⟨(hCJ _ hc).1, (hCJ _ hc).2.1, (hCJ _ hc).2.2, fun w hw => ?_⟩
    have hw' := hs' hw
    rw [hmj]
    exact hw'
  · intro f hf
    refine ⟨Fintype.equivFin _ ⟨f, hf⟩, ?_⟩
    simpa using (hC' ⟨f, hf⟩).2

private theorem edge_covered_by_selected_circuit
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    {Γ₃ : Drawing S}
    {J : Drawing S}
    {ins : Drawing S → Set S}
    (H : Drawing S)
    (hrad₂ : PreRad (PaintingOrDrawing.drawing H) J)
    (F₂ : RegionFacts (PaintingOrDrawing.drawing H) J)
    (e : Set S)
    (x : S)
    (s : Set S)
    (hs : s ∈ J.R)
    (hxs : x ∈ s)
    (hes : e ⊆ s)
    (g : Set S)
    (hg : g ∈ (PaintingOrDrawing.drawing H).E)
    (hgs : g ⊆ s)
    (Z : Set (Set S))
    (hsmall : IsSmall J ins (2 * 2) (PaintingOrDrawing.drawing Γ₃).V 2 Z)
    (hsZ : ∀ r ∈ J.R, r ≠ s → r ∈ Z)
    :
    ∀ f ∈ H.E, f ≠ g → ∃ C : Drawing S,
      (C.IsCircuit ∧ C.IsSubdrawing (boundaryDrawing J Z) ∧ C.length < 2 * 2) ∧ f ⊆ ins C := by
  intro f hf hfg
  obtain ⟨y, hy⟩ := hf.1
  have hfdis : Disjoint f J.U := edge_disjoint hrad₂ hf
  obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem (disjoint_left.mp hfdis hy)
  have hfr' : f ⊆ r := subset_region hr hf.2.2.1.isConnected.isPreconnected hfdis hy hyr
  have hrs : r ≠ s := by
    rintro rfl
    exact hfg (F₂.2.1 r hr f hf g hg hfr' hgs)
  obtain ⟨C, hC, hCsub, hl, hin⟩ := hsmall.2 r (hsZ r hr hrs)
  exact ⟨C, ⟨hC, hCsub, hl⟩, hfr'.trans hin⟩

/-- See the module docstring. -/
theorem isTangle_induced_of_order_three (hS : IsClosedSurface S) {Γ₁ Γ₃ J : Drawing S} {v : S}
    {T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hT₁ : IsTangle Γ₁.toHypergraph 3 T₁) (hv : v ∈ Γ₁.V)
    (hresp : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRespectful 2
      (deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3))
    (hJ₂ : (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})).IsRadialDrawing J)
    (hJ₃ : (PaintingOrDrawing.drawing Γ₃).IsRadialDrawing J)
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ₁ {v})) J 2
      (deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3) ins)
    (hE₂ : (deleteVertices Γ₁ {v}).E.Nonempty) (hE₃ : Γ₃.E.Nonempty) :
    IsTangle Γ₃.toHypergraph 2 (inducedPretangle (PaintingOrDrawing.drawing Γ₃) J 2 ins) := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set H := deleteVertices Γ₁ {v} with hH
  set T₂ := deleteVerticesTangle Γ₁.toHypergraph {v} T₁ 3 with hT₂def
  have hT₂ : IsTangle H.toHypergraph 2 T₂ := theorem_7_3_tangle (by decide) hT₁ hv
  have hT₂' : IsTangle (Γ₁.toHypergraph.deleteVertices {v}) 2 T₂ := by
    rw [← deleteVertices_toHypergraph]
    exact hT₂
  have hp₂ : IsPretangle (PaintingOrDrawing.drawing H).toHypergraph 2 T₂ :=
    IsTangle.isPretangle hT₂
  have hsl := isSlope_of_derived hS hp₂ hJ₂.2.1.1 hins
  obtain ⟨hp₃, -, -⟩ := theorem_6_1_proof (Γ := PaintingOrDrawing.drawing Γ₃) hS hE₃ hJ₃
    (by norm_num) hsl
  have hrad₂ : PreRad (PaintingOrDrawing.drawing H) J := ⟨hJ₂.1, hJ₂.2.1⟩
  have hrad₃ : PreRad (PaintingOrDrawing.drawing Γ₃) J := ⟨hJ₃.1, hJ₃.2.1⟩
  have F₂ := regionFacts_of_radial hrad₂ hS hJ₂.2.2 hE₂
  have F₃ := regionFacts_of_radial hrad₃ hS hJ₃.2.2 hE₃
  refine (GraphMinor.GM10.theorem_2_7_proof hp₃.one_le hp₃.isSeparation hp₃.order_lt hp₃.axiom1
    hp₃.axiom2).mpr ?_
  intro e he hsize
  have heE : e ∈ Γ₃.E := he
  have hsep := isSeparation_edgeHypergraph_deleteEdges (G := Γ₃.toHypergraph) he
  have hord : separationOrder (edgeHypergraph Γ₃.toHypergraph e)
      (Γ₃.toHypergraph.deleteEdges {e}) < 2 := by
    rwa [separationOrder_edgeHypergraph_deleteEdges]
  refine (hp₃.axiom1 hsep hord).resolve_right fun hbad => ?_
  obtain ⟨-, -, hsmall⟩ := hbad
  -- The region `s` of `J` containing `e`, and the edge `g` of `Γ₂` in it.
  obtain ⟨x, hx⟩ := heE.1
  have hedis : Disjoint e J.U := edge_disjoint hrad₃ heE
  obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem (disjoint_left.mp hedis hx)
  have hes : e ⊆ s := subset_region hs heE.2.2.1.isConnected.isPreconnected hedis hx hxs
  obtain ⟨g, hg, hgs⟩ := F₂.1 s hs
  set Z := PaintingOrDrawing.regionsIncludingEdge J (Γ₃.toHypergraph.deleteEdges {e}) with hZ
  have hsZ : ∀ r ∈ J.R, r ≠ s → r ∈ Z := by
    intro r hr hrs
    obtain ⟨e', he', he'r⟩ := F₃.1 r hr
    refine ⟨hr, e', ⟨he', fun h' => hrs ?_⟩, he'r⟩
    obtain rfl : e' = e := h'
    exact region_eq_of_mem hr hs (he'r hx) hxs
  set N := boundaryDrawing J Z with hN
  have hNsub : N.IsSubdrawing J := Drawing.span_isSubdrawing J _ _
  -- A vertex of `Γ₂` on `N(Z)` is an end of `g`.
  have hNV : ∀ w ∈ N.V, w ∈ H.V → w ∈ closure g := by
    intro w hw hwH
    have hcl : w ∈ closure s := by
      rcases hw with ⟨⟨-, r, ⟨hrR, hrZ⟩, -, -, hwr⟩, -⟩ | hw
      · by_cases hrs : r = s
        · exact hrs ▸ hwr
        · exact absurd (hsZ r hrR hrs) hrZ
      · obtain ⟨e', ⟨⟨-, r, ⟨hrR, hrZ⟩, -, -, hne⟩, he'J⟩, hwe'⟩ := mem_iUnion₂.mp hw
        have hrs : r = s := by
          by_contra hrs
          exact hrZ (hsZ r hrR hrs)
        subst hrs
        exact closure_minimal (edge_subset_closure_of_incident hS he'J hrR hne) isClosed_closure
          hwe'.1
    exact F₂.2.2 s hs g hg hgs w hwH hcl
  set Cs : Set (Drawing S) := {C | C.IsCircuit ∧ C.IsSubdrawing N ∧ C.length < 2 * 2} with hCs
  have hCJ : ∀ C ∈ Cs, C.IsCircuit ∧ C.IsSubdrawing J ∧ C.length < 2 * 2 :=
    fun C hC => ⟨hC.1, hC.2.1.trans hNsub, hC.2.2⟩
  let pair : Drawing S → Hypergraph S (Set S) × Hypergraph S (Set S) := fun C =>
    ((PaintingOrDrawing.drawing H).inter (ins C), (PaintingOrDrawing.drawing H).interOutside
      (ins C))
  have hpair : ∀ C ∈ Cs, pair C ∈ T₂ := fun C hC =>
    (hins C (hCJ C hC).1 (hCJ C hC).2.1 (hCJ C hC).2.2).2.2
  have hfr : ∀ C ∈ Cs, frontier (ins C) = C.U := fun C hC => by
    rw [← subBd_eq_frontier]
    exact (hins C (hCJ C hC).1 (hCJ C hC).2.1 (hCJ C hC).2.2).2.1
  have hcl : ∀ C ∈ Cs, IsClosed (ins C) := fun C hC =>
    (IsClosedDisc.isCompact (hins C (hCJ C hC).1 (hCJ C hC).2.1 (hCJ C hC).2.2).1).isClosed
  -- The two sides of `pair C` meet in the vertices of `Γ₂` on `C`.
  have hmeet : ∀ C ∈ Cs, ((pair C).1 ∩ (pair C).2).vertexSet = C.V ∩ H.V := by
    intro C hC
    ext w
    constructor
    · rintro ⟨⟨hwH, hwi⟩, -, hwo⟩
      have hwf : w ∈ frontier (ins C) := by
        rw [frontier_eq_closure_inter_closure]
        refine ⟨subset_closure hwi, ?_⟩
        rwa [compl_eq_univ_sdiff]
      rw [hfr C hC] at hwf
      refine ⟨?_, hwH⟩
      by_contra hwV
      obtain ⟨f, hf, hwfe⟩ := C.exists_edge_of_mem hwf hwV
      exact ((hCJ C hC).2.1.2 hf).2.1 hwfe |>.2 (hJ₂.2.1.2.1 hwH)
    · rintro ⟨hwC, hwH⟩
      have hwf : w ∈ frontier (ins C) := by
        rw [hfr C hC]
        exact C.V_subset_U hwC
      have hwf' := hwf
      rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff] at hwf'
      have hwi : w ∈ ins C := (hcl C hC).closure_eq ▸ hwf'.1
      exact ⟨⟨hwH, hwi⟩, hwH, hwf'.2⟩
  have hlt : ∀ C ∈ Cs, (C.V ∩ H.V).ncard < 2 := by
    intro C hC
    rw [← hmeet C hC]
    exact hT₂.order_lt (hpair C hC)
  obtain ⟨h₁, h₂, hh₁, hh₂, hgends⟩ : ∃ h₁ h₂, h₁ ∈ H.V ∧ h₂ ∈ H.V ∧
      closure g ∩ H.V = {h₁, h₂} := by
    rcases H.edge_cond g hg with ⟨a, b, -, hc, -⟩ | ⟨a, hc, -⟩
    · have ha : a ∈ closure g ∩ H.V := by rw [hc]; simp
      have hb : b ∈ closure g ∩ H.V := by rw [hc]; simp
      exact ⟨a, b, ha.2, hb.2, hc⟩
    · have ha : a ∈ closure g ∩ H.V := by rw [hc]; simp
      exact ⟨a, a, ha.2, ha.2, by rw [hc]; simp⟩
  -- Each short circuit in `N(Z)` meets `Γ₂` in at most one of the ends of `g`.
  have hend : ∀ C ∈ Cs, C.V ∩ H.V ⊆ {h₁} ∨ C.V ∩ H.V ⊆ {h₂} := by
    intro C hC
    have hfin : (C.V ∩ H.V).Finite := C.finite_V.subset inter_subset_left
    have hone : ∀ a ∈ C.V ∩ H.V, ∀ b ∈ C.V ∩ H.V, a = b := fun a ha b hb => by
      by_contra hab
      have h2 := ncard_le_ncard (show ({a, b} : Set S) ⊆ C.V ∩ H.V by
        rintro z (rfl | rfl)
        · exact ha
        · exact hb) hfin
      rw [ncard_pair hab] at h2
      have := hlt C hC
      omega
    rcases (C.V ∩ H.V).eq_empty_or_nonempty with he | ⟨a, ha⟩
    · exact Or.inl (he ▸ empty_subset _)
    have hag : a ∈ closure g ∩ H.V := ⟨hNV a (hC.2.1.1 ha.1) ha.2, ha.2⟩
    rw [hgends] at hag
    rcases hag with rfl | rfl
    · exact Or.inl fun b hb => hone b hb _ ha
    · exact Or.inr fun b hb => hone b hb _ ha
  let P : S → Set (Hypergraph S (Set S) × Hypergraph S (Set S)) := fun h =>
    pair '' {C | C ∈ Cs ∧ C.V ∩ H.V ⊆ {h}}
  have hPs : ∀ h, ∀ p ∈ P h, H.toHypergraph.IsSeparation p.1 p.2 := by
    rintro h _ ⟨C, hC, rfl⟩
    exact hT₂.isSeparation (hpair C hC.1)
  have hPm : ∀ h, ∀ p ∈ P h, (p.1 ∩ p.2).vertexSet ⊆ {h} := by
    rintro h _ ⟨C, hC, rfl⟩
    rw [hmeet C hC.1]
    exact hC.2
  have hthe := fun (h : S) (hh : h ∈ H.toHypergraph.vertexSet) =>
    join_isSeparation (hPs h) hh (hPm h)
  -- The join for an end of `g` is in `T₂`, by (6.3).
  have hjoin : ∀ h (hh : h ∈ H.toHypergraph.vertexSet),
      (joinLeft H.toHypergraph (P h) h (hPs h) hh,
        joinRight H.toHypergraph (P h) h (hPs h) hh (hPm h)) ∈ T₂ := by
    exact vertex_side_join_contains_selected_insides (S := S) hS (J := J) (ins := ins)
      H hJ₂ hE₂ T₂ hresp hins hp₂ Cs hCJ pair (fun _ _ hf => hf.2) P (fun _ => rfl) hPs hPm
  -- Every edge of `Γ₂` other than `g` lies in the disc of a short circuit in `N(Z)`.
  have hcover : ∀ f ∈ H.E, f ≠ g → ∃ C ∈ Cs, f ⊆ ins C := by
    exact edge_covered_by_selected_circuit (S := S) (Γ₃ := Γ₃) (J := J) (ins := ins) H hrad₂ F₂ e
      x s hs hxs hes g hg hgs Z hsmall hsZ
  have hmemP : ∀ C ∈ Cs, pair C ∈ P h₁ ∨ pair C ∈ P h₂ := fun C hC =>
    (hend C hC).imp (fun h' => ⟨C, ⟨hC, h'⟩, rfl⟩) (fun h' => ⟨C, ⟨hC, h'⟩, rfl⟩)
  have hedge : ∀ {f}, f ∈ H.E → ∀ C ∈ Cs, f ⊆ ins C → f ∈ (pair C).1.edgeSet :=
    fun hf C _ hsub => ⟨hf, hsub⟩
  rw [← deleteVertices_toHypergraph] at hT₂'
  refine false_of_cover_of_edge (A₁ := joinLeft H.toHypergraph (P h₁) h₁ (hPs h₁) hh₁)
    (A₂ := joinLeft H.toHypergraph (P h₂) h₂ (hPs h₂) hh₂)
    (drawing_toHypergraph_isGraph Γ₁) hT₁ hv ?_ (hjoin h₁ hh₁) (hjoin h₂ hh₂)
    (g := g) ((deleteVertices_isSubdrawing Γ₁ {v}).2 hg) ?_ ?_
  · rw [← deleteVertices_toHypergraph]
    exact hT₂
  · intro w hw hwv
    have hwH : w ∈ H.V := by
      rw [hH, deleteVertices_V]
      exact ⟨hw, hwv⟩
    obtain ⟨f, hf, hwf⟩ := exists_edge_of_regionFacts hS F₂ hwH
    by_cases hfg : f = g
    · have : w ∈ closure g ∩ H.V := ⟨hfg ▸ hwf, hwH⟩
      rw [hgends] at this
      rcases this with rfl | rfl
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
    · obtain ⟨C, hC, hin⟩ := hcover f hf hfg
      have hwi : w ∈ ins C := (hcl C hC).closure_eq ▸ closure_mono hin hwf
      rcases hmemP C hC with h' | h'
      · exact Or.inl (Or.inr (mem_biUnion h' ⟨hwH, hwi⟩))
      · exact Or.inr (Or.inr (mem_biUnion h' ⟨hwH, hwi⟩))
  · intro f hf hfv hfg
    have hfH : f ∈ H.E := by
      have h' : f ∈ (Γ₁.toHypergraph.deleteVertices {v}).edgeSet := ⟨hf, fun u hu => hu ▸ hfv⟩
      rw [← deleteVertices_toHypergraph] at h'
      exact h'
    obtain ⟨C, hC, hin⟩ := hcover f hfH hfg
    rcases hmemP C hC with h' | h'
    · exact Or.inl (mem_biUnion h' (hedge hfH C hC hin))
    · exact Or.inr (mem_biUnion h' (hedge hfH C hC hin))

end GraphMinor.GM12
