/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AbsorbingVertices
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumFourFree
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Scheide Absorbing Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hcross_39.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
    G e0) {a b : Fin k} {v u : V}, v ∉ TreeSequenceVertexSet T → u ∈ TreeSequenceVertexSet T →
    Sum.inl u ∈ TwoColorComponent G phi a b (Sum.inl v) → a ∈ MissingColors G phi u → ∃ f ∈
    BoundaryEdges G (TreeSequenceVertexSet T), phi f = some a ∨ phi f = some b := by
  classical
  intro V E _ _ G k e0 phi T a b v u hv hu hcomp ham
  let H := TwoColorIncidenceGraph G phi a b
  have hr : H.Reachable (Sum.inl v) (Sum.inl u) := by
    apply SimpleGraph.ConnectedComponent.exact
    have hm := (SimpleGraph.ConnectedComponent.mem_supp_iff
      (H.connectedComponentMk (Sum.inl v)) (Sum.inl u)).mp hcomp
    exact hm.symm
  obtain ⟨p⟩ := hr
  let S : Set (Sum V E) := {y | match y with
    | Sum.inl q => q ∈ TreeSequenceVertexSet T
    | Sum.inr f => ∀ q, Incident G q f → q ∈ TreeSequenceVertexSet T}
  have hSu : Sum.inl u ∈ S := hu
  have hSv : Sum.inl v ∉ S := by simp [S, hv]
  obtain ⟨d, hd, hds, hdt⟩ := p.reverse.exists_boundary_dart S hSu hSv
  have hadj := d.adj
  have hdmem : d.toProd.1 ∈ p.reverse.support :=
    p.reverse.dart_fst_mem_support_of_mem_darts hd
  have hdtmem : d.toProd.2 ∈ p.reverse.support :=
    p.reverse.dart_snd_mem_support_of_mem_darts hd
  have hfirst : ∃ q : V, d.toProd.1 = Sum.inl q ∧
      q ∈ TreeSequenceVertexSet T := by
    cases h : d.toProd.1 with
    | inl q =>
      rw [h] at hds
      exact ⟨q, rfl, by simpa [S] using hds⟩
    | inr f =>
      exfalso
      cases h2 : d.toProd.2 with
      | inl r =>
        rw [h, h2] at hadj
        change Incident G r f ∧ (phi f = some a ∨ phi f = some b) at hadj
        rw [h] at hds
        have hall : ∀ q, Incident G q f → q ∈ TreeSequenceVertexSet T := by
          simpa [S] using hds
        have hrnot : r ∉ TreeSequenceVertexSet T := by
          intro hr
          apply hdt
          simpa [S, h2] using hr
        exact hrnot (hall r hadj.1)
      | inr e =>
        exfalso
        rw [h, h2] at hadj
        change False at hadj
        exact hadj.elim
  obtain ⟨q, hq, hqT⟩ := hfirst
  have hde : ∃ f : E, d.toProd.2 = Sum.inr f := by
    cases h : d.toProd.2 with
    | inl r =>
      exfalso
      rw [hq, h] at hadj
      change False at hadj
      exact hadj.elim
    | inr f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hde
  have hfadj : (TwoColorIncidenceGraph G phi a b).Adj (Sum.inl q) (Sum.inr f) := by
    rw [hq, hf] at hadj
    exact hadj
  have hfdata : Incident G q f ∧ (phi f = some a ∨ phi f = some b) := by
    simpa [TwoColorIncidenceGraph] using hfadj
  have hnotall : ¬ ∀ r, Incident G r f → r ∈ TreeSequenceVertexSet T := by
    intro hall
    have : d.toProd.2 ∈ S := by simpa [S, hf, hall]
    exact hdt this
  obtain ⟨r, hrf, hrT⟩ : ∃ r, Incident G r f ∧ r ∉ TreeSequenceVertexSet T := by
    push Not at hnotall
    exact hnotall
  have hend : G.ends f = s(q, r) := by
    have hqr : q ≠ r := by
      intro h
      exact hrT (h ▸ hqT)
    exact (Sym2.mem_and_mem_iff hqr).mp ⟨hfdata.1, hrf⟩
  have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, hqT, r, hrT, hend⟩
  exact ⟨f, hfb, hfdata.2⟩

private theorem helper_branch_185.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
    (T : TreeSequence G e0), IsProperEdgeColoring G phi → (4 : ℕ) ≤ (TreeFreeColors phi
    T).card → (∀ (a b : Fin k) (v : V), a ≠ b → a ∈ MissingColors G phi v →
    @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k phi a b) (@Sum.inl V E v)
    (@Fintype.ofFinite (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E)
    (@TwoColorIncidenceGraph V E G k phi a b) (@Sum.inl V E v))) (@Subtype.finite (Sum V E)
    (inferInstance : Finite (Sum V E)) (@Membership.mem (Sum V
    E) (Set (Sum V E)) (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E)
    (@TwoColorIncidenceGraph V E G k phi a b) (@Sum.inl V E v))))) ≤ (1 : ℕ)) → ∀ {u v : V}, u
    ≠ v → u ∈ AbsorbingVertices T phi → v ∈ AbsorbingVertices T phi → Disjoint (MissingColors
    G phi u) (MissingColors G phi v) := by
  classical
  intro V E _ _ G k e0 phi T hproper hfree endpoint u v huv huA hvA
  refine Finset.disjoint_left.mpr ?_
  intro delta hdu hdv
  have huabs : AbsorbingVertex T phi u := by
    simpa [AbsorbingVertices] using huA
  have hvabs : AbsorbingVertex T phi v := by
    simpa [AbsorbingVertices] using hvA
  obtain ⟨gamma, hgamma, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (TreeFreeColors phi
      T).card) delta
  have hgraph : TwoColorIncidenceGraph G phi delta gamma =
      TwoColorIncidenceGraph G phi gamma delta := by
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  obtain ⟨wu, hwuT, hwug, hwuc, huniq_u⟩ := huabs.2 delta hdu gamma hgamma hne
  obtain ⟨wv, hwvT, hwvg, hwvc, huniq_v⟩ := hvabs.2 delta hdv gamma hgamma hne
  have hwvw : wv = wu := huniq_u wv hwvT hwvg
  rw [hwvw] at hwvc
  have hproper_u : @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi gamma delta)
      (Sum.inl u) (Fintype.ofFinite _) ≤ 1 := by
    rw [← hgraph]
    exact endpoint delta gamma u hne.symm hdu
  have hproper_v : @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi gamma delta)
      (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
    rw [← hgraph]
    exact endpoint delta gamma v hne.symm hdv
  obtain ⟨s, t, p, hp, hps⟩ :=
    TwoColorComponentSpanningPath G phi gamma delta hproper (Sum.inl u)
  have hpu : Sum.inl u ∈ p.support := by
    have hm : Sum.inl u ∈ TwoColorComponent G phi gamma delta (Sum.inl u) := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    have hm' : Sum.inl u ∈ {x | x ∈ p.support} := hps.symm ▸ hm
    exact hm'
  have hpv : Sum.inl v ∈ p.support := by
    have hwu_u := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hwuc
    have hwu_v := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hwvc
    have heq : TwoColorComponent G phi gamma delta (Sum.inl u) =
        TwoColorComponent G phi gamma delta (Sum.inl v) := by
      unfold TwoColorComponent
      exact congrArg SimpleGraph.ConnectedComponent.supp (hwu_u.symm.trans hwu_v)
    have hm : Sum.inl v ∈ {x | x ∈ p.support} := hps.symm ▸ (heq ▸
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl)
    exact hm
  have hpsw : Sum.inl wu ∈ p.support := by
    have hm : Sum.inl wu ∈ {x | x ∈ p.support} := hps.symm ▸ hwuc
    exact hm
  have hu_leaf : ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl
      u)).Subsingleton := by
    let : Fintype ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl u)) :=
        Fintype.ofFinite _
    intro z hz z2 hz2
    have hc : Fintype.card ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl u))
        ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hproper_u
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z2, hz2⟩)
  have hv_leaf : ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl
      v)).Subsingleton := by
    let : Fintype ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl v)) :=
        Fintype.ofFinite _
    intro z hz z2 hz2
    have hc : Fintype.card ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl v))
        ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hproper_v
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z2, hz2⟩)
  have hwu_degree := endpoint gamma delta wu hne hwug
  have hwu_leaf : ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl
      wu)).Subsingleton := by
    let : Fintype ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl wu)) :=
        Fintype.ofFinite _
    intro z hz z2 hz2
    have hc : Fintype.card ((TwoColorIncidenceGraph G phi gamma delta).neighborSet (Sum.inl
        wu)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hwu_degree
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨z2, hz2⟩)
  have hu_end : Sum.inl u = s ∨ Sum.inl u = t := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hu_leaf) hpu
  have hv_end : Sum.inl v = s ∨ Sum.inl v = t := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hv_leaf) hpv
  have hwu_end : Sum.inl wu = s ∨ Sum.inl wu = t := by
    by_contra hn
    push Not at hn
    exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hwu_leaf) hpsw
  have huv' : (Sum.inl u : Sum V E) ≠ Sum.inl v := by simpa using huv
  have huw' : (Sum.inl u : Sum V E) ≠ Sum.inl wu := by
    intro h
    apply huabs.1
    exact (Sum.inl.inj h) ▸ hwuT
  have hvw' : (Sum.inl v : Sum V E) ≠ Sum.inl wu := by
    intro h
    apply hvabs.1
    exact (Sum.inl.inj h) ▸ hwuT
  rcases hu_end with hus | hut <;> rcases hv_end with hvs | hvt <;>
    rcases hwu_end with hws | hwt <;>
    all_goals aesop

theorem ScheideAbsorbingElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T ∪ AbsorbingVertices T phi) := by
  classical
  rcases hglobal with ⟨htriple, htree, hcard⟩
  have horder := ScheideGlobalMaximumOrder G k e0 phi T ⟨htriple, htree, hcard⟩
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) := horder.2.2.2.2
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hfree : 4 ≤ (TreeFreeColors phi T).card :=
    ScheideGlobalMaximumFourFree G k e0 phi T ⟨htriple, htree, hcard⟩
  have hcross := @helper_hcross_39 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
  have endpoint := fun a b v (_ : a ≠ b) hm ↦
    TwoColorMissingVertexDegreeAtMostOne G phi hproper a b v
      (neighborEnumeration := Fintype.ofFinite _) (Or.inl hm)
  unfold ColoredVertexSetElementary
  intro u hu v hv huv
  rw [Finset.mem_union] at hu hv
  rcases hu with huT | huA <;> rcases hv with hvT | hvA
  · exact helem huT hvT huv
  · refine Finset.disjoint_left.mpr ?_
    intro delta hdu hdv
    have hvabs : AbsorbingVertex T phi v := by
      simpa [AbsorbingVertices] using hvA
    obtain ⟨gamma, hgamma, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (TreeFreeColors phi
        T).card) delta
    rcases hvabs.2 delta hdv gamma hgamma hne with ⟨w, hwT, hwg, hwc, huniq⟩
    obtain ⟨f, hfb, hfc⟩ := hcross (a := gamma) (b := delta)
      hvabs.1 hwT hwc hwg
    rcases hfc with hfc | hfc
    · exact hclosed hfb hwT hfc hwg
    · exact hclosed hfb huT hfc hdu
  · refine Finset.disjoint_left.mpr ?_
    intro delta hdu hdv
    have huabs : AbsorbingVertex T phi u := by
      simpa [AbsorbingVertices] using huA
    obtain ⟨gamma, hgamma, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (TreeFreeColors phi
        T).card) delta
    rcases huabs.2 delta hdu gamma hgamma hne with ⟨w, hwT, hwg, hwc, huniq⟩
    obtain ⟨f, hfb, hfc⟩ := hcross (a := gamma) (b := delta)
      huabs.1 hwT hwc hwg
    rcases hfc with hfc | hfc
    · exact hclosed hfb hwT hfc hwg
    · exact hclosed hfb hvT hfc hdv
  · exact @helper_branch_185 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
      (@hproper) (@hfree) (@endpoint) (@u) (@v) (@huv) (@huA) (@hvA)
end GoldbergSeymour

end
