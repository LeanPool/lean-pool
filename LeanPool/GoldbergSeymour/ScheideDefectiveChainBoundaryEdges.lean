/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPath
public import LeanPool.GoldbergSeymour.ScheideDefectiveChainPathExists
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumBoundaryFacts
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TreeUsedColors
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

public import LeanPool.GoldbergSeymour.TashkinovOrderBound

/-!
# Scheide Defective Chain Boundary Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_present_eq_179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k) (u
        : V) (f : E), alpha ≠ gamma →
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha gamma (Sum.inr f);
        Sum.inl u ∉ Q → (
    ∀ (e : E), Sum.inr e ∈ Q → phi e = some alpha ∨ phi e = some gamma) → (
    ∀ (v : V) (e : E), Incident G v e → Sum.inr e ∈ Q → Sum.inl v ∈ Q) → (
    ∀ v ∈ TreeSequenceVertexSet T, alpha ∈ PresentColors G phi v) → (
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ u → gamma ∈ PresentColors G phi v) → (
    ∀ (v : V) (e : E), Sum.inl v ∈ Q → Incident G v e → phi e = some alpha ∨ phi e = some gamma →
        Sum.inr e ∈ Q) →
    ∀ v ∈ TreeSequenceVertexSet T, PresentColors G psi v = PresentColors G phi v := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma u f hne Q psi huQ qcolor qvertex halpha_present
      hgamma_present qedge_of_vertex v hv
  let _ := Fintype.ofFinite V
  have vnot : Sum.inl v ∉ Q ∨ v ≠ u := by
    by_cases hvq : Sum.inl v ∈ Q
    · right
      intro hvu
      exact huQ (hvu ▸ hvq)
    · exact Or.inl hvq
  ext c
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, hev, hec⟩
    by_cases heq : Sum.inr e ∈ Q
    · have hce : phi e = some alpha ∨ phi e = some gamma := qcolor e heq
      rcases hce with hca | hcg
      · have hvne : v ≠ u := by
          intro hvu
          exact huQ (hvu ▸ qvertex v e hev heq)
        have hgp : gamma ∈ PresentColors G phi v :=
          hgamma_present v hv hvne
        obtain ⟨g, hgv, hgc⟩ := by simpa [PresentColors] using hgp
        have hc : c = gamma := by
          apply Option.some.inj
          simpa [psi, Q, TwoColorComponentSwap, heq, hca, hne, hne.symm] using hec.symm
        subst c
        refine ⟨g, hgv, ?_⟩
        have hgq := qedge_of_vertex v g (qvertex v e hev heq) hgv (Or.inr hgc)
        simp [hgc]
      · have hap := halpha_present v hv
        obtain ⟨a, hav, hac⟩ := by simpa [PresentColors] using hap
        have hc : c = alpha := by
          apply Option.some.inj
          simpa [psi, Q, TwoColorComponentSwap, heq, hcg, hne, hne.symm] using hec.symm
        subst c
        refine ⟨a, hav, ?_⟩
        have haq := qedge_of_vertex v a (qvertex v e hev heq) hav (Or.inl hac)
        simp [hac]
    · refine ⟨e, hev, ?_⟩
      simpa [psi, Q, TwoColorComponentSwap, heq] using hec
  · rintro ⟨e, hev, hec⟩
    by_cases heq : Sum.inr e ∈ Q
    · have hce : phi e = some alpha ∨ phi e = some gamma := qcolor e heq
      rcases hce with hca | hcg
      · have hvne : v ≠ u := by
          intro hvu
          exact huQ (hvu ▸ qvertex v e hev heq)
        have hgp := hgamma_present v hv hvne
        obtain ⟨g, hgv, hgc⟩ := by simpa [PresentColors] using hgp
        have hc : c = alpha := Option.some.inj (hec.symm.trans hca)
        subst c
        refine ⟨g, hgv, ?_⟩
        have hgq : Sum.inr g ∈ Q :=
          qedge_of_vertex v g (qvertex v e hev heq) hgv (Or.inr hgc)
        simp [hgq, psi, Q, TwoColorComponentSwap, hgc]
      · have hap := halpha_present v hv
        obtain ⟨a, hav, hac⟩ := by simpa [PresentColors] using hap
        have hc : c = gamma := Option.some.inj (hec.symm.trans hcg)
        subst c
        refine ⟨a, hav, ?_⟩
        have haq := qedge_of_vertex v a (qvertex v e hev heq) hav (Or.inl hac)
        simp [haq, psi, Q, TwoColorComponentSwap, hac]
    · refine ⟨e, hev, ?_⟩
      simpa [psi, Q, TwoColorComponentSwap, heq] using hec

private theorem helper_huQ_190.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k) (u z :
        V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p →
    ∀ (f : E), Sum.inr f ∉ p.support →
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f); Sum.inl u ∉ Q := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma u z p hp f hnot Q huq
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  have huf : Sum.inl u ∈ TwoColorComponent G phi alpha gamma (Sum.inr f) := huq
  have huf' : Sum.inr f ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
    change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
        (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
        (Sum.inl u)
    exact huf.symm
  have hps : Sum.inr f ∈ p.support := by
    have hh : Sum.inr f ∈ {x | x ∈ p.support} := by
      rw [hp.2.2.2]
      exact huf'
    exact hh
  exact hnot hps

private theorem helper_qcolor_204.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k) (f
        : E), f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi f = some alpha →
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f);
    ∀ (e : E), Sum.inr e ∈ Q → phi e = some alpha ∨ phi e = some gamma := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma f h Q e he
  by_cases hef : e = f
  · exact Or.inl (by simpa [hef] using h.2)
  · have hs : Sum.inr e ∈
        (TwoColorIncidenceGraph G phi alpha gamma).support := by
      apply SimpleGraph.mem_support_of_reachable
      · intro hh
        apply hef
        exact Sum.inr.inj hh
      · change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
          (Sum.inr e) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
          (Sum.inr f) at he
        exact SimpleGraph.ConnectedComponent.eq.mp he
    obtain ⟨w, hw⟩ := (TwoColorIncidenceGraph G phi alpha gamma).mem_support.mp hs
    cases w with
    | inl v => exact hw.2
    | inr e' => simp [TwoColorIncidenceGraph] at hw

private theorem helper_one_psi_274.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (alpha gamma : Fin k) (f : E), alpha ≠ gamma →
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha gamma (Sum.inr f); (
    ∀ (e : E), Sum.inr e ∈ Q → phi e = some alpha ∨ phi e = some gamma) → IsOneEdgeUncolored phi
        e0 → Sum.inr e0 ∉ Q → IsOneEdgeUncolored psi e0 := by
  classical
  intro V E G k e0 phi alpha gamma f hne Q psi qcolor one e0not
  refine ⟨?_, ?_⟩
  · simpa [psi, Q, TwoColorComponentSwap, e0not] using one.1
  · intro e he
    obtain ⟨c, hc⟩ := one.2 e he
    by_cases hqe : Sum.inr e ∈ Q
    · rcases qcolor e hqe with hα | hγ
      · refine ⟨gamma, ?_⟩
        simp [psi, Q, TwoColorComponentSwap, hqe, hα]
      · refine ⟨alpha, ?_⟩
        simp [psi, Q, TwoColorComponentSwap, hqe, hγ, hne.symm]
    · refine ⟨c, ?_⟩
      simpa [psi, Q, TwoColorComponentSwap, hqe] using hc

private theorem helper_tree_fixed_287.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
        alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T) → gamma ∈ TreeFreeColors phi T →
        Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧
        Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) →
    ∀ (f : E),
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f);
    let psi : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha gamma (Sum.inr f); (
    ∀ (e : E), Sum.inr e ∈ Q → phi e = some alpha ∨ phi e = some gamma) → IsOneEdgeUncolored phi
        e0 → Sum.inr e0 ∉ Q →
    ∀ (j : Fin T.length), psi (T.edge j) = phi (T.edge j) := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma halpha hgammaFree hunused f Q psi qcolor one e0not j
  by_cases hj : j.val = 0
  · have hje : j = ⟨0, T.positive⟩ := by apply Fin.ext; exact hj
    subst j
    rw [T.first_edge]
    simp [one.1, e0not, psi, Q, TwoColorComponentSwap]
  · by_cases hqe : Sum.inr (T.edge j) ∈ Q
    · rcases qcolor (T.edge j) hqe with hα | hγ
      · have hused : alpha ∈ TreeUsedColors phi T := by
          simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, by omega, hα⟩
        exact False.elim ((Finset.disjoint_left.mp hunused.1 halpha) hused)
      · have hused : gamma ∈ TreeUsedColors phi T := by
          simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, by omega, hγ⟩
        exact False.elim ((Finset.disjoint_left.mp hunused.2 hgammaFree) hused)
    · simp [psi, Q, TwoColorComponentSwap, hqe]

private theorem helper_qvertex_297.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (phi :
        PartialEdgeColoring E k) (alpha gamma : Fin k) (f : E),
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f); (
    ∀ (e : E), Sum.inr e ∈ Q → phi e = some alpha ∨ phi e = some gamma) →
    ∀ (v : V) (e : E), Incident G v e → Sum.inr e ∈ Q → Sum.inl v ∈ Q := by
  classical
  intro V E G k phi alpha gamma f Q qcolor v e hev he
  have hc := qcolor e he
  have hadj : (TwoColorIncidenceGraph G phi alpha gamma).Adj
      (Sum.inl v) (Sum.inr e) := by
    simp [TwoColorIncidenceGraph, hev, hc]
  change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inl v) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inr f)
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans he

private theorem helper_hgamma_present_318.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (gamma : Fin k),
    ∀ u ∈ TreeSequenceVertexSet T, gamma ∈ MissingColors G phi u → TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) →
    ∀ v ∈ TreeSequenceVertexSet T, v ≠ u → gamma ∈ PresentColors G phi v := by
  classical
  intro V E _ _ _ G k e0 phi T gamma u hu hgamma horder v hv hnevu
  have helem := horder.2.2.2.1 hu hv hnevu.symm
  have hn : gamma ∉ MissingColors G phi v := by
    intro hm
    exact Finset.disjoint_left.mp helem hgamma hm
  simpa [MissingColors] using hn

private theorem helper_qedge_of_vertex_326.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (phi :
        PartialEdgeColoring E k) (alpha gamma : Fin k) (f : E),
    let Q : Set (V ⊕ E) := TwoColorComponent G phi alpha gamma (Sum.inr f);
    ∀ (v : V) (e : E), Sum.inl v ∈ Q → Incident G v e → phi e = some alpha ∨ phi e = some gamma →
        Sum.inr e ∈ Q := by
  classical
  intro V E G k phi alpha gamma f Q v e hv hev hc
  change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inr e) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inr f)
  apply (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ?_).trans hv
  simp [TwoColorIncidenceGraph, hev, hc]

private theorem helper_fnew_362.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (e0 : E) (T
        : TreeSequence G e0) (f : E) (x y : V), y ∉ TreeSequenceVertexSet T → G.ends f = s(x, y) →
        (
    ∀ (i : Fin (T.length + (1 : ℕ))), T.vertex i ∈ TreeSequenceVertexSet T) →
    ∀ (j : Fin T.length), f ≠ T.edge j := by
  classical
  intro V E _ _ G e0 T f x y hy hends vertex_mem j heq
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨i, hi⟩ := T.attaches j
  have hyend : y ∈ G.ends (T.edge j) := by
    rw [← heq, hends]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  rw [hi] at hyend
  rcases Sym2.mem_iff.mp hyend with hvv | hvv
  · exact hy (hvv ▸ vertex_mem j.succ)
  · exact hy (hvv ▸ vertex_mem (Fin.castLT i (by omega)))

private theorem helper_first_edge_499.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E]
    (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0) (f : E),
  Fin.lastCases f (fun (i : Fin T.length) ↦ T.edge i)
      (⟨(0 : ℕ), by
          omega⟩ :
        Fin (T.length + (1 : ℕ))) =
    e0 := by
  classical
  intro V E _ _ G e0 T f
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  have hz : (⟨0, Nat.succ_pos _⟩ : Fin (T.length + 1)) =
      (⟨0, T.positive⟩ : Fin T.length).castSucc := by rfl
  rw [hz]
  simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
  exact T.first_edge

private noncomputable abbrev helperTplus474.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [Fintype V] →
  [Fintype E] →
  (G : LooplessMultigraph V E) →
  (e0 : E) →
  (T : TreeSequence G e0) →
  (f : E) →
  (x : V) →
  (hx : x ∈ TreeSequenceVertexSet T) →
  (y : V) →
  (hy : y ∉ TreeSequenceVertexSet T) →
  (hends : G.ends f = s(x, y)) →
  (vertex_mem :
      ∀ (i : Fin (T.length + (1 : ℕ))),
        T.vertex i ∈ TreeSequenceVertexSet T) →
  (fnew : ∀ (j : Fin T.length), f ≠ T.edge j) →
  TreeSequence G e0 := by
  classical
  intro V E _ _ G e0 T f x hx y hy hends vertex_mem fnew
  exact {
    length := T.length + 1
    positive := by omega
    vertex := Fin.lastCases y (fun i => T.vertex i)
    edge := Fin.lastCases f (fun i => T.edge i)
    vertex_injective := by
      intro i j
      revert j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij; rfl
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
          exact (hy (hij ▸ vertex_mem j)).elim
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
          exact (hy (hij ▸ vertex_mem i)).elim
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
          exact congrArg Fin.castSucc (T.vertex_injective hij)
    edge_injective := by
      intro i j
      revert j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij; rfl
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
          exact (fnew j hij).elim
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
          exact (fnew i hij.symm).elim
        · intro hij
          dsimp only [Fin.lastCases] at hij
          rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
          exact congrArg Fin.castSucc (T.edge_injective hij)
    first_edge := by
      exact @helper_first_edge_499 (@V) (@E) inferInstance inferInstance  (@G) (@e0)
          (@T) (@f)
    attaches := by
      intro j
      by_cases hj : j = Fin.last T.length
      · subst j
        obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hx
        refine ⟨i, ?_⟩
        have hc : (Fin.castLT i (by omega) : Fin (T.length + 1 + 1)) = i.castSucc := by
          apply Fin.ext; rfl
        rw [hc]
        simp only [Fin.lastCases, Fin.reverseInduction_last, Fin.succ_last, Nat.succ_eq_add_one,
  Fin.reverseInduction_castSucc]
        rw [hends, ← hi]
        exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩)
      · have hjle : j.val ≤ T.length := Nat.lt_succ_iff.mp j.isLt
        have hjne : j.val ≠ T.length := by
          intro heq; apply hj; apply Fin.ext; simpa using heq
        have hj' : j.val < T.length := Nat.lt_of_le_of_ne hjle hjne
        obtain ⟨i, hi⟩ := T.attaches (j.castPred hj)
        have hjform : j = (j.castPred hj).castSucc := by apply Fin.ext; rfl
        have hji : (j.castPred hj).val + 1 ≤ j.val + 1 := by
          rw [show (j.castPred hj).val = j.val by rfl]
        refine ⟨Fin.castLE hji i, ?_⟩
        convert hi using 1
        · apply congrArg G.ends
          conv_lhs => rw [hjform]
          simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
        · apply (Sym2.eq_iff).2
          left
          constructor
          · have hjs : j.succ = (j.castPred hj).succ.castSucc := by apply Fin.ext; rfl
            rw [hjs]
            simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
          · have hi' : i.val < T.length + 1 := by omega
            have hq : (Fin.castLE hji i).castLT (by omega) =
                (i.castLT hi').castSucc := by apply Fin.ext; rfl
            rw [hq]
            simp only [Fin.lastCases, Fin.reverseInduction_castSucc] }

private theorem helper_branch_75.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), GlobalMaximumTriple G k e0 phi T →
    ∀ (alpha gamma : Fin k), alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T) → gamma ∈
        TreeFreeColors phi T →
    ∀ u ∈ TreeSequenceVertexSet T, gamma ∈ MissingColors G phi u →
    ∀ (z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p → TashkinovOrder G =
        (TreeSequenceVertexSet T).card ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd
        (TreeSequenceVertexSet T).card ∧ ColoredVertexSetElementary G phi (TreeSequenceVertexSet
        T) ∧ ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) → ((DefectiveColors G phi
        (TreeSequenceVertexSet T) = ∅ → ColoredVertexSetStronglyClosed G phi
        (TreeSequenceVertexSet T)) ∧ (
    ∀ alpha ∈ TreeMissingColors phi T, BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha =
        ∅) ∧
    ∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T), Odd (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card ∧ (3 : ℕ) ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card) → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) →
    ∀ (f : E), f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi f = some alpha → f ∈
        BoundaryEdges G (TreeSequenceVertexSet T) ∧ Sum.inr f ∈ p.support := by
  classical
  intro V E _ _ _ G k e0 phi T hglobal alpha gamma halpha hgammaFree u hu hgamma z p hp horder
      hfacts hunused f h
  refine ⟨h.1, ?_⟩
  by_contra hnot
  have htreegamma : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨u, hu, hgamma⟩
  have hgammaempty := hfacts.2.1 gamma htreegamma
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hne : alpha ≠ gamma := by
    intro heq
    have ha : alpha ∉ MissingColors G phi u := by
      exact hclosed h.1 hu h.2
    exact ha (heq ▸ hgamma)
  let Q := TwoColorComponent G phi alpha gamma (Sum.inr f)
  let psi := TwoColorComponentSwap G phi alpha gamma (Sum.inr f)
  have hfQ : Sum.inr f ∈ Q := by
    change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
      (Sum.inr f)
    rfl
  have huQ : Sum.inl u ∉ Q := by
    exact @helper_huQ_190 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
        (@alpha) (@gamma) (@u) (@z) (@p) (@hp) (@f) (@hnot)
  have qcolor : ∀ e, Sum.inr e ∈ Q →
      phi e = some alpha ∨ phi e = some gamma := by
    exact @helper_qcolor_204 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T)
        (@alpha) (@gamma) (@f) (@h)
  have qvertex : ∀ v e, Incident G v e → Sum.inr e ∈ Q →
      Sum.inl v ∈ Q := by
    exact @helper_qvertex_297 (@V) (@E) (@G) (@k) (@phi) (@alpha) (@gamma) (@f) (@qcolor)
  have qedge_not : ∀ v e, Incident G v e → Sum.inl v ∉ Q →
      Sum.inr e ∉ Q := by
    intro v e hev hv he
    exact hv (qvertex v e hev he)
  have halpha_present : ∀ v, v ∈ TreeSequenceVertexSet T →
      alpha ∈ PresentColors G phi v := by
    intro v hv
    have hn : alpha ∉ MissingColors G phi v := by
      exact hclosed h.1 hv h.2
    simpa [MissingColors] using hn
  have hgamma_present : ∀ v, v ∈ TreeSequenceVertexSet T → v ≠ u →
      gamma ∈ PresentColors G phi v := by
    exact @helper_hgamma_present_318 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@gamma) (@u) (@hu) (@hgamma) (@horder)
  have qedge_of_vertex : ∀ v e, Sum.inl v ∈ Q → Incident G v e →
      (phi e = some alpha ∨ phi e = some gamma) → Sum.inr e ∈ Q := by
    exact @helper_qedge_of_vertex_326 (@V) (@E) (@G) (@k) (@phi) (@alpha) (@gamma) (@f)
  have present_eq : ∀ v, v ∈ TreeSequenceVertexSet T →
      PresentColors G psi v = PresentColors G phi v := by
    exact @helper_present_eq_179 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
        (@T) (@alpha) (@gamma) (@u) (@f) (@hne) (@huQ) (@qcolor) (@qvertex) (@halpha_present)
        (@hgamma_present) (@qedge_of_vertex)
  have missing_eq : ∀ v, v ∈ TreeSequenceVertexSet T →
      MissingColors G psi v = MissingColors G phi v := by
    intro v hv
    simp [MissingColors, present_eq v hv]
  have proper_psi : IsProperEdgeColoring G psi := by
    exact TwoColorComponentSwapProper G phi alpha gamma hne
      hglobal.1.2.2.2.1 (Sum.inr f)
  have one : IsOneEdgeUncolored phi e0 := hglobal.1.2.2.2.2
  have e0not : Sum.inr e0 ∉ Q := by
    intro he
    rcases qcolor e0 he with hc | hc <;> simp [one.1] at hc
  have one_psi : IsOneEdgeUncolored psi e0 := by
    exact @helper_one_psi_274 (@V) (@E) (@G) (@k) (@e0) (@phi) (@alpha) (@gamma) (@f) (@hne)
        (@qcolor) (@one) (@e0not)
  have tree_fixed : ∀ j : Fin T.length, psi (T.edge j) = phi (T.edge j) := by
    exact @helper_tree_fixed_287 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
        (@T) (@alpha) (@gamma) (@halpha) (@hgammaFree) (@hunused) (@f) (@qcolor) (@one) (@e0not)
  obtain ⟨x, hx, y, hy, hends⟩ := by
    simpa [BoundaryEdges] using h.1
  have vertex_mem : ∀ i : Fin (T.length + 1),
      T.vertex i ∈ TreeSequenceVertexSet T := by
    intro i
    simp [TreeSequenceVertexSet]
  have fnew : ∀ j : Fin T.length, f ≠ T.edge j := by
    exact @helper_fnew_362 (@V) (@E) inferInstance inferInstance  (@G) (@e0) (@T)
        (@f) (@x) (@y) (@hy) (@hends) (@vertex_mem)
  let Tplus : TreeSequence G e0 := by
    exact @helperTplus474 (@V) (@E) inferInstance inferInstance  (@G) (@e0) (@T)
        (@f) (@x) (@hx) (@y) (@hy) (@hends) (@vertex_mem) (@fnew)
  have hTash : TashkinovTree G e0 psi Tplus := by
    intro j
    revert j
    refine Fin.lastCases ?_ (fun q => ?_)
    · intro hj
      obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hu
      have hi_lt := i.isLt
      refine ⟨i, ?_⟩
      refine ⟨gamma, ?_, ?_⟩
      · simp [Tplus, psi, Q, TwoColorComponentSwap, hfQ, h.2]
      · have hiold : i.val < T.length + 1 := by omega
        have hb : i.val < T.length + 1 + 1 := by omega
        have hii : Tplus.vertex (Fin.castLT i hb) =
            T.vertex (i.castLT hiold) := by
          have heq : (Fin.castLT i hb : Fin (T.length + 1 + 1)) =
              (i.castLT hiold).castSucc := by apply Fin.ext; rfl
          rw [heq]
          simp [Tplus]
        have hmu : MissingColors G psi
            (Tplus.vertex (Fin.castLT i hb)) =
            MissingColors G phi u := by
          rw [hii]
          rw [missing_eq _ (by simp [TreeSequenceVertexSet])]
          exact congrArg (MissingColors G phi) hi
        exact hmu.symm ▸ hgamma
    · intro hj
      have hqbound : q.val < T.length := by simp []
      have hq : 1 ≤ q.val := by
        simpa [Fin.lastCases] using hj
      obtain ⟨i, c, hc, hcm⟩ := hglobal.2.1 q hq
      refine ⟨i, c, ?_, ?_⟩
      · simpa [Tplus, Fin.lastCases, Fin.reverseInduction_castSucc] using
          (tree_fixed q ▸ hc)
      · have hiX : T.vertex (i.castLT (by omega)) ∈ TreeSequenceVertexSet T := by
          have hi_lt := i.isLt
          simp [TreeSequenceVertexSet]
        have hmi := missing_eq _ hiX
        have hiold : i.val < T.length + 1 := by omega
        have hb : i.val < T.length + 1 + 1 := by omega
        have hiv : Tplus.vertex (Fin.castLT i hb) =
            T.vertex (i.castLT hiold) := by
          have heq : (Fin.castLT i hb : Fin (T.length + 1 + 1)) =
              (i.castLT hiold).castSucc := by apply Fin.ext; rfl
          rw [heq]
          simp [Tplus]
        rw [hiv, hmi]
        exact hcm
  have hK : KTriple G k e0 psi := by
    refine ⟨hglobal.1.1, hglobal.1.2.1, hglobal.1.2.2.1, proper_psi, one_psi⟩
  have hsizeplus : (TreeSequenceVertexSet Tplus).card = Tplus.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Tplus.vertex_injective]
  have hle := treeCard_le_tashkinovOrder G k e0 psi Tplus hK hTash
  rw [hsizeplus] at hle
  rw [horder.1] at hle
  have hsizeold : (TreeSequenceVertexSet T).card = T.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective, T.vertex_injective]
  have hlen : Tplus.length = T.length + 1 := rfl
  exact False.elim (by omega)

private theorem helper_branch_436.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
    ∀ u ∈ TreeSequenceVertexSet T, gamma ∈ MissingColors G phi u →
    ∀ (z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ((DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ → ColoredVertexSetStronglyClosed G
        phi (TreeSequenceVertexSet T)) ∧ (
    ∀ alpha ∈ TreeMissingColors phi T, BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha =
        ∅) ∧
    ∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T), Odd (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card ∧ (3 : ℕ) ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card) →
    ∀ (f : E), f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ Sum.inr f ∈ p.support → f ∈
        BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi f = some alpha := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma u hu hgamma z p hfacts f h
  have left_7 : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := h.1
  have right_3 : Sum.inr f ∈ p.support := h.2
  have htreegamma : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨u, hu, hgamma⟩
  have hgammaempty := hfacts.2.1 gamma htreegamma
  have hnalpha : phi f = some alpha ∨ phi f = some gamma := by
    obtain ⟨n, hn, hnl⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp right_3
    have hn0 : 0 < n := by
      by_contra hh
      have he : n = 0 := by omega
      subst he
      simp at hn
    have hnlast : n < p.length := by
      by_contra hh
      have he := p.getVert_of_length_le (i := n) (by omega)
      rw [hn] at he
      simp at he
    have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx, hn] at hadj
    cases hprev : p.getVert (n - 1) with
    | inl v =>
        rw [hprev] at hadj
        simp only [TwoColorIncidenceGraph] at hadj
        exact hadj.2
    | inr e =>
        rw [hprev] at hadj
        simp [TwoColorIncidenceGraph] at hadj
  rcases hnalpha with hfa | hfg
  · exact ⟨left_7, hfa⟩
  · exfalso
    have hbad : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) gamma := by
      simpa [BoundaryColorEdges] using (show
        f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi f = some gamma
        from ⟨left_7, hfg⟩)
    rw [hgammaempty] at hbad
    simp at hbad

theorem ScheideDefectiveChainBoundaryEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p) :
    ∀ f : E, f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha ↔ f ∈ BoundaryEdges G
        (TreeSequenceVertexSet T) ∧ Sum.inr f ∈ p.support := by
  classical
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
  have hunused := ScheideGlobalMaximumUnused G k e0 phi T hglobal
  intro f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  constructor
  · exact @helper_branch_75 V E inferInstance inferInstance inferInstance G k e0
      phi T hglobal alpha gamma halpha hgammaFree u hu hgamma z p hp horder hfacts hunused f
  · exact @helper_branch_436 V E inferInstance inferInstance G k e0 phi T alpha
      gamma u hu hgamma z p hfacts f
end GoldbergSeymour

end
