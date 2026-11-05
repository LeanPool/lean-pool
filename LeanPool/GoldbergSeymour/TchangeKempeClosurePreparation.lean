/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTree
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovClosureExists
public import LeanPool.GoldbergSeymour.TchangeKempeClosureData
public import LeanPool.GoldbergSeymour.TreeExitComponentMeetsTreeOnlyAtExit
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.TreeVertexOrder
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint

/-!
# Tchange Kempe Closure Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_graphEq_137.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let _ : Set (V ⊕ E) := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        TwoColorIncidenceGraph G sigma C.a C.b = TwoColorIncidenceGraph G C.phi C.a C.b := by
  classical
  intro V E _ _ _ _ G k e0 C component sigma
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr f =>
          simp only [TwoColorIncidenceGraph, sigma]
          by_cases hf : Sum.inr f ∈ component
          · by_cases hfa : C.phi f = some C.a
            · simp [TwoColorComponentSwap, component, hf, hfa,
                C.colorsDistinct, C.colorsDistinct.symm]
            · by_cases hfb : C.phi f = some C.b
              · simp [TwoColorComponentSwap, component, hf, hfb,
                  C.colorsDistinct, C.colorsDistinct.symm]
              · simp [TwoColorComponentSwap, component, hf, hfa, hfb]
          · simp [TwoColorComponentSwap, component, hf]
  | inr f =>
      cases y with
      | inl v =>
          simp only [TwoColorIncidenceGraph, sigma]
          by_cases hf : Sum.inr f ∈ component
          · by_cases hfa : C.phi f = some C.a
            · simp [TwoColorComponentSwap, component, hf, hfa,
                C.colorsDistinct, C.colorsDistinct.symm]
            · by_cases hfb : C.phi f = some C.b
              · simp [TwoColorComponentSwap, component, hf, hfb,
                  C.colorsDistinct, C.colorsDistinct.symm]
              · simp [TwoColorComponentSwap, component, hf, hfa, hfb]
          · simp [TwoColorComponentSwap, component, hf]
      | inr g => simp [TwoColorIncidenceGraph]

private theorem helper_fixedBefore_250.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let component : Set (V ⊕ E) := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3); (
    ∀ w ∈ TreeSequenceVertexSet C.T, Sum.inl w ∈ component ↔ w = C.b3) →
    ∀ (_ : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)) (_ i3 : Fin
        (C.T.length + (1 : ℕ))), C.T.vertex i3 = C.b3 →
    ∀ (_ : Fin (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤
        C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
        baseTree.length = (↑i3 : ℕ) → (
    ∀ (r : Fin (C.T.length + (1 : ℕ))), C.T.vertex r ∈ TreeSequenceVertexSet C.T) →
    ∀ (r : Fin C.T.length), (↑r : ℕ) < (↑i3 : ℕ) → sigma (C.T.edge r) = C.phi (C.T.edge r) := by
  classical
  intro V E _ _ _ _ G k e0 C component sigma hcomponentTree Q1 Q2 Q3 i1 i3 hi3 i2 hi3pos hi3le
      baseTree hbaseLen fullVertexMem r hr3
  by_cases he : Sum.inr (C.T.edge r) ∈ component
  · by_cases hea : C.phi (C.T.edge r) = some C.a
    · obtain ⟨q, hq⟩ := C.T.attaches r
      let qFull : Fin (C.T.length + 1) :=
        Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ r.isLt))
      have hincident : Incident G (C.T.vertex qFull) (C.T.edge r) := by
        rw [Incident, hq]
        simp [qFull]
      have hadj : (TwoColorIncidenceGraph G C.phi C.a C.b).Adj
          (Sum.inl (C.T.vertex qFull)) (Sum.inr (C.T.edge r)) := by
        exact ⟨hincident, Or.inl hea⟩
      have hqComponent : Sum.inl (C.T.vertex qFull) ∈ component := by
        change (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
            (Sum.inl (C.T.vertex qFull)) =
          (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
            (Sum.inl C.b3)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).trans he
      have hqb3 := (hcomponentTree _ (fullVertexMem qFull)).mp hqComponent
      have hqi3 : qFull = i3 := C.T.vertex_injective (hqb3.trans hi3.symm)
      have : qFull.val < i3.val := by
        dsimp [qFull]
        omega
      omega
    · by_cases heb : C.phi (C.T.edge r) = some C.b
      · obtain ⟨q, hq⟩ := C.T.attaches r
        let qFull : Fin (C.T.length + 1) :=
          Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ r.isLt))
        have hincident : Incident G (C.T.vertex qFull) (C.T.edge r) := by
          rw [Incident, hq]
          simp [qFull]
        have hadj : (TwoColorIncidenceGraph G C.phi C.a C.b).Adj
            (Sum.inl (C.T.vertex qFull)) (Sum.inr (C.T.edge r)) := by
          exact ⟨hincident, Or.inr heb⟩
        have hqComponent : Sum.inl (C.T.vertex qFull) ∈ component := by
          change (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
              (Sum.inl (C.T.vertex qFull)) =
            (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
              (Sum.inl C.b3)
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).trans he
        have hqb3 := (hcomponentTree _ (fullVertexMem qFull)).mp hqComponent
        have hqi3 : qFull = i3 := C.T.vertex_injective (hqb3.trans hi3.symm)
        have : qFull.val < i3.val := by
          dsimp [qFull]
          omega
        omega
      · simp [sigma, TwoColorComponentSwap, component, he, hea, heb]
  · simp [sigma, TwoColorComponentSwap, component, he]

private theorem helper_hbaseTree_302.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let component : Set (V ⊕ E) := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        IsProperEdgeColoring G C.phi → (
    ∀ w ∈ TreeSequenceVertexSet C.T, Sum.inl w ∈ component ↔ w = C.b3) →
    ∀ (_ : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)) (_ i3 : Fin
        (C.T.length + (1 : ℕ))), C.T.vertex i3 = C.b3 →
    ∀ (_ : Fin (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤
        C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
        baseTree.length = (↑i3 : ℕ) → TreeSequenceInitialSegment baseTree C.T → (
    ∀ (r : Fin (C.T.length + (1 : ℕ))), C.T.vertex r ∈ TreeSequenceVertexSet C.T) → (
    ∀ (r : Fin C.T.length), (↑r : ℕ) < (↑i3 : ℕ) → sigma (C.T.edge r) = C.phi (C.T.edge r)) →
        TashkinovTree G e0 sigma baseTree := by
  classical
  intro V E _ _ _ _ G k e0 C component sigma hproper hcomponentTree Q1 Q2 Q3 i1 i3 hi3 i2 hi3pos
      hi3le baseTree hbaseLen hbaseInitial fullVertexMem fixedBefore r hr
  let rFull : Fin C.T.length := ⟨r.val, by rw [hbaseLen] at r; omega⟩
  obtain ⟨q, c, hcolor, hmiss⟩ := C.tree rFull (by simpa [rFull] using hr)
  let qFull : Fin (C.T.length + 1) :=
    Fin.castLT q (Nat.lt_trans q.isLt (Nat.succ_lt_succ rFull.isLt))
  have hrBefore : r.val < i3.val := by
    rw [← hbaseLen]
    exact r.isLt
  have hqBefore : qFull.val < i3.val := by
    have hrFull : rFull.val = r.val := rfl
    have hq : q.val < r.val + 1 := by
      calc
        q.val < rFull.val + 1 := q.isLt
        _ = r.val + 1 := by rw [hrFull]
    change q.val < i3.val
    omega
  have hqOutside : Sum.inl (C.T.vertex qFull) ∉ component := by
    intro hqComponent
    have hqb3 := (hcomponentTree _ (fullVertexMem qFull)).mp hqComponent
    have hqi3 : qFull = i3 := C.T.vertex_injective (hqb3.trans hi3.symm)
    omega
  have hmissSigma : c ∈ MissingColors G sigma (C.T.vertex qFull) := by
    rw [(TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
      C.colorsDistinct hproper (Sum.inl C.b3)).1 _ hqOutside]
    exact hmiss
  let qBase : Fin (r.val + 1) := Fin.cast (by simp [rFull]) q
  refine ⟨qBase, c, ?_, ?_⟩
  · have hedgeBase := hbaseInitial.2.2 r
    have hrEq : Fin.castLE hbaseInitial.1 r = rFull := by
      apply Fin.ext
      rfl
    rw [hrEq] at hedgeBase
    rw [← hedgeBase]
    exact (fixedBefore rFull (by dsimp [rFull]; rw [hbaseLen] at r; omega)).trans
      hcolor
  · have hvertexBase := hbaseInitial.2.1
        (Fin.castLT qBase
          (Nat.lt_trans qBase.isLt (Nat.succ_lt_succ r.isLt)))
    have hindex : Fin.castLE (Nat.succ_le_succ hbaseInitial.1)
        (Fin.castLT qBase
          (Nat.lt_trans qBase.isLt (Nat.succ_lt_succ r.isLt))) = qFull := by
      apply Fin.ext
      rfl
    rw [hindex] at hvertexBase
    simpa [hvertexBase] using hmissSigma

private theorem helper_componentContained_600.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
    ∀ (twoTree closedTree : TreeSequence G e0), TashkinovClosure sigma twoTree closedTree → (
    ∀ {f : E} {x y : V}, Incident G x f → Incident G y f → x ≠ y → G.ends f = s(x, y)) →
    ∀ root ∈ TreeSequenceVertexSet closedTree, C.a ∈ TreeMissingColors sigma closedTree → C.b ∈
        TreeMissingColors sigma closedTree →
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G sigma C.a C.b (Sum.inl root) → w ∈
        TreeSequenceVertexSet closedTree := by
  classical
  intro V E _ _ _ _ G k e0 C sigma twoTree closedTree hclosure endsEqOfIncidents root hroot
      haTree hbTree
  obtain ⟨wa, hwa, hwaMissing⟩ := by
    simpa [TreeMissingColors] using haTree
  obtain ⟨wb, hwb, hwbMissing⟩ := by
    simpa [TreeMissingColors] using hbTree
  let H := TwoColorIncidenceGraph G sigma C.a C.b
  let insideNode : Sum V E → Prop := fun z =>
    match z with
    | Sum.inl v => v ∈ TreeSequenceVertexSet closedTree
    | Sum.inr f => ∀ v, Incident G v f →
        v ∈ TreeSequenceVertexSet closedTree
  have neighborClosed : ∀ x, insideNode x → ∀ y, H.Adj x y →
      insideNode y := by
    intro x hx y hxy
    cases x with
    | inl v =>
        cases y with
        | inl w => simp [H, TwoColorIncidenceGraph] at hxy
        | inr f =>
            have hdata : Incident G v f ∧
                (sigma f = some C.a ∨ sigma f = some C.b) := by
              simpa [H, TwoColorIncidenceGraph] using hxy
            intro w hwf
            by_contra hw
            have hvw : v ≠ w := by
              intro hvw
              exact hw (hvw ▸ hx)
            have hfBoundary : f ∈ BoundaryEdges G
                (TreeSequenceVertexSet closedTree) := by
              simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨v, hx, w, hw,
                endsEqOfIncidents hdata.1 hwf hvw⟩
            rcases hdata.2 with hfa | hfb
            · exact (hclosure.2 hfBoundary hwa hfa) hwaMissing
            · exact (hclosure.2 hfBoundary hwb hfb) hwbMissing
    | inr f =>
        cases y with
        | inl v =>
            have hinc : Incident G v f := by
              have hdata : Incident G v f ∧
                  (sigma f = some C.a ∨ sigma f = some C.b) := by
                simpa [H, TwoColorIncidenceGraph] using hxy
              exact hdata.1
            exact hx v hinc
        | inr g => simp [H, TwoColorIncidenceGraph] at hxy
  intro w hwComponent
  have reach : H.Reachable (Sum.inl root) (Sum.inl w) := by
    change H.connectedComponentMk (Sum.inl w) =
      H.connectedComponentMk (Sum.inl root) at hwComponent
    exact SimpleGraph.ConnectedComponent.exact hwComponent |>.symm
  have hwInside : insideNode (Sum.inl w) := by
    apply reach.mem_subgraphVerts
      (H := (⊤ : H.Subgraph).induce {z | insideNode z})
      (fun x hx y hadj =>
        ⟨by simpa using hx,
          neighborClosed x (by simpa using hx) y hadj,
          hadj⟩)
      (by simpa [insideNode] using hroot)
  simpa [insideNode] using hwInside

private theorem helper_oneVertexCases_629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
    ∀ (_ : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)) (_ :
        (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)) (_ i3 _ : Fin
        (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤ C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
    ∀ (x1 : V) (oneTree : TreeSequence G e0), oneTree.length = baseTree.length + (1 : ℕ) →
        TreeSequenceInitialSegment baseTree oneTree →
    let new1 : V := oneTree.vertex (Fin.last oneTree.length); new1 = x1 →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet oneTree → v ∈ TreeSequenceVertexSet baseTree ∨ v = x1 := by
  classical
  intro V E _ _ _ _ G k e0 C sigma Q1 Q2 Q3 i1 i3 i2 hi3pos hi3le baseTree x1 oneTree hlen1 hseg1
      new1 hnew1 v hv
  have hv' : v ∈ Finset.image oneTree.vertex Finset.univ := by
    simpa [TreeSequenceVertexSet] using hv
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hv'
  by_cases hold : r.val ≤ baseTree.length
  · let q : Fin (baseTree.length + 1) := ⟨r.val, by omega⟩
    left
    have hrq : r = Fin.castLE (Nat.succ_le_succ hseg1.1) q := by
      apply Fin.ext
      rfl
    have hq : baseTree.vertex q = v := by
      rw [← hseg1.2.1 q, ← hrq]
      exact hr
    simpa [TreeSequenceVertexSet] using
      (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩)
  · right
    have hlast : r = Fin.last oneTree.length := by
      apply Fin.ext
      simp [hlen1]
      omega
    rw [hlast] at hr
    exact hr.symm.trans hnew1

private theorem helper_remoteOutside_770.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        C.a ∈ MissingColors G sigma C.a1 ∨ C.b ∈ MissingColors G sigma C.a1 → C.a ∈ MissingColors
        G sigma C.a2 ∨ C.b ∈ MissingColors G sigma C.a2 →
    ∀ (closedTree : TreeSequence G e0), ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        closedTree) → (
    ∀ {a : V}, a ∈ TreeSequenceVertexSet closedTree → a ≠ C.b3 → C.b ∉ MissingColors G sigma a) →
        (C.a ∈ TreeMissingColors sigma closedTree → C.a1 ∈ TreeSequenceVertexSet closedTree ∧ C.a2
        ∈ TreeSequenceVertexSet closedTree ∧ C.a3 ∈ TreeSequenceVertexSet closedTree) →
    ∀ a ∉ TreeSequenceVertexSet C.T, C.a ∈ MissingColors G sigma a ∨ C.b ∈ MissingColors G sigma a
        → a ∉ TreeSequenceVertexSet closedTree := by
  classical
  intro V E _ _ _ _ G k e0 C sigma hremote1 hremote2 closedTree hclosedElementary remoteNotB
      allRemoteInside a haOld haremote haClosed
  have hab3 : a ≠ C.b3 := by
    intro h
    exact haOld (h ▸ C.exit3.2.2.2.1)
  have haMissing : C.a ∈ MissingColors G sigma a :=
    haremote.resolve_right (remoteNotB haClosed hab3)
  have haTree : C.a ∈ TreeMissingColors sigma closedTree := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨a, haClosed, haMissing⟩
  obtain ⟨ha1, ha2, ha3⟩ := allRemoteInside haTree
  have ha1b3 : C.a1 ≠ C.b3 := by
    intro h
    exact C.exit1.2.2.1 (h ▸ C.exit3.2.2.2.1)
  have ha2b3 : C.a2 ≠ C.b3 := by
    intro h
    exact C.exit2.2.2.1 (h ▸ C.exit3.2.2.2.1)
  have ha1Missing : C.a ∈ MissingColors G sigma C.a1 :=
    hremote1.resolve_right (remoteNotB ha1 ha1b3)
  have ha2Missing : C.a ∈ MissingColors G sigma C.a2 :=
    hremote2.resolve_right (remoteNotB ha2 ha2b3)
  exact (Finset.disjoint_left.mp
    (hclosedElementary ha1 ha2 C.remote12) ha1Missing ha2Missing)

private theorem helper_transferExit_476.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        TwoColorIncidenceGraph G sigma C.a C.b = TwoColorIncidenceGraph G C.phi C.a C.b →
    ∀ {u v : V} (p : (TwoColorIncidenceGraph G C.phi C.a C.b).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath C.T C.phi C.a C.b u v p → C.a ∈ MissingColors G sigma u ∨ C.b ∈ MissingColors
        G sigma u →
    ∃ (q : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath
        C.T sigma C.a C.b u v q ∧ q.support = p.support ∧ q.length = p.length := by
  classical
  intro V E _ _ _ _ G k e0 C sigma graphEq u v p hexit hremote
  have hedges : ∀ z, z ∈ p.edges →
      z ∈ (TwoColorIncidenceGraph G sigma C.a C.b).edgeSet := by
    intro z hz
    rw [graphEq]
    exact p.edges_subset_edgeSet hz
  let q := p.transfer (TwoColorIncidenceGraph G sigma C.a C.b) hedges
  refine ⟨q, ?_, ?_, ?_⟩
  · unfold TreeExitPath
    refine ⟨hexit.1.transfer hedges, ?_, hexit.2.2.1,
      hexit.2.2.2.1, hremote, ?_⟩
    · simpa [q] using hexit.2.1
    · intro w hw
      simpa [q] using hexit.2.2.2.2.2 w hw
  · simp [q]
  · simp [q]

private theorem helper_hsigmaOne_593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let _ : Set (V ⊕ E) := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 C component sigma
  refine ⟨?_, ?_⟩
  · have he0 := C.triple.2.2.2.2.1
    by_cases he : Sum.inr e0 ∈ component
    · simp [sigma, TwoColorComponentSwap, component, he, he0]
    · simp [sigma, TwoColorComponentSwap, component, he, he0]
  · intro f hf
    obtain ⟨c, hc⟩ := C.triple.2.2.2.2.2 f hf
    by_cases he : Sum.inr f ∈ component
    · by_cases hca : c = C.a
      · refine ⟨C.b, ?_⟩
        simp [sigma, TwoColorComponentSwap, component, he, hc, hca]
      · by_cases hcb : c = C.b
        · refine ⟨C.a, ?_⟩
          simp [sigma, TwoColorComponentSwap, component, he, hc, hcb,
            C.colorsDistinct.symm]
        · refine ⟨c, ?_⟩
          simp [sigma, TwoColorComponentSwap, component, he, hc, hca, hcb]
    · exact ⟨c, by simpa [sigma, TwoColorComponentSwap, component, he] using hc⟩

private theorem helper_continuation_610.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        C.b ∈ MissingColors G sigma C.b3 → C.a ∈ MissingColors G sigma C.a1 ∨ C.b ∈ MissingColors
        G sigma C.a1 → C.a ∈ MissingColors G sigma C.a2 ∨ C.b ∈ MissingColors G sigma C.a2 → C.a ∈
        MissingColors G sigma C.a3 ∨ C.b ∈ MissingColors G sigma C.a3 →
    ∀ (Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)),
        TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1 → Q1.support = C.P1.support → Q1.length =
        C.P1.length →
    ∀ (Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)),
        TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2 → Q2.support = C.P2.support → Q2.length =
        C.P2.length →
    ∀ (Q3 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)),
        TreeExitPath C.T sigma C.a C.b C.a3 C.b3 Q3 → Q3.support = C.P3.support → Q3.length =
        C.P3.length →
    ∀ (i3 : Fin (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤
        C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
        TreeSequenceInitialSegment baseTree C.T → baseTree.vertex (Fin.last baseTree.length) =
        C.b3 → C.b1 ∈ TreeSequenceVertexSet baseTree → C.b2 ∈ TreeSequenceVertexSet baseTree →
        TashkinovTree G e0 sigma baseTree → KTriple G k e0 sigma →
    ∀ (oneTree twoTree : TreeSequence G e0), TashkinovAugmentation sigma baseTree oneTree →
        TashkinovAugmentation sigma oneTree twoTree →
    ∀ (closedTree : TreeSequence G e0), TashkinovClosure sigma twoTree closedTree → TashkinovTree
        G e0 sigma closedTree → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        closedTree) → C.b1 ∈ TreeSequenceVertexSet closedTree → C.b2 ∈ TreeSequenceVertexSet
        closedTree → C.b3 ∈ TreeSequenceVertexSet closedTree → (
    ∀ (v : V), Incident G v C.f1 → v ∈ TreeSequenceVertexSet closedTree) → (
    ∀ {a : V}, a ∈ TreeSequenceVertexSet closedTree → a ≠ C.b3 → C.b ∉ MissingColors G sigma a) →
        (C.a ∈ TreeMissingColors sigma closedTree → C.a1 ∈ TreeSequenceVertexSet closedTree ∧ C.a2
        ∈ TreeSequenceVertexSet closedTree ∧ C.a3 ∈ TreeSequenceVertexSet closedTree) → Nonempty
        (TchangeKempeClosureData C) := by
  classical
  intro V E _ _ _ _ G k e0 C sigma hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1 hQ1support
      hQ1length Q2 hQ2 hQ2support hQ2length Q3 hQ3 hQ3support hQ3length i3 hi3pos hi3le baseTree
      hbaseInitial hbaseLast hb1Base hb2Base hbaseTree hsigmaTriple oneTree twoTree haug1 haug2
      closedTree hclosure hclosedTree hclosedElementary hb1Closed hb2Closed hb3Closed
      hf1EndsClosed remoteNotB allRemoteInside
  have remoteOutside := @helper_remoteOutside_770 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C hremote1 hremote2 closedTree hclosedElementary remoteNotB
      allRemoteInside
  have ha1Outside : C.a1 ∉ TreeSequenceVertexSet closedTree :=
    remoteOutside C.a1 C.exit1.2.2.1 hremote1
  have ha2Outside : C.a2 ∉ TreeSequenceVertexSet closedTree :=
    remoteOutside C.a2 C.exit2.2.2.1 hremote2
  have ha3Outside : C.a3 ∉ TreeSequenceVertexSet closedTree :=
    remoteOutside C.a3 C.exit3.2.2.1 hremote3
  exact ⟨{
    sigma := sigma
    baseTree := baseTree
    oneTree := oneTree
    twoTree := twoTree
    closedTree := closedTree
    sigmaEq := rfl
    baseInitial := hbaseInitial
    baseLast := hbaseLast
    b1InBase := hb1Base
    b2InBase := hb2Base
    baseIsTree := hbaseTree
    firstAugmentation := haug1
    secondAugmentation := haug2
    closureRoute := hclosure
    triple := hsigmaTriple
    closureTree := hclosedTree
    closureClosed := hclosure.2
    closureElementary := hclosedElementary
    betaMissing := hbetaMissing
    b1InClosure := hb1Closed
    b2InClosure := hb2Closed
    b3InClosure := hb3Closed
    a1Outside := ha1Outside
    a2Outside := ha2Outside
    a3Outside := ha3Outside
    f1EndsInside := hf1EndsClosed
    Q1 := Q1
    Q2 := Q2
    Q3 := Q3
    exit1 := hQ1
    exit2 := hQ2
    exit3 := hQ3
    support1 := hQ1support
    support2 := hQ2support
    support3 := hQ3support
    length1 := hQ1length
    length2 := hQ2length
    length3 := hQ3length }⟩

private theorem helper_continuation_583.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        C.b ∈ MissingColors G sigma C.b3 → C.a ∈ MissingColors G sigma C.a1 ∨ C.b ∈ MissingColors
        G sigma C.a1 → C.a ∈ MissingColors G sigma C.a2 ∨ C.b ∈ MissingColors G sigma C.a2 → C.a ∈
        MissingColors G sigma C.a3 ∨ C.b ∈ MissingColors G sigma C.a3 →
    ∀ (Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)),
        TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1 → Q1.support = C.P1.support → Q1.length =
        C.P1.length →
    ∀ (Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)),
        TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2 → Q2.support = C.P2.support → Q2.length =
        C.P2.length →
    ∀ (Q3 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)),
        TreeExitPath C.T sigma C.a C.b C.a3 C.b3 Q3 → Q3.support = C.P3.support → Q3.length =
        C.P3.length →
    ∀ (i3 : Fin (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤
        C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
        TreeSequenceInitialSegment baseTree C.T → baseTree.vertex (Fin.last baseTree.length) =
        C.b3 → C.b1 ∈ TreeSequenceVertexSet baseTree → C.b2 ∈ TreeSequenceVertexSet baseTree →
        TashkinovTree G e0 sigma baseTree → sigma C.f1 = some C.b → sigma C.f2 = some C.b →
        KTriple G k e0 sigma → (
    ∀ (A B : TreeSequence G e0), TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ x1 ∉ TreeSequenceVertexSet C.T, G.ends C.f1 = s(C.b1, x1) →
    ∀ (x2 : V), Incident G x1 C.f1 → x1 ≠ x2 → x1 ∉ TreeSequenceVertexSet baseTree →
    ∀ (oneTree : TreeSequence G e0) (hlen1 : oneTree.length = baseTree.length + (1 : ℕ)),
        TreeSequenceInitialSegment baseTree oneTree → oneTree.edge (Fin.cast ((
    by first  | omega
    )) (Fin.last baseTree.length)) = C.f1 →
    let new1 : V := oneTree.vertex (Fin.last oneTree.length); new1 = x1 → (
    ∀ {v : V}, v ∈ TreeSequenceVertexSet oneTree → v ∈ TreeSequenceVertexSet baseTree ∨ v = x1) →
        C.f2 ∈ BoundaryEdges G (TreeSequenceVertexSet oneTree) → Nonempty (TchangeKempeClosureData
        C) := by
  classical
  intro V E _ _ _ _ G k e0 C sigma hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1 hQ1support
      hQ1length Q2 hQ2 hQ2support hQ2length Q3 hQ3 hQ3support hQ3length i3 hi3pos hi3le baseTree
      hbaseInitial hbaseLast hb1Base hb2Base hbaseTree hf1Sigma hf2Sigma hsigmaTriple
      initialVertexSubset x1 hx1 hends1 x2 hx1Incident hx12 hx1Base oneTree hlen1 hseg1 hedge1
      new1 hnew1 oneVertexCases hf2OneBoundary
  obtain ⟨twoTree, hadjoin2⟩ :=
    TreeSequenceBoundaryEdgeAppendExists oneTree C.f2 hf2OneBoundary
  obtain ⟨hlen2, hseg2, hedge2⟩ := hadjoin2
  have hb3Base : C.b3 ∈ TreeSequenceVertexSet baseTree := by
    have : baseTree.vertex (Fin.last baseTree.length) ∈
        TreeSequenceVertexSet baseTree := by
      simp [TreeSequenceVertexSet]
    simpa [hbaseLast] using this
  have hbetaBase : C.b ∈ TreeMissingColors sigma baseTree := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨C.b3, hb3Base, hbetaMissing⟩
  have haug1 : TashkinovAugmentation sigma baseTree oneTree := by
    refine ⟨hlen1, hseg1, C.b, ?_, hbetaBase⟩
    rw [hedge1]
    exact hf1Sigma
  have hb3One : C.b3 ∈ TreeSequenceVertexSet oneTree :=
    initialVertexSubset baseTree oneTree hseg1 hb3Base
  have hbetaOne : C.b ∈ TreeMissingColors sigma oneTree := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨C.b3, hb3One, hbetaMissing⟩
  have haug2 : TashkinovAugmentation sigma oneTree twoTree := by
    refine ⟨hlen2, hseg2, C.b, ?_, hbetaOne⟩
    rw [hedge2]
    exact hf2Sigma
  have htwoSequence : TashkinovAugmentationSequence sigma baseTree twoTree :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single haug1) haug2
  have htwoTree : TashkinovTree G e0 sigma twoTree :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 sigma
      baseTree twoTree hbaseTree htwoSequence
  obtain ⟨closedTree, hclosure⟩ := TashkinovClosureExists sigma twoTree
  have hclosedTree : TashkinovTree G e0 sigma closedTree :=
    TashkinovAugmentationSequencePreservesTashkinovTree G e0 sigma
      twoTree closedTree htwoTree hclosure.1
  have hclosedElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet closedTree) :=
    TashTree G k e0 sigma closedTree hsigmaTriple hclosedTree
  have htwoInitial : TreeSequenceInitialSegment twoTree closedTree :=
    TashkinovAugmentationSequenceInitialSegment sigma twoTree closedTree hclosure.1
  have honeSubset : TreeSequenceVertexSet oneTree ⊆
      TreeSequenceVertexSet closedTree :=
    (initialVertexSubset oneTree twoTree hseg2).trans
      (initialVertexSubset twoTree closedTree htwoInitial)
  have hbaseSubset : TreeSequenceVertexSet baseTree ⊆
      TreeSequenceVertexSet closedTree :=
    (initialVertexSubset baseTree oneTree hseg1).trans honeSubset
  have hb1Closed : C.b1 ∈ TreeSequenceVertexSet closedTree :=
    hbaseSubset hb1Base
  have hb2Closed : C.b2 ∈ TreeSequenceVertexSet closedTree :=
    hbaseSubset hb2Base
  have hb3Closed : C.b3 ∈ TreeSequenceVertexSet closedTree :=
    hbaseSubset hb3Base
  have hx1One : x1 ∈ TreeSequenceVertexSet oneTree := by
    have hnewMem : new1 ∈ TreeSequenceVertexSet oneTree := by
      simp [new1, TreeSequenceVertexSet]
    simpa [hnew1] using hnewMem
  have hx1Closed : x1 ∈ TreeSequenceVertexSet closedTree := honeSubset hx1One
  have hf1EndsClosed : ∀ v, Incident G v C.f1 →
      v ∈ TreeSequenceVertexSet closedTree := by
    intro v hv
    have hvEnds : v = C.b1 ∨ v = x1 := by
      rw [Incident, hends1] at hv
      simpa using hv
    rcases hvEnds with rfl | rfl
    · exact hb1Closed
    · exact hx1Closed
  have endsEqOfIncidents : ∀ {f : E} {x y : V},
      Incident G x f → Incident G y f → x ≠ y → G.ends f = s(x, y) := by
    intro f x y hx hy hxy
    exact (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
  have componentContained := @helper_componentContained_600 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 C twoTree closedTree hclosure endsEqOfIncidents
  have newComponentOfWalk {u v : V}
      (p : (TwoColorIncidenceGraph G sigma C.a C.b).Walk
        (Sum.inl u) (Sum.inl v)) :
      Sum.inl u ∈ TwoColorComponent G sigma C.a C.b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G sigma C.a C.b).connectedComponentMk
        (Sum.inl u) =
      (TwoColorIncidenceGraph G sigma C.a C.b).connectedComponentMk
        (Sum.inl v)
    exact SimpleGraph.ConnectedComponent.sound ⟨p⟩
  have remoteNotB :
    ∀ {a : V}, a ∈ TreeSequenceVertexSet closedTree → a ≠ C.b3 → C.b ∉ MissingColors G sigma a := by
    intro a ha hab hbMissing
    exact (Finset.disjoint_left.mp
      (hclosedElementary ha hb3Closed hab) hbMissing hbetaMissing)
  have allRemoteInside :
      C.a ∈ TreeMissingColors sigma closedTree →
      C.a1 ∈ TreeSequenceVertexSet closedTree ∧
      C.a2 ∈ TreeSequenceVertexSet closedTree ∧
      C.a3 ∈ TreeSequenceVertexSet closedTree := by
    intro haTree
    have hbTree : C.b ∈ TreeMissingColors sigma closedTree := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨C.b3, hb3Closed, hbetaMissing⟩
    exact ⟨componentContained C.b1 hb1Closed haTree hbTree C.a1
        (newComponentOfWalk Q1),
      componentContained C.b2 hb2Closed haTree hbTree C.a2
        (newComponentOfWalk Q2),
      componentContained C.b3 hb3Closed haTree hbTree C.a3
        (newComponentOfWalk Q3)⟩
  exact @helper_continuation_610 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1 hQ1support hQ1length Q2 hQ2 hQ2support
      hQ2length Q3 hQ3 hQ3support hQ3length i3 hi3pos hi3le hbaseInitial hbaseLast hb1Base
      hb2Base hbaseTree hsigmaTriple oneTree twoTree haug1 haug2 closedTree hclosure hclosedTree
      hclosedElementary hb1Closed hb2Closed hb3Closed hf1EndsClosed remoteNotB allRemoteInside
private theorem helper_continuation_572.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        IsProperEdgeColoring G C.phi → C.b ∈ MissingColors G sigma C.b3 → C.a ∈ MissingColors G
        sigma C.a1 ∨ C.b ∈ MissingColors G sigma C.a1 → C.a ∈ MissingColors G sigma C.a2 ∨ C.b ∈
        MissingColors G sigma C.a2 → C.a ∈ MissingColors G sigma C.a3 ∨ C.b ∈ MissingColors G
        sigma C.a3 →
    ∀ (Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)),
        TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1 → Q1.support = C.P1.support → Q1.length =
        C.P1.length →
    ∀ (Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)),
        TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2 → Q2.support = C.P2.support → Q2.length =
        C.P2.length →
    ∀ (Q3 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl C.b3)),
        TreeExitPath C.T sigma C.a C.b C.a3 C.b3 Q3 → Q3.support = C.P3.support → Q3.length =
        C.P3.length →
    ∀ (_ i3 _ : Fin (C.T.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤
        C.T.length),
    let baseTree : TreeSequence G e0 := TreeSequencePrefix C.T (↑i3 : ℕ) hi3pos hi3le;
        TreeSequenceInitialSegment baseTree C.T → baseTree.vertex (Fin.last baseTree.length) =
        C.b3 → C.b1 ∈ TreeSequenceVertexSet baseTree → C.b2 ∈ TreeSequenceVertexSet baseTree →
        TashkinovTree G e0 sigma baseTree → C.f1 ∈ BoundaryEdges G (TreeSequenceVertexSet C.T) ∧
        C.phi C.f1 = some C.b → C.f2 ∈ BoundaryEdges G (TreeSequenceVertexSet C.T) ∧ C.phi C.f2 =
        some C.b → sigma C.f1 = some C.b → sigma C.f2 = some C.b → KTriple G k e0 sigma → (
    ∀ (A B : TreeSequence G e0), TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → Nonempty (TchangeKempeClosureData C) := by
  classical
  intro V E _ _ _ _ G k e0 C sigma hproper hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1
      hQ1support hQ1length Q2 hQ2 hQ2support hQ2length Q3 hQ3 hQ3support hQ3length i1 i3 i2
      hi3pos hi3le baseTree hbaseInitial hbaseLast hb1Base hb2Base hbaseTree hf1Data hf2Data
      hf1Sigma hf2Sigma hsigmaTriple initialVertexSubset
  obtain ⟨u1, hu1, x1, hx1, hends1⟩ := by
    simpa [BoundaryEdges] using hf1Data.1
  have hb1u1 : C.b1 = u1 := by
    have hmem : C.b1 = u1 ∨ C.b1 = x1 := by
      have hinc := C.incident1
      rw [Incident, hends1] at hinc
      simpa using hinc
    exact hmem.resolve_right (by
      intro h
      apply hx1
      rw [← h]
      exact C.exit1.2.2.2.1)
  subst u1
  obtain ⟨u2, hu2, x2, hx2, hends2⟩ := by
    simpa [BoundaryEdges] using hf2Data.1
  have hb2u2 : C.b2 = u2 := by
    have hmem : C.b2 = u2 ∨ C.b2 = x2 := by
      have hinc := C.incident2
      rw [Incident, hends2] at hinc
      simpa using hinc
    exact hmem.resolve_right (by
      intro h
      apply hx2
      rw [← h]
      exact C.exit2.2.2.2.1)
  subst u2
  have hx1Incident : Incident G x1 C.f1 := by
    rw [Incident, hends1]
    simp
  have hx2Incident : Incident G x2 C.f2 := by
    rw [Incident, hends2]
    simp
  have hf12 : C.f1 ≠ C.f2 := by
    intro hf
    have hb2mem : C.b2 = C.b1 ∨ C.b2 = x1 := by
      have : C.b2 ∈ s(C.b1, x1) := by
        rw [← hends1, hf]
        exact C.incident2
      simpa using this
    rcases hb2mem with hb | hb
    · exact C.tree12 hb.symm
    · exact hx1 (hb ▸ C.exit2.2.2.2.1)
  have hx12 : x1 ≠ x2 := by
    intro hx
    apply (hproper hf12 ⟨x1, hx1Incident, hx ▸ hx2Incident⟩ hf1Data.2)
    exact hf2Data.2
  have hx1Base : x1 ∉ TreeSequenceVertexSet baseTree := by
    intro hx
    exact hx1 (initialVertexSubset baseTree C.T hbaseInitial hx)
  have hf1BaseBoundary : C.f1 ∈ BoundaryEdges G
      (TreeSequenceVertexSet baseTree) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.b1, hb1Base, x1, hx1Base, hends1⟩
  obtain ⟨oneTree, hadjoin1⟩ :=
    TreeSequenceBoundaryEdgeAppendExists baseTree C.f1 hf1BaseBoundary
  obtain ⟨hlen1, hseg1, hedge1⟩ := hadjoin1
  let new1 := oneTree.vertex (Fin.last oneTree.length)
  have hnew1Outside : new1 ∉ TreeSequenceVertexSet baseTree := by
    intro hnew
    have hnew' : new1 ∈ Finset.image baseTree.vertex Finset.univ := by
      simpa [TreeSequenceVertexSet] using hnew
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hnew'
    have hsame : oneTree.vertex (Fin.last oneTree.length) =
        oneTree.vertex (Fin.castLE (Nat.succ_le_succ hseg1.1) r) := by
      rw [hseg1.2.1 r, hr]
    have hidx := congrArg Fin.val (oneTree.vertex_injective hsame)
    simp [hlen1] at hidx
    omega
  have hnew1Incident : Incident G new1 C.f1 := by
    let lastEdge : Fin oneTree.length :=
      Fin.cast hlen1.symm (Fin.last baseTree.length)
    obtain ⟨q, hq⟩ := oneTree.attaches lastEdge
    have hsucc : lastEdge.succ = Fin.last oneTree.length := by
      apply Fin.ext
      simp [lastEdge, hlen1]
    rw [Incident, ← hedge1, hq, hsucc]
    simp [new1]
  have hnew1 : new1 = x1 := by
    have hm : new1 = C.b1 ∨ new1 = x1 := by
      rw [Incident, hends1] at hnew1Incident
      simpa using hnew1Incident
    exact hm.resolve_left (by
      intro h
      apply hnew1Outside
      rw [h]
      exact hb1Base)
  have oneVertexCases := @helper_oneVertexCases_629 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C Q1 Q2 Q3 i1 i3 i2 hi3pos hi3le x1 oneTree hlen1 hseg1 hnew1
  have hx2One : x2 ∉ TreeSequenceVertexSet oneTree := by
    intro hx
    rcases oneVertexCases hx with hxBase | hxeq
    · exact hx2 (initialVertexSubset baseTree C.T hbaseInitial hxBase)
    · exact hx12 hxeq.symm
  have hb2One : C.b2 ∈ TreeSequenceVertexSet oneTree :=
    initialVertexSubset baseTree oneTree hseg1 hb2Base
  have hf2OneBoundary : C.f2 ∈ BoundaryEdges G
      (TreeSequenceVertexSet oneTree) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.b2, hb2One, x2, hx2One, hends2⟩
  exact @helper_continuation_583 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1 hQ1support hQ1length Q2 hQ2 hQ2support
      hQ2length Q3 hQ3 hQ3support hQ3length i3 hi3pos hi3le hbaseInitial hbaseLast hb1Base
      hb2Base hbaseTree hf1Sigma hf2Sigma hsigmaTriple initialVertexSubset x1 hx1 hends1 x2
      hx1Incident hx12 hx1Base oneTree hlen1 hseg1 hedge1 hnew1 oneVertexCases hf2OneBoundary
private theorem helper_continuation_549.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0),
        TreeVertexOrder C.T C.b1 C.b3 → TreeVertexOrder C.T C.b2 C.b3 →
    let component : Set (V ⊕ E) := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3);
        IsProperEdgeColoring G C.phi → IsProperEdgeColoring G sigma → (
    ∀ w ∈ TreeSequenceVertexSet C.T, Sum.inl w ∈ component ↔ w = C.b3) → C.b ∈ MissingColors G
        sigma C.b3 → C.a ∈ MissingColors G sigma C.a1 ∨ C.b ∈ MissingColors G sigma C.a1 → C.a ∈
        MissingColors G sigma C.a2 ∨ C.b ∈ MissingColors G sigma C.a2 → C.a ∈ MissingColors G
        sigma C.a3 ∨ C.b ∈ MissingColors G sigma C.a3 → (
    ∀ {u v : V} (p : (TwoColorIncidenceGraph G C.phi C.a C.b).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath C.T C.phi C.a C.b u v p → C.a ∈ MissingColors G sigma u ∨ C.b ∈ MissingColors
        G sigma u →
    ∃ (q : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath
        C.T sigma C.a C.b u v q ∧ q.support = p.support ∧ q.length = p.length) →
    ∀ (Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl C.b1)),
        TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1 → Q1.support = C.P1.support → Q1.length =
        C.P1.length →
    ∀ (Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl C.b2)),
        TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2 → Q2.support = C.P2.support → Q2.length =
        C.P2.length → Nonempty (TchangeKempeClosureData C) := by
  classical
  intro V E _ _ _ _ G k e0 C h13 h23 component sigma hproper hsigmaProper hcomponentTree
      hbetaMissing hremote1 hremote2 hremote3 transferExit Q1 hQ1 hQ1support hQ1length Q2 hQ2
      hQ2support hQ2length
  obtain ⟨Q3, hQ3, hQ3support, hQ3length⟩ :=
    transferExit C.P3 C.exit3 hremote3
  obtain ⟨i1, i3, hi1, hi3, hi13⟩ := h13
  obtain ⟨i2, i3', hi2, hi3', hi23⟩ := h23
  have hi3eq : i3' = i3 := by
    apply C.T.vertex_injective
    rw [hi3', hi3]
  subst i3'
  have hi3pos : 1 ≤ i3.val := by omega
  have hi3le : i3.val ≤ C.T.length := by omega
  let baseTree := TreeSequencePrefix C.T i3.val hi3pos hi3le
  have hbaseLen : baseTree.length = i3.val := by
    simp [baseTree, TreeSequencePrefix]
  have hbaseInitial : TreeSequenceInitialSegment baseTree C.T := by
    refine ⟨hi3le, ?_, ?_⟩
    · intro i
      simp [baseTree, TreeSequencePrefix]
    · intro j
      simp [baseTree, TreeSequencePrefix]
  have hbaseLast : baseTree.vertex (Fin.last baseTree.length) = C.b3 := by
    calc
      baseTree.vertex (Fin.last baseTree.length) =
          C.T.vertex (Fin.castLE (Nat.succ_le_succ hbaseInitial.1)
            (Fin.last baseTree.length)) := (hbaseInitial.2.1 _).symm
      _ = C.T.vertex i3 := by
        congr 1
      _ = C.b3 := hi3
  have hb1Base : C.b1 ∈ TreeSequenceVertexSet baseTree := by
    let r : Fin (baseTree.length + 1) := ⟨i1.val, by rw [hbaseLen]; omega⟩
    have hr : baseTree.vertex r = C.b1 := by calc
      baseTree.vertex r =
          C.T.vertex (Fin.castLE (Nat.succ_le_succ hbaseInitial.1) r) :=
        (hbaseInitial.2.1 r).symm
      _ = C.T.vertex i1 := by
        congr 1
      _ = C.b1 := hi1
    simpa [TreeSequenceVertexSet] using
      (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩)
  have hb2Base : C.b2 ∈ TreeSequenceVertexSet baseTree := by
    let r : Fin (baseTree.length + 1) := ⟨i2.val, by rw [hbaseLen]; omega⟩
    have hr : baseTree.vertex r = C.b2 := by calc
      baseTree.vertex r =
          C.T.vertex (Fin.castLE (Nat.succ_le_succ hbaseInitial.1) r) :=
        (hbaseInitial.2.1 r).symm
      _ = C.T.vertex i2 := by
        congr 1
      _ = C.b2 := hi2
    simpa [TreeSequenceVertexSet] using
      (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩)
  have fullVertexMem (r : Fin (C.T.length + 1)) :
      C.T.vertex r ∈ TreeSequenceVertexSet C.T := by
    simp [TreeSequenceVertexSet]
  have fixedBefore := @helper_fixedBefore_250 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C hcomponentTree Q1 Q2 Q3 i1 i3 hi3 i2 hi3pos hi3le hbaseLen
      fullVertexMem
  have hbaseTree := @helper_hbaseTree_302 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C hproper hcomponentTree Q1 Q2 Q3 i1 i3 hi3 i2 hi3pos hi3le hbaseLen
      hbaseInitial fullVertexMem fixedBefore
  have coloredIncidentOutside {w : V} {f : E}
      (hw : w ∈ TreeSequenceVertexSet C.T) (hwb3 : w ≠ C.b3)
      (hinc : Incident G w f) (hcolor : C.phi f = some C.b) :
      Sum.inr f ∉ component := by
    intro hfComponent
    have hadj : (TwoColorIncidenceGraph G C.phi C.a C.b).Adj
        (Sum.inl w) (Sum.inr f) := ⟨hinc, Or.inr hcolor⟩
    have hwComponent : Sum.inl w ∈ component := by
      change (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
          (Sum.inl w) =
        (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
          (Sum.inl C.b3)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hadj).trans hfComponent
    exact hwb3 ((hcomponentTree w hw).mp hwComponent)
  have hf1Data : C.f1 ∈ BoundaryEdges G (TreeSequenceVertexSet C.T) ∧
      C.phi C.f1 = some C.b := by
    simpa [BoundaryColorEdges] using C.boundary1
  have hf2Data : C.f2 ∈ BoundaryEdges G (TreeSequenceVertexSet C.T) ∧
      C.phi C.f2 = some C.b := by
    simpa [BoundaryColorEdges] using C.boundary2
  have hf1OutsideComponent : Sum.inr C.f1 ∉ component :=
    coloredIncidentOutside C.exit1.2.2.2.1 C.tree13 C.incident1 hf1Data.2
  have hf2OutsideComponent : Sum.inr C.f2 ∉ component :=
    coloredIncidentOutside C.exit2.2.2.2.1 C.tree23 C.incident2 hf2Data.2
  have hf1Sigma : sigma C.f1 = some C.b := by
    simpa [sigma, TwoColorComponentSwap, component, hf1OutsideComponent] using
      hf1Data.2
  have hf2Sigma : sigma C.f2 = some C.b := by
    simpa [sigma, TwoColorComponentSwap, component, hf2OutsideComponent] using
      hf2Data.2
  have hsigmaOne := @helper_hsigmaOne_593 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C
  have hsigmaTriple : KTriple G k e0 sigma :=
    ⟨C.triple.1, C.triple.2.1, C.triple.2.2.1, hsigmaProper, hsigmaOne⟩
  have initialVertexSubset : ∀ (A B : TreeSequence G e0),
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hAB v hv
    obtain ⟨r, _, hr⟩ := by
      simpa [TreeSequenceVertexSet] using hv
    have hmem : B.vertex (Fin.castLE (Nat.succ_le_succ hAB.1) r) ∈
        TreeSequenceVertexSet B := by
      simp [TreeSequenceVertexSet]
    simpa [hAB.2.1 r] using hmem
  exact @helper_continuation_572 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C hproper hbetaMissing hremote1 hremote2 hremote3 Q1 hQ1 hQ1support hQ1length Q2 hQ2
      hQ2support hQ2length Q3 hQ3 hQ3support hQ3length i1 i3 i2 hi3pos hi3le hbaseInitial
      hbaseLast hb1Base hb2Base hbaseTree hf1Data hf2Data hf1Sigma hf2Sigma hsigmaTriple
      initialVertexSubset
theorem TchangeKempeClosurePreparation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0)
    (hmissing : C.a ∈ MissingColors G C.phi C.b3)
    (h13 : TreeVertexOrder C.T C.b1 C.b3)
    (h23 : TreeVertexOrder C.T C.b2 C.b3) :
    Nonempty (TchangeKempeClosureData C) := by
  classical
  let component := TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3)
  let sigma := TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3)
  have hproper : IsProperEdgeColoring G C.phi := C.triple.2.2.2.1
  have hsigmaProper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G C.phi C.a C.b C.colorsDistinct hproper _
  have hcomponentTree : ∀ w, w ∈ TreeSequenceVertexSet C.T →
      (Sum.inl w ∈ component ↔ w = C.b3) := by
    intro w hw
    exact TreeExitComponentMeetsTreeOnlyAtExit C.T C.phi C.a C.b C.b3
      hproper hmissing ⟨C.a3, C.P3, C.exit3⟩ w hw
  have hcomponentB3 : Sum.inl C.b3 ∈ component := by
    rfl
  have hbetaMissing : C.b ∈ MissingColors G sigma C.b3 := by
    exact (TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
      C.colorsDistinct hproper (Sum.inl C.b3)).2.1 C.b3 hcomponentB3 hmissing
  have componentOfWalk {u v : V}
      (p : (TwoColorIncidenceGraph G C.phi C.a C.b).Walk
        (Sum.inl u) (Sum.inl v)) :
      Sum.inl u ∈ TwoColorComponent G C.phi C.a C.b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
        (Sum.inl u) =
      (TwoColorIncidenceGraph G C.phi C.a C.b).connectedComponentMk
        (Sum.inl v)
    exact SimpleGraph.ConnectedComponent.sound ⟨p⟩
  have hcomponentA3 : Sum.inl C.a3 ∈ component := by
    exact componentOfWalk C.P3
  have disjointComponent1 : Disjoint
      (TwoColorComponent G C.phi C.a C.b (Sum.inl C.b1)) component := by
    rcases TwoColorComponentsDisjoint G C.phi C.a C.b
      (Sum.inl C.b1) (Sum.inl C.b3) with heq | hdisjoint
    · exfalso
      have hb1Component : Sum.inl C.b1 ∈ component := by
        change Sum.inl C.b1 ∈
          TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3)
        rw [← heq]
        rfl
      exact C.tree13 ((hcomponentTree C.b1 C.exit1.2.2.2.1).mp hb1Component)
    · exact hdisjoint
  have disjointComponent2 : Disjoint
      (TwoColorComponent G C.phi C.a C.b (Sum.inl C.b2)) component := by
    rcases TwoColorComponentsDisjoint G C.phi C.a C.b
      (Sum.inl C.b2) (Sum.inl C.b3) with heq | hdisjoint
    · exfalso
      have hb2Component : Sum.inl C.b2 ∈ component := by
        change Sum.inl C.b2 ∈
          TwoColorComponent G C.phi C.a C.b (Sum.inl C.b3)
        rw [← heq]
        rfl
      exact C.tree23 ((hcomponentTree C.b2 C.exit2.2.2.2.1).mp hb2Component)
    · exact hdisjoint
  have hcomponentA1 :
      Sum.inl C.a1 ∈ TwoColorComponent G C.phi C.a C.b (Sum.inl C.b1) :=
    componentOfWalk C.P1
  have hcomponentA2 :
      Sum.inl C.a2 ∈ TwoColorComponent G C.phi C.a C.b (Sum.inl C.b2) :=
    componentOfWalk C.P2
  have ha1OutsideComponent : Sum.inl C.a1 ∉ component := by
    exact Set.disjoint_left.mp disjointComponent1 hcomponentA1
  have ha2OutsideComponent : Sum.inl C.a2 ∉ component := by
    exact Set.disjoint_left.mp disjointComponent2 hcomponentA2
  have hmissingA1 :
      MissingColors G sigma C.a1 = MissingColors G C.phi C.a1 := by
    exact (TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
      C.colorsDistinct hproper (Sum.inl C.b3)).1 C.a1 ha1OutsideComponent
  have hmissingA2 :
      MissingColors G sigma C.a2 = MissingColors G C.phi C.a2 := by
    exact (TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
      C.colorsDistinct hproper (Sum.inl C.b3)).1 C.a2 ha2OutsideComponent
  have hremote1 : C.a ∈ MissingColors G sigma C.a1 ∨
      C.b ∈ MissingColors G sigma C.a1 := by
    simpa [hmissingA1] using C.exit1.2.2.2.2.1
  have hremote2 : C.a ∈ MissingColors G sigma C.a2 ∨
      C.b ∈ MissingColors G sigma C.a2 := by
    simpa [hmissingA2] using C.exit2.2.2.2.2.1
  have hremote3 : C.a ∈ MissingColors G sigma C.a3 ∨
      C.b ∈ MissingColors G sigma C.a3 := by
    rcases C.exit3.2.2.2.2.1 with ha | hb
    · exact Or.inr
        ((TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
          C.colorsDistinct hproper (Sum.inl C.b3)).2.1 C.a3 hcomponentA3 ha)
    · exact Or.inl
        ((TwoColorComponentSwapMissingBehavior G C.phi C.a C.b
          C.colorsDistinct hproper (Sum.inl C.b3)).2.2.1 C.a3 hcomponentA3 hb)
  have graphEq := @helper_graphEq_137 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 C
  have transferExit := @helper_transferExit_476 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 C graphEq
  obtain ⟨Q1, hQ1, hQ1support, hQ1length⟩ :=
    transferExit C.P1 C.exit1 hremote1
  obtain ⟨Q2, hQ2, hQ2support, hQ2length⟩ :=
    transferExit C.P2 C.exit2 hremote2
  exact @helper_continuation_549 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C h13 h23 hproper hsigmaProper hcomponentTree hbetaMissing hremote1 hremote2 hremote3
      transferExit Q1 hQ1 hQ1support hQ1length Q2 hQ2 hQ2support hQ2length
end GoldbergSeymour

end
