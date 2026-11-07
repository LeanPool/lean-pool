/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TchangeCounterexampleMeasure
public import LeanPool.GoldbergSeymour.TchangeKempeClosureData

/-!
# Tchange Strict Shortening

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_hf1NotL_369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0)
      (D : TchangeKempeClosureData C),
    let _ : Finset V := TreeSequenceVertexSet D.closedTree;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G D.sigma C.a C.b;
    ∀ (c1 : V) (hc1Q : Sum.inl c1 ∈ D.Q1.support),
    TreeExitPath D.closedTree D.sigma C.a C.b C.a1 c1 (D.Q1.takeUntil (Sum.inl c1) hc1Q) →
    ∀ (c2 : V),
    Sum.inl c2 ∈ D.Q2.support →
    ∀ (c3 : V),
    Sum.inl c3 ∈ D.Q3.support →
    let L1 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl c1) :=
      D.Q1.takeUntil (Sum.inl c1) hc1Q;
    H = TwoColorIncidenceGraph G D.sigma C.b C.a →
    Sum.inr C.f1 ∉ L1.support := by
  classical
  intro V E _ _ _ _ G k e0 C D U H c1 hc1Q hExit1 c2 hc2Q c3 hc3Q L1 hGraph hf1L
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf1L
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    rw [hnzero, L1.getVert_zero] at hn
    simp at hn
  have hnlt : n < L1.length := by
    by_contra hnlt
    have hneq : n = L1.length := by omega
    rw [hneq, L1.getVert_length] at hn
    simp at hn
  have hprevAdj := L1.adj_getVert_succ (i := n - 1) (by omega)
  have hprevSucc : n - 1 + 1 = n := by omega
  rw [hprevSucc, hn] at hprevAdj
  cases hprev : L1.getVert (n - 1) with
  | inr f =>
      rw [hprev] at hprevAdj
      simp [TwoColorIncidenceGraph] at hprevAdj
  | inl x =>
      rw [hprev] at hprevAdj
      have hxf1 : Incident G x C.f1 := by
        have hdata : Incident G x C.f1 ∧
            (D.sigma C.f1 = some C.a ∨ D.sigma C.f1 = some C.b) := by
          simpa [H, TwoColorIncidenceGraph] using hprevAdj
        exact hdata.1
      have hxU : x ∈ U := D.f1EndsInside x hxf1
      have hxc : x = c1 := (hExit1.2.2.2.2.2 x hxU).mp (by
        rw [← hprev]
        exact L1.getVert_mem_support (n - 1))
      have heq : L1.getVert (n - 1) = L1.getVert L1.length := by
        rw [hprev, L1.getVert_length, hxc]
      have hpathL1 : L1.IsPath := hExit1.1
      have hindices := hpathL1.getVert_injOn
        ((Nat.sub_le n 1).trans hnle) (by simp) heq
      omega

private theorem helper_continuation_388.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0)
      (D : TchangeKempeClosureData C),
    let U : Finset V := TreeSequenceVertexSet D.closedTree;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G D.sigma C.a C.b;
    ∀ (c1 : V) (hc1Q : Sum.inl c1 ∈ D.Q1.support),
    TreeExitPath D.closedTree D.sigma C.a C.b C.a1 c1 (D.Q1.takeUntil (Sum.inl c1) hc1Q) →
    ∀ (g1 : E) (hg1L : Sum.inr g1 ∈ (D.Q1.takeUntil (Sum.inl c1) hc1Q).support)
      (hg1c : Incident G c1 g1) (c2 : V) (hc2Q : Sum.inl c2 ∈ D.Q2.support) (g2 : E)
      (hg2L : Sum.inr g2 ∈ (D.Q2.takeUntil (Sum.inl c2) hc2Q).support)
      (hg2c : Incident G c2 g2) (c3 : V) (hc3Q : Sum.inl c3 ∈ D.Q3.support) (g3 : E)
      (hg3L : Sum.inr g3 ∈ (D.Q3.takeUntil (Sum.inl c3) hc3Q).support)
      (hg3c : Incident G c3 g3),
    let L1 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl c1) :=
      D.Q1.takeUntil (Sum.inl c1) hc1Q;
    let L2 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl c2) :=
      D.Q2.takeUntil (Sum.inl c2) hc2Q;
    let L3 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl c3) :=
      D.Q3.takeUntil (Sum.inl c3) hc3Q;
    ∀ (hc12 : c1 ≠ c2) (hc13 : c1 ≠ c3) (hc23 : c2 ≠ c3)
      (hbTree : C.b ∈ TreeMissingColors D.sigma D.closedTree)
      (haNotTree : C.a ∉ TreeMissingColors D.sigma D.closedTree)
      (hGraph : H = TwoColorIncidenceGraph G D.sigma C.b C.a),
    let L1' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk (Sum.inl C.a1) (Sum.inl c1) :=
      hGraph ▸ L1;
    let L2' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk (Sum.inl C.a2) (Sum.inl c2) :=
      hGraph ▸ L2;
    let L3' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk (Sum.inl C.a3) (Sum.inl c3) :=
      hGraph ▸ L3;
    ∀ (hL1Support : L1'.support = L1.support) (hL2Support : L2'.support = L2.support)
      (hL3Support : L3'.support = L3.support),
    L1'.length = L1.length →
    L2'.length = L2.length →
    L3'.length = L3.length →
    ∀ (hExit1' : TreeExitPath D.closedTree D.sigma C.b C.a C.a1 c1 L1')
      (hExit2' : TreeExitPath D.closedTree D.sigma C.b C.a C.a2 c2 L2')
      (hExit3' : TreeExitPath D.closedTree D.sigma C.b C.a C.a3 c3 L3')
      (hdis12' : ∀ z ∈ L1'.support, z ∉ L2'.support)
      (hdis13' : ∀ z ∈ L1'.support, z ∉ L3'.support)
      (hdis23' : ∀ z ∈ L2'.support, z ∉ L3'.support)
      (hg1BoundaryColor : g1 ∈ BoundaryColorEdges G D.sigma U C.a)
      (hg2BoundaryColor : g2 ∈ BoundaryColorEdges G D.sigma U C.a)
      (hg3BoundaryColor : g3 ∈ BoundaryColorEdges G D.sigma U C.a),
    let _ : TchangeCounterexample G k e0 :=
      { phi := D.sigma, T := D.closedTree, a := C.b, b := C.a,
        colorsDistinct := Ne.symm C.colorsDistinct, triple := D.triple,
        tree := D.closureTree, closed := fun {_ : E} {_ : Fin k} {_ : V} => D.closureClosed,
        aMissing := hbTree, bNotMissing := haNotTree, a1 := C.a1, b1 := c1, a2 := C.a2,
        b2 := c2, a3 := C.a3, b3 := c3, P1 := L1', P2 := L2', P3 := L3', exit1 := hExit1',
        exit2 := hExit2', exit3 := hExit3', disjoint12 := hdis12', disjoint13 := hdis13',
        disjoint23 := hdis23', remote12 := C.remote12, remote13 := C.remote13,
        remote23 := C.remote23, tree12 := hc12, tree13 := hc13, tree23 := hc23, f1 := g1,
        f2 := g2, f3 := g3, boundary1 := hg1BoundaryColor, boundary2 := hg2BoundaryColor,
        boundary3 := hg3BoundaryColor, incident1 := hg1c, incident2 := hg2c,
        incident3 := hg3c,
        support1 :=
          Eq.mpr (id (congrArg (fun (_a : List (V ⊕ E)) => Sum.inr g1 ∈ _a) hL1Support))
            hg1L,
        support2 :=
          Eq.mpr (id (congrArg (fun (_a : List (V ⊕ E)) => Sum.inr g2 ∈ _a) hL2Support))
            hg2L,
        support3 :=
          Eq.mpr (id (congrArg (fun (_a : List (V ⊕ E)) => Sum.inr g3 ∈ _a) hL3Support))
            hg3L :
        TchangeCounterexample G k e0 };
    ∃ (C' : TchangeCounterexample G k e0),
    TchangeCounterexampleMeasure C' < TchangeCounterexampleMeasure C := by
  classical
  intro V E _ _ _ _ G k e0 C D U H c1 hc1Q hExit1 g1 hg1L hg1c c2 hc2Q g2 hg2L hg2c c3 hc3Q g3
      hg3L hg3c L1 L2 L3 hc12 hc13 hc23 hbTree haNotTree hGraph L1' L2' L3' hL1Support hL2Support
      hL3Support hL1Length hL2Length hL3Length hExit1' hExit2' hExit3' hdis12' hdis13' hdis23'
      hg1BoundaryColor hg2BoundaryColor hg3BoundaryColor C'
  have hf1Q : Sum.inr C.f1 ∈ D.Q1.support := by
    rw [D.support1]
    exact C.support1
  have hf1NotL := @helper_hf1NotL_369 V E inferInstance inferInstance inferInstance inferInstance G
      k e0 C D c1 hc1Q hExit1 c2 hc2Q c3 hc3Q hGraph
  have hlen1 : L1.length < D.Q1.length := by
    have hle : L1.length ≤ D.Q1.length := by
      exact D.Q1.length_takeUntil_le_length hc1Q
    by_contra hnlt
    have heqLen : L1.length = D.Q1.length := by omega
    have hsupportEq : L1.support = D.Q1.support := by
      apply (D.Q1.support_takeUntil_prefix_support hc1Q).eq_of_length
      rw [L1.length_support, D.Q1.length_support, heqLen]
    apply hf1NotL
    rw [hsupportEq]
    exact hf1Q
  have hlen2 : L2.length ≤ D.Q2.length :=
    D.Q2.length_takeUntil_le_length hc2Q
  have hlen3 : L3.length ≤ D.Q3.length :=
    D.Q3.length_takeUntil_le_length hc3Q
  refine ⟨C', ?_⟩
  unfold TchangeCounterexampleMeasure
  dsimp [C']
  rw [hL1Length, hL2Length, hL3Length, ← D.length1, ← D.length2,
    ← D.length3]
  omega

private theorem helper_continuation_315.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (C : TchangeCounterexample G k e0)
      (D : TchangeKempeClosureData C),
    let U : Finset V := TreeSequenceVertexSet D.closedTree;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G D.sigma C.a C.b;
    ∀ (c1 : V) (hc1Q : Sum.inl c1 ∈ D.Q1.support),
    TreeExitPath D.closedTree D.sigma C.a C.b C.a1 c1 (D.Q1.takeUntil (Sum.inl c1) hc1Q) →
    ∀ (g1 : E),
    Sum.inr g1 ∈ (D.Q1.takeUntil (Sum.inl c1) hc1Q).support →
    Incident G c1 g1 →
    g1 ∈ BoundaryEdges G U →
    ∀ (c2 : V) (hc2Q : Sum.inl c2 ∈ D.Q2.support),
    TreeExitPath D.closedTree D.sigma C.a C.b C.a2 c2 (D.Q2.takeUntil (Sum.inl c2) hc2Q) →
    ∀ (g2 : E),
    Sum.inr g2 ∈ (D.Q2.takeUntil (Sum.inl c2) hc2Q).support →
    Incident G c2 g2 →
    g2 ∈ BoundaryEdges G U →
    ∀ (c3 : V) (hc3Q : Sum.inl c3 ∈ D.Q3.support),
    TreeExitPath D.closedTree D.sigma C.a C.b C.a3 c3 (D.Q3.takeUntil (Sum.inl c3) hc3Q) →
    ∀ (g3 : E),
    Sum.inr g3 ∈ (D.Q3.takeUntil (Sum.inl c3) hc3Q).support →
    Incident G c3 g3 →
    g3 ∈ BoundaryEdges G U →
    let L1 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a1) (Sum.inl c1) :=
      D.Q1.takeUntil (Sum.inl c1) hc1Q;
    let L2 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a2) (Sum.inl c2) :=
      D.Q2.takeUntil (Sum.inl c2) hc2Q;
    let L3 : (TwoColorIncidenceGraph G D.sigma C.a C.b).Walk (Sum.inl C.a3) (Sum.inl c3) :=
      D.Q3.takeUntil (Sum.inl c3) hc3Q;
    D.sigma g1 = some C.a →
    D.sigma g2 = some C.a →
    D.sigma g3 = some C.a →
    (∀ z ∈ L1.support, z ∉ L2.support) →
    (∀ z ∈ L1.support, z ∉ L3.support) →
    (∀ z ∈ L2.support, z ∉ L3.support) →
    c1 ≠ c2 →
    c1 ≠ c3 →
    c2 ≠ c3 →
    C.b ∈ TreeMissingColors D.sigma D.closedTree →
    C.a ∉ TreeMissingColors D.sigma D.closedTree →
    H = TwoColorIncidenceGraph G D.sigma C.b C.a →
    ∃ (C' : TchangeCounterexample G k e0),
    TchangeCounterexampleMeasure C' < TchangeCounterexampleMeasure C := by
  classical
  intro V E _ _ _ _ G k e0 C D U H c1 hc1Q hExit1 g1 hg1L hg1c hg1Boundary c2 hc2Q hExit2 g2 hg2L
      hg2c hg2Boundary c3 hc3Q hExit3 g3 hg3L hg3c hg3Boundary L1 L2 L3 hg1a hg2a hg3a hdis12
      hdis13 hdis23 hc12 hc13 hc23 hbTree haNotTree hGraph
  have walkCastSupport {H1 H2 : SimpleGraph (Sum V E)} (h : H1 = H2)
      {z w : Sum V E} (p : H1.Walk z w) :
      (h ▸ p).support = p.support := by
    subst H2
    rfl
  have walkCastLength {H1 H2 : SimpleGraph (Sum V E)} (h : H1 = H2)
      {z w : Sum V E} (p : H1.Walk z w) :
      (h ▸ p).length = p.length := by
    subst H2
    rfl
  have walkCastPath {H1 H2 : SimpleGraph (Sum V E)} (h : H1 = H2)
      {z w : Sum V E} (p : H1.Walk z w) (hp : p.IsPath) :
      (h ▸ p).IsPath := by
    subst H2
    exact hp
  let L1' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk
      (Sum.inl C.a1) (Sum.inl c1) := hGraph ▸ L1
  let L2' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk
      (Sum.inl C.a2) (Sum.inl c2) := hGraph ▸ L2
  let L3' : (TwoColorIncidenceGraph G D.sigma C.b C.a).Walk
      (Sum.inl C.a3) (Sum.inl c3) := hGraph ▸ L3
  have hL1Support : L1'.support = L1.support := by
    exact walkCastSupport hGraph L1
  have hL2Support : L2'.support = L2.support := by
    exact walkCastSupport hGraph L2
  have hL3Support : L3'.support = L3.support := by
    exact walkCastSupport hGraph L3
  have hL1Length : L1'.length = L1.length := by
    exact walkCastLength hGraph L1
  have hL2Length : L2'.length = L2.length := by
    exact walkCastLength hGraph L2
  have hL3Length : L3'.length = L3.length := by
    exact walkCastLength hGraph L3
  have hExit1' : TreeExitPath D.closedTree D.sigma C.b C.a C.a1 c1 L1' := by
    unfold TreeExitPath at hExit1 ⊢
    refine ⟨?_, ?_, hExit1.2.2.1, hExit1.2.2.2.1, ?_, ?_⟩
    · exact walkCastPath hGraph L1 hExit1.1
    · rw [hL1Length]
      exact hExit1.2.1
    · exact hExit1.2.2.2.2.1.symm
    · intro w hw
      rw [hL1Support]
      exact hExit1.2.2.2.2.2 w hw
  have hExit2' : TreeExitPath D.closedTree D.sigma C.b C.a C.a2 c2 L2' := by
    unfold TreeExitPath at hExit2 ⊢
    refine ⟨?_, ?_, hExit2.2.2.1, hExit2.2.2.2.1, ?_, ?_⟩
    · exact walkCastPath hGraph L2 hExit2.1
    · rw [hL2Length]
      exact hExit2.2.1
    · exact hExit2.2.2.2.2.1.symm
    · intro w hw
      rw [hL2Support]
      exact hExit2.2.2.2.2.2 w hw
  have hExit3' : TreeExitPath D.closedTree D.sigma C.b C.a C.a3 c3 L3' := by
    unfold TreeExitPath at hExit3 ⊢
    refine ⟨?_, ?_, hExit3.2.2.1, hExit3.2.2.2.1, ?_, ?_⟩
    · exact walkCastPath hGraph L3 hExit3.1
    · rw [hL3Length]
      exact hExit3.2.1
    · exact hExit3.2.2.2.2.1.symm
    · intro w hw
      rw [hL3Support]
      exact hExit3.2.2.2.2.2 w hw
  have hdis12' : ∀ z, z ∈ L1'.support → z ∉ L2'.support := by
    intro z hz1 hz2
    rw [hL1Support] at hz1
    rw [hL2Support] at hz2
    exact hdis12 z hz1 hz2
  have hdis13' : ∀ z, z ∈ L1'.support → z ∉ L3'.support := by
    intro z hz1 hz3
    rw [hL1Support] at hz1
    rw [hL3Support] at hz3
    exact hdis13 z hz1 hz3
  have hdis23' : ∀ z, z ∈ L2'.support → z ∉ L3'.support := by
    intro z hz2 hz3
    rw [hL2Support] at hz2
    rw [hL3Support] at hz3
    exact hdis23 z hz2 hz3
  have hg1BoundaryColor :
      g1 ∈ BoundaryColorEdges G D.sigma U C.a := by
    simp [BoundaryColorEdges, hg1Boundary, hg1a]
  have hg2BoundaryColor :
      g2 ∈ BoundaryColorEdges G D.sigma U C.a := by
    simp [BoundaryColorEdges, hg2Boundary, hg2a]
  have hg3BoundaryColor :
      g3 ∈ BoundaryColorEdges G D.sigma U C.a := by
    simp [BoundaryColorEdges, hg3Boundary, hg3a]
  let C' : TchangeCounterexample G k e0 := {
    phi := D.sigma
    T := D.closedTree
    a := C.b
    b := C.a
    colorsDistinct := C.colorsDistinct.symm
    triple := D.triple
    tree := D.closureTree
    closed := D.closureClosed
    aMissing := hbTree
    bNotMissing := haNotTree
    a1 := C.a1
    b1 := c1
    a2 := C.a2
    b2 := c2
    a3 := C.a3
    b3 := c3
    P1 := L1'
    P2 := L2'
    P3 := L3'
    exit1 := hExit1'
    exit2 := hExit2'
    exit3 := hExit3'
    disjoint12 := hdis12'
    disjoint13 := hdis13'
    disjoint23 := hdis23'
    remote12 := C.remote12
    remote13 := C.remote13
    remote23 := C.remote23
    tree12 := hc12
    tree13 := hc13
    tree23 := hc23
    f1 := g1
    f2 := g2
    f3 := g3
    boundary1 := hg1BoundaryColor
    boundary2 := hg2BoundaryColor
    boundary3 := hg3BoundaryColor
    incident1 := hg1c
    incident2 := hg2c
    incident3 := hg3c
    support1 := by rw [hL1Support]; exact hg1L
    support2 := by rw [hL2Support]; exact hg2L
    support3 := by rw [hL3Support]; exact hg3L }
  exact @helper_continuation_388 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C D c1 hc1Q hExit1 g1 hg1L hg1c c2 hc2Q g2 hg2L hg2c c3 hc3Q g3 hg3L hg3c hc12 hc13 hc23
      hbTree haNotTree hGraph hL1Support hL2Support hL3Support hL1Length hL2Length hL3Length
      hExit1' hExit2' hExit3' hdis12' hdis13' hdis23' hg1BoundaryColor hg2BoundaryColor
      hg3BoundaryColor
theorem TchangeStrictShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0)
    (D : TchangeKempeClosureData C) :
    ∃ C' : TchangeCounterexample G k e0,
    TchangeCounterexampleMeasure C' < TchangeCounterexampleMeasure C := by
  classical
  let U := TreeSequenceVertexSet D.closedTree
  let H := TwoColorIncidenceGraph G D.sigma C.a C.b
  have firstEntry (a b : V) (Q : H.Walk (Sum.inl a) (Sum.inl b))
      (path : Q.IsPath)
      (missing : C.a ∈ MissingColors G D.sigma a ∨ C.b ∈ MissingColors G D.sigma a)
      (outside : a ∉ U) (inside : b ∈ U) :
      ∃ (c : V) (_ : c ∈ U) (member : Sum.inl c ∈ Q.support),
        let L := Q.takeUntil (Sum.inl c) member
        TreeExitPath D.closedTree D.sigma C.a C.b a c L ∧
        ∃ (edge : E) (other : V), Sum.inr edge ∈ L.support ∧ Incident G c edge ∧
          Incident G other edge ∧ other ∉ U ∧ edge ∈ BoundaryEdges G U ∧
          (D.sigma edge = some C.a ∨ D.sigma edge = some C.b) := by
    obtain ⟨c, hcU, member, exit⟩ :=
      TreeExitPath.firstEntry D.closedTree Q path missing outside ⟨b, inside, Q.end_mem_support⟩
    obtain ⟨edge, other, _, support, incident, otherIncident, otherOutside, boundary, colors⟩ :=
      exit.lastBoundaryEdge
    exact ⟨c, hcU, member, exit, edge, other, support, incident, otherIncident,
      otherOutside, boundary, colors⟩
  obtain ⟨c1, hc1U, hc1Q, hExit1, g1, x1, hg1L, hg1c, hg1x,
      hx1out, hg1Boundary, hg1Color⟩ :=
    firstEntry C.a1 C.b1 D.Q1 D.exit1.1 D.exit1.2.2.2.2.1
      D.a1Outside D.b1InClosure
  obtain ⟨c2, hc2U, hc2Q, hExit2, g2, x2, hg2L, hg2c, hg2x,
      hx2out, hg2Boundary, hg2Color⟩ :=
    firstEntry C.a2 C.b2 D.Q2 D.exit2.1 D.exit2.2.2.2.2.1
      D.a2Outside D.b2InClosure
  obtain ⟨c3, hc3U, hc3Q, hExit3, g3, x3, hg3L, hg3c, hg3x,
      hx3out, hg3Boundary, hg3Color⟩ :=
    firstEntry C.a3 C.b3 D.Q3 D.exit3.1 D.exit3.2.2.2.2.1
      D.a3Outside D.b3InClosure
  let L1 := D.Q1.takeUntil (Sum.inl c1) hc1Q
  let L2 := D.Q2.takeUntil (Sum.inl c2) hc2Q
  let L3 := D.Q3.takeUntil (Sum.inl c3) hc3Q
  have hL1Q1 : L1.support ⊆ D.Q1.support :=
    D.Q1.support_takeUntil_subset_support hc1Q
  have hL2Q2 : L2.support ⊆ D.Q2.support :=
    D.Q2.support_takeUntil_subset_support hc2Q
  have hL3Q3 : L3.support ⊆ D.Q3.support :=
    D.Q3.support_takeUntil_subset_support hc3Q
  have hg1a : D.sigma g1 = some C.a := by
    apply hg1Color.resolve_right
    intro hg1b
    exact (D.closureClosed hg1Boundary D.b3InClosure hg1b) D.betaMissing
  have hg2a : D.sigma g2 = some C.a := by
    apply hg2Color.resolve_right
    intro hg2b
    exact (D.closureClosed hg2Boundary D.b3InClosure hg2b) D.betaMissing
  have hg3a : D.sigma g3 = some C.a := by
    apply hg3Color.resolve_right
    intro hg3b
    exact (D.closureClosed hg3Boundary D.b3InClosure hg3b) D.betaMissing
  have hdis12 : ∀ z, z ∈ L1.support → z ∉ L2.support := by
    intro z hz1 hz2
    exact C.disjoint12 z (by rw [← D.support1]; exact hL1Q1 hz1)
      (by rw [← D.support2]; exact hL2Q2 hz2)
  have hdis13 : ∀ z, z ∈ L1.support → z ∉ L3.support := by
    intro z hz1 hz3
    exact C.disjoint13 z (by rw [← D.support1]; exact hL1Q1 hz1)
      (by rw [← D.support3]; exact hL3Q3 hz3)
  have hdis23 : ∀ z, z ∈ L2.support → z ∉ L3.support := by
    intro z hz2 hz3
    exact C.disjoint23 z (by rw [← D.support2]; exact hL2Q2 hz2)
      (by rw [← D.support3]; exact hL3Q3 hz3)
  have hc12 : c1 ≠ c2 := by
    intro hc
    have hgne : g1 ≠ g2 := by
      intro hge
      subst g2
      exact hdis12 (Sum.inr g1) hg1L hg2L
    exact D.triple.2.2.2.1 hgne ⟨c1, hg1c, hc ▸ hg2c⟩ hg1a
      (by simpa using hg2a)
  have hc13 : c1 ≠ c3 := by
    intro hc
    have hgne : g1 ≠ g3 := by
      intro hge
      subst g3
      exact hdis13 (Sum.inr g1) hg1L hg3L
    exact D.triple.2.2.2.1 hgne ⟨c1, hg1c, hc ▸ hg3c⟩ hg1a
      (by simpa using hg3a)
  have hc23 : c2 ≠ c3 := by
    intro hc
    have hgne : g2 ≠ g3 := by
      intro hge
      subst g3
      exact hdis23 (Sum.inr g2) hg2L hg3L
    exact D.triple.2.2.2.1 hgne ⟨c2, hg2c, hc ▸ hg3c⟩ hg2a
      (by simpa using hg3a)
  have hbTree : C.b ∈ TreeMissingColors D.sigma D.closedTree := by
    unfold TreeMissingColors
    simp only [Finset.mem_biUnion]
    exact ⟨C.b3, D.b3InClosure, D.betaMissing⟩
  have haNotTree : C.a ∉ TreeMissingColors D.sigma D.closedTree := by
    intro haTree
    unfold TreeMissingColors at haTree
    simp only [Finset.mem_biUnion] at haTree
    obtain ⟨v, hvU, hva⟩ := haTree
    exact (D.closureClosed hg1Boundary hvU hg1a) hva
  have hGraph : H = TwoColorIncidenceGraph G D.sigma C.b C.a := by
    apply SimpleGraph.ext
    funext z w
    cases z <;> cases w <;>
      simp [H, TwoColorIncidenceGraph, or_comm]
  exact @helper_continuation_315 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 C D c1 hc1Q hExit1 g1 hg1L hg1c hg1Boundary c2 hc2Q hExit2 g2 hg2L hg2c hg2Boundary c3
      hc3Q hExit3 g3 hg3L hg3c hg3Boundary hg1a hg2a hg3a hdis12 hdis13 hdis23 hc12 hc13 hc23
      hbTree haNotTree hGraph
end GoldbergSeymour

end
