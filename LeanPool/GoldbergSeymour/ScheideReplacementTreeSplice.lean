/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideSelectedBlockDeletion
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists

/-!
# Scheide Replacement Tree Splice

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_adjoin_facts_94.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
        (e0 : E) (A B : TreeSequence G e0) (f : E) (x y : V), G.ends f = s(x, y) → y ∉
        TreeSequenceVertexSet A → TreeSequenceAdjoinEdge A f B → B.vertex (Fin.last B.length) = y
        ∧ TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) ∧ Finset.image B.edge
        Finset.univ = insert f (Finset.image A.edge Finset.univ) := by
  classical
  intro V E _ _ G e0 A B f x y hxy hyA hAB
  rcases hAB with ⟨hlen, hinit, hlast⟩
  rcases hinit with ⟨hle, hvertices, hedges⟩
  let j : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  have hjval : j.val = A.length := by simp [j]
  obtain ⟨a, ha⟩ := B.attaches j
  let aA : Fin (A.length + 1) := ⟨a.val, by simpa [hjval] using a.isLt⟩
  have haIndex :
      Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)) =
        Fin.castLE (Nat.succ_le_succ hle) aA := by
    apply Fin.ext
    rfl
  have haOld : B.vertex
      (Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt))) =
        A.vertex aA := by
    rw [haIndex]
    exact hvertices aA
  have haMem : B.vertex
      (Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt))) ∈
        TreeSequenceVertexSet A := by
    rw [haOld]
    simp [TreeSequenceVertexSet]
  have hjSucc : j.succ = Fin.last B.length := by
    apply Fin.ext
    simp [hjval]
    omega
  have hpair : s(x, y) = s(B.vertex j.succ,
      B.vertex (Fin.castLT a
        (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)))) := by
    rw [← hxy, ← hlast]
    exact ha
  have hlastVertex : B.vertex (Fin.last B.length) = y := by
    rcases Sym2.eq_iff.mp hpair with hstraight | hcross
    · exact (hyA (hstraight.2 ▸ haMem)).elim
    · rw [← hjSucc]
      exact hcross.2.symm
  refine ⟨hlastVertex, ?_, ?_⟩
  · ext z
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · rintro ⟨q, rfl⟩
      by_cases hq : q.val < A.length + 1
      · right
        let qA : Fin (A.length + 1) := ⟨q.val, hq⟩
        refine ⟨qA, ?_⟩
        have hqIndex : q = Fin.castLE (Nat.succ_le_succ hle) qA := by
          apply Fin.ext
          rfl
        rw [hqIndex, hvertices]
      · left
        have hqLast : q = Fin.last B.length := by
          apply Fin.ext
          simp
          omega
        rw [hqLast, hlastVertex]
    · rintro (rfl | ⟨q, rfl⟩)
      · exact ⟨Fin.last B.length, hlastVertex⟩
      · exact ⟨Fin.castLE (Nat.succ_le_succ hle) q, hvertices q⟩
  · ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨q, rfl⟩
      by_cases hq : q.val < A.length
      · right
        let qA : Fin A.length := ⟨q.val, hq⟩
        refine ⟨qA, ?_⟩
        have hqIndex : q = Fin.castLE hle qA := by
          apply Fin.ext
          rfl
        rw [hqIndex, hedges]
      · left
        have hqj : q = j := by
          apply Fin.ext
          simpa [hjval] using (show q.val = A.length by omega)
        rw [hqj, hlast]
    · rintro (rfl | ⟨q, rfl⟩)
      · exact ⟨j, hlast⟩
      · exact ⟨Fin.castLE hle q, hedges q⟩

private theorem helper_branch_362.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (f1 f2 : E) (S :
        TreeSequence G e0), S.length + (2 : ℕ) = T.length →
    ∀ (rE : Fin S.length → Fin T.length), (
    ∀ (q : Fin S.length), S.edge q = T.edge (rE q)) → (
    ∀ (q : Fin S.length), (↑q : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) → (↑(rE q)
        : ℕ) = (↑q : ℕ)) → (
    ∀ (q : Fin S.length), C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) ≤ (↑q : ℕ) → (↑(rE q)
        : ℕ) = (↑q : ℕ) + (2 : ℕ)) →
    ∀ (S1 : TreeSequence G e0), Finset.image S1.edge Finset.univ = insert f1 (Finset.image S.edge
        Finset.univ) →
    ∀ (S2 : TreeSequence G e0), Finset.image S2.edge Finset.univ = insert f2 (Finset.image S1.edge
        Finset.univ) → S1.length = S.length + (1 : ℕ) → S2.length = S1.length + (1 : ℕ) →
        Finset.image S2.edge Finset.univ = ((Finset.image T.edge Finset.univ).erase (C.blockEdge
        (D.gammaIndex d) (0 : Fin (2 : ℕ)))).erase (C.blockEdge (D.gammaIndex d) (1 : Fin (2 :
        ℕ))) ∪ { f1, f2 } := by
  classical
  intro V E _ _ _ G k e0 phi T C D d f1 f2 S hSlen rE hSE hreBefore hreAfter S1 hS1edges S2
      hS2edges hlen1 hlen2
  have hnoBlock (q : Fin S.length) (j : Fin 2) :
      S.edge q ≠ C.blockEdge (D.gammaIndex d) j := by
    intro heq
    let blockIndex : Fin T.length :=
      ⟨C.p - 1 + 2 * (D.gammaIndex d).val + j.val, by
        have hi := (D.gammaIndex d).isLt
        have hj := j.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        omega⟩
    have hindex : rE q = blockIndex := by
      apply T.edge_injective
      calc
        T.edge (rE q) = S.edge q := (hSE q).symm
        _ = C.blockEdge (D.gammaIndex d) j := heq
        _ = T.edge blockIndex := by
          symm
          exact C.block_edge_position (D.gammaIndex d) j
    have hval := congrArg Fin.val hindex
    by_cases hq : q.val < C.p - 1 + 2 * (D.gammaIndex d).val
    · rw [hreBefore q hq] at hval
      dsimp [blockIndex] at hval
      omega
    · rw [hreAfter q (by omega)] at hval
      dsimp [blockIndex] at hval
      have hj := j.isLt
      omega
  have hSedges : Finset.univ.image S.edge =
      ((Finset.univ.image T.edge).erase
        (C.blockEdge (D.gammaIndex d) 0)).erase
          (C.blockEdge (D.gammaIndex d) 1) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨hnoBlock q 1, hnoBlock q 0, rE q, (hSE q).symm⟩
    · rintro ⟨hne1, hne0, t, rfl⟩
      let cut := C.p - 1 + 2 * (D.gammaIndex d).val
      by_cases ht : t.val < cut
      · let q : Fin S.length := ⟨t.val, by
          have hi := (D.gammaIndex d).isLt
          have hp := C.p_ge_two
          have hc := C.length_eq
          dsimp [cut] at ht
          omega⟩
        refine ⟨q, ?_⟩
        rw [hSE q]
        congr 1
        apply Fin.ext
        apply hreBefore q
        simpa [q, cut] using ht
      · have ht0 : t.val ≠ cut := by
          intro ht0
          apply hne0
          rw [← C.block_edge_position (D.gammaIndex d) 0]
          congr 1
          apply Fin.ext
          simpa [cut] using ht0
        have ht1 : t.val ≠ cut + 1 := by
          intro ht1
          apply hne1
          rw [← C.block_edge_position (D.gammaIndex d) 1]
          congr 1
          apply Fin.ext
          simpa [cut] using ht1
        have ht2 : cut + 2 ≤ t.val := by omega
        let q : Fin S.length := ⟨t.val - 2, by omega⟩
        refine ⟨q, ?_⟩
        rw [hSE q]
        congr 1
        apply Fin.ext
        have hr := hreAfter q (by dsimp [q]; omega)
        rw [hr]
        dsimp [q]
        omega
  rw [hS2edges, hS1edges, hSedges]
  ext e
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  tauto

private theorem helper_branch_396.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (S : TreeSequence G e0)
        (hSlen : S.length + (2 : ℕ) = T.length) (rV : Fin (S.length + (1 : ℕ)) → Fin (T.length +
        (1 : ℕ))), (
    ∀ (q : Fin (S.length + (1 : ℕ))), S.vertex q = T.vertex (rV q)) → (
    ∀ (q : Fin (S.length + (1 : ℕ))), (↑q : ℕ) < C.p + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) → (↑(rV
        q) : ℕ) = (↑q : ℕ)) →
    ∀ (S1 S2 : TreeSequence G e0) (hlen1 : S1.length = S.length + (1 : ℕ)) (hlen2 : S2.length =
        S1.length + (1 : ℕ)), S.length ≤ S1.length →
    ∀ (_ : S2.length = T.length), (
    ∀ (q : Fin (S.length + (1 : ℕ))), S1.vertex (⟨(↑q : ℕ), Decidable.byContradiction fun (a :
        ¬(↑q : ℕ) < S1.length + (1 : ℕ)) =>
    by
                  omega
    ⟩ : Fin (S1.length + (1 : ℕ))) = S.vertex q) → (
    ∀ (q : Fin (S1.length + (1 : ℕ))), S2.vertex (⟨(↑q : ℕ), Decidable.byContradiction fun (a :
        ¬(↑q : ℕ) < S2.length + (1 : ℕ)) =>
    by
                  omega
    ⟩ : Fin (S2.length + (1 : ℕ))) = S1.vertex q) →
    ∀ q ≤ C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ),
    ∀ (hq : q < T.length + (1 : ℕ)), S2.vertex (⟨q,
    by omega
    ⟩ : Fin (S2.length + (1 : ℕ))) = T.vertex (⟨q, hq⟩ : Fin (T.length + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d S hSlen rV hSV hrvBefore S1 S2 hlen1 hlen2 hle1
      hreplacementLength hS1Vertex hS2Vertex q hqBefore hqT
  let qS : Fin (S.length + 1) := ⟨q, by
    have hi := (D.gammaIndex d).isLt
    have hp := C.p_ge_two
    have hc := C.length_eq
    omega⟩
  let qS1 : Fin (S1.length + 1) :=
    ⟨q, Nat.lt_of_lt_of_le qS.isLt (Nat.succ_le_succ hle1)⟩
  calc
    S2.vertex ⟨q, by rw [hreplacementLength]; omega⟩ = S1.vertex qS1 :=
      hS2Vertex qS1
    _ = S.vertex qS := hS1Vertex qS
    _ = T.vertex (rV qS) := hSV qS
    _ = T.vertex ⟨q, hqT⟩ := by
      congr 1
      apply Fin.ext
      apply hrvBefore qS
      change q < C.p + 2 * (D.gammaIndex d).val
      have hp := C.p_ge_two
      omega

private theorem helper_branch_429.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (S : TreeSequence G e0)
        (hSlen : S.length + (2 : ℕ) = T.length) (rE : Fin S.length → Fin T.length), (
    ∀ (q : Fin S.length), S.edge q = T.edge (rE q)) → (
    ∀ (q : Fin S.length), (↑q : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) → (↑(rE q)
        : ℕ) = (↑q : ℕ)) →
    ∀ (S1 S2 : TreeSequence G e0) (hlen1 : S1.length = S.length + (1 : ℕ)) (hlen2 : S2.length =
        S1.length + (1 : ℕ)), S.length ≤ S1.length →
    ∀ (_ : S2.length = T.length), (
    ∀ (q : Fin S.length), S1.edge (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S1.length) =>
    by omega
    ⟩ : Fin S1.length) = S.edge q) → (
    ∀ (q : Fin S1.length), S2.edge (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S2.length) =>
    by omega
    ⟩ : Fin S2.length) = S1.edge q) →
    ∀ q < C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ),
    ∀ (hq : q < T.length), S2.edge (⟨q,
    by omega
    ⟩ : Fin S2.length) = T.edge (⟨q, hq⟩ : Fin T.length) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d S hSlen rE hSE hreBefore S1 S2 hlen1 hlen2 hle1
      hreplacementLength hS1Edge hS2Edge q hqBefore hqT
  let qS : Fin S.length := ⟨q, by
    have hi := (D.gammaIndex d).isLt
    have hp := C.p_ge_two
    have hc := C.length_eq
    omega⟩
  let qS1 : Fin S1.length :=
    ⟨q, Nat.lt_of_lt_of_le qS.isLt hle1⟩
  calc
    S2.edge ⟨q, by rw [hreplacementLength]; exact hqT⟩ = S1.edge qS1 :=
      hS2Edge qS1
    _ = S.edge qS := hS1Edge qS
    _ = T.edge (rE qS) := hSE qS
    _ = T.edge ⟨q, hqT⟩ := by
      congr 1
      apply Fin.ext
      exact hreBefore qS hqBefore

private theorem helper_branch_447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (S : TreeSequence G e0)
        (hSlen : S.length + (2 : ℕ) = T.length) (rE : Fin S.length → Fin T.length), (
    ∀ (q : Fin S.length), S.edge q = T.edge (rE q)) → (
    ∀ (q : Fin S.length), C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) ≤ (↑q : ℕ) → (↑(rE q)
        : ℕ) = (↑q : ℕ) + (2 : ℕ)) →
    ∀ (S1 S2 : TreeSequence G e0) (hlen1 : S1.length = S.length + (1 : ℕ)) (hlen2 : S2.length =
        S1.length + (1 : ℕ)), S.length ≤ S1.length →
    ∀ (_ : S2.length = T.length), (
    ∀ (q : Fin S.length), S1.edge (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S1.length) =>
    by omega
    ⟩ : Fin S1.length) = S.edge q) → (
    ∀ (q : Fin S1.length), S2.edge (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S2.length) =>
    by omega
    ⟩ : Fin S2.length) = S1.edge q) →
    ∀ (q : ℕ), C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) ≤ q →
    ∀ (hq : q + (2 : ℕ) < T.length), S2.edge (⟨q,
    by omega
    ⟩ : Fin S2.length) = T.edge (⟨q + (2 : ℕ), hq⟩ : Fin T.length) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d S hSlen rE hSE hreAfter S1 S2 hlen1 hlen2 hle1
      hreplacementLength hS1Edge hS2Edge q hqAfter hqT
  let qS : Fin S.length := ⟨q, by omega⟩
  let qS1 : Fin S1.length :=
    ⟨q, Nat.lt_of_lt_of_le qS.isLt hle1⟩
  calc
    S2.edge ⟨q, by rw [hreplacementLength]; omega⟩ = S1.edge qS1 :=
      hS2Edge qS1
    _ = S.edge qS := hS1Edge qS
    _ = T.edge (rE qS) := hSE qS
    _ = T.edge ⟨q + 2, hqT⟩ := by
      congr 1
      apply Fin.ext
      exact hreAfter qS hqAfter

private theorem helper_branch_460.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (S : TreeSequence G e0)
        (hSlen : S.length + (2 : ℕ) = T.length) (rV : Fin (S.length + (1 : ℕ)) → Fin (T.length +
        (1 : ℕ))), (
    ∀ (q : Fin (S.length + (1 : ℕ))), S.vertex q = T.vertex (rV q)) → (
    ∀ (q : Fin (S.length + (1 : ℕ))), C.p + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) ≤ (↑q : ℕ) → (↑(rV
        q) : ℕ) = (↑q : ℕ) + (2 : ℕ)) →
    ∀ (S1 S2 : TreeSequence G e0) (hlen1 : S1.length = S.length + (1 : ℕ)) (hlen2 : S2.length =
        S1.length + (1 : ℕ)), S.length ≤ S1.length →
    ∀ (_ : S2.length = T.length), (
    ∀ (q : Fin (S.length + (1 : ℕ))), S1.vertex (⟨(↑q : ℕ), Decidable.byContradiction fun (a :
        ¬(↑q : ℕ) < S1.length + (1 : ℕ)) => (
    by first  | omega
    )⟩ : Fin (S1.length + (1 : ℕ))) = S.vertex q) → (
    ∀ (q : Fin (S1.length + (1 : ℕ))), S2.vertex (⟨(↑q : ℕ), Decidable.byContradiction fun (a :
        ¬(↑q : ℕ) < S2.length + (1 : ℕ)) => (
    by first  | omega
    )⟩ : Fin (S2.length + (1 : ℕ))) = S1.vertex q) →
    ∀ (q : ℕ), C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.gammaIndex d) : ℕ) < q →
    ∀ (hq : q + (2 : ℕ) < T.length + (1 : ℕ)), S2.vertex (⟨q,
    by omega
    ⟩ : Fin (S2.length + (1 : ℕ))) = T.vertex (⟨q + (2 : ℕ), hq⟩ : Fin (T.length + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d S hSlen rV hSV hrvAfter S1 S2 hlen1 hlen2 hle1
      hreplacementLength hS1Vertex hS2Vertex q hqAfter hqT
  let qS : Fin (S.length + 1) := ⟨q, by omega⟩
  let qS1 : Fin (S1.length + 1) :=
    ⟨q, Nat.lt_of_lt_of_le qS.isLt (Nat.succ_le_succ hle1)⟩
  calc
    S2.vertex ⟨q, by rw [hreplacementLength]; omega⟩ = S1.vertex qS1 :=
      hS2Vertex qS1
    _ = S.vertex qS := hS1Vertex qS
    _ = T.vertex (rV qS) := hSV qS
    _ = T.vertex ⟨q + 2, hqT⟩ := by
      congr 1
      apply Fin.ext
      apply hrvAfter qS
      change C.p + 2 * (D.gammaIndex d).val ≤ q
      omega

private theorem helper_branch_475.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (_ : ScheideDefectiveSetup G k e0 phi
        T C) (_ : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (f1 f2 : E) (S :
        TreeSequence G e0), S.length + (2 : ℕ) = T.length →
    ∀ (S1 S2 : TreeSequence G e0) (hlen1 : S1.length = S.length + (1 : ℕ)), S1.edge (Fin.cast ((
    by first  | omega
    )) (Fin.last S.length)) = f1 →
    ∀ (hlen2 : S2.length = S1.length + (1 : ℕ)), S2.edge (Fin.cast ((
    by first  | omega
    )) (Fin.last S1.length)) = f2 →
    ∀ (hreplacementLength : S2.length = T.length), (
    ∀ (q : Fin S1.length), S2.edge (⟨(↑q : ℕ), Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S2.length) =>
    by omega
    ⟩ : Fin S2.length) = S1.edge q) → S2.edge (⟨T.length - (2 : ℕ),
    by omega
    ⟩ : Fin S2.length) = f1 ∧ S2.edge (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin S2.length) = f2 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d f1 f2 S hSlen S1 S2 hlen1 hlastEdge1 hlen2 hlastEdge2
      hreplacementLength hS2Edge
  constructor
  · let qS1 : Fin S1.length := ⟨T.length - 2, by omega⟩
    calc
      S2.edge ⟨T.length - 2, by omega⟩ = S1.edge qS1 := hS2Edge qS1
      _ = S1.edge (Fin.cast hlen1.symm (Fin.last S.length)) := by
        congr 1
        apply Fin.ext
        simp [qS1]
        omega
      _ = f1 := hlastEdge1
  · calc
      S2.edge ⟨T.length - 1, by omega⟩ =
          S2.edge (Fin.cast hlen2.symm (Fin.last S1.length)) := by
        congr 1
        apply Fin.ext
        simp
        omega
      _ = f2 := hlastEdge2

private theorem helper_branch_493.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (_ : ScheideDefectiveSetup G k e0 phi
        T C) (_ : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (u1 u2 : V) (S :
        TreeSequence G e0), S.length + (2 : ℕ) = T.length →
    ∀ (S1 : TreeSequence G e0), S1.vertex (Fin.last S1.length) = u1 →
    ∀ (S2 : TreeSequence G e0), S2.vertex (Fin.last S2.length) = u2 → S1.length = S.length + (1 :
        ℕ) →
    ∀ (hlen2 : S2.length = S1.length + (1 : ℕ)) (hreplacementLength : S2.length = T.length), (
    ∀ (q : Fin (S1.length + (1 : ℕ))), S2.vertex (⟨(↑q : ℕ), Decidable.byContradiction fun (a :
        ¬(↑q : ℕ) < S2.length + (1 : ℕ)) => (
    by first  | omega
    )⟩ : Fin (S2.length + (1 : ℕ))) = S1.vertex q) → S2.vertex (⟨T.length - (1 : ℕ),
    by omega
    ⟩ : Fin (S2.length + (1 : ℕ))) = u1 ∧ S2.vertex (⟨T.length,
    by omega
    ⟩ : Fin (S2.length + (1 : ℕ))) = u2 := by
  classical
  intro V E _ _ _ G k e0 phi T C D d u1 u2 S hSlen S1 hlastVertex1 S2 hlastVertex2 hlen1 hlen2
      hreplacementLength hS2Vertex
  constructor
  · let qS1 : Fin (S1.length + 1) := ⟨T.length - 1, by omega⟩
    calc
      S2.vertex ⟨T.length - 1, by omega⟩ = S1.vertex qS1 :=
        hS2Vertex qS1
      _ = S1.vertex (Fin.last S1.length) := by
        congr 1
        apply Fin.ext
        simp [qS1]
        omega
      _ = u1 := hlastVertex1
  · calc
      S2.vertex ⟨T.length, by omega⟩ = S2.vertex (Fin.last S2.length) := by
        congr 1
        apply Fin.ext
        simp
        omega
      _ = u2 := hlastVertex2

theorem ScheideReplacementTreeSplice {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ (d : { delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T) }) (f1 f2 : E) (v1
        v2 u1 u2 : V), f1 ≠ f2 → u1 ≠ u2 → v1 ∈ TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} → v2 ∈
        TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1} → u1 ∉
        TreeSequenceVertexSet T → u2 ∉ TreeSequenceVertexSet T → G.ends f1 = s(v1, u1) → G.ends f2
        = s(v2, u2) →
    ∃ replacementTree : TreeSequence G e0,
    ∃ replacement_length : replacementTree.length = T.length, (
    ∀ q : ℕ, q < C.p - 1 + 2 * (D.gammaIndex d).val →
    ∀ hq : q < T.length, replacementTree.edge ⟨q,
    by omega
    ⟩ = T.edge ⟨q, hq⟩) ∧ (
    ∀ q : ℕ, q ≤ C.p - 1 + 2 * (D.gammaIndex d).val →
    ∀ hq : q < T.length + 1, replacementTree.vertex ⟨q,
    by omega
    ⟩ = T.vertex ⟨q, hq⟩) ∧ (
    ∀ q : ℕ, C.p - 1 + 2 * (D.gammaIndex d).val ≤ q →
    ∀ hq : q + 2 < T.length, replacementTree.edge ⟨q,
    by omega
    ⟩ = T.edge ⟨q + 2, hq⟩) ∧ (
    ∀ q : ℕ, C.p - 1 + 2 * (D.gammaIndex d).val < q →
    ∀ hq : q + 2 < T.length + 1, replacementTree.vertex ⟨q,
    by omega
    ⟩ = T.vertex ⟨q + 2, hq⟩) ∧ (replacementTree.edge ⟨T.length - 2,
    by
                      have hi := (D.gammaIndex d).isLt
                      have hp := C.p_ge_two
                      have hc := C.length_eq
                      have _ := replacement_length
                      omega
    ⟩ = f1 ∧ replacementTree.edge ⟨T.length - 1,
    by
                      have hi := (D.gammaIndex d).isLt
                      have hp := C.p_ge_two
                      have hc := C.length_eq
                      have _ := replacement_length
                      omega
    ⟩ = f2) ∧ (replacementTree.vertex ⟨T.length - 1,
    by
                        have _ := (D.gammaIndex d).isLt
                        have _ := C.p_ge_two
                        have hc := C.length_eq
                        have _ := replacement_length
                        omega
    ⟩ = u1 ∧ replacementTree.vertex ⟨T.length,
    by
                        have _ := replacement_length
                        omega
    ⟩ = u2) ∧ TreeSequenceVertexSet replacementTree = (TreeSequenceVertexSet T \
        {C.blockVertex (D.gammaIndex d) 0, C.blockVertex (D.gammaIndex d) 1}) ∪ { u1, u2 } ∧
        Finset.univ.image replacementTree.edge = (((Finset.univ.image T.edge).erase (C.blockEdge
        (D.gammaIndex d) 0)).erase (C.blockEdge (D.gammaIndex d) 1)) ∪ { f1, f2 } := by
  classical
  intro d f1 f2 v1 v2 u1 u2 hf12 hu12 hv1 hv2 hu1T hu2T hf1ends hf2ends
  have adjoin_facts := @helper_adjoin_facts_94 V E inferInstance inferInstance G e0
  obtain ⟨S, hSvertices, hSlen, hVembedding, hEembedding,
      hbaseVertices, hbaseEdges, hremainingBlocks, hedgeClass,
      hSedgeOld, hSavoids⟩ :=
    ScheideSelectedBlockDeletion G k e0 phi T C (D.gammaIndex d)
  obtain ⟨rV, hSV, hrvBefore, hrvAfter⟩ := hVembedding
  obtain ⟨rE, hSE, hreBefore, hreAfter⟩ := hEembedding
  have hv1S : v1 ∈ TreeSequenceVertexSet S := by
    rw [hSvertices]
    exact hv1
  have hv2S : v2 ∈ TreeSequenceVertexSet S := by
    rw [hSvertices]
    exact hv2
  have hu1S : u1 ∉ TreeSequenceVertexSet S := by
    rw [hSvertices]
    exact fun h => hu1T (Finset.mem_sdiff.mp h).1
  have hu2S : u2 ∉ TreeSequenceVertexSet S := by
    rw [hSvertices]
    exact fun h => hu2T (Finset.mem_sdiff.mp h).1
  have hf1Boundary : f1 ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v1, hv1S, u1, hu1S, hf1ends⟩
  obtain ⟨S1, hSS1⟩ :=
    TreeSequenceBoundaryEdgeAppendExists S f1 hf1Boundary
  obtain ⟨hlastVertex1, hS1vertices, hS1edges⟩ :=
    adjoin_facts S S1 f1 v1 u1 hf1ends hu1S hSS1
  have hv2S1 : v2 ∈ TreeSequenceVertexSet S1 := by
    rw [hS1vertices]
    exact Finset.mem_insert_of_mem hv2S
  have hu2S1 : u2 ∉ TreeSequenceVertexSet S1 := by
    rw [hS1vertices]
    simp only [Finset.mem_insert, not_or]
    exact ⟨hu12.symm, hu2S⟩
  have hf2Boundary : f2 ∈ BoundaryEdges G (TreeSequenceVertexSet S1) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v2, hv2S1, u2, hu2S1, hf2ends⟩
  obtain ⟨S2, hS1S2⟩ :=
    TreeSequenceBoundaryEdgeAppendExists S1 f2 hf2Boundary
  obtain ⟨hlastVertex2, hS2vertices, hS2edges⟩ :=
    adjoin_facts S1 S2 f2 v2 u2 hf2ends hu2S1 hS1S2
  rcases hSS1 with ⟨hlen1, hinit1, hlastEdge1⟩
  rcases hS1S2 with ⟨hlen2, hinit2, hlastEdge2⟩
  rcases hinit1 with ⟨hle1, hV1, hE1⟩
  rcases hinit2 with ⟨hle2, hV2, hE2⟩
  have hreplacementLength : S2.length = T.length := by omega
  have hS1Vertex (q : Fin (S.length + 1)) :
      S1.vertex ⟨q.val, by omega⟩ = S.vertex q := by
    have hq : (⟨q.val, by omega⟩ : Fin (S1.length + 1)) =
        Fin.castLE (Nat.succ_le_succ hle1) q := by
      apply Fin.ext
      rfl
    rw [hq]
    exact hV1 q
  have hS1Edge (q : Fin S.length) :
      S1.edge ⟨q.val, by omega⟩ = S.edge q := by
    have hq : (⟨q.val, by omega⟩ : Fin S1.length) =
        Fin.castLE hle1 q := by
      apply Fin.ext
      rfl
    rw [hq]
    exact hE1 q
  have hS2Vertex (q : Fin (S1.length + 1)) :
      S2.vertex ⟨q.val, by omega⟩ = S1.vertex q := by
    have hq : (⟨q.val, by omega⟩ : Fin (S2.length + 1)) =
        Fin.castLE (Nat.succ_le_succ hle2) q := by
      apply Fin.ext
      rfl
    rw [hq]
    exact hV2 q
  have hS2Edge (q : Fin S1.length) :
      S2.edge ⟨q.val, by omega⟩ = S1.edge q := by
    have hq : (⟨q.val, by omega⟩ : Fin S2.length) =
        Fin.castLE hle2 q := by
      apply Fin.ext
      rfl
    rw [hq]
    exact hE2 q
  refine ⟨S2, hreplacementLength, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact @helper_branch_429 V E inferInstance inferInstance inferInstance G k e0 phi T C D d S
      hSlen rE hSE hreBefore S1 S2 hlen1 hlen2 hle1 hreplacementLength hS1Edge hS2Edge
  · exact @helper_branch_396 V E inferInstance inferInstance inferInstance G k e0 phi T C D d S
      hSlen rV hSV hrvBefore S1 S2 hlen1 hlen2 hle1 hreplacementLength hS1Vertex hS2Vertex
  · exact @helper_branch_447 V E inferInstance inferInstance inferInstance G k e0 phi T C D d S
      hSlen rE hSE hreAfter S1 S2 hlen1 hlen2 hle1 hreplacementLength hS1Edge hS2Edge
  · exact @helper_branch_460 V E inferInstance inferInstance inferInstance G k e0 phi T C D d S
      hSlen rV hSV hrvAfter S1 S2 hlen1 hlen2 hle1 hreplacementLength hS1Vertex hS2Vertex
  · exact @helper_branch_475 V E inferInstance inferInstance inferInstance G k e0 phi T C D d f1
      f2 S hSlen S1 S2 hlen1 hlastEdge1 hlen2 hlastEdge2 hreplacementLength hS2Edge
  · exact @helper_branch_493 V E inferInstance inferInstance inferInstance G k e0 phi T C D d u1
      u2 S hSlen S1 hlastVertex1 S2 hlastVertex2 hlen1 hlen2 hreplacementLength hS2Vertex
  · rw [hS2vertices, hS1vertices, hSvertices]
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  · exact @helper_branch_362 V E inferInstance inferInstance inferInstance G k e0 phi T C D d f1
      f2 S hSlen rE hSE hreBefore hreAfter S1 hS1edges S2 hS2edges hlen1 hlen2
end GoldbergSeymour

end
