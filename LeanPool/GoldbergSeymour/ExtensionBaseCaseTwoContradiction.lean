/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationBeforeVertex

public import LeanPool.GoldbergSeymour.SharedFacts.ExtensionBranches


public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport

public import LeanPool.GoldbergSeymour.TreeVerticesBeforeFacts

public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.OrderedTreeUnionExists
public import LeanPool.GoldbergSeymour.TashkinovClosureExists
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Extension Base Case Two Contradiction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hiSeed_234.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E} (Tj seed TjPrime :
        TreeSequence G e0) (zPosition : Fin (Tj.length + (1 : ℕ))) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤
        (↑zPosition : ℕ)) (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed U) (_ : TreeSequence G e0) (_ :
        TreeSequenceInitialSegment seed Z) (_ : ℕ) (i : Fin Z.length) (_ : Z.vertex i.succ ∉
        TreeSequenceVertexSet U), seed.length ≤ (↑i : ℕ) := by
  classical
  intro V E G e0 Tj seed TjPrime zPosition uPosition huPositionPositive huPositionBound
      hzPositionPositive hzPositionBound U Z hseedU M hseedZSegment n i hrightOutside
  by_contra hnot
  have hi : i.val < seed.length := Nat.lt_of_not_ge hnot
  let a : Fin (seed.length + 1) := ⟨i.val + 1, by omega⟩
  have hZSeedA : Z.vertex
        (Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a) =
      seed.vertex a := hseedZSegment.2.1 a
  apply hrightOutside
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) a, ?_⟩
  have hia : Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a =
      i.succ := Fin.ext (by simp [a])
  rw [hia] at hZSeedA
  exact (hseedU.2.1 a).trans hZSeedA.symm

private theorem helper_hseedZX_252.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E} (Tj seed : TreeSequence
        G e0) (zPosition : Fin (Tj.length + (1 : ℕ))) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition
        : ℕ)) (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed Z) (i : Fin Z.length) (hiSeed : seed.length ≤ (↑i : ℕ))
        (hiZ : (↑i : ℕ) < Z.length),
    let ZX : TreeSequence G e0 := TreeSequencePrefix Z (↑i : ℕ) (Nat.le_trans seed.positive
        hiSeed) (Nat.le_of_lt hiZ); TreeSequenceInitialSegment seed ZX := by
  classical
  intro V E G e0 Tj seed zPosition hzPositionPositive hzPositionBound Z hseedZSegment i hiSeed
      hiZ ZX
  refine ⟨hiSeed, ?_, ?_⟩
  · intro a
    change Z.vertex _ = seed.vertex a
    calc
      Z.vertex _ = Z.vertex
          (Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a) := by
        congr 1
      _ = seed.vertex a := hseedZSegment.2.1 a
  · intro a
    change Z.edge _ = seed.edge a
    calc
      Z.edge _ = Z.edge (Fin.castLE hseedZSegment.1 a) := by
        congr 1
      _ = seed.edge a := hseedZSegment.2.2 a

private theorem helper_hmissingX_305.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj seed TjPrime : TreeSequence G e0) (phiJ rho3 : PartialEdgeColoring E k)
        (terminalSupport u z : V) (hzTj : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin
        (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : Tj.vertex
        zPosition = z) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound :
        (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ))
        (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (_ : TreeSequenceInitialSegment seed U) (_ :
        MissingColors G phiJ terminalSupport ⊆ MissingColors G rho3 terminalSupport ∪
        MissingColors G rho3 u) (_ : (
    ∀ v ∈ TreeVerticesBefore Tj z hzTj, v ≠ terminalSupport → MissingColors G rho3 v =
        MissingColors G phiJ v)) (M : TreeSequence G e0) (_ : u ∈ TreeSequenceVertexSet U) (_ : (
    ∀ (i : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U),
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex
        i.succ)) (_ : (
    ∀ (i j : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U) (_ : Z.vertex j.succ ∉
        TreeSequenceVertexSet U) (_ : (↑i : ℕ) < (↑j : ℕ)) (p q : Fin M.length) (_ : M.vertex
        p.succ = Z.vertex i.succ) (_ : M.vertex q.succ = Z.vertex j.succ), (↑p : ℕ) < (↑q : ℕ)))
        (_ : TreeSequenceInitialSegment seed Z) (_ n : ℕ) (hnU : U.length ≤ n) (hnM : n + (1 : ℕ)
        ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let j : Fin M.length := (⟨n, Decidable.byContradiction fun (a : ¬n < M.length) ↦
    by omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Z.length) (_ : M.vertex j.succ = Z.vertex i.succ) (_ : Z.vertex i.succ ∉
        TreeSequenceVertexSet U) (hiSeed : seed.length ≤ (↑i : ℕ)) (hiZ : (↑i : ℕ) < Z.length),
    let ZX : TreeSequence G e0 := TreeSequencePrefix Z (↑i : ℕ) (Nat.le_trans seed.positive
        hiSeed) (Nat.le_of_lt hiZ);
    ∀ (_ : TreeSequenceInitialSegment ZX Z) (_ : ZX.length = (↑i : ℕ)) (A : TreeSequence G e0) (_
        : A.length = ZX.length + (1 : ℕ)),
    ∀ c ∈ TreeMissingColors phiJ ZX, (
    ∀ {v : V}, v ∈ TreeSequenceVertexSet U → v ∈ TreeSequenceVertexSet X) → c ∈ TreeMissingColors
        rho3 X := by
  classical
  intro V E _ _ G k e0 Tj seed TjPrime phiJ rho3 terminalSupport u z hzTj zPosition uPosition
      hzPosition huPositionPositive huPositionBound hzPositionPositive hzPositionBound U Z hZTj
      hseedU hterminalInclusion hbeforeZMissing M huU heveryNewRightEntry hrightOrder hseedZSegment
      n n hnU hnM hnM' X j i hvertexMZ hrightOutside hiSeed hiZ ZX hZXZ hZXlen A hlenA c hmissingZX
      hleftX
  let _ := Fintype.ofFinite V
  unfold TreeMissingColors at hmissingZX ⊢
  obtain ⟨v, hvZX, hcMissing⟩ :=
    Finset.mem_biUnion.mp hmissingZX
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hvZX
  obtain ⟨a, ha⟩ := hvZX
  have hcMissingV : c ∈ MissingColors G phiJ v := by
    simpa [ha] using hcMissing
  have hvX : v ∈ TreeSequenceVertexSet X := by
    by_cases hvU : v ∈ TreeSequenceVertexSet U
    · exact hleftX hvU
    · have haPos : 1 ≤ a.val := by
        by_contra hzero
        have haZero : a.val = 0 := by omega
        let p0 : Fin (seed.length + 1) := ⟨0, by omega⟩
        have hZp0 := hseedZSegment.2.1 p0
        have hUp0 := hseedU.2.1 p0
        apply hvU
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) p0, ?_⟩
        have haZ : Z.vertex (Fin.castLE
              (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a) = v := by
          simpa [ZX, TreeSequencePrefix] using ha
        have ha0 : Fin.castLE
              (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a =
            Fin.castLE (Nat.succ_le_succ hseedZSegment.1) p0 := by
          apply Fin.ext
          exact haZero
        rw [ha0, hZp0] at haZ
        exact hUp0.trans haZ
      let r : Fin Z.length := ⟨a.val - 1, by
        have haLt : a.val < ZX.length + 1 := a.isLt
        simp [ZX] at haLt
        omega⟩
      have hrSucc : r.succ = Fin.castLE
          (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a := by
        apply Fin.ext
        exact Nat.sub_add_cancel haPos
      have hrv : Z.vertex r.succ = v := by
        rw [hrSucc]
        simpa [ZX, TreeSequencePrefix] using ha
      have hrOutside :
          Z.vertex r.succ ∉ TreeSequenceVertexSet U := by
        simpa [hrv] using hvU
      have hri : r.val < i.val := by
        have haLt : a.val < ZX.length + 1 := a.isLt
        simp [ZX, r] at haLt ⊢
        omega
      obtain ⟨q, hqU, hedgeq, hvertexq⟩ :=
        heveryNewRightEntry r hrOutside
      have hqn : q.val < n :=
        hrightOrder r i hrOutside hrightOutside hri q j
          hvertexq hvertexMZ
      simp only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and]
      let qX : Fin (X.length + 1) := ⟨q.val + 1, by
        change q.val + 1 < n + 1
        omega⟩
      refine ⟨qX, ?_⟩
      rw [← hrv, ← hvertexq]
      change M.vertex _ = M.vertex q.succ
      congr 1
  by_cases hvTerminal : v = terminalSupport
  · have hcTerminalOld :
        c ∈ MissingColors G phiJ terminalSupport := by
      rw [← hvTerminal]
      exact hcMissingV
    rcases Finset.mem_union.mp (hterminalInclusion hcTerminalOld) with
      hcTerminal | hcU
    · have hterminalX :
          terminalSupport ∈ TreeSequenceVertexSet X := by
        simpa [hvTerminal] using hvX
      exact Finset.mem_biUnion.mpr
        ⟨terminalSupport, hterminalX, hcTerminal⟩
    · exact Finset.mem_biUnion.mpr ⟨u, hleftX huU, hcU⟩
  · have hvBefore : v ∈ TreeVerticesBefore Tj z hzTj := by
      unfold TreeVerticesBefore
      apply Finset.mem_filter.mpr
      let aZ : Fin (Z.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hZXZ.1) a
      let aTj : Fin (Tj.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hZTj.1) aZ
      have haTj : Tj.vertex aTj = v :=
        (hZTj.2.1 aZ).trans ((hZXZ.2.1 a).trans ha)
      constructor
      · simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨aTj, haTj⟩
      · unfold TreeVertexOrder
        refine ⟨aTj, zPosition, haTj, hzPosition, ?_⟩
        change a.val < zPosition.val
        have haLt := a.isLt
        have hiLt := i.isLt
        simp [ZX, Z, TreeSequencePrefix] at haLt hiLt
        omega
    refine Finset.mem_biUnion.mpr ⟨v, hvX, ?_⟩
    rw [hbeforeZMissing v hvBefore hvTerminal]
    exact hcMissingV

private theorem helper_hXY_405.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (phiJ rho1 rho3 : PartialEdgeColoring E k)
        (zPosition : Fin (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ :
        (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ)
        ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ)) (hzPositionBound :
        (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (M : TreeSequence G e0) (_ : (
    ∀ (A : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqA : q + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq (Nat.le_trans (Nat.le_succ q) hqA))
        (TreeSequencePrefix A (q + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ q + (1
        : ℕ)) ↦
    by omega
    ) hqA))) (_ n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤
        M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 := TreeSequencePrefix M (n + (1 : ℕ)) (Nat.le_trans U.positive
        (Nat.le_trans hnU (Nat.le_succ n))) hnSuccM;
    let j : Fin M.length := (⟨n, Decidable.byContradiction fun (a : ¬n < M.length) ↦
    by omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Z.length) (_ : M.edge j = Z.edge i) (c : Fin k) (_ : phiJ (Z.edge i) = some c) (_ :
        c ∈ TreeMissingColors rho3 X), TashkinovAugmentation rho3 X Y := by
  classical
  intro V E _ _ G k e0 Tj TjPrime phiJ rho1 rho3 zPosition uPosition hb2Edges hd2Edges
      huPositionPositive huPositionBound hzPositionPositive hzPositionBound U Z hZTj M prefixPrefix
      n n hnU hnM hnSuccM hnM' X Y j i hedgeMZ c hcolorZ hmissingX
  let _ := Fintype.ofFinite V
  have hlenXY : Y.length = X.length + 1 := by
    change n + 1 = n + 1
    rfl
  refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
  · simpa [X, Y] using prefixPrefix M n
      (Nat.le_trans U.positive hnU) hnSuccM
  · let iTj : Fin Tj.length := Fin.castLE hZTj.1 i
    have hiTj : iTj.val < zPosition.val := by
      change i.val < zPosition.val
      have hiLt := i.isLt
      simp only [TreeSequencePrefix, Nat.succ_eq_add_one, Z] at hiLt
      exact hiLt
    have hedgeTj : Tj.edge iTj = Z.edge i := hZTj.2.2 i
    have hfixedZ : rho3 (Z.edge i) = phiJ (Z.edge i) := by
      calc
        rho3 (Z.edge i) = rho1 (Z.edge i) :=
          hd2Edges (Z.edge i) (Or.inl ⟨iTj, hiTj, hedgeTj⟩)
        _ = phiJ (Z.edge i) := by
          rw [← hedgeTj]
          exact hb2Edges iTj
    have hcolorM : rho3 (M.edge j) = some c := by
      rw [hedgeMZ]
      exact hfixedZ.trans hcolorZ
    change rho3 (M.edge _) = some c
    convert hcolorM using 1
    apply congrArg rho3
    apply congrArg M.edge
    apply Fin.ext
    rfl

private theorem helper_branch_209.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj seed TjPrime : TreeSequence G e0) (phiJ rho1 rho3 : PartialEdgeColoring E k)
        (terminalSupport u z : V) (hzTj : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin
        (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : Tj.vertex
        zPosition = z) (_ : (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ)
        ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ)) (hzPositionBound :
        (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (_ : TreeSequenceInitialSegment seed U) (_ :
        MissingColors G phiJ terminalSupport ⊆ MissingColors G rho3 terminalSupport ∪
        MissingColors G rho3 u) (_ : (
    ∀ v ∈ TreeVerticesBefore Tj z hzTj, v ≠ terminalSupport → MissingColors G rho3 v =
        MissingColors G phiJ v)) (M : TreeSequence G e0) (_ : u ∈ TreeSequenceVertexSet U) (_ :
        TashkinovAugmentationSequence phiJ seed Z) (_ : TreeSequenceInitialSegment U M) (_ : (
    ∀ (j : Fin M.length) (_ : U.length ≤ (↑j : ℕ)),
    ∃ (i : Fin Z.length), M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex i.succ)) (_ : (
    ∀ (i : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U),
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex
        i.succ)) (_ : (
    ∀ (i j : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U) (_ : Z.vertex j.succ ∉
        TreeSequenceVertexSet U) (_ : (↑i : ℕ) < (↑j : ℕ)) (p q : Fin M.length) (_ : M.vertex
        p.succ = Z.vertex i.succ) (_ : M.vertex q.succ = Z.vertex j.succ), (↑p : ℕ) < (↑q : ℕ)))
        (_ : (
    ∀ (A : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqA : q ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq hqA) A)) (_ : (
    ∀ (A : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqA : q + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq (Nat.le_trans (Nat.le_succ q) hqA))
        (TreeSequencePrefix A (q + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ q + (1
        : ℕ)) ↦
    by omega
    ) hqA))) (_ : TreeSequenceInitialSegment seed Z) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TashkinovAugmentationSequence phiJ A B) (_ : A.length <
        B.length),
    ∃ (C : TreeSequence G e0), TashkinovAugmentation phiJ A C ∧ TashkinovAugmentationSequence phiJ
        C B)) (_ n : ℕ) (hnU : U.length ≤ n) (_ : (
    ∀ (hnM : n ≤ M.length), TashkinovAugmentationSequence rho3 U (TreeSequencePrefix M n
        (Nat.le_trans U.positive hnU) hnM))) (hnM : n + (1 : ℕ) ≤ M.length),
        TashkinovAugmentationSequence rho3 U (TreeSequencePrefix M (n + (1 : ℕ)) (Nat.le_trans
        U.positive (Nat.le_succ_of_le hnU)) hnM) := by
  classical
  intro V E _ _ G k e0 Tj seed TjPrime phiJ rho1 rho3 terminalSupport u z hzTj zPosition uPosition
      hzPosition hb2Edges hd2Edges huPositionPositive huPositionBound hzPositionPositive
      hzPositionBound U Z hZTj hseedU hterminalInclusion hbeforeZMissing M huU hroutePhiZ
      hleftSegment hnewEntryFromRight heveryNewRightEntry hrightOrder prefixSegment prefixPrefix
      hseedZSegment firstStep n n hnU ih hnM
  let _ := Fintype.ofFinite V
  by_cases hnEq : n = M.length
  · omega
  have hnSuccM : n + 1 ≤ M.length := by omega
  have hnM' : n ≤ M.length := Nat.le_trans (Nat.le_succ n) hnSuccM
  have ih' := ih hnM'
  let X := TreeSequencePrefix M n
    (Nat.le_trans U.positive hnU) hnM'
  let Y := TreeSequencePrefix M (n + 1)
    (Nat.le_trans U.positive (Nat.le_trans hnU (Nat.le_succ n)))
    hnSuccM
  let j : Fin M.length := ⟨n, by omega⟩
  obtain ⟨i, hedgeMZ, hvertexMZ⟩ := hnewEntryFromRight j hnU
  have hrightOutside : Z.vertex i.succ ∉ TreeSequenceVertexSet U := by
    rw [← hvertexMZ]
    exact hleftSegment.vertex_not_mem_after (by change U.length < n + 1; omega)
  have hiSeed := @helper_hiSeed_234 V E G e0 Tj seed TjPrime zPosition uPosition huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound hseedU M hseedZSegment n i hrightOutside
  have hiZ : i.val < Z.length := i.isLt
  let ZX := TreeSequencePrefix Z i.val
    (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiZ)
  have hseedZX := @helper_hseedZX_252 V E G e0 Tj seed zPosition hzPositionPositive hzPositionBound
      hseedZSegment i hiSeed hiZ
  have hZXZ : TreeSequenceInitialSegment ZX Z :=
    prefixSegment Z i.val (Nat.le_trans seed.positive hiSeed)
      (Nat.le_of_lt hiZ)
  have hsuffix : TashkinovAugmentationSequence phiJ ZX Z :=
    TashkinovAugmentationSequenceSuffix phiJ seed ZX Z
      hroutePhiZ hseedZX hZXZ
  have hZXlen : ZX.length = i.val := rfl
  obtain ⟨A, hZXA, hAZ⟩ := firstStep hsuffix (by omega)
  rcases hZXA with ⟨hlenA, hZXASegment, c, hcolorA, hmissingZX⟩
  have hAZSegment : TreeSequenceInitialSegment A Z :=
    TashkinovAugmentationSequenceInitialSegment phiJ A Z hAZ
  have hAi : A.length = i.val + 1 := by omega
  let ai : Fin A.length := ⟨i.val, by omega⟩
  have hcolorZ : phiJ (Z.edge i) = some c := by
    have haiLast : ai =
        Fin.cast hlenA.symm (Fin.last ZX.length) := by
      apply Fin.ext
      simp [ai, hZXlen]
    have hZai : Z.edge (Fin.castLE hAZSegment.1 ai) = A.edge ai :=
      hAZSegment.2.2 ai
    have hcast : Fin.castLE hAZSegment.1 ai = i := by
      apply Fin.ext
      simp [ai]
    rw [← hcast, hZai, haiLast]
    exact hcolorA
  have hleftX {v : V} (hvU : v ∈ TreeSequenceVertexSet U) :
      v ∈ TreeSequenceVertexSet X := by
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hvU ⊢
    obtain ⟨b, hb⟩ := hvU
    refine ⟨Fin.castLE (Nat.succ_le_succ hnU) b, ?_⟩
    change M.vertex _ = v
    calc
      M.vertex _ = M.vertex
          (Fin.castLE (Nat.succ_le_succ hleftSegment.1) b) := by
        congr 1
      _ = U.vertex b := hleftSegment.2.1 b
      _ = v := hb
  have hmissingX := @helper_hmissingX_305 V E inferInstance inferInstance G k e0 Tj seed TjPrime
      phiJ rho3 terminalSupport u z hzTj zPosition uPosition hzPosition huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound hZTj hseedU hterminalInclusion
      hbeforeZMissing M huU heveryNewRightEntry hrightOrder hseedZSegment n n hnU hnM hnM' i
      hvertexMZ hrightOutside hiSeed hiZ hZXZ hZXlen A hlenA c hmissingZX hleftX
  have hXY := @helper_hXY_405 V E inferInstance inferInstance G k e0 Tj TjPrime phiJ rho1 rho3
      zPosition uPosition hb2Edges hd2Edges huPositionPositive huPositionBound hzPositionPositive
      hzPositionBound hZTj M prefixPrefix n n hnU hnM hnSuccM hnM' i hedgeMZ c hcolorZ hmissingX
  change TashkinovAugmentationSequence rho3 U Y
  exact Relation.ReflTransGen.tail ih' hXY

private theorem helper_replay_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj seed TjPrime : TreeSequence G e0) (phiJ rho1 rho3 : PartialEdgeColoring E k)
        (terminalSupport u z : V) (hzTj : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin
        (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : Tj.vertex
        zPosition = z) (_ : (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ)
        ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ)) (hzPositionBound :
        (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (_ : TreeSequenceInitialSegment seed U) (_ :
        MissingColors G phiJ terminalSupport ⊆ MissingColors G rho3 terminalSupport ∪
        MissingColors G rho3 u) (_ : (
    ∀ v ∈ TreeVerticesBefore Tj z hzTj, v ≠ terminalSupport → MissingColors G rho3 v =
        MissingColors G phiJ v)) (M : TreeSequence G e0) (_ : u ∈ TreeSequenceVertexSet U) (_ :
        TashkinovAugmentationSequence phiJ seed Z) (hleftSegment : TreeSequenceInitialSegment U M)
        (_ : (
    ∀ (j : Fin M.length) (_ : U.length ≤ (↑j : ℕ)),
    ∃ (i : Fin Z.length), M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex i.succ)) (_ : (
    ∀ (i : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U),
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex
        i.succ)) (_ : (
    ∀ (i j : Fin Z.length) (_ : Z.vertex i.succ ∉ TreeSequenceVertexSet U) (_ : Z.vertex j.succ ∉
        TreeSequenceVertexSet U) (_ : (↑i : ℕ) < (↑j : ℕ)) (p q : Fin M.length) (_ : M.vertex
        p.succ = Z.vertex i.succ) (_ : M.vertex q.succ = Z.vertex j.succ), (↑p : ℕ) < (↑q : ℕ)))
        (_ : (
    ∀ (A : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqA : q ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq hqA) A)) (_ : (
    ∀ (A : TreeSequence G e0) (q : ℕ) (hq : (1 : ℕ) ≤ q) (hqA : q + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q hq (Nat.le_trans (Nat.le_succ q) hqA))
        (TreeSequencePrefix A (q + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ q + (1
        : ℕ)) ↦
    by omega
    ) hqA))) (_ : TreeSequencePrefix M U.length U.positive hleftSegment.1 = U) (_ :
        TreeSequenceInitialSegment seed Z) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TashkinovAugmentationSequence phiJ A B) (_ : A.length <
        B.length),
    ∃ (C : TreeSequence G e0), TashkinovAugmentation phiJ A C ∧ TashkinovAugmentationSequence phiJ
        C B)) (n : ℕ) (hnU : U.length ≤ n) (hnM : n ≤ M.length), TashkinovAugmentationSequence
        rho3 U (TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM) := by
  classical
  intro V E _ _ G k e0 Tj seed TjPrime phiJ rho1 rho3 terminalSupport u z hzTj zPosition uPosition
      hzPosition hb2Edges hd2Edges huPositionPositive huPositionBound hzPositionPositive
      hzPositionBound U Z hZTj hseedU hterminalInclusion hbeforeZMissing M huU hroutePhiZ
      hleftSegment hnewEntryFromRight heveryNewRightEntry hrightOrder prefixSegment prefixPrefix
      prefixAtLeft hseedZSegment firstStep n hnU hnM
  let _ := Fintype.ofFinite V
  induction n, hnU using Nat.le_induction with
  | base =>
      simpa [prefixAtLeft] using
        (show TashkinovAugmentationSequence rho3 U U from
          Relation.ReflTransGen.refl)
  | @succ n hnU ih =>
      exact @helper_branch_209 V E inferInstance inferInstance G k e0 Tj seed
          TjPrime phiJ rho1 rho3 terminalSupport u z hzTj zPosition uPosition hzPosition hb2Edges
          hd2Edges huPositionPositive huPositionBound hzPositionPositive hzPositionBound hZTj
          hseedU hterminalInclusion hbeforeZMissing M huU hroutePhiZ hleftSegment
          hnewEntryFromRight heveryNewRightEntry hrightOrder prefixSegment prefixPrefix
          hseedZSegment firstStep n n hnU ih hnM
private theorem helper_hrouteUM_530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) {lowerInput : PartialEdgeColoring E k}
        {lowerTree : TreeSequence G e0} {lowerGenerating : PartialEdgeColoring E k} (_ :
        ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating) (_ : Fin ett.rounds)
        (Tj seed TjPrime : TreeSequence G e0) (phiJ rho1 rho3 : PartialEdgeColoring E k)
        (terminalSupport u z : V) (hzTj : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin
        (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : Tj.vertex
        zPosition = z) (_ : TashkinovAugmentationSequence phiJ seed Tj) (_ : (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ)
        ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ)) (hzPositionBound :
        (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (_ : TreeSequenceInitialSegment seed U) (_ :
        TreeSequenceInitialSegment seed Z) (_ : MissingColors G phiJ terminalSupport ⊆
        MissingColors G rho3 terminalSupport ∪ MissingColors G rho3 u) (_ : (
    ∀ v ∈ TreeVerticesBefore Tj z hzTj, v ≠ terminalSupport → MissingColors G rho3 v =
        MissingColors G phiJ v)) (M : TreeSequence G e0) (_ : OrderedTreeUnion U Z M) (_ : u ∈
        TreeSequenceVertexSet U), TashkinovAugmentationSequence rho3 U M := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower
      jSlot Tj seed TjPrime phiJ rho1 rho3 terminalSupport u z hzTj zPosition uPosition
      hzPosition hTjAugmentation hb2Edges hd2Edges huPositionPositive huPositionBound
      hzPositionPositive hzPositionBound U Z hZTj hseedU hseedZ hterminalInclusion
      hbeforeZMissing M hunion huU
  have hroutePhiZ : TashkinovAugmentationSequence phiJ seed Z :=
    TashkinovAugmentationSequenceRestrict phiJ seed Z Tj
      hTjAugmentation hseedZ hZTj
  have hleftSegment := hunion.leftSegment
  have hnewEntryFromRight := hunion.newEntryFromRight
  have heveryNewRightEntry := hunion.everyNewRightEntry
  have hrightOrder := hunion.rightOrder
  have prefixSegment (A : TreeSequence G e0) (q : Nat)
      (hq : 1 ≤ q) (hqA : q ≤ A.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix A q hq hqA) A := by
    exact TreeSequenceInitialSegment.prefix_segment A q hq hqA
  have prefixPrefix (A : TreeSequence G e0) (q : Nat)
      (hq : 1 ≤ q) (hqA : q + 1 ≤ A.length) :
      TreeSequenceInitialSegment
        (TreeSequencePrefix A q hq (Nat.le_trans (Nat.le_succ q) hqA))
        (TreeSequencePrefix A (q + 1) (by omega) hqA) := by
    exact TreeSequenceInitialSegment.prefix_prefix A q (q + 1) hq (by omega)
      (Nat.le_trans (Nat.le_succ q) hqA) hqA (Nat.le_succ q)
  have prefixSelf (A : TreeSequence G e0) :
      TreeSequencePrefix A A.length A.positive le_rfl = A := by
    exact TreeSequenceInitialSegment.prefix_self A
  have equalPrefixes := @SharedFacts.ExtensionBranches.equalPrefixes V E G e0
  have prefixAtLeft :
      TreeSequencePrefix M U.length U.positive hleftSegment.1 = U := by
    apply equalPrefixes
      (prefixSegment M U.length U.positive hleftSegment.1)
      hleftSegment
    rfl
  have hseedZSegment : TreeSequenceInitialSegment seed Z :=
    TashkinovAugmentationSequenceInitialSegment phiJ seed Z hroutePhiZ
  have firstStep {A B : TreeSequence G e0}
      (hAB : TashkinovAugmentationSequence phiJ A B)
      (hlt : A.length < B.length) :
      ∃ C, TashkinovAugmentation phiJ A C ∧
        TashkinovAugmentationSequence phiJ C B := by
    unfold TashkinovAugmentationSequence at hAB ⊢
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => omega
    | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
  have replay := @helper_replay_227 V E inferInstance inferInstance G k e0 Tj seed TjPrime phiJ rho1
      rho3 terminalSupport u z hzTj zPosition uPosition hzPosition hb2Edges hd2Edges
      huPositionPositive huPositionBound hzPositionPositive hzPositionBound hZTj hseedU
      hterminalInclusion hbeforeZMissing M huU hroutePhiZ hleftSegment hnewEntryFromRight
      heveryNewRightEntry hrightOrder prefixSegment prefixPrefix prefixAtLeft hseedZSegment
      firstStep
  have hfull := replay M.length hleftSegment.1 le_rfl
  simpa [prefixSelf] using hfull

private theorem helper_hbound_937.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) {lowerInput : PartialEdgeColoring E k}
    {lowerTree : TreeSequence G e0} {lowerGenerating : PartialEdgeColoring E k} (lower :
    ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating) (jSlot : Fin
    ett.rounds), (1 : ℕ) ≤ (↑jSlot : ℕ) → ∀ (Tjm1 Tj seed TjPrime : TreeSequence G e0) (rho3 :
    PartialEdgeColoring E k) (_ : Fin (Tj.length + (1 : ℕ))) (_ : Fin (TjPrime.length + (1 :
    ℕ))), ett.series.data.tree jSlot.castSucc.castSucc = Tjm1 → ett.series.data.tree
    jSlot.succ.castSucc = Tj → lower.rounds = (↑jSlot : ℕ) → MaximumProperty ett →
    IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 → (ett.series.data.kind
    jSlot.castSucc = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence rho3 Tjm1
    seed ∨ (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.SE ∨
    ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.RE) ∧ ∃ (f : E)
    (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
    TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧ TashkinovAugmentationSequence rho3 adjoinSeed
    seed) → ∀ (C : TreeSequence G e0), TashkinovAugmentationSequence rho3 seed C →
    ColoredVertexSetClosed G rho3 (TreeSequenceVertexSet C) → StableColoring
    (ett.series.data.tree jSlot.castSucc.castSucc) (TashkinovStoredColors ett.series.data
    jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho3 → (TreeSequenceVertexSet
    C).card ≤ (TreeSequenceVertexSet Tj).card := by
  classical
  intro V E _ _ _ G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower jSlot
      hjPositive Tjm1 Tj seed TjPrime rho3 zPosition uPosition hTjm1Stored hTjStored hLowerRounds
      hMP hrhoProper hrhoOne hseedBuildRho C hrouteSeedC hclosedC hstableAtSlot
  have hMP' := hMP
  unfold MaximumProperty at hMP'
  have hstage := hMP'.2 jSlot.val hjPositive jSlot.isLt
  dsimp only at hstage
  have hidx : (⟨jSlot.val, by omega⟩ : Fin (ett.rounds + 1)) =
      jSlot.castSucc := by
    apply Fin.ext
    rfl
  have hnextIdx : (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
      jSlot.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx, hnextIdx] at hstage
  rcases hseedBuildRho with hparallel | hserial
  · have hclosureTjm1C : TashkinovClosure rho3 Tjm1 C :=
      ⟨Relation.ReflTransGen.trans hparallel.2 hrouteSeedC, hclosedC⟩
    have hraw := hstage rho3 Tjm1 C
      hrhoProper hrhoOne
      hstableAtSlot
      (by
        left
        refine ⟨?_, ?_⟩
        · exact hparallel.1
        · exact hTjm1Stored.symm)
      hclosureTjm1C
    simpa only [hTjStored] using hraw
  · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
        hadjoin, hroute⟩
    have hclosureAdjoinC : TashkinovClosure rho3 adjoinSeed C :=
      ⟨Relation.ReflTransGen.trans hroute hrouteSeedC, hclosedC⟩
    have hraw := hstage rho3 adjoinSeed C
      hrhoProper hrhoOne
      hstableAtSlot
      (by
        right
        refine ⟨?_, f, ?_, ?_⟩
        · exact hkind
        · exact hconnecting
        · rw [hTjm1Stored]
          exact hadjoin)
      hclosureAdjoinC
    simpa only [hTjStored] using hraw

private theorem helper_branch_1101.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) {lowerInput : PartialEdgeColoring E k}
        {lowerTree : TreeSequence G e0} {lowerGenerating : PartialEdgeColoring E k} (_ :
        ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating) (_ : Fin ett.rounds) (_
        Tj _ TjPrime : TreeSequence G e0) (u : V) (zPosition : Fin (Tj.length + (1 : ℕ))) (_ : Fin
        (TjPrime.length + (1 : ℕ))) (_ : u ∉ TreeSequenceVertexSet Tj) (hzPositionPositive : (1 :
        ℕ) ≤ (↑zPosition : ℕ)) (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (C : TreeSequence G e0) (_ : u ∈ TreeSequenceVertexSet
        C) (_ : (TreeSequenceVertexSet C).card ≤ (TreeSequenceVertexSet Tj).card) (_ :
        TreeSequenceVertexSet Z ⊆ TreeSequenceVertexSet C) (_ : zPosition = Fin.last Tj.length),
        False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower jSlot
      Tjm1 Tj seed TjPrime u zPosition uPosition huOutsideTj hzPositionPositive hzPositionBound Z
      hZTj C huC hbound hZC hzLast
  have hZlen : Z.length = Tj.length := by
    simp [Z, TreeSequencePrefix, hzLast]
  have hTjZ : TreeSequenceVertexSet Tj ⊆ TreeSequenceVertexSet Z := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    let iZ : Fin (Z.length + 1) := ⟨i.val, by omega⟩
    refine ⟨iZ, ?_⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hZTj.1) iZ = i := by
      apply Fin.ext
      rfl
    rw [← hcast]
    exact hZTj.2.1 iZ
  have hTjC : TreeSequenceVertexSet Tj ⊆ TreeSequenceVertexSet C :=
    fun _ hv => hZC (hTjZ hv)
  have hstrict : TreeSequenceVertexSet Tj < TreeSequenceVertexSet C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hTjC, by
      intro heq
      exact huOutsideTj (heq.symm.subset huC)⟩
  exact (Nat.not_lt_of_ge hbound) (Finset.card_lt_card hstrict)

private theorem helper_hstableLower_821.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G :
    LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tjm1 Tj : TreeSequence G e0) (phiJ rho3 :
    PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (terminalSupport : V) (hterminalTj :
    terminalSupport ∈ TreeSequenceVertexSet Tj), TreeSequenceVertexSet Tjm1 ⊆
    TreeVerticesBefore Tj terminalSupport hterminalTj → StableColoringBeforeVertex Tj
    terminalSupport hterminalTj Dprev phiJ rho3 → StableColoring Tjm1 Dprev phiJ rho3 := by
  classical
  intro V E _ _ G k e0 Tjm1 Tj phiJ rho3 Dprev terminalSupport hterminalTj hTjm1Before hd1
  let _ := Fintype.ofFinite V
  unfold StableColoring
  constructor
  · intro f hfIncident hfControlled
    obtain ⟨v, hvTjm1, hvf⟩ := hfIncident
    have hvBefore : v ∈ TreeVerticesBefore Tj terminalSupport hterminalTj :=
      hTjm1Before hvTjm1
    apply hd1.1 f ⟨v, hvBefore, hvf⟩
    obtain ⟨c, hcControlled, hfc⟩ := hfControlled
    refine ⟨c, ?_, hfc⟩
    rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
    · apply Finset.mem_union_left
      unfold TreeMissingColors at hcMissing
      obtain ⟨w, hwTjm1, hcw⟩ := Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨w, hTjm1Before hwTjm1, hcw⟩
    · exact Finset.mem_union_right _ hcStored
  · intro v hvTjm1
    exact hd1.2 v (hTjm1Before hvTjm1)

private theorem helper_commonPrefix_864.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0
    : E} {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C →
    TreeSequenceInitialSegment B C → A.length ≤ B.length → TreeSequenceInitialSegment A B := by
  classical
  intro V E G e0 A B C hAC hBC hlen
  rcases hAC with ⟨hlenAC, hvertexAC, hedgeAC⟩
  rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    calc
      B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
          C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
            (Fin.castLE (Nat.succ_le_succ hlen) i)) :=
        (hvertexBC _).symm
      _ = C.vertex (Fin.castLE (Nat.succ_le_succ hlenAC) i) := by
        congr 1
      _ = A.vertex i := hvertexAC i
  · intro i
    calc
      B.edge (Fin.castLE hlen i) =
          C.edge (Fin.castLE hlenBC (Fin.castLE hlen i)) :=
        (hedgeBC _).symm
      _ = C.edge (Fin.castLE hlenAC i) := by congr 1
      _ = A.edge i := hedgeAC i

private theorem helper_hseedVertexBefore_888.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] {G :
    LooplessMultigraph V E} {e0 : E} (Tj seed : TreeSequence G e0) (terminalSupport : V)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj), TreeSequenceInitialSegment
    seed Tj → seed.vertex (Fin.last seed.length) = terminalSupport → ∀ (i : Fin (seed.length +
    (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈ TreeVerticesBefore Tj terminalSupport
    hterminalTj := by
  classical
  intro V E _ G e0 Tj seed terminalSupport hterminalTj hseedJ hseedTerminal i hi
  let _ := Fintype.ofFinite V
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  constructor
  · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨Fin.castLE (Nat.succ_le_succ hseedJ.1) i,
      hseedJ.2.1 i⟩
  · unfold TreeVertexOrder
    let p : Fin (Tj.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedJ.1) i
    let q : Fin (Tj.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedJ.1) (Fin.last seed.length)
    refine ⟨p, q, ?_, ?_, ?_⟩
    · exact hseedJ.2.1 i
    · exact (hseedJ.2.1 (Fin.last seed.length)).trans hseedTerminal
    · simpa [p, q] using hi

private theorem helper_hbeforeZMissing_1101.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
    [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tj TjPrime : TreeSequence G
    e0) (phiJ rho1 rho3 : PartialEdgeColoring E k) (terminalSupport u z : V) (huPrime : u ∈
    TreeSequenceVertexSet TjPrime) (hzTj : z ∈ TreeSequenceVertexSet Tj), u ∉
    TreeSequenceVertexSet Tj → (∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport,
    MissingColors G rho1 v = MissingColors G phiJ v) → (∀ v ∈ ((TreeVerticesBefore Tj z hzTj ∪
    {z} ∪ (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z, MissingColors G rho3
    v = MissingColors G rho1 v) → (∀ {v : V}, v ∈ TreeVerticesBefore Tj z hzTj → v ∈
    TreeSequenceVertexSet Tj ∧ v ≠ z) → ∀ v ∈ TreeVerticesBefore Tj z hzTj, v ≠
    terminalSupport → MissingColors G rho3 v = MissingColors G phiJ v := by
  classical
  intro V E _ _ _ G k e0 Tj TjPrime phiJ rho1 rho3 terminalSupport u z huPrime hzTj huOutsideTj
      hb2Missing hd2Missing hbeforeZData v hv hvTerminal
  let _ := Fintype.ofFinite V
  have hvData := hbeforeZData hv
  have hvU : v ≠ u := by
    intro hvu
    subst v
    exact huOutsideTj hvData.1
  have hRhoThreeOne :
      MissingColors G rho3 v = MissingColors G rho1 v := by
    apply hd2Missing v
    apply Finset.mem_erase.mpr
    refine ⟨hvData.2, Finset.mem_erase.mpr ⟨hvU, ?_⟩⟩
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ hv
  exact hRhoThreeOne.trans
    (hb2Missing v (Finset.mem_erase.mpr ⟨hvTerminal, hvData.1⟩))

private theorem helper_continuation_1296.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) {lowerInput : PartialEdgeColoring E k}
        {lowerTree : TreeSequence G e0} {lowerGenerating : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating) (jSlot : Fin
        ett.rounds) (_ : (1 : ℕ) ≤ (↑jSlot : ℕ)) (Tjm1 Tj seed TjPrime : TreeSequence G e0) (phiJ
        rho1 rho3 : PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (terminalSupport u z : V)
        (beta deltaN : Fin k) (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj) (huPrime
        : u ∈ TreeSequenceVertexSet TjPrime) (hzTj : z ∈ TreeSequenceVertexSet Tj) (zPosition :
        Fin (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : Tj.vertex
        zPosition = z) (_ : TjPrime.vertex uPosition = u) (_ : seed.vertex (Fin.last seed.length)
        = terminalSupport) (_ : u ∉ TreeSequenceVertexSet Tj) (_ : ett.series.data.tree
        jSlot.castSucc.castSucc = Tjm1) (_ : ett.series.data.coloring jSlot.castSucc = phiJ) (_ :
        ett.series.data.tree jSlot.succ.castSucc = Tj) (_ : TashkinovStoredColors ett.series.data
        jSlot.castSucc = Dprev) (_ : lower.rounds = (↑jSlot : ℕ)) (_ : lower.series.data.tree
        (Fin.last lower.rounds).castSucc = Tjm1) (_ : lower.series.data.kind (Fin.last
        lower.rounds) = ett.series.data.kind jSlot.castSucc) (_ :
        lower.series.data.connectingEdges (Fin.last lower.rounds) =
        ett.series.data.connectingEdges jSlot.castSucc) (_ : TreeSequenceVertexSet Tjm1 ⊆
        TreeVerticesBefore Tj terminalSupport hterminalTj) (_ : TashkinovAugmentationSequence phiJ
        seed Tj) (_ : MaximumProperty ett) (_ : MaximumProperty lower) (_ : (
    ∀ (Tstar : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3
        Tstar) (_ : MaximumProperty corr.replacementETT), ColoredVertexSetElementary G rho3
        (TreeSequenceVertexSet Tstar))) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport, MissingColors G rho1 v = MissingColors
        G phiJ v)) (_ : (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : deltaN ∈ MissingColors G
        rho1 terminalSupport) (_ : IsProperEdgeColoring G rho3) (_ : IsOneEdgeUncolored rho3 e0)
        (_ : (
    ∀ v ∈ ((TreeVerticesBefore Tj z hzTj ∪ { z } ∪ (TreeVerticesBefore TjPrime u huPrime ∪
        { u })).erase u).erase z, MissingColors G rho3 v = MissingColors G rho1 v)) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (_ : (
    ∀ (_ : beta ∈ MissingColors G rho1 z), deltaN ∈ MissingColors G rho3 z)) (_ : zPosition =
        Fin.last Tj.length ∨ (↑zPosition : ℕ) < (↑(Fin.last Tj.length) : ℕ) ∧ beta ∈ MissingColors
        G rho1 z) (_ : StableColoring Tjm1 Dprev phiJ rho3) (_ : ModColoring lower rho3) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ :
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tjm1 seed ∨ (ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        { f } ∧ TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧ TashkinovAugmentationSequence rho3
        adjoinSeed seed)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound :
        (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ))
        (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z Tj) (_ : TreeSequenceInitialSegment seed U) (_ :
        TreeSequenceInitialSegment seed Z) (_ : TashkinovAugmentationSequence rho3 seed U) (_ :
        terminalSupport ≠ z) (_ : MissingColors G rho3 terminalSupport = MissingColors G rho1
        terminalSupport) (_ : MissingColors G phiJ terminalSupport ⊆ MissingColors G rho3
        terminalSupport ∪ MissingColors G rho3 u) (_ : (
    ∀ {v : V} (_ : v ∈ TreeVerticesBefore Tj z hzTj), v ∈ TreeSequenceVertexSet Tj ∧ v ≠ z)),
        False := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower
      jSlot hjPositive Tjm1 Tj seed TjPrime phiJ rho1 rho3 Dprev terminalSupport u z beta deltaN
      hterminalTj huPrime hzTj zPosition uPosition hzPosition huPosition hseedTerminal
      huOutsideTj hTjm1Stored hPhiJStored hTjStored hDprevStored hLowerRounds hLowerTree
      hLowerKind hLowerConnecting hTjm1Before hTjAugmentation hMP hLowerMP hLowerI hb2Missing
      hb2Edges hdeltaRho1 hrhoProper hrhoOne hd2Missing hd2Edges hd2Delta hzChoice hstableLower
      hmod segmentTrans hseedBuildRho huPositionPositive huPositionBound hzPositionPositive
      hzPositionBound U Z hZTj hseedU hseedZ hrouteRhoThreeU hterminalNeZ hterminalMissingEq
      hterminalInclusion hbeforeZData
  have hbeforeZMissing := @helper_hbeforeZMissing_1101 V E inferInstance inferInstance inferInstance
      G k e0 Tj TjPrime phiJ rho1 rho3 terminalSupport u z huPrime hzTj huOutsideTj hb2Missing
      hd2Missing hbeforeZData
  obtain ⟨M, ⟨hunion⟩⟩ := OrderedTreeUnionExists U Z
  have huU : u ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨Fin.last U.length, ?_⟩
    change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
      (Fin.last uPosition.val)) = u
    have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
        (Fin.last uPosition.val) = uPosition := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact huPosition
  have hrouteUM := @helper_hrouteUM_530 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower jSlot Tj seed TjPrime
      phiJ rho1 rho3 terminalSupport u z hzTj zPosition uPosition hzPosition hTjAugmentation
      hb2Edges hd2Edges huPositionPositive huPositionBound hzPositionPositive hzPositionBound hZTj
      hseedU hseedZ hterminalInclusion hbeforeZMissing M hunion huU
  obtain ⟨C, hclosureMC⟩ := TashkinovClosureExists rho3 M
  have hrouteUC : TashkinovAugmentationSequence rho3 U C :=
    Relation.ReflTransGen.trans hrouteUM hclosureMC.1
  have hrouteSeedC : TashkinovAugmentationSequence rho3 seed C :=
    Relation.ReflTransGen.trans hrouteRhoThreeU hrouteUC
  have hclosedC :
      ColoredVertexSetClosed G rho3 (TreeSequenceVertexSet C) :=
    hclosureMC.2
  have huM : u ∈ TreeSequenceVertexSet M := by
    rw [hunion.vertexSet]
    exact Finset.mem_union_left _ huU
  have hMCsegment : TreeSequenceInitialSegment M C :=
    TashkinovAugmentationSequenceInitialSegment rho3 M C hclosureMC.1
  have huC : u ∈ TreeSequenceVertexSet C :=
    TreeSequenceInitialSegmentVertexSetSubset hMCsegment huM
  have huNotTjm1 : u ∉ TreeSequenceVertexSet Tjm1 := by
    intro huLower
    exact huOutsideTj (Finset.mem_filter.mp (hTjm1Before huLower)).1
  have hTjm1C : TreeSequenceInitialSegment Tjm1 C := by
    rcases hseedBuildRho with hparallel | hserial
    · exact TashkinovAugmentationSequenceInitialSegment rho3 Tjm1 C
        (Relation.ReflTransGen.trans hparallel.2 hrouteSeedC)
    · rcases hserial with ⟨-, f, adjoinSeed, -, hadjoin, hroute⟩
      exact segmentTrans hadjoin.2.1
        (TashkinovAugmentationSequenceInitialSegment rho3 adjoinSeed C
          (Relation.ReflTransGen.trans hroute hrouteSeedC))
  have hTjm1StrictC : Tjm1.length < C.length := by
    have hsubset : TreeSequenceVertexSet Tjm1 ⊆ TreeSequenceVertexSet C :=
      TreeSequenceInitialSegmentVertexSetSubset hTjm1C
    have hstrictSet : TreeSequenceVertexSet Tjm1 < TreeSequenceVertexSet C :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
        intro heq
        exact huNotTjm1 (heq.symm.subset huC)⟩
    have hcard := Finset.card_lt_card hstrictSet
    simpa [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Tjm1.vertex_injective, C.vertex_injective] using hcard
  have hLowerEligible :
      ((lower.series.data.kind (Fin.last lower.rounds) =
            some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence rho3 Tjm1 C) ∨
        ((lower.series.data.kind (Fin.last lower.rounds) =
              some TashkinovExtensionKind.SE ∨
            lower.series.data.kind (Fin.last lower.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (adjoinSeed : TreeSequence G e0),
            lower.series.data.connectingEdges (Fin.last lower.rounds) = {f} ∧
              TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
              TashkinovAugmentationSequence rho3 adjoinSeed C)) := by
    rcases hseedBuildRho with hparallel | hserial
    · exact Or.inl ⟨hLowerKind.trans hparallel.1,
        Relation.ReflTransGen.trans hparallel.2 hrouteSeedC⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨Or.imp (hLowerKind.trans) (hLowerKind.trans) hkind,
        f, adjoinSeed, hLowerConnecting.trans hconnecting, hadjoin,
        Relation.ReflTransGen.trans hroute hrouteSeedC⟩
  have hcorrNonempty :
      Nonempty (CorrespondingExtendedTashkinovTree G k e0 lower rho3 C) := by
    have hmod' := hmod
    unfold ModColoring at hmod'
    dsimp only at hmod'
    apply hmod'.2.2 C
    · rw [hLowerTree]
      exact hTjm1C
    · rw [hLowerTree]
      exact hTjm1StrictC
    · simpa [hLowerTree] using hLowerEligible
  obtain ⟨corr⟩ := hcorrNonempty
  have hreplacementMP : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 lower rho3 hmod C corr hLowerMP
  have hCElementary :
      ColoredVertexSetElementary G rho3 (TreeSequenceVertexSet C) :=
    hLowerI C corr hreplacementMP
  have hstableAtSlot : StableColoring
      (ett.series.data.tree jSlot.castSucc.castSucc)
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho3 := by
    rw [hTjm1Stored, hDprevStored, hPhiJStored]
    exact hstableLower
  have hbound := @helper_hbound_937 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett lowerInput lowerTree lowerGenerating lower jSlot hjPositive Tjm1 Tj seed
      TjPrime rho3 zPosition uPosition hTjm1Stored hTjStored hLowerRounds hMP hrhoProper hrhoOne
      hseedBuildRho C hrouteSeedC hclosedC hstableAtSlot
  have hseedC : TreeSequenceInitialSegment seed C :=
    TashkinovAugmentationSequenceInitialSegment rho3 seed C hrouteSeedC
  have hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨Fin.last seed.length, hseedTerminal⟩
  have hterminalC : terminalSupport ∈ TreeSequenceVertexSet C :=
    TreeSequenceInitialSegmentVertexSetSubset hseedC hterminalSeed
  have hZC : TreeSequenceVertexSet Z ⊆ TreeSequenceVertexSet C := by
    intro v hvZ
    have hvM : v ∈ TreeSequenceVertexSet M := by
      rw [hunion.vertexSet]
      exact Finset.mem_union_right _ hvZ
    exact TreeSequenceInitialSegmentVertexSetSubset hMCsegment hvM
  have hzZ : z ∈ TreeSequenceVertexSet Z := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨Fin.last Z.length, ?_⟩
    change Tj.vertex (Fin.castLE (Nat.succ_le_succ hzPositionBound)
      (Fin.last zPosition.val)) = z
    have hindex : Fin.castLE (Nat.succ_le_succ hzPositionBound)
        (Fin.last zPosition.val) = zPosition := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hzPosition
  have hzC : z ∈ TreeSequenceVertexSet C := hZC hzZ
  rcases hzChoice with hzLast | hzEarlier
  · exact @helper_branch_1101 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett lowerInput lowerTree lowerGenerating lower jSlot Tjm1 Tj seed TjPrime u
      zPosition uPosition huOutsideTj hzPositionPositive hzPositionBound hZTj C huC hbound hZC
      hzLast
  · have hdeltaZ : deltaN ∈ MissingColors G rho3 z :=
      hd2Delta hzEarlier.2
    have hdeltaTerminal :
        deltaN ∈ MissingColors G rho3 terminalSupport := by
      rw [hterminalMissingEq]
      exact hdeltaRho1
    have hdisjoint := hCElementary hterminalC hzC hterminalNeZ
    exact (Finset.disjoint_left.mp hdisjoint) hdeltaTerminal hdeltaZ

private theorem helper_continuation_1295.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) {lowerInput : PartialEdgeColoring E k}
        {lowerTree : TreeSequence G e0} {lowerGenerating : PartialEdgeColoring E k} (lower :
        ExtendedTashkinovTree G k e0 lowerInput lowerTree lowerGenerating) (jSlot : Fin
        ett.rounds) (_ : (1 : ℕ) ≤ (↑jSlot : ℕ)) (Tjm1 Tj seed TjPrime : TreeSequence G e0) (phiJ
        rho1 rho3 : PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (terminalSupport u z : V)
        (beta gammaFirst deltaN : Fin k) (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet
        Tj) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (hzTj : z ∈ TreeSequenceVertexSet Tj)
        (zPosition : Fin (Tj.length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ :
        Tj.vertex zPosition = z) (_ : TjPrime.vertex uPosition = u) (_ : seed.vertex (Fin.last
        seed.length) = terminalSupport) (_ : terminalSupport ∈ TreeVerticesBefore Tj z hzTj) (_ :
        u ∉ TreeSequenceVertexSet Tj) (_ : ett.series.data.tree jSlot.castSucc.castSucc = Tjm1) (_
        : ett.series.data.coloring jSlot.castSucc = phiJ) (_ : ett.series.data.tree
        jSlot.succ.castSucc = Tj) (_ : TashkinovStoredColors ett.series.data jSlot.castSucc =
        Dprev) (_ : lower.rounds = (↑jSlot : ℕ)) (_ : lower.series.data.tree (Fin.last
        lower.rounds).castSucc = Tjm1) (_ : lower.series.data.kind (Fin.last lower.rounds) =
        ett.series.data.kind jSlot.castSucc) (_ : lower.series.data.connectingEdges (Fin.last
        lower.rounds) = ett.series.data.connectingEdges jSlot.castSucc) (_ : TreeSequenceVertexSet
        Tjm1 ⊆ TreeVerticesBefore Tj terminalSupport hterminalTj) (_ :
        TashkinovAugmentationSequence phiJ seed Tj) (_ : TashkinovClosure rho1 seed TjPrime) (_ :
        MaximumProperty ett) (_ : MaximumProperty lower) (_ : (
    ∀ (Tstar : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3
        Tstar) (_ : MaximumProperty corr.replacementETT), ColoredVertexSetElementary G rho3
        (TreeSequenceVertexSet Tstar))) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport, MissingColors G rho1 v = MissingColors
        G phiJ v)) (_ : (
    ∀ (a : Fin Tj.length), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ : MissingColors G phiJ
        terminalSupport ⊆ MissingColors G rho1 terminalSupport ∪ { gammaFirst }) (_ : deltaN ∈
        MissingColors G rho1 terminalSupport) (_ : IsProperEdgeColoring G rho3) (_ :
        IsOneEdgeUncolored rho3 e0) (_ : (
    ∀ v ∈ ((TreeVerticesBefore Tj z hzTj ∪ { z } ∪ (TreeVerticesBefore TjPrime u huPrime ∪
        { u })).erase u).erase z, MissingColors G rho3 v = MissingColors G rho1 v)) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin Tj.length), (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length), (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1
        f)) (_ : (
    ∀ (_ : beta ∈ MissingColors G rho1 z), deltaN ∈ MissingColors G rho3 z)) (_ : (
    ∀ (_ : z ∈ TreeVerticesBefore TjPrime u huPrime), MissingColors G rho3 z = MissingColors G
        rho1 z)) (_ : gammaFirst ∈ MissingColors G rho3 u) (_ : zPosition = Fin.last Tj.length ∨
        (↑zPosition : ℕ) < (↑(Fin.last Tj.length) : ℕ) ∧ beta ∈ MissingColors G rho1 z) (_ :
        StableColoring Tjm1 Dprev phiJ rho3) (_ : ModColoring lower rho3) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (_ :
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tjm1 seed ∨ (ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        { f } ∧ TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧ TashkinovAugmentationSequence rho3
        adjoinSeed seed)) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound :
        (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition : ℕ))
        (hzPositionBound : (↑zPosition : ℕ) ≤ Tj.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix Tj (↑zPosition : ℕ) hzPositionPositive
        hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : TreeSequenceInitialSegment Z Tj) (_ :
        TreeSequenceInitialSegment seed U) (_ : TreeSequenceInitialSegment seed Z), False := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett lowerInput lowerTree lowerGenerating lower
      jSlot hjPositive Tjm1 Tj seed TjPrime phiJ rho1 rho3 Dprev terminalSupport u z beta
      gammaFirst deltaN hterminalTj huPrime hzTj zPosition uPosition hzPosition huPosition
      hseedTerminal hterminalBeforeZ huOutsideTj hTjm1Stored hPhiJStored hTjStored hDprevStored
      hLowerRounds hLowerTree hLowerKind hLowerConnecting hTjm1Before hTjAugmentation
      hprimeClosure hMP hLowerMP hLowerI hb2Missing hb2Edges huniquezang hdeltaRho1 hrhoProper
      hrhoOne hd2Missing hd2Edges hd2Delta hd2Z hd3 hzChoice hstableLower hmod segmentTrans
      hseedBuildRho huPositionPositive huPositionBound hzPositionPositive hzPositionBound U Z
      hUPrime hZTj hseedU hseedZ
  have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
    TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
      hprimeClosure.1 hseedU hUPrime
  have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
      (hi : i.val < uPosition.val) :
      TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u huPrime := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    constructor
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨i, rfl⟩
    · unfold TreeVertexOrder
      exact ⟨i, uPosition, rfl, huPosition, hi⟩
  have hUsegmentVertexBefore {A : TreeSequence G e0}
      (hAU : TreeSequenceInitialSegment A U) (hAlen : A.length < U.length)
      {w : V} (hwA : w ∈ TreeSequenceVertexSet A) :
      w ∈ TreeVerticesBefore TjPrime u huPrime := by
    exact TreeSequenceInitialSegment.mem_before_of_length hAU hUPrime hAlen
      hprimeVertexBefore hwA
  have hbeforePrimeMissing (w : V)
      (hw : w ∈ TreeVerticesBefore TjPrime u huPrime) :
      MissingColors G rho3 w = MissingColors G rho1 w := by
    exact TreeVerticesBefore.missingColors_eq_of_erase hd2Missing hd2Z hw
  have transportURoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence rho1 S U) :
      TashkinovAugmentationSequence rho3 S U := by
    apply TashkinovAugmentationSequence.transport_of_fixed (target := U) ?_ ?_ hroute
    · intro index
      let primeIndex : Fin TjPrime.length := Fin.castLE hUPrime.1 index
      have atPosition : primeIndex.val < uPosition.val := by
        change index.val < uPosition.val
        exact index.isLt
      have agreement : rho3 (TjPrime.edge primeIndex) =
          rho1 (TjPrime.edge primeIndex) := by
        apply hd2Edges (TjPrime.edge primeIndex)
        exact Or.inr ⟨primeIndex, atPosition, rfl⟩
      rw [show TjPrime.edge primeIndex = U.edge index from hUPrime.2.2 index] at agreement
      exact agreement
    · intro A hAU hAlen vertex member
      exact hbeforePrimeMissing vertex (hUsegmentVertexBefore hAU hAlen member)
  have hrouteRhoThreeU : TashkinovAugmentationSequence rho3 seed U :=
    transportURoute seed hrouteRhoOneU
  have hterminalNeZ : terminalSupport ≠ z := by
    unfold TreeVerticesBefore at hterminalBeforeZ
    obtain ⟨-, i, j, hit, hjz, hij⟩ :=
      Finset.mem_filter.mp hterminalBeforeZ
    intro htz
    have hijEq : i = j := Tj.vertex_injective
      (hit.trans (htz.trans hjz.symm))
    omega
  have hterminalNeU : terminalSupport ≠ u := by
    intro htu
    apply huOutsideTj
    rw [← htu]
    exact hterminalTj
  have hterminalMissingEq :
      MissingColors G rho3 terminalSupport =
        MissingColors G rho1 terminalSupport := by
    apply hd2Missing terminalSupport
    apply Finset.mem_erase.mpr
    refine ⟨hterminalNeZ, Finset.mem_erase.mpr ⟨hterminalNeU, ?_⟩⟩
    apply Finset.mem_union_left
    exact Finset.mem_union_left _ hterminalBeforeZ
  have hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho3 terminalSupport ∪ MissingColors G rho3 u := by
    intro c hc
    have hcCases := huniquezang hc
    rcases Finset.mem_union.mp hcCases with hcTerminal | hcGamma
    · apply Finset.mem_union_left
      rw [hterminalMissingEq]
      exact hcTerminal
    · apply Finset.mem_union_right
      have hcgamma : c = gammaFirst := Finset.mem_singleton.mp hcGamma
      simpa [hcgamma] using hd3
  have hbeforeZData {v : V}
      (hv : v ∈ TreeVerticesBefore Tj z hzTj) :
      v ∈ TreeSequenceVertexSet Tj ∧ v ≠ z := by
    unfold TreeVerticesBefore at hv
    obtain ⟨hvTj, i, j, hiv, hjz, hij⟩ := Finset.mem_filter.mp hv
    refine ⟨hvTj, ?_⟩
    intro hvz
    have hijEq : i = j := Tj.vertex_injective
      (hiv.trans (hvz.trans hjz.symm))
    omega
  exact @helper_continuation_1296 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett lowerInput lowerTree lowerGenerating lower jSlot hjPositive Tjm1
      Tj seed TjPrime phiJ rho1 rho3 Dprev terminalSupport u z beta deltaN hterminalTj huPrime
      hzTj zPosition uPosition hzPosition huPosition hseedTerminal huOutsideTj hTjm1Stored
      hPhiJStored hTjStored hDprevStored hLowerRounds hLowerTree hLowerKind hLowerConnecting
      hTjm1Before hTjAugmentation hMP hLowerMP hLowerI hb2Missing hb2Edges hdeltaRho1 hrhoProper
      hrhoOne hd2Missing hd2Edges hd2Delta hzChoice hstableLower hmod segmentTrans hseedBuildRho
      huPositionPositive huPositionBound hzPositionPositive hzPositionBound hZTj hseedU hseedZ
      hrouteRhoThreeU hterminalNeZ hterminalMissingEq hterminalInclusion hbeforeZData
theorem ExtensionBaseCaseTwoContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    {lowerInput : PartialEdgeColoring E k}
    {lowerTree : TreeSequence G e0}
    {lowerGenerating : PartialEdgeColoring E k}
    (lower : ExtendedTashkinovTree G k e0 lowerInput lowerTree
      lowerGenerating)
    (jSlot : Fin ett.rounds) (hjPositive : 1 ≤ jSlot.val)
    (Tjm1 Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 rho3 : PartialEdgeColoring E k)
    (Dprev : Finset (Fin k))
    (terminalSupport u z : V) (beta gammaFirst deltaN : Fin k)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (hzTj : z ∈ TreeSequenceVertexSet Tj)
    (zPosition : Fin (Tj.length + 1))
    (uPosition : Fin (TjPrime.length + 1))
    (hzPosition : Tj.vertex zPosition = z)
    (huPosition : TjPrime.vertex uPosition = u)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hseedAtMostZ : seed.length ≤ zPosition.val)
    (hseedBeforeU : seed.length < uPosition.val)
    (hterminalBeforeZ : terminalSupport ∈ TreeVerticesBefore Tj z hzTj)
    (huOutsideTj : u ∉ TreeSequenceVertexSet Tj)
    (hTjm1Stored :
      ett.series.data.tree jSlot.castSucc.castSucc = Tjm1)
    (hPhiJStored : ett.series.data.coloring jSlot.castSucc = phiJ)
    (hTjStored : ett.series.data.tree jSlot.succ.castSucc = Tj)
    (hDprevStored :
      TashkinovStoredColors ett.series.data jSlot.castSucc = Dprev)
    (hLowerRounds : lower.rounds = jSlot.val)
    (hLowerTree : lower.series.data.tree
      (Fin.last lower.rounds).castSucc = Tjm1)
    (_ : lower.series.data.coloring
      (Fin.last lower.rounds) = phiJ)
    (_ : TashkinovStoredColors lower.series.data
      (Fin.last lower.rounds) = Dprev)
    (hLowerKind : lower.series.data.kind (Fin.last lower.rounds) =
      ett.series.data.kind jSlot.castSucc)
    (hLowerConnecting : lower.series.data.connectingEdges
      (Fin.last lower.rounds) =
        ett.series.data.connectingEdges jSlot.castSucc)
    (hTjm1Before : TreeSequenceVertexSet Tjm1 ⊆
      TreeVerticesBefore Tj terminalSupport hterminalTj)
    (hseedBuild :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phiJ Tjm1 seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
            TashkinovAugmentationSequence phiJ adjoinSeed seed))
    (hTjAugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hprimeClosure : TashkinovClosure rho1 seed TjPrime)
    (_ : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hMP : MaximumProperty ett)
    (hLowerMP : MaximumProperty lower)
    (hLowerI : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3 Tstar),
      MaximumProperty corr.replacementETT →
        ColoredVertexSetElementary G rho3
          (TreeSequenceVertexSet Tstar))
    (hLowerVI : ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tjm1 Dprev phiJ sigma → ModColoring lower sigma)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
        MissingColors G rho1 v = MissingColors G phiJ v)
    (hb2Edges : ∀ a : Fin Tj.length,
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (huniquezang : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (hdeltaRho1 : deltaN ∈ MissingColors G rho1 terminalSupport)
    (_ : beta ∈ MissingColors G rho1 u)
    (hrhoProper : IsProperEdgeColoring G rho3)
    (hrhoOne : IsOneEdgeUncolored rho3 e0)
    (hd1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3)
    (hd2Missing : ∀ v : V,
      v ∈ (((TreeVerticesBefore Tj z hzTj ∪ {z}) ∪
          (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v)
    (hd2Edges : ∀ f : E,
      ((∃ a : Fin Tj.length, a.val < zPosition.val ∧ Tj.edge a = f) ∨
        (∃ a : Fin TjPrime.length,
          a.val < uPosition.val ∧ TjPrime.edge a = f)) →
      rho3 f = rho1 f)
    (hd2Delta : beta ∈ MissingColors G rho1 z →
      deltaN ∈ MissingColors G rho3 z)
    (hd2Z : z ∈ TreeVerticesBefore TjPrime u huPrime →
      MissingColors G rho3 z = MissingColors G rho1 z)
    (hd3 : gammaFirst ∈ MissingColors G rho3 u)
    (hzChoice : zPosition = Fin.last Tj.length ∨
      (zPosition.val < (Fin.last Tj.length).val ∧
        beta ∈ MissingColors G rho1 z)) : False := by
  classical
  have hstableLower := @helper_hstableLower_821 V E inferInstance inferInstance G k e0 Tjm1 Tj phiJ
      rho3 Dprev terminalSupport hterminalTj hTjm1Before hd1
  have hmod : ModColoring lower rho3 :=
    hLowerVI rho3 hrhoProper hrhoOne hstableLower
  have segmentTrans := @TreeSequenceInitialSegment.trans V E G e0
  have commonPrefix := @helper_commonPrefix_864 V E G e0
  have hseedVertexBefore := @helper_hseedVertexBefore_888 V E inferInstance G e0 Tj seed
      terminalSupport hterminalTj hseedJ hseedTerminal
  have hsegmentVertexBefore {A : TreeSequence G e0}
      (hAseed : TreeSequenceInitialSegment A seed)
      (hAlen : A.length < seed.length) {v : V}
      (hvA : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeVerticesBefore Tj terminalSupport hterminalTj := by
    obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hvA
    obtain ⟨i, rfl⟩ := hvA
    have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
        seed.length := by
      change i.val < seed.length
      omega
    rw [← hAseedVertices i]
    exact hseedVertexBefore _ hi
  have transportStep {A B : TreeSequence G e0}
      (step : TashkinovAugmentation phiJ A B) (withinSeed : TreeSequenceInitialSegment B seed) :
      TashkinovAugmentation rho3 A B :=
    TashkinovAugmentation.transportBeforeVertex Tj seed phiJ rho3 Dprev terminalSupport
      hterminalTj hd1 hsegmentVertexBefore step withinSeed
  have transportSeedRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence phiJ S seed) :
      TashkinovAugmentationSequence rho3 S seed := by
    unfold TashkinovAugmentationSequence at hroute ⊢
    induction hroute using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head A B hAB hBseed ih =>
        have hBsegment : TreeSequenceInitialSegment B seed :=
          TashkinovAugmentationSequenceInitialSegment phiJ B seed hBseed
        exact Relation.ReflTransGen.head (transportStep hAB hBsegment) ih
  have hseedBuildRho :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tjm1 seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tjm1 f adjoinSeed ∧
            TashkinovAugmentationSequence rho3 adjoinSeed seed) := by
    rcases hseedBuild with hparallel | hserial
    · exact Or.inl ⟨hparallel.1, transportSeedRoute Tjm1 hparallel.2⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
        transportSeedRoute adjoinSeed hroute⟩
  have huPositionPositive : 1 ≤ uPosition.val := by omega
  have huPositionBound : uPosition.val ≤ TjPrime.length :=
    Nat.lt_succ_iff.mp uPosition.isLt
  have hzPositionPositive : 1 ≤ zPosition.val :=
    seed.positive.trans hseedAtMostZ
  have hzPositionBound : zPosition.val ≤ Tj.length :=
    Nat.lt_succ_iff.mp zPosition.isLt
  let U : TreeSequence G e0 :=
    TreeSequencePrefix TjPrime uPosition.val huPositionPositive huPositionBound
  let Z : TreeSequence G e0 :=
    TreeSequencePrefix Tj zPosition.val hzPositionPositive hzPositionBound
  have hUPrime : TreeSequenceInitialSegment U TjPrime := by
    refine ⟨?_, ?_, ?_⟩
    · change uPosition.val ≤ TjPrime.length
      exact huPositionBound
    · intro i
      simp [U, TreeSequencePrefix]
    · intro i
      simp [U, TreeSequencePrefix]
  have hZTj : TreeSequenceInitialSegment Z Tj := by
    refine ⟨?_, ?_, ?_⟩
    · change zPosition.val ≤ Tj.length
      exact hzPositionBound
    · intro i
      simp [Z, TreeSequencePrefix]
    · intro i
      simp [Z, TreeSequencePrefix]
  have hseedU : TreeSequenceInitialSegment seed U := by
    apply commonPrefix hseedPrime hUPrime
    change seed.length ≤ uPosition.val
    omega
  have hseedZ : TreeSequenceInitialSegment seed Z := by
    apply commonPrefix hseedJ hZTj
    change seed.length ≤ zPosition.val
    exact hseedAtMostZ
  exact @helper_continuation_1295 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett lowerInput lowerTree lowerGenerating lower jSlot hjPositive Tjm1
      Tj seed TjPrime phiJ rho1 rho3 Dprev terminalSupport u z beta gammaFirst deltaN hterminalTj
      huPrime hzTj zPosition uPosition hzPosition huPosition hseedTerminal hterminalBeforeZ
      huOutsideTj hTjm1Stored hPhiJStored hTjStored hDprevStored hLowerRounds hLowerTree
      hLowerKind hLowerConnecting hTjm1Before hTjAugmentation hprimeClosure hMP hLowerMP hLowerI
      hb2Missing hb2Edges huniquezang hdeltaRho1 hrhoProper hrhoOne hd2Missing hd2Edges hd2Delta
      hd2Z hd3 hzChoice hstableLower hmod segmentTrans hseedBuildRho huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound hUPrime hZTj hseedU hseedZ
end GoldbergSeymour

end
