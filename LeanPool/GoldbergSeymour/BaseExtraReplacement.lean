/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoStarredTail
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.ElementaryTerminalComponent

/-!
# P2905_T2_Base Extra Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation903Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    ∀ alpha ∉ (HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
        (C.good.gamma (Fin.last C.hierarchy.dividerCount)),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; TreeSequenceInitialSegment A T →
        TreeSequenceInitialSegment A B → TreeSequenceInitialSegment base.core B →
    ∀ beta ∈ TreeMissingColors phi Tn, beta ∉ Gamma ∧ beta ∉ M0 → beta ∈ TreeMissingColors phi A →
        alpha ∈ TreeMissingColors phi A → beta ≠ alpha → beta ∈ TreeMissingColors phi B ∧ alpha ∈
        TreeMissingColors phi B → (T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet A ∧ beta ∈ MissingColors G phi (T.vertex
        (HierarchyFirstMissingPosition phi T beta))) ∧ (↑(HierarchyFirstMissingPosition phi T
        beta) : ℕ) ≤ A.length →
    let u : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    let _ : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let w : V := T.vertex (Fin.last T.length); B.length + (1 : ℕ) = T.length →
        TreeSequenceInitialSegment B T → w ≠ u → Disjoint (TwoColorComponent G phi beta alpha
        (Sum.inl w)) (TwoColorComponent G phi beta alpha (Sum.inl u)) → TwoColorPathComponent G
        phi beta alpha (Sum.inl w) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi beta alpha
        (Sum.inl w)) x = MissingColors G phi x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta alpha (Sum.inl w);
        sigma = TwoColorComponentSwap G phi beta alpha (Sum.inl w) → beta ∈ MissingColors G sigma
        w → (
    ∀ c ∈ TreeMissingColors phi A, c ∈ TreeMissingColors sigma A) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∃ beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), beta ∈ TreeMissingColors
        P.coloring (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) ∧
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v

private theorem helper_hCoreB_124.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    ∀ alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ)); (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → TreeSequenceInitialSegment A B →
        TreeSequenceInitialSegment base.core B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha hstar H q A ell B segTrans hAB
  have hcoreA : TreeSequenceInitialSegment base.core A := by
    by_cases hq : H.dividerCount = 0
    · have hA : A = base.core := by
        simp [A, q, HierarchyStarredStage, hq, Fin.last]
      rw [hA]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · have hstar : A = H.stage q.castSucc := by
        have hAstage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
          have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
              (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
            apply Fin.ext
            simp
            omega
          dsimp [A, q, HierarchyStarredStage]
          rw [hlast]
          simp only [Fin.cases]
          apply congrArg H.stage
          apply Fin.ext
          simp
          omega
        have hidx : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) = q.castSucc := by
          apply Fin.ext
          rfl
        rw [hAstage, hidx]
      have chain : TreeSequenceInitialSegment (H.stage 1) A := by
        have reach : ∀ (m : ℕ) (hm : m ≤ H.dividerCount) (hlow : 1 ≤ m),
            TreeSequenceInitialSegment (H.stage 1) (H.stage ⟨m, by omega⟩) := by
          intro m
          induction m with
          | zero => intro hm hlow; omega
          | succ m ih =>
              intro hm hlow
              by_cases hm : m = 0
              · subst m
                have hidx : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
                    (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := rfl
                exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
              · have hprev := ih (by omega) (by omega)
                let j : Fin (H.dividerCount + 1) := ⟨m, by omega⟩
                have hstep := H.nested j
                have heq₁ : j.castSucc = (⟨m, by omega⟩ : Fin (H.dividerCount + 2)) := by
                  apply Fin.ext
                  rfl
                have heq₂ : j.succ = (⟨m + 1, by omega⟩ : Fin (H.dividerCount + 2)) := by
                  apply Fin.ext
                  rfl
                rw [heq₁, heq₂] at hstep
                exact segTrans hprev hstep
        have hf := reach H.dividerCount (by omega) (by omega)
        rw [hstar]
        have hidx : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) = q.castSucc := by
          apply Fin.ext
          rfl
        rw [← hidx]
        exact hf
      exact segTrans H.coreInsideFirst chain
  exact segTrans hcoreA hAB

private theorem helper_hcoreA_183.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segTrans
  by_cases hq : H.dividerCount = 0
  · have hA : A = base.core := by simp [A, q, HierarchyStarredStage, hq, Fin.last]
    rw [hA]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · have hAstage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
          (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp
        omega
      dsimp [A, q, HierarchyStarredStage]
      rw [hlast]
      simp only [Fin.cases]
      apply congrArg H.stage
      apply Fin.ext
      simp
      omega
    have chain : TreeSequenceInitialSegment (H.stage 1) A := by
      have reach : ∀ (m : ℕ) (hm : m ≤ H.dividerCount) (hlow : 1 ≤ m),
          TreeSequenceInitialSegment (H.stage 1) (H.stage ⟨m, by omega⟩) := by
        intro m
        induction m with
        | zero => intro hm hlow; omega
        | succ m ih =>
            intro hm hlow
            by_cases hm0 : m = 0
            · subst m
              exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
            · have hprev := ih (by omega) (by omega)
              let j : Fin (H.dividerCount + 1) := ⟨m, by omega⟩
              have hstep := H.nested j
              have heq₁ : j.castSucc = (⟨m, by omega⟩ : Fin (H.dividerCount + 2)) := by
                apply Fin.ext
                rfl
              have heq₂ : j.succ = (⟨m + 1, by omega⟩ : Fin (H.dividerCount + 2)) := by
                apply Fin.ext
                rfl
              rw [heq₁, heq₂] at hstep
              exact segTrans hprev hstep
      have hf := reach H.dividerCount (by omega) (by omega)
      rw [hAstage]
      exact hf
    exact segTrans H.coreInsideFirst chain

private theorem helper_firstWitness_341.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T →
    ∀ c ∈ TreeMissingColors phi A, (T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet A ∧ c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition
        phi T c))) ∧ (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hAT c hc
  unfold TreeMissingColors at hc
  simp only [Finset.mem_biUnion] at hc
  obtain ⟨v, hv, hvc⟩ := hc
  unfold TreeSequenceVertexSet at hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨ia, hia⟩ := hv
  let iaT : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hAT.1) ia
  have hvertex : T.vertex iaT = A.vertex ia := hAT.2.1 ia
  have hca : c ∈ MissingColors G phi (T.vertex iaT) := by rw [hvertex, hia]; exact hvc
  let candidates : Finset (Fin (T.length + 1)) :=
    Finset.univ.filter fun i => c ∈ MissingColors G phi (T.vertex i)
  have hcand : candidates.Nonempty := ⟨iaT, by simp [candidates, hca]⟩
  have hpos : HierarchyFirstMissingPosition phi T c = candidates.min' hcand := by
    simp [HierarchyFirstMissingPosition, candidates, hcand]
  have hmin : (HierarchyFirstMissingPosition phi T c).val ≤ iaT.val := by
    rw [hpos]
    exact Finset.min'_le candidates iaT (by simp [candidates, hca])
  have hbound : (HierarchyFirstMissingPosition phi T c).val ≤ A.length := by
    dsimp [iaT] at hmin
    exact le_trans hmin (Nat.le_of_lt_succ ia.isLt)
  let x : Fin (A.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi T c).val, Nat.lt_succ_of_le hbound⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hAT.1) x =
      HierarchyFirstMissingPosition phi T c := Fin.ext rfl
  have hmiss : c ∈ MissingColors G phi (A.vertex x) := by
    have hm := Finset.min'_mem candidates hcand
    have hm' : c ∈ MissingColors G phi
        (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
      rw [hpos]
      exact (Finset.mem_filter.mp hm).2
    rw [← hcast, hAT.2.1 x] at hm'
    exact hm'
  constructor
  · simp only [TreeSequenceVertexSet, Finset.mem_image]
    constructor
    · exact ⟨x, Finset.mem_univ _, (hAT.2.1 x).symm.trans (congrArg T.vertex hcast)⟩
    · have hvertexEq := (hAT.2.1 x).symm.trans (congrArg T.vertex hcast)
      rw [hvertexEq] at hmiss
      exact hmiss
  · exact hbound

private theorem helper_hstoredFirst_499.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (beta : Fin k), beta ∈ TreeMissingColors phi B ∧ alpha ∈ TreeMissingColors phi B →
    let w : V := T.vertex (Fin.last T.length); B.length + (1 : ℕ) = T.length →
        TreeSequenceInitialSegment B T → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi beta alpha
        (Sum.inl w)) x = MissingColors G phi x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta alpha (Sum.inl w); (
    ∀ (eta : Fin k), HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi
        B eta) → (
    ∀ (psi : PartialEdgeColoring E k) (eta : Fin k), (↑(HierarchyFirstMissingPosition psi T eta) :
        ℕ) < T.length → eta ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T
        eta))) → (
    ∀ (psi : PartialEdgeColoring E k) (eta : Fin k) (i : Fin (T.length + (1 : ℕ))), eta ∈
        MissingColors G psi (T.vertex i) → (↑(HierarchyFirstMissingPosition psi T eta) : ℕ) ≤ (↑i
        : ℕ)) → (
    ∀ (eta : Fin k) (psi : PartialEdgeColoring E k), (↑(HierarchyFirstMissingPosition psi T eta) :
        ℕ) = B.length → eta ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T
        eta)) → eta ∈ MissingColors G psi (B.vertex (Fin.last B.length))) →
    ∀ eta ∈ D, HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q ell B D beta hmissB w hlenB hBT
      hmissEq sigma hfirstEqB posMissing posLe transportAtLast eta heta
  have hcut : min (HierarchyFirstMissingPosition sigma T eta).val B.length =
      min (HierarchyFirstMissingPosition phi T eta).val B.length := by
    rw [← HierarchyFirstMissingPositionPrefixCutoff sigma B T hBT eta B.length le_rfl,
      hfirstEqB eta,
      HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta B.length le_rfl]
  apply Fin.ext
  by_cases hs : (HierarchyFirstMissingPosition sigma T eta).val < B.length
  · have hsmin : min (HierarchyFirstMissingPosition sigma T eta).val B.length =
        (HierarchyFirstMissingPosition sigma T eta).val := Nat.min_eq_left (by omega)
    rw [hsmin] at hcut
    have hphi : (HierarchyFirstMissingPosition phi T eta).val < B.length := by
      have := Nat.min_le_right
        (HierarchyFirstMissingPosition phi T eta).val B.length
      omega
    have hpmin : min (HierarchyFirstMissingPosition phi T eta).val B.length =
        (HierarchyFirstMissingPosition phi T eta).val := Nat.min_eq_left (by omega)
    rw [hpmin] at hcut
    exact hcut
  · have hsge : B.length ≤ (HierarchyFirstMissingPosition sigma T eta).val := by omega
    have hpge : B.length ≤ (HierarchyFirstMissingPosition phi T eta).val := by
      by_contra h
      have hp : (HierarchyFirstMissingPosition phi T eta).val < B.length := by omega
      have hmin : min (HierarchyFirstMissingPosition phi T eta).val B.length =
          (HierarchyFirstMissingPosition phi T eta).val := Nat.min_eq_left (by omega)
      rw [hmin] at hcut
      omega
    by_cases hse : (HierarchyFirstMissingPosition sigma T eta).val = B.length
    · have hmissS : eta ∈ MissingColors G sigma
          (T.vertex (HierarchyFirstMissingPosition sigma T eta)) :=
        posMissing sigma eta (by rw [hse]; omega)
      have hmissB := transportAtLast eta sigma hse hmissS
      have hvB : B.vertex (Fin.last B.length) ∈ TreeSequenceVertexSet B := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨Fin.last B.length, rfl⟩
      have hmissOld : eta ∈ MissingColors G phi (B.vertex (Fin.last B.length)) := by
        rw [hmissEq _ hvB] at hmissB
        exact hmissB
      have hmissOldCast : eta ∈ MissingColors G phi
          (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length))) := by
        rw [hBT.2.1 (Fin.last B.length)]
        exact hmissOld
      have hposOld : (HierarchyFirstMissingPosition phi T eta).val ≤ B.length :=
        posLe phi eta (Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length))
          hmissOldCast
      have hpEq : (HierarchyFirstMissingPosition phi T eta).val = B.length := by omega
      exact hse.trans hpEq.symm
    · have hphiNe : (HierarchyFirstMissingPosition phi T eta).val ≠ B.length := by
        intro he
        have hmissOld : eta ∈ MissingColors G phi
            (T.vertex (HierarchyFirstMissingPosition phi T eta)) :=
          posMissing phi eta (by rw [he]; omega)
        have hmissB := transportAtLast eta phi he hmissOld
        have hvB : B.vertex (Fin.last B.length) ∈ TreeSequenceVertexSet B := by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
            true_and]
          exact ⟨Fin.last B.length, rfl⟩
        have hmissSigmaB : eta ∈ MissingColors G sigma (B.vertex (Fin.last B.length)) := by
          rw [hmissEq _ hvB]
          exact hmissB
        have hmissSigmaCast : eta ∈ MissingColors G sigma
            (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length))) := by
          rw [hBT.2.1 (Fin.last B.length)]
          exact hmissSigmaB
        have hposSigma : (HierarchyFirstMissingPosition sigma T eta).val ≤ B.length :=
          posLe sigma eta (Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length))
            hmissSigmaCast
        have : (HierarchyFirstMissingPosition sigma T eta).val = B.length := by
          have hmin : min (HierarchyFirstMissingPosition sigma T eta).val B.length =
              (HierarchyFirstMissingPosition sigma T eta).val := Nat.min_eq_left hposSigma
          rw [he] at hcut
          simpa [hmin] using hcut
        exact hse this
      have hsEq : (HierarchyFirstMissingPosition sigma T eta).val = T.length := by
        have hge : B.length + 1 ≤ (HierarchyFirstMissingPosition sigma T eta).val := by omega
        rw [hlenB] at hge
        have hle := Nat.le_of_lt_succ (HierarchyFirstMissingPosition sigma T eta).isLt
        omega
      have hpEq : (HierarchyFirstMissingPosition phi T eta).val = T.length := by
        have hge : B.length + 1 ≤
            (HierarchyFirstMissingPosition phi T eta).val := by omega
        rw [hlenB] at hge
        have hle := Nat.le_of_lt_succ (HierarchyFirstMissingPosition phi T eta).isLt
        omega
      exact hsEq.trans hpEq.symm

private theorem helper_hfinalTree_741.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : Fin k) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let H' : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let Tn' : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; H.dividerCount = H'.dividerCount → Tn' =
        Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha H n Tn beta P H' Tn' hcount
  let corr := P.corresponding
  change corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc =
    ett.series.data.tree (Fin.last ett.rounds).castSucc
  let terminalIndex : Fin ett.rounds :=
    ⟨ett.rounds - 1, by have hp := C.positive; omega⟩
  have terminalSucc : terminalIndex.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    have hp := C.positive
    have hi : terminalIndex.val = ett.rounds - 1 := rfl
    rw [hi]
    omega
  have terminalTree : terminalIndex.castSucc.succ =
      (Fin.last ett.rounds).castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc]
    have hp := C.positive
    have hi : terminalIndex.val = ett.rounds - 1 := rfl
    rw [hi]
    omega
  have presentation : corr.replacementETT.series =
      corr.rungAgreement.symm ▸ corr.replacementSeries := by
    have typeLink : TashkinovSeries G k ett.rounds e0 corr.replacementInput =
        TashkinovSeries G k corr.replacementETT.rounds e0 corr.replacementInput :=
      congrArg (fun r => TashkinovSeries G k r e0 corr.replacementInput)
        corr.rungAgreement.symm
    have castProof : HEq corr.replacementSeries
        (corr.rungAgreement.symm ▸ corr.replacementSeries) := by
      simp
    exact eq_of_heq (HEq.trans corr.seriesPresentation castProof)
  have castTree {a b : Nat} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)) :
      (cast (congrArg (fun r => TashkinovSeries G k r e0 corr.replacementInput) h) s).data.tree i =
        s.data.tree (Fin.cast (congrArg (fun r => r + 2) h.symm) i) := by
    cases h
    rfl
  have transportEq : corr.rungAgreement.symm ▸ corr.replacementSeries =
      cast (congrArg (fun r => TashkinovSeries G k r e0 corr.replacementInput)
        corr.rungAgreement.symm) corr.replacementSeries := by
    symm
    apply cast_eq_iff_heq.mpr
    simp
  rw [presentation]
  calc
    (corr.rungAgreement.symm ▸ corr.replacementSeries).data.tree
        (Fin.last corr.replacementETT.rounds).castSucc =
      corr.replacementSeries.data.tree
        (Fin.cast (congrArg (fun r => r + 2) corr.rungAgreement)
          (Fin.last corr.replacementETT.rounds).castSucc) := by
            rw [transportEq]
            simpa using castTree corr.rungAgreement.symm corr.replacementSeries
              (Fin.last corr.replacementETT.rounds).castSucc
    _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      simpa [terminalTree, terminalSucc, corr] using
        corr.ladderTreesAgree terminalIndex

private theorem helper_hExtraEq_799.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (alpha : Fin k),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; TreeSequenceInitialSegment base.core B →
    ∀ (beta : Fin k),
    let _ : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let w : V := T.vertex (Fin.last T.length); (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi beta alpha
        (Sum.inl w)) x = MissingColors G phi x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta alpha (Sum.inl w);
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), P.coloring = sigma
        →
    let Tn' : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; base.core = P.replacementBase.core → Tn'
        = Tn → ((TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn').biUnion
        fun (v : V) ↦ MissingColors G P.coloring v) = M0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha ell B n Tn M0 hCoreB beta v w hmissEq
      sigma P hPcolor Tn' hcore hfinalTree
  apply Finset.ext
  intro c
  change c ∈ (TreeSequenceVertexSet P.replacementBase.core \
      TreeSequenceVertexSet Tn').biUnion (fun v => MissingColors G P.coloring v) ↔
    c ∈ (TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet Tn).biUnion (fun v => MissingColors G phi v)
  rw [Finset.mem_biUnion, Finset.mem_biUnion]
  have hcoreSet : TreeSequenceVertexSet base.core =
      TreeSequenceVertexSet P.replacementBase.core := congrArg TreeSequenceVertexSet hcore
  have htreeSet : TreeSequenceVertexSet Tn = TreeSequenceVertexSet Tn' :=
    congrArg TreeSequenceVertexSet hfinalTree.symm
  constructor
  · rintro ⟨v, hv, hc⟩
    have hvOld : v ∈ TreeSequenceVertexSet base.core \
        TreeSequenceVertexSet Tn := by
      rw [hcoreSet, htreeSet]
      exact hv
    refine ⟨v, hvOld, ?_⟩
    have hvCore : v ∈ TreeSequenceVertexSet base.core :=
      (Finset.mem_sdiff.mp hvOld).1
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hCoreB hvCore
    have hmiss := hmissEq v hvB
    rw [hPcolor] at hc
    exact hmiss ▸ hc
  · rintro ⟨v, hv, hc⟩
    have hvNew : v ∈ TreeSequenceVertexSet P.replacementBase.core \
        TreeSequenceVertexSet Tn' := by
      rw [← hcoreSet, ← htreeSet]
      exact hv
    refine ⟨v, hvNew, ?_⟩
    have hvCore : v ∈ TreeSequenceVertexSet base.core :=
      (Finset.mem_sdiff.mp hv).1
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hCoreB hvCore
    have hmiss := hmissEq v hvB
    exact hPcolor ▸ hmiss.symm ▸ hc

private theorem helper_hsame_665.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ beta ∈ TreeMissingColors phi Tn, beta ∈ TreeMissingColors phi A → (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    have vb : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    have sameComponent : Prop := TwoColorComponent G phi beta alpha (Sum.inl va) =
        TwoColorComponent G phi beta alpha (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (beta ∈
        TreeMissingColors phi Tnq ∨ Disjoint { beta, alpha } Dnq) → sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧ (beta ∈ TreeMissingColors phi Tn ∨ Disjoint { beta, alpha }
        Dn) → sameComponent) ∧ (beta ∈ TreeMissingColors phi A ∧ TreeColorSetClosed G phi A
        { beta } → sameComponent ∧ TreeInterchangeable G A phi beta alpha)) → TwoColorComponent G
        phi beta alpha (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
        TwoColorComponent G phi beta alpha (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T
        alpha))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q A n Tn beta hbetaTn hbetaA hchange
  by_cases hq : H.dividerCount = 0
  · have hq' : C.hierarchy.dividerCount = 0 := by simpa [H] using hq
    have hpart := hchange.2.1 ⟨hq', Or.inl hbetaTn⟩
    exact hpart
  · have hqpos : 0 < H.dividerCount := by omega
    have hq' : C.hierarchy.dividerCount > 0 := by simpa [H] using hqpos
    have hstage : H.stage ⟨H.dividerCount, by omega⟩ = A := by
      have hAstage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
        have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
            (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
          apply Fin.ext
          simp
          omega
        dsimp [A, q, HierarchyStarredStage]
        rw [hlast]
        simp only [Fin.cases]
        apply congrArg H.stage
        apply Fin.ext
        simp
        omega
      exact hAstage.symm
    have hpart := hchange.1 ⟨hqpos, Or.inl (by
      rw [hstage]
      exact hbetaA)⟩
    exact hpart

private theorem helper_seriesProper_846.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (j : Fin (ett.rounds + (1 : ℕ))),
    IsProperEdgeColoring G (ett.series.data.coloring j) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett j
  cases ett.series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
    simpa [initialColoring] using triple.2.2.2.1
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentColoring]
    exact choice.selectedProper
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension => exact currentProper
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    rw [currentColoring]
    exact previousProper

private theorem helper_seriesOne_873.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (j : Fin (ett.rounds + (1 : ℕ))),
    IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
  classical
  intro V E _ _ _ G k e0 input T phi ett j
  cases ett.series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
    simpa [initialColoring] using triple.2.2.2.2
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [currentColoring]
    exact choice.selectedOneUncolored
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension => exact currentOneUncolored
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    rw [currentColoring]
    exact previousOneUncolored

private theorem helper_hMdis_717.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet B) → TreeSequenceInitialSegment base.core B →
        TreeSequenceInitialSegment Tn B → Disjoint (TreeMissingColors phi Tn) M0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ell B n Tn M0 hpen hCoreB hTnB
  rw [Finset.disjoint_left]
  intro c hc hM
  simp only [Finset.mem_biUnion, Finset.mem_sdiff, M0] at hM
  obtain ⟨v, hv, hvc⟩ := hM
  have hvCore : v ∈ TreeSequenceVertexSet base.core := hv.1
  have hvNotTn : v ∉ TreeSequenceVertexSet Tn := hv.2
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hCoreB hvCore
  have hTnB' := TreeSequenceInitialSegmentVertexSetSubset hTnB
  have hcTn : c ∈ TreeMissingColors phi Tn := hc
  obtain ⟨w, hw, hcw⟩ := Finset.mem_biUnion.mp hcTn
  have hwB := hTnB' hw
  have hne : v ≠ w := by
    intro heq
    subst w
    exact hvNotTn hw
  exact (Finset.disjoint_left.mp (hpen hvB hwB hne) hvc hcw)

private theorem helper_hbetaSet_749.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; Disjoint (TreeMissingColors phi Tn) M0 →
        Gamma.card ≤ (2 : ℕ) * ett.rounds → (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors
        phi Tn).card → (TreeMissingColors phi Tn \ (Gamma ∪ M0)).Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q n Tn D Gamma M0 hMdis hGammacard hlarge
  have hInter : (TreeMissingColors phi Tn ∩ (Gamma ∪ M0)).card ≤ Gamma.card := by
    apply Finset.card_le_card
    intro c hc
    simp only [Finset.mem_inter] at hc
    rcases Finset.mem_union.mp hc.2 with h | h
    · exact h
    · exact (Finset.disjoint_left.mp hMdis hc.1 h).elim
  have hcard : (TreeMissingColors phi Tn \ (Gamma ∪ M0)).card ≥ 11 := by
    have hInter' : ((Gamma ∪ M0) ∩ TreeMissingColors phi Tn).card ≤ Gamma.card := by
      simpa [Finset.inter_comm] using hInter
    rw [Finset.card_sdiff]
    omega
  exact Finset.card_pos.mp (by omega)

private theorem helper_hfirstEqB_873.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (beta : Fin k),
    let w : V := T.vertex (Fin.last T.length); (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi beta alpha
        (Sum.inl w)) x = MissingColors G phi x) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi beta alpha (Sum.inl w);
    ∀ (eta : Fin k), HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi
        B eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha ell B beta w hmissEq sigma eta
  have hc : (Finset.univ.filter fun j : Fin (B.length + 1) =>
      eta ∈ MissingColors G sigma (B.vertex j)) =
      (Finset.univ.filter fun j : Fin (B.length + 1) =>
        eta ∈ MissingColors G phi (B.vertex j)) := by
    apply Finset.filter_congr
    intro j _
    rw [hmissEq (B.vertex j) (by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨j, rfl⟩)]
  unfold HierarchyFirstMissingPosition
  rw [hc]

private theorem helper_hcase_921.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha :
        Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ beta ∈ TreeMissingColors phi Tn, beta ∈ TreeMissingColors phi A → (0 : ℕ) < H.dividerCount ∧
        beta ∈ TreeMissingColors phi (H.stage (⟨H.dividerCount, Decidable.byContradiction fun (a :
        ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (beta ∈ TreeMissingColors
        phi Tn ∨ beta ∈ TreeMissingColors phi A ∧ beta ∉ TashkinovStoredColors ett.series.data n ∧
        alpha ∉ TashkinovStoredColors ett.series.data n) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha H q A n Tn beta hbetaTn hbetaA
  by_cases hq : H.dividerCount = 0
  · exact Or.inr ⟨hq, Or.inl hbetaTn⟩
  · have hqpos : 0 < H.dividerCount := by omega
    have hAstage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
          (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp
        omega
      dsimp [A, q, HierarchyStarredStage]
      rw [hlast]
      simp only [Fin.cases]
      apply congrArg H.stage
      apply Fin.ext
      simp
      omega
    exact Or.inl ⟨hqpos, hAstage ▸ hbetaA⟩

private theorem helper_continuation_903.{u_1, u_2} :
    helperContinuation903Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hgamma H q A ell B n Tn D Gamma M0
      hAT hAB hCoreB beta hbetaTn hbetaNot hbetaA halphaA hne hmissB huData u v w hlenB hBT hwu
      hdisjoint hpath hmissEq sigma hsigma hbetaW hmissSigmaA
  have hstarSigma : beta ∈ TreeMissingColors sigma A ∧
      alpha ∈ TreeMissingColors sigma A := by
    exact ⟨hmissSigmaA beta hbetaA, hmissSigmaA alpha halphaA⟩
  have hgammaOutside : beta ∉ Gamma ∧ alpha ∉ Gamma := by
    exact ⟨hbetaNot.1, hgamma⟩
  have hpenultimateMissing : ∀ x, x ∈ TreeSequenceVertexSet B →
      MissingColors G sigma x = MissingColors G phi x := hmissEq
  have hfirstEqB (eta : Fin k) :
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
    exact @helper_hfirstEqB_873 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C alpha beta hmissEq eta
  have posMissing (psi : PartialEdgeColoring E k) (eta : Fin k)
      (hp : (HierarchyFirstMissingPosition psi T eta).val < T.length) :
      eta ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T eta)) := by
    unfold HierarchyFirstMissingPosition at hp ⊢
    by_cases hc : (Finset.univ.filter fun i : Fin (T.length + 1) =>
        eta ∈ MissingColors G psi (T.vertex i)).Nonempty
    · rw [dite_eq_left hc] at hp ⊢
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2
    · simp [dite_eq_right hc, Fin.val_last] at hp
  have posLe (psi : PartialEdgeColoring E k) (eta : Fin k)
      (i : Fin (T.length + 1))
      (hm : eta ∈ MissingColors G psi (T.vertex i)) :
      (HierarchyFirstMissingPosition psi T eta).val ≤ i.val := by
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      eta ∈ MissingColors G psi (T.vertex j)
    have hc : candidates.Nonempty := ⟨i, by simp [candidates, hm]⟩
    have heq : HierarchyFirstMissingPosition psi T eta = candidates.min' hc := by
      simp [HierarchyFirstMissingPosition, candidates, hc]
    rw [heq]
    exact Finset.min'_le candidates i (by simp [candidates, hm])
  have transportAtLast (eta : Fin k) (psi : PartialEdgeColoring E k)
      (hp : (HierarchyFirstMissingPosition psi T eta).val = B.length)
      (hm : eta ∈ MissingColors G psi
        (T.vertex (HierarchyFirstMissingPosition psi T eta))) :
      eta ∈ MissingColors G psi (B.vertex (Fin.last B.length)) := by
    have hcast : Fin.castLE (Nat.succ_le_succ hBT.1) (Fin.last B.length) =
        HierarchyFirstMissingPosition psi T eta := by
      apply Fin.ext
      simp [hp]
    rw [← hBT.2.1 (Fin.last B.length), hcast]
    exact hm
  have hstoredFirst : ∀ eta, eta ∈ D →
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta := by
    exact @helper_hstoredFirst_499 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C alpha beta hmissB hlenB hBT hmissEq hfirstEqB posMissing
        posLe transportAtLast
  have hcase :
      (0 < H.dividerCount ∧ beta ∈ TreeMissingColors phi
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧
          (beta ∈ TreeMissingColors phi Tn ∨
            (beta ∈ TreeMissingColors phi A ∧
              beta ∉ TashkinovStoredColors ett.series.data n ∧
                alpha ∉ TashkinovStoredColors ett.series.data n))) := by
    exact @helper_hcase_921 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C alpha beta hbetaTn hbetaA
  have stableResult := StableChangeCasesOneTwoStarredTail G k e0 input T phi
    ett base C ctx beta alpha hne hmissB (Sum.inl w) hpath sigma hsigma hcase
    hdisjoint hstarSigma hgammaOutside hpenultimateMissing hstoredFirst
  rcases stableResult with ⟨weak, mod, corrT, maxT, baseT, K, goodT, sameT⟩
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
    exact @helper_seriesProper_846 V E inferInstance inferInstance inferInstance G k e0 input T
        phi ett
  have seriesOne : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    exact @helper_seriesOne_873 V E inferInstance inferInstance inferInstance G k e0 input T phi ett
  let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := seriesProper
    replacementOneUncolored := seriesOne
    replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := phi
    corresponding := selfCorr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    minimumContext := ctx }
  have hbetaU : beta ∈ MissingColors G sigma u := by
    have hOld := huData.1.2
    have huB := TreeSequenceInitialSegmentVertexSetSubset hAB huData.1.1
    change beta ∈ MissingColors G phi u at hOld
    exact (hmissEq u huB).symm ▸ hOld
  let Cnew : HierarchyCounterexample baseT := {
    positive := by simpa [corrT.rungAgreement] using C.positive
    hierarchy := K
    good := goodT
    maximum := maxT
    notElementary := by
      intro helem
      have huT := TreeSequenceInitialSegmentVertexSetSubset hAT huData.1.1
      have hwT : w ∈ TreeSequenceVertexSet T := by
        simp [w, TreeSequenceVertexSet]
      exact (Finset.disjoint_left.mp (helem huT hwT hwu.symm) hbetaU hbetaW) }
  have transResult := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx P0 sigma corrT baseT Cnew sameT
  rcases transResult with ⟨P, hPcolor⟩
  let H' := P.counterexample.hierarchy
  let q' : Fin (H'.dividerCount + 1) := Fin.last H'.dividerCount
  let Tn' := P.corresponding.replacementETT.series.data.tree
    (Fin.last P.corresponding.replacementETT.rounds).castSucc
  have hStages := P.sameGood.1
  have hcore : base.core = P.replacementBase.core := hStages.1
  have hcount : H.dividerCount = H'.dividerCount := P.sameGood.2.choose
  have hAt := (P.sameGood.2.choose_spec) q
  have hqcast : Fin.cast (congrArg (fun m => m + 1) hcount) q = q' := by
    apply Fin.ext
    simp [q, q']
  have hD' : D = HierarchyStoredColorsAt H' q' := by
    simpa [D, q', hqcast] using hAt.1
  have hGammaPair : ∀ eta, eta ∈ D →
      C.good.gamma q eta = P.counterexample.good.gamma q' eta := by
    intro eta heta
    simpa [q', hqcast] using hAt.2 eta heta
  have hGammaEq :
      (HierarchyStoredColorsAt H' q').biUnion (P.counterexample.good.gamma q') = Gamma := by
    apply Finset.ext
    intro c
    change c ∈ (HierarchyStoredColorsAt H' q').biUnion
        (P.counterexample.good.gamma q') ↔ c ∈ D.biUnion (C.good.gamma q)
    rw [Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨eta, heta, hc⟩
      have hetaD : eta ∈ D := hD'.symm ▸ heta
      exact ⟨eta, hetaD, (hGammaPair eta hetaD).symm ▸ hc⟩
    · rintro ⟨eta, heta, hc⟩
      exact ⟨eta, hD' ▸ heta, (hGammaPair eta heta) ▸ hc⟩
  have hfinalTree : Tn' = Tn := by
    exact @helper_hfinalTree_741 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx alpha beta P hcount
  have hExtraEq :
      ((TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn').biUnion
        fun v => MissingColors G P.coloring v) = M0 := by
    exact @helper_hExtraEq_799 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx alpha hCoreB beta hmissEq P hPcolor hcore hfinalTree
  refine ⟨P, beta, ?_, ?_, ?_⟩
  · rw [hPcolor]
    simpa [w] using hbetaW
  · rw [hPcolor]
    simpa [A, H, q] using hstarSigma.1
  · change beta ∉
      (HierarchyStoredColorsAt H' q').biUnion (P.counterexample.good.gamma q') ∪
        ((TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn').biUnion
          fun v => MissingColors G P.coloring v)
    rw [hGammaEq, hExtraEq]
    simpa [Finset.mem_union] using hbetaNot

private theorem helper_continuation_882.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (2 : ℕ) ≤
        HierarchyPathNumber C.hierarchy → HierarchyPathNumber C.hierarchy <
        HierarchyFullTailLength C →
    ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)), alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) → (alpha ∈
        (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)).biUnion fun (v : V) ↦ MissingColors G phi v) → alpha ∉
        (HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
        (C.good.gamma (Fin.last C.hierarchy.dividerCount)) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
    let M0 : Finset (Fin k) := (TreeSequenceVertexSet base.core \ TreeSequenceVertexSet
        Tn).biUnion fun (v : V) ↦ MissingColors G phi v; ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T → TreeSequenceInitialSegment A
        B → TreeSequenceInitialSegment base.core B → TreeSequenceInitialSegment Tn A → (
    ∀ {X Y : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeMissingColors phi X ⊆
        TreeMissingColors phi Y) →
    ∀ beta ∈ TreeMissingColors phi Tn, beta ∉ Gamma ∧ beta ∉ M0 →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∃ beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)), beta ∈ TreeMissingColors
        P.coloring (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) ∧
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc; beta ∉ (HierarchyStoredColorsAt H
        q).biUnion (P.counterexample.good.gamma q) ∪ (TreeSequenceVertexSet P.replacementBase.core
        \ TreeSequenceVertexSet Tn).biUnion fun (v : V) ↦ MissingColors G P.coloring v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper alpha hterminal hstar
      hextra hgamma H q A ell B n Tn D Gamma M0 hpen hAT hAB hCoreB hTnA treeMissingMono beta
      hbetaTn hbetaNot
  have hbetaA : beta ∈ TreeMissingColors phi A :=
    treeMissingMono hTnA hbetaTn
  have halphaA : alpha ∈ TreeMissingColors phi A := by
    simpa [A, q, H] using hstar
  have hne : beta ≠ alpha := by
    intro heq
    exact hbetaNot.2 (heq ▸ hextra)
  have hmissB : beta ∈ TreeMissingColors phi B ∧ alpha ∈ TreeMissingColors phi B := by
    exact ⟨treeMissingMono hAB hbetaA, treeMissingMono hAB halphaA⟩
  have horderedUnused :
      let ia := HierarchyFirstMissingPosition phi T beta
      let ib := HierarchyFirstMissingPosition phi T alpha
      (beta ∉ TreeMissingColors phi A ∨ alpha ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          beta ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧ phi (T.edge t) = some c) := by
    intro ia ib hnot
    rcases hnot with hn | hn
    · exact False.elim (hn hbetaA)
    · exact False.elim (hn halphaA)
  have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
    ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hpen ctx.largeMissingSet beta alpha hne hmissB
    horderedUnused
  have hsame :
      TwoColorComponent G phi beta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
        TwoColorComponent G phi beta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) := by
    exact @helper_hsame_665 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C alpha beta hbetaTn hbetaA hchange
  have firstWitness (c : Fin k) (hc : c ∈ TreeMissingColors phi A) :
      (T.vertex (HierarchyFirstMissingPosition phi T c) ∈ TreeSequenceVertexSet A ∧
        c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c))) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ A.length := by
    exact @helper_firstWitness_341 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C hAT c hc
  have huData := firstWitness beta hbetaA
  have hvData := firstWitness alpha halphaA
  let u := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let v := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let w := T.vertex (Fin.last T.length)
  have hell : 3 ≤ ell := by
    have hp := hpathLower
    have hq := hpathUpper
    dsimp [ell, HierarchyFullTailLength] at hq
    omega
  have hlenAT : A.length < T.length := by
    change 3 ≤ T.length - A.length at hell
    omega
  have hlenB : B.length + 1 = T.length := by
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    change 3 ≤ T.length - A.length at hell
    have hsum : A.length + (T.length - A.length - 1) = T.length - 1 := by omega
    rw [hsum, Nat.min_eq_left (by omega)]
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hwu : w ≠ u := by
    intro heq
    have hidx := T.vertex_injective heq.symm
    have hpos : (HierarchyFirstMissingPosition phi T beta).val < T.length :=
      lt_of_le_of_lt huData.2 hlenAT
    have : (HierarchyFirstMissingPosition phi T beta).val = T.length := by
      exact congrArg Fin.val hidx
    omega
  have hwv : w ≠ v := by
    intro heq
    have hidx := T.vertex_injective heq.symm
    have hpos : (HierarchyFirstMissingPosition phi T alpha).val < T.length :=
      lt_of_le_of_lt hvData.2 hlenAT
    have hlast : (HierarchyFirstMissingPosition phi T alpha).val = T.length := congrArg Fin.val hidx
    omega
  have hterminalAlpha : alpha ∈ MissingColors G phi w := by simpa [w] using hterminal
  have terminalData := P2905_T2_ElementaryTerminalComponent G phi beta alpha hne
    ctx.proper (TreeSequenceVertexSet B) hpen u v w
    (TreeSequenceInitialSegmentVertexSetSubset hAB huData.1.1)
    (TreeSequenceInitialSegmentVertexSetSubset hAB hvData.1.1) hwu hwv
    huData.1.2 hvData.1.2 (Or.inr hterminalAlpha) hsame
  have hdisjoint := terminalData.1
  have hpath := terminalData.2.1
  have hmissEq := terminalData.2.2
  let sigma := TwoColorComponentSwap G phi beta alpha (Sum.inl w)
  have hsigma : sigma = TwoColorComponentSwap G phi beta alpha (Sum.inl w) := rfl
  obtain ⟨outside, betaGain, alphaGain, unaffected⟩ :=
    TwoColorComponentSwapMissingBehavior G phi beta alpha hne ctx.proper (Sum.inl w)
  have hbetaW : beta ∈ MissingColors G sigma w := by
    exact alphaGain w (by rfl) hterminalAlpha
  have hmissSigmaA : ∀ c ∈ TreeMissingColors phi A,
      c ∈ TreeMissingColors sigma A := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    obtain ⟨x, hx, hcx⟩ := hc
    have hxB := TreeSequenceInitialSegmentVertexSetSubset hAB hx
    exact ⟨x, hx, (hmissEq x hxB).symm ▸ hcx⟩
  exact @helper_continuation_903 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha hgamma hAT hAB hCoreB beta hbetaTn hbetaNot hbetaA
      halphaA hne hmissB huData hlenB hBT hwu hdisjoint hpath hmissEq hsigma hbetaW hmissSigmaA
theorem P2905_T2_BaseExtraReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (alpha : Fin k)
    (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hstar : alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)))
    (hextra : alpha ∈ ((TreeSequenceVertexSet base.core \
        TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion
        fun v => MissingColors G phi v))
    (hgamma : alpha ∉ (HierarchyStoredColorsAt C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).biUnion (C.good.gamma (Fin.last C.hierarchy.dividerCount))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
    ∃ beta : Fin k,
    beta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
      beta ∈
          TreeMissingColors P.coloring
            (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) ∧
        (let H := P.counterexample.hierarchy
        let q := Fin.last H.dividerCount
        let Tn :=
          P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc
        beta ∉
          (HierarchyStoredColorsAt H q).biUnion (P.counterexample.good.gamma q) ∪
            ((TreeSequenceVertexSet P.replacementBase.core \
                  TreeSequenceVertexSet Tn).biUnion
              fun v => MissingColors G P.coloring v)) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (C.good.gamma q)
  let M0 := ((TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G phi v)
  have segTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) : TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, hvxy, hexy⟩
    rcases hYZ with ⟨hyz, hvyz, heyz⟩
    refine ⟨hxy.trans hyz, ?_, ?_⟩
    · intro i
      exact (hvyz (Fin.castLE (Nat.succ_le_succ hxy) i)).trans (hvxy i)
    · intro i
      exact (heyz (Fin.castLE hxy i)).trans (hexy i)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have hpen : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    intro u hu v hv huv
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi
      ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet (u := u) hu (v := v) hv huv
  have hAT : TreeSequenceInitialSegment A T := by
    have hstep : TreeSequenceInitialSegment
        (HierarchyStarredStage H q) (H.stage q.succ) := by
      cases q using Fin.cases with
      | zero => exact H.coreInsideFirst
      | succ i => exact H.nested i.succ
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp [q]
    rw [← H.terminalStage]
    simpa only [hlast] using hstep
  have hlenAB : A.length ≤ B.length := by
    change A.length ≤ min (A.length + (ell - 1)) T.length
    have hp := hpathUpper
    have hl := hpathLower
    dsimp [ell, H, HierarchyFullTailLength] at hp hl
    have ht := hAT.1
    omega
  have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩ hlenAB
  have hTnCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · obtain ⟨_, _, hu⟩ := base.parallel hp
      rcases hu with ⟨u⟩
      exact u.leftSegment
    · have heq : base.core = Tn := base.nonparallel hp
      rw [heq]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hCoreB : TreeSequenceInitialSegment base.core B := by
    exact @helper_hCoreB_124 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C alpha hstar segTrans hAB
  have hTnB : TreeSequenceInitialSegment Tn B := segTrans hTnCore hCoreB
  have hcoreA : TreeSequenceInitialSegment base.core A := by
    exact @helper_hcoreA_183 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C segTrans
  have hTnA : TreeSequenceInitialSegment Tn A := segTrans hTnCore hcoreA
  have treeMissingMono {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors phi X ⊆ TreeMissingColors phi Y := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    obtain ⟨v, hv, hvc⟩ := hc
    exact ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hvc⟩
  have hMdis : Disjoint (TreeMissingColors phi Tn) M0 := by
    exact @helper_hMdis_717 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hpen hCoreB hTnB
  have hDcard : D.card ≤ ett.rounds := by
    simpa [D, H, q] using HierarchyStoredColorsCardinality H (Fin.last H.dividerCount)
  have hGammacard : Gamma.card ≤ 2 * ett.rounds := by
    calc
      Gamma.card ≤ ∑ eta ∈ D, (C.good.gamma q eta).card := Finset.card_biUnion_le
      _ = D.card * 2 := by
        calc
          (∑ eta ∈ D, (C.good.gamma q eta).card) = ∑ eta ∈ D, 2 := by
            apply Finset.sum_congr rfl
            intro eta heta
            exact C.good.twoColors q eta heta
          _ = D.card * 2 := by simp
      _ ≤ 2 * ett.rounds := by omega
  have hlarge : 2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card := by
    simpa [Tn, n] using ctx.largeMissingSet
  have hbetaSet : (TreeMissingColors phi Tn \ (Gamma ∪ M0)).Nonempty := by
    exact @helper_hbetaSet_749 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C hMdis hGammacard hlarge
  obtain ⟨beta, hbeta⟩ := hbetaSet
  have hbetaTn : beta ∈ TreeMissingColors phi Tn := (Finset.mem_sdiff.mp hbeta).1
  have hbetaNot : beta ∉ Gamma ∧ beta ∉ M0 := by
    have := (Finset.mem_sdiff.mp hbeta).2
    simpa [Finset.mem_union] using this
  exact @helper_continuation_882 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hpathLower hpathUpper alpha hterminal hstar hextra hgamma
      hpen hAT hAB hCoreB hTnA treeMissingMono beta hbetaTn hbetaNot
end GoldbergSeymour

end
