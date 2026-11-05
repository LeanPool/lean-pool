/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans

/-!
# Hierarchy Claim Nine First Use After Seed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperCs723.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [ Fintype V] →
            [ Fintype E] →
              [ DecidableEq V] →
                [ DecidableEq E] →
                  (G : LooplessMultigraph V E) →
                    (k : ℕ) →
                      (e0 : E) →
                        (input : PartialEdgeColoring E k) →
                          (T : TreeSequence G e0) →
                            (phi : PartialEdgeColoring E k) →
                              (ett : ExtendedTashkinovTree G k e0 input T phi) →
                                (base : HierarchyBase ett phi) →
                                  (C : HierarchyCounterexample base) →
                                    (ctx :
                                        HierarchyMinimumCounterexampleContext G k e0 input T phi ett
                                          base C) →
                                      (P :
                                          HierarchyReplacementPresentation G k e0 input T phi ett
                                            base C ctx) →
                                        (alpha : Fin k) →
                                          (j : ℕ) →
                                            let mu : PartialEdgeColoring E k := P.coloring;
                                            let em :
                                              ExtendedTashkinovTree G k e0
                                                P.corresponding.replacementInput T P.coloring :=
                                              P.corresponding.replacementETT;
                                            let Cm : HierarchyCounterexample P.replacementBase :=
                                              P.counterexample;
                                            let H :
                                              TashkinovHierarchy P.corresponding.replacementETT
                                                P.replacementBase :=
                                              Cm.hierarchy;
                                            let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                              Fin.last H.dividerCount;
                                            let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                            let ell : ℕ := HierarchyFullTailLength Cm;
                                            let B : TreeSequence G e0 :=
                                              HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
                                            let X : TreeSequence G e0 :=
                                              HierarchyFullTailPrefix Cm (j - (1 : ℕ));
                                            let y : V := T.vertex (Fin.last T.length);
                                            (hsum : A.length + ell = T.length) →
                                              (hXT : TreeSequenceInitialSegment X T) →
                                                let ip : Fin (T.length + (1 : ℕ)) :=
                                                  (⟨X.length, by
                                                      have this : X.length ≤ T.length := hXT.1;
                                                      omega⟩ :
                                                    Fin (T.length + (1 : ℕ)));
                                                let x : V := T.vertex ip;
                                                x ∈ TreeSequenceVertexSet B →
                                                  (beta : Fin k) →
                                                    beta ∈ MissingColors G mu x →
                                                      x ≠ y →
                                                        let sigma : PartialEdgeColoring E k :=
                                                          TwoColorComponentSwap G mu alpha beta
                                                            (Sum.inl y);
                                                        (∀ v ∈ TreeSequenceVertexSet B,
                                                            MissingColors G sigma v =
                                                              MissingColors G mu v) →
                                                          beta ∈ MissingColors G sigma y →
                                                            (corr :
                                                                CorrespondingExtendedTashkinovTree G
                                                                  k e0 em sigma T) →
                                                              MaximumProperty corr.replacementETT →
                                                                (bs :
                                                                    HierarchyBase
                                                                      corr.replacementETT sigma) →
                                                                  (K :
                                                                      TashkinovHierarchy
                                                                        corr.replacementETT bs) →
                                                                    GoodHierarchy K →
                                                                      x ∈ TreeSequenceVertexSet T →
                                                                        y ∈
                                                                            TreeSequenceVertexSet
                                                                              T →
                                                                          HierarchyCounterexample
                                                                            bs := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j mu em Cm H q A ell B X y hsum hXT ip
      x hxB beta hbeta hxy sigma hmissingB hbetaNewY corr hmax bs K good hxT hyT
  exact {
    positive := by rw [corr.rungAgreement]; exact Cm.positive
    hierarchy := K
    good := good
    maximum := hmax
    notElementary := by
      intro he
      have hbnew : beta ∈ MissingColors G sigma x := by rw [hmissingB x hxB]; exact hbeta
      exact Finset.disjoint_left.mp (he hxT hyT hxy) hbnew hbetaNewY }

private abbrev helperContinuation1607Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ), (2 : ℕ) ≤ j → j ≤ HierarchyFullTailLength C →
    ∀ (ej : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
        (P.coloring (T.edge ej) = some alpha ∧
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑ej : ℕ) → P.coloring (T.edge t) ≠
        some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); (
    ∀ (i : ℕ), HierarchyFullTailPrefix C i = HierarchyFullTailPrefix Cm i) → j ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        → A.length + ell = T.length → B.length = T.length - (1 : ℕ) → X.length = A.length + (j -
        (1 : ℕ)) → A.length < X.length → X.length ≤ B.length → TreeSequenceInitialSegment B T →
    ∀ (hXT : TreeSequenceInitialSegment X T), (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment A X →
        TreeSequenceInitialSegment X B → TreeSequenceInitialSegment A B →
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    have this : X.length ≤ T.length := hXT.1; Decidable.byContradiction fun (a : ¬X.length <
        T.length + (1 : ℕ)) ↦
    by
      have := GoldbergSeymour.TreeSequence.positive T
      have := GoldbergSeymour.TreeSequence.positive A
      have := GoldbergSeymour.TreeSequence.positive B
      have := GoldbergSeymour.TreeSequence.positive X
      omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; X.vertex (Fin.last X.length) = x → x ∈ TreeSequenceVertexSet X → x ∈
        TreeSequenceVertexSet B → j - (1 : ℕ) ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1
        : ℕ)) →
    ∀ beta ∈ MissingColors G mu x, alpha ∈ TreeMissingColors mu A → alpha ≠ beta → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → (↑ia : ℕ) ≤ A.length → ib = ip → a ∈
        TreeSequenceVertexSet A → a ∈ TreeSequenceVertexSet B → alpha ∈ TreeMissingColors mu B ∧
        beta ∈ TreeMissingColors mu B → (↑ej : ℕ) = X.length → x ≠ y → Disjoint (TwoColorComponent
        G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) (TwoColorComponent G
        P.coloring alpha beta (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T
        alpha)))) → TwoColorPathComponent G mu alpha beta (Sum.inl y) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (0 :
        ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors mu (H.stage (⟨H.dividerCount,
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive A
                        have := GoldbergSeymour.TreeSequence.positive B
                        have := GoldbergSeymour.TreeSequence.positive X
                        omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨ alpha ∈ TreeMissingColors mu A ∧
        alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧ beta ∉
        TashkinovStoredColors em.series.data (Fin.last em.rounds)) → (if em.series.data.kind
        (Fin.last em.rounds) = some TashkinovExtensionKind.PE then CombinedStableColoring
        (em.series.data.tree (Fin.last em.rounds).castSucc) bm.closure (TashkinovStoredColors
        em.series.data (Fin.last em.rounds)) mu sigma else StableColoring (em.series.data.tree
        (Fin.last em.rounds).castSucc) (TashkinovStoredColors em.series.data (Fin.last em.rounds))
        mu sigma) → IsOneEdgeUncolored sigma e0 → HierarchyWeaklyStable H q sigma → (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ v ∈ TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength
        P.counterexample - (1 : ℕ))), MissingColors G (TwoColorComponentSwap G P.coloring alpha
        beta (Sum.inl (T.vertex (Fin.last T.length)))) v = MissingColors G P.coloring v) → beta ∈
        MissingColors G sigma y → (
    ∀ (t : Fin T.length), (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length ≤ (↑t : ℕ) → (↑t : ℕ) <
        (HierarchyFullTailPrefix P.counterexample (j - (1 : ℕ))).length → TwoColorComponentSwap G
        P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length))) (T.edge t) = P.coloring
        (T.edge t)) → j - (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett
        base C ctx

private theorem helper_hAT_246.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P Cm H q A
  have hs : TreeSequenceInitialSegment (HierarchyStarredStage H q) (H.stage q.succ) := by
    refine Fin.cases ?_ (fun i => ?_) q
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
  simpa only [hlast, H.terminalStage] using hs

private theorem helper_commonPrefix_268.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U
        W → S.length ≤ U.length → TreeSequenceInitialSegment S U := by
  classical
  intro V E G e0 S U W hSW hUW hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)

private theorem helper_hyNotB_289.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (ej : Fin
        T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); A.length + ell = T.length → B.length = T.length -
        (1 : ℕ) → X.length = A.length + (j - (1 : ℕ)) → X.length ≤ B.length →
        TreeSequenceInitialSegment B T → y ∉ TreeSequenceVertexSet B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P j ej hej Cm H q A ell B X y hsum hBlen
      hXlen hXleB hBT hy
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, hi⟩ := hy
  have he := T.vertex_injective ((hBT.2.1 i).trans hi)
  have hv := congrArg Fin.val he
  have := i.isLt
  simp only [Fin.val_castLE, Fin.val_last] at hv
  omega

private theorem helper_firstSpec_312.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (T : TreeSequence G e0) (_ : ℕ) (rho : PartialEdgeColoring E k)
      (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
    c ∈ MissingColors G rho (T.vertex i) →
    c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      HierarchyFirstMissingPosition rho T c ≤ i := by
  classical
  intro V E _ _ G k e0 T j rho c i hi
  let _ := Fintype.ofFinite V
  let s : Finset (Fin (T.length + 1)) :=
    Finset.univ.filter fun j => c ∈ MissingColors G rho (T.vertex j)
  have his : i ∈ s := by simp [s, hi]
  have hs : s.Nonempty := ⟨i, his⟩
  have hp : HierarchyFirstMissingPosition rho T c = s.min' hs := by
    simp only [HierarchyFirstMissingPosition, s, dite_eq_left hs]
  rw [hp]
  exact ⟨(Finset.mem_filter.mp (Finset.min'_mem s hs)).2, Finset.min'_le s i his⟩

private theorem helper_hib_340.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k) (j : ℕ) (_
        : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) →
    ∀ (_ : A.length + ell = T.length), B.length = T.length - (1 : ℕ) → X.length ≤ B.length →
        TreeSequenceInitialSegment B T →
    ∀ (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; x ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu x, (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta; ib = ip := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm H q A ell B X helem hsum
      hBlen hXleB hBT hXT ip x hxB beta hbeta firstSpec ib
  have hs := firstSpec mu beta ip hbeta
  have hbound : ib.val ≤ B.length := le_trans hs.2 hXleB
  let i : Fin (B.length + 1) := ⟨ib.val, by omega⟩
  have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i = ib := Fin.ext rfl
  have hbB : T.vertex ib ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (hBT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
  have hv : T.vertex ib = x := by
    by_contra hn
    exact Finset.disjoint_left.mp (helem hbB hxB hn) hs.1 hbeta
  exact T.vertex_injective hv

private theorem helper_hordered_369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (ej : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
        (P.coloring (T.edge ej) = some alpha ∧
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑ej : ℕ) → P.coloring (T.edge t) ≠
        some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    ∀ (_ : A.length + ell = T.length), X.length = A.length + (j - (1 : ℕ)) → A.length < X.length →
    ∀ (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (beta : Fin k),
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
    let a : V := T.vertex ia; (↑ia : ℕ) ≤ A.length → ib = ip → (↑ej : ℕ) = X.length → alpha ∉
        TreeMissingColors mu A ∨ beta ∉ TreeMissingColors mu A → TreeVertexOrder T a (T.vertex ib)
        ∧ alpha ∉ ({c : Fin k |
    ∃ (t : Fin T.length), A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ mu (T.edge t) = some c} :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej hej hfirst mu Cm H q A ell X
      hsum hXlen hAXstrict hXT ip beta ia ib a hia hib hejX _
  refine ⟨⟨ia, ib, rfl, rfl, ?_⟩, ?_⟩
  · rw [hib]
    change ia.val < X.length
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨t, ht, hlt, he⟩
    have hltX : t.val < X.length := by simpa only [hib] using hlt
    exact hfirst.2 t ht (by omega) he

private theorem helper_hsame_386.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k), (
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds; (0 : ℕ) < H.dividerCount ∧ alpha ∈
        TreeMissingColors P.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ alpha ∈ TreeMissingColors
        P.coloring (P.corresponding.replacementETT.series.data.tree n.castSucc)) →
    ∀ (j : ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    ∀ (_ : A.length + ell = T.length) (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip;
    ∀ (beta : Fin k),
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
    let a : V := T.vertex ia; ib = ip → (
    let H : TashkinovHierarchy em bm := Cm.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors em.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition mu T alpha);
    have vb : V := T.vertex (HierarchyFirstMissingPosition mu T beta);
    have sameComponent : Prop := TwoColorComponent G mu alpha beta (Sum.inl va) =
        TwoColorComponent G mu alpha beta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors mu Tnq ∨ Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors mu
        Tn ∨ Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (alpha ∈ TreeMissingColors mu A ∧ TreeColorSetClosed G mu A ({ alpha } :
        Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A mu alpha beta)) →
        TwoColorComponent G mu alpha beta (Sum.inl a) = TwoColorComponent G mu alpha beta (Sum.inl
        x) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha hnormalized j ej mu em bm Cm H q A
      ell X hsum hXT ip x beta ia ib a hib changeResult
  have hc : TwoColorComponent G mu alpha beta (Sum.inl a) =
      TwoColorComponent G mu alpha beta (Sum.inl (T.vertex ib)) := by
    rcases hnormalized with hp | hz
    · exact changeResult.1 ⟨hp.1, Or.inl hp.2⟩
    · exact changeResult.2.1 ⟨hz.1, Or.inl hz.2⟩
  simpa only [hib] using hc

private theorem helper_leaf_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ)); j ≤ ell →
    ∀ (_ : A.length + ell = T.length) (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; X.vertex (Fin.last X.length) = x →
    ∀ (beta : Fin k), alpha ≠ beta →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu alpha beta;
    ∀ (v : V), alpha ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v → (J.neighborSet
        (Sum.inl v)).Subsingleton := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm cm H q A ell X hj hsum
      hXT ip x hx beta hne J v hv
  have hd : @SimpleGraph.degree _ J (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
    rcases hv with hv | hv
    · exact MissingColorIncidenceEndpoint G mu alpha beta hne cm.proper v hv
    · have hj : J = TwoColorIncidenceGraph G mu beta alpha := by
        ext x z
        cases x <;> cases z <;> simp [J, TwoColorIncidenceGraph, or_comm]
      rw [hj]
      exact MissingColorIncidenceEndpoint G mu beta alpha hne.symm cm.proper v hv
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
  intro x hx z hz
  exact Finset.card_le_one_iff.mp hd
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hx)
    (by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet] using hz)

private theorem helper_hdisjoint_416.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (_ : A.length + ell = T.length) (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip;
    ∀ beta ∈ MissingColors G mu x, alpha ∈ MissingColors G mu y →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → a ≠ x → TwoColorComponent G mu alpha
        beta (Sum.inl a) = TwoColorComponent G mu alpha beta (Sum.inl x) →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu alpha beta;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v)) → (
    ∀ (v : V), alpha ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v → (J.neighborSet
        (Sum.inl v)).Subsingleton) → a ≠ y → x ≠ y → Disjoint Q (TwoColorComponent G mu alpha beta
        (Sum.inl a)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm cm H q A ell X y hsum
      hXT ip x beta hbeta haY ia a ha hab hsame J Q self leaf hay hxy
  rcases TwoColorComponentsDisjoint G mu alpha beta (Sum.inl y) (Sum.inl a) with heq | hd
  · obtain ⟨u, v, path, hp, hs⟩ :=
      TwoColorComponentSpanningPath G mu alpha beta cm.proper (Sum.inl y)
    have endpoint (w : V) (hw : Sum.inl w ∈ Q)
        (hl : Set.Subsingleton (J.neighborSet (Sum.inl w))) :
        Sum.inl w = u ∨ Sum.inl w = v := by
      have hm : Sum.inl w ∈ path.support := by
        change Sum.inl w ∈ {x | x ∈ path.support}
        rw [hs]
        exact hw
      by_contra hn
      push Not at hn
      exact hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hl hm
    change Q = TwoColorComponent G mu alpha beta (Sum.inl a) at heq
    have haQ : Sum.inl a ∈ Q := by rw [heq]; exact self a
    have hbQ : Sum.inl x ∈ Q := by rw [heq, hsame]; exact self x
    have hae := endpoint a haQ (leaf a (Or.inl ha))
    have hbe := endpoint x hbQ (leaf x (Or.inr hbeta))
    have hye := endpoint y (self y) (leaf y (Or.inl haY))
    have hnab : (Sum.inl a : Sum V E) ≠ Sum.inl x := fun h => hab (Sum.inl.inj h)
    have hnay : (Sum.inl a : Sum V E) ≠ Sum.inl y := fun h => hay (Sum.inl.inj h)
    have hnby : (Sum.inl x : Sum V E) ≠ Sum.inl y := fun h => hxy (Sum.inl.inj h)
    rcases hae with hae | hae <;> rcases hbe with hbe | hbe <;>
      rcases hye with hye | hye <;> simp_all
  · exact hd

private theorem helper_edgeOfVertex_465.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (beta : Fin k),
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu alpha beta;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y);
    ∀ {v : V} {f : E}, Sum.inl v ∈ Q → Incident G v f → mu f = some alpha ∨ mu f = some beta →
        Sum.inr f ∈ Q := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu y beta J Q v f hv hf hc
  change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl y) at hv
  change J.connectedComponentMk (Sum.inr f) = J.connectedComponentMk (Sum.inl y)
  have hadj : J.Adj (Sum.inr f) (Sum.inl v) := by
    simpa only [J, TwoColorIncidenceGraph] using And.intro hf hc
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv

private theorem helper_hmissingB_473.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) →
    ∀ (_ : A.length + ell = T.length) (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; x ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu x, alpha ≠ beta →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → a ∈ TreeSequenceVertexSet B →
        TwoColorComponent G mu alpha beta (Sum.inl a) = TwoColorComponent G mu alpha beta (Sum.inl
        x) →
    let Q : Set (V ⊕ E) := TwoColorComponent G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v)) → Disjoint Q
        (TwoColorComponent G mu alpha beta (Sum.inl a)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G mu alpha beta (Sum.inl y) → MissingColors G
        (TwoColorComponentSwap G mu alpha beta (Sum.inl y)) v = MissingColors G mu v) → (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ {v : V} {f : E}, Sum.inl v ∈ Q → Incident G v f → mu f = some alpha ∨ mu f = some beta →
        Sum.inr f ∈ Q) →
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm H q A ell B X y helem
      hsum hXT ip x hxB beta hbeta hne ia a ha haB hsame Q self hdisjoint sigma missingOutside
      missingOther edgeOfVertex v hv
  by_cases hvQ : Sum.inl v ∈ Q
  · have hva : v ≠ a := by
      intro he
      subst v
      exact Set.disjoint_left.mp hdisjoint hvQ (self a)
    have hvb : v ≠ x := by
      intro he
      subst v
      apply Set.disjoint_left.mp hdisjoint hvQ
      rw [hsame]
      exact self x
    have hna : alpha ∉ MissingColors G mu v := fun hm =>
      Finset.disjoint_left.mp (helem hv haB hva) hm ha
    have hnb : beta ∉ MissingColors G mu v := fun hm =>
      Finset.disjoint_left.mp (helem hv hxB hvb) hm hbeta
    obtain ⟨fa, hfa, hfca⟩ : ∃ f, Incident G v f ∧ mu f = some alpha := by
      simpa [MissingColors, PresentColors] using hna
    obtain ⟨fb, hfb, hfcb⟩ : ∃ f, Incident G v f ∧ mu f = some beta := by
      simpa [MissingColors, PresentColors] using hnb
    have hfaQ := edgeOfVertex hvQ hfa (Or.inl hfca)
    have hfbQ := edgeOfVertex hvQ hfb (Or.inr hfcb)
    simp only [Q] at hfaQ hfbQ
    have hnewa : sigma fb = some alpha := by
      simp [sigma, TwoColorComponentSwap, hfbQ, hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      simp [sigma, TwoColorComponentSwap, hfaQ, hfca]
    have hnsa : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fb, hfb, hnewa⟩
    have hnsb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp only [hna, hnsa]
    by_cases hcb : c = beta
    · subst c; simp only [hnb, hnsb]
    exact missingOther v c hca hcb
  · exact missingOutside v hvQ

private theorem helper_seedIncident_520.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (f : E), TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds) → em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.RE → em.series.data.connectingEdges (Fin.last em.rounds) = ({ f } :
        Finset E) → TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P em f hstep hkind hedges
  generalize hn : Fin.last em.rounds = r at hstep hkind hedges ⊢
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [initialKind] at hkind
      simp at hkind
  | SE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      have he : choice.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
      rw [← he]
      exact ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
  | PE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
      rw [currentKind] at hkind
      simp at hkind
  | RE r previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
      have he : available.edge = f := Finset.singleton_injective (currentEdges.symm.trans hedges)
      rw [← he]
      refine ⟨available.insideEndpoint, available.insideInCurrent, ?_⟩
      simp only [Incident, available.edgeEnds, Sym2.mem_iff, true_or]

private theorem helper_hfixedPrefix_556.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (ej : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
        (P.coloring (T.edge ej) = some alpha ∧
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑ej : ℕ) → P.coloring (T.edge t) ≠
        some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) →
    ∀ (_ : A.length + ell = T.length), X.length = A.length + (j - (1 : ℕ)) → A.length < X.length →
    ∀ (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; X.vertex (Fin.last X.length) = x →
    ∀ beta ∈ MissingColors G mu x, (↑ej : ℕ) = X.length →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (if
        em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (em.series.data.tree (Fin.last em.rounds).castSucc) bm.closure
        (TashkinovStoredColors em.series.data (Fin.last em.rounds)) mu sigma else StableColoring
        (em.series.data.tree (Fin.last em.rounds).castSucc) (TashkinovStoredColors em.series.data
        (Fin.last em.rounds)) mu sigma) → (
    ∀ (f : E), TashkinovSeriesStep G k em.rounds e0 P.corresponding.replacementInput
        em.series.data (Fin.last em.rounds) → em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.RE → em.series.data.connectingEdges (Fin.last em.rounds) = ({ f } :
        Finset E) → TreeIncidentEdge (em.series.data.tree (Fin.last em.rounds).castSucc) f) →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = mu
        (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej hej hfirst mu em bm Cm H q A
      ell B X y helem hsum hXlen hAXstrict hXT ip x hx beta hbeta hejX sigma hbaseStable
      seedIncident t ht hlt
  have hna : mu (T.edge t) ≠ some alpha := hfirst.2 t ht (by omega)
  by_cases hb : mu (T.edge t) = some beta
  · let tX : Fin X.length := ⟨t.val, hlt⟩
    have hcast : Fin.castLE hXT.1 tX = t := Fin.ext rfl
    have heX : mu (X.edge tX) = some beta := by
      rw [← hXT.2.2 tX, hcast]
      exact hb
    obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, hedge, hcolor, hstored⟩ :=
      HierarchyTailMissingColorExclusion G k e0 P.corresponding.replacementInput T mu em bm H
        helem (j - 1) (by omega) (by change j - 1 < ell; omega)
        beta (hx.symm ▸ hbeta) tX ht (by change t.val < A.length + (j - 1); omega) heX
    have hnotPE : em.series.data.kind (Fin.last em.rounds) ≠
        some TashkinovExtensionKind.PE := by
      rcases hkind with hs | hr
      · rw [hs]; simp
      · rw [hr]; simp
    have hstable : StableColoring (em.series.data.tree (Fin.last em.rounds).castSucc)
        (TashkinovStoredColors em.series.data (Fin.last em.rounds)) mu sigma := by
      simpa only [ite_eq_right hnotPE] using hbaseStable
    have hf := hstable.1 f (seedIncident f hstep hkind hedges)
      ⟨beta, Finset.mem_union_right _ hstored, hcolor⟩
    have he : T.edge t = f := by rw [← hcast, hXT.2.2 tX]; exact hedge
    simpa only [he] using hf
  · simp [sigma, TwoColorComponentSwap, hna, hb]

private theorem helper_hstoredFirst_583.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) →
    ∀ (_ : A.length + ell = T.length), B.length = T.length - (1 : ℕ) → X.length ≤ B.length →
        TreeSequenceInitialSegment B T →
    ∀ (hXT : TreeSequenceInitialSegment X T),
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; x ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu x, alpha ∈ TreeMissingColors mu A → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta; ib = ip →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G mu
        alpha beta (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) →
    ∀ eta ∈ HierarchyStoredColorsAt H q, HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm H q A ell B X y helem
      hsum hBlen hXleB hBT hXT ip x hxB beta hbeta haA firstSpec ib hib sigma missingOther
      hmissingB eta heta
  have hnotA : eta ∉ TreeMissingColors mu A := (Finset.mem_sdiff.mp heta).2
  have hna : eta ≠ alpha := by intro he; exact hnotA (he.symm ▸ haA)
  by_cases heb : eta = beta
  · subst eta
    have hbnew : beta ∈ MissingColors G sigma x := by rw [hmissingB x hxB]; exact hbeta
    have hs := firstSpec sigma beta ip hbnew
    let is := HierarchyFirstMissingPosition sigma T beta
    have hbound : is.val ≤ B.length := le_trans hs.2 hXleB
    let i : Fin (B.length + 1) := ⟨is.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i = is := Fin.ext rfl
    have hvB : T.vertex is ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, (hBT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
    have hbOld : beta ∈ MissingColors G mu (T.vertex is) := by
      rw [← hmissingB _ hvB]
      exact hs.1
    have hv : T.vertex is = x := by
      by_contra hn
      exact Finset.disjoint_left.mp (helem hvB hxB hn) hbOld hbeta
    exact (T.vertex_injective hv).trans hib.symm
  · have heq : (Finset.univ.filter fun i : Fin (T.length + 1) =>
          eta ∈ MissingColors G sigma (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
          eta ∈ MissingColors G mu (T.vertex i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact missingOther _ eta hna heb
    simp only [HierarchyFirstMissingPosition, heq]

private theorem helper_segTrans_616.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U
        W → TreeSequenceInitialSegment S W := by
  classical
  intro V E G e0 S U W hSU hUW
  refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)

private theorem helper_lastPositive_633.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k)
      (j : ℕ) (_ : Fin T.length),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    ∀ (_ : A.length + ell = T.length) (_ : TreeSequenceInitialSegment X T) (_ : Fin k),
    H.dividerCount ≠ (0 : ℕ) →
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej Cm H q A ell X hsum hXT beta hz
  obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
    exact (hz hv).elim
  · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hr
    simpa [q] using hv.symm

private theorem helper_coreToA_644.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k) (j : ℕ) (_
        : Fin T.length),
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    ∀ (_ : A.length + ell = T.length) (_ : TreeSequenceInitialSegment X T) (_ : Fin k), (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) → (H.dividerCount = (0 : ℕ) → A = bm.core) →
        (H.dividerCount ≠ (0 : ℕ) → A = H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → TreeSequenceInitialSegment bm.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej bm Cm H q A ell X hsum hXT
      beta segTrans stageSegment lastZero lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

private theorem helper_hbetaNotA_656.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k) (j : ℕ) (_
        : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        →
    ∀ (_ : A.length + ell = T.length), A.length < X.length →
    ∀ (hXT : TreeSequenceInitialSegment X T), TreeSequenceInitialSegment A B →
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; x ∈ TreeSequenceVertexSet B →
    ∀ beta ∈ MissingColors G mu x, beta ∉ TreeMissingColors mu A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm H q A ell B X helem hAT
      hsum hAXstrict hXT hAB ip x hxB beta hbeta hbA
  obtain ⟨v, hvA, hbv⟩ := Finset.mem_biUnion.mp hbA
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
  have hvx : v ≠ x := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvA
    obtain ⟨i, hi⟩ := hvA
    intro he
    have hinj := T.vertex_injective ((hAT.2.1 i).trans (hi.trans he))
    have hval := congrArg Fin.val hinj
    have := i.isLt
    change i.val = X.length at hval
    omega
  exact Finset.disjoint_left.mp (helem hvB hxB hvx) hbv hbeta

private theorem helper_stageMissingSub_670.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc; TreeSequenceInitialSegment Tn A
        → HierarchyStageMissingColors H q ⊆ TreeMissingColors mu A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu em Cm H q A n Tn hTnA
  by_cases hz : H.dividerCount = 0
  · have hq : q = 0 := Fin.ext (by simp [q, hz])
    simp only [HierarchyStageMissingColors, hq, Fin.cases_zero]
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hcv⟩
  · obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      exact (hz hv).elim
    · simp only [HierarchyStageMissingColors, hr, Fin.cases_succ,
        A, HierarchyStarredStage]
      exact Finset.Subset.refl _

private theorem helper_hgammaCutoff_684.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (ej : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
        (P.coloring (T.edge ej) = some alpha ∧
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑ej : ℕ) → P.coloring (T.edge t) ≠
        some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ)); A.length + ell =
        T.length → X.length = A.length + (j - (1 : ℕ)) → A.length < X.length →
        TreeSequenceInitialSegment X T →
    ∀ (beta : Fin k), (↑ej : ℕ) = X.length → beta ∉ TreeMissingColors mu A →
        HierarchyStageMissingColors H q ⊆ TreeMissingColors mu A →
    ∀ eta ∈ HierarchyStoredColorsAt H q, alpha ∈ Cm.good.gamma q eta ∨ beta ∈ Cm.good.gamma q eta
        → (↑(HierarchyFirstMissingPosition mu T eta) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej hej hfirst mu Cm H q A ell X
      hsum hXlen hAXstrict hXT beta hejX hbetaNotA stageMissingSub eta heta hgamma
  have havoid := Cm.good.avoidance q eta heta
  rcases hgamma with haGamma | hbGamma
  · by_contra hnot
    have hp : X.length < (HierarchyFirstMissingPosition mu T eta).val := by omega
    have hlast : H.stage q.succ = T := by
      have hq : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
      rw [hq, H.terminalStage]
    have hsegment : alpha ∈ HierarchySegmentColors H q eta := by
      change alpha ∈ (Finset.univ.filter fun c =>
        ∃ r : Fin (H.stage q.succ).length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition mu T eta).val (H.stage q.succ).length ∧
            mu ((H.stage q.succ).edge r) = some c)
      rw [hlast]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨ej, ?_, ?_, hfirst.1⟩
      · omega
      · have := ej.isLt
        omega
    exact (Finset.mem_sdiff.mp (havoid haGamma)).2 hsegment
  · exact (hbetaNotA (stageMissingSub (Finset.mem_sdiff.mp (havoid hbGamma)).1)).elim

private theorem helper_hfixedA_709.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); A.length + ell = T.length →
        TreeSequenceInitialSegment X T →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (if
        em.series.data.kind (Fin.last em.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (em.series.data.tree (Fin.last em.rounds).castSucc) bm.closure
        (TashkinovStoredColors em.series.data (Fin.last em.rounds)) mu sigma else StableColoring
        (em.series.data.tree (Fin.last em.rounds).castSucc) (TashkinovStoredColors em.series.data
        (Fin.last em.rounds)) mu sigma) → IsOneEdgeUncolored sigma e0 → HierarchyWeaklyStable H q
        sigma →
    ∀ (t : Fin A.length), sigma (A.edge t) = mu (A.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu em bm Cm cm H q A ell X y
      hsum hXT beta sigma hbaseStable hsone hweak
  obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
  · have hAcore : A = bm.core := by
      change HierarchyStarredStage H q = bm.core
      rw [hzero]
      rfl
    rw [hAcore]
    exact P2813_T1_BaseDisplayedEdges G k e0 P.corresponding.replacementInput T mu em bm
      sigma cm.oneEdgeUncolored hsone hbaseStable
  · have hinvariant : TreeColoringInvariant A mu sigma := by
      have hw := hweak
      simp only [HierarchyWeaklyStable, hr, Fin.cases_succ] at hw
      simpa only [A, hr, HierarchyStarredStage, Fin.cases_succ] using hw.2
    intro t
    by_cases ht : t.val = 0
    · have he : A.edge t = e0 := by
        rw [show t = ⟨0, A.positive⟩ from Fin.ext ht]
        exact A.first_edge
      rw [he]
      exact hsone.1.trans cm.oneEdgeUncolored.1.symm
    · exact hinvariant.1 t (by omega)

private theorem helper_hfixedX_730.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); A.length + ell = T.length →
        TreeSequenceInitialSegment X T → TreeSequenceInitialSegment A X →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = mu
        (T.edge t)) → (
    ∀ (t : Fin A.length), sigma (A.edge t) = mu (A.edge t)) →
    ∀ (t : Fin X.length), sigma (X.edge t) = mu (X.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu Cm H q A ell X y hsum hXT
      hAX beta sigma hfixedPrefix hfixedA t
  by_cases ht : t.val < A.length
  · let tA : Fin A.length := ⟨t.val, ht⟩
    have hcast : Fin.castLE hAX.1 tA = t := Fin.ext rfl
    rw [← hcast, hAX.2.2 tA]
    exact hfixedA tA
  · have hf := hfixedPrefix (Fin.castLE hXT.1 t) (by simp only [Fin.val_castLE]; omega)
      (by simpa only [Fin.val_castLE] using t.isLt)
    simpa only [hXT.2.2 t] using hf

private theorem helper_transportRoute_741.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); TreeSequenceInitialSegment X B →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y); (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → (
    ∀ (t : Fin X.length), sigma (X.edge t) = mu (X.edge t)) →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence mu S X →
        TashkinovAugmentationSequence sigma S X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j mu Cm ell B X y hXB beta sigma
      hmissingB segTrans hfixedX S hroute
  unfold TashkinovAugmentationSequence at hroute ⊢
  refine Relation.ReflTransGen.head_induction_on hroute ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro U W hstep htail ih
    obtain ⟨hlen, hUW, c, hcolor, hc⟩ := hstep
    have hWX := TashkinovAugmentationSequenceInitialSegment mu W X htail
    have hUX := segTrans hUW hWX
    have hcNew : c ∈ TreeMissingColors sigma U := by
      obtain ⟨v, hvU, hcv⟩ := Finset.mem_biUnion.mp hc
      have hvB := TreeSequenceInitialSegmentVertexSetSubset hXB
        (TreeSequenceInitialSegmentVertexSetSubset hUX hvU)
      exact Finset.mem_biUnion.mpr ⟨v, hvU, (hmissingB v hvB).symm ▸ hcv⟩
    let tW : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
    have hf := hfixedX (Fin.castLE hWX.1 tW)
    rw [hWX.2.2 tW] at hf
    exact Relation.ReflTransGen.head ⟨hlen, hUW, c, hf.trans hcolor, hcNew⟩ ih

private theorem helper_routes_759.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (j :
        ℕ) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); A.length + ell = T.length → A.length < X.length →
        TreeSequenceInitialSegment X T → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment A X →
    ∀ (beta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu alpha beta (Sum.inl y);
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc; (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) → TreeSequenceInitialSegment Tn A → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence mu S X →
        TashkinovAugmentationSequence sigma S X) → (em.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma Tn X ∨
        (em.series.data.kind n = some TashkinovExtensionKind.SE ∨ em.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), em.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) ∧
        TashkinovAugmentationSequence mu X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j ej mu em Cm H q A ell X y hsum
      hAXstrict hXT commonPrefix hAX beta sigma n Tn segTrans hTnA transportRoute
  have old := P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu em
  rcases old with ⟨hkind, hroute⟩ | ⟨hkind, f, seed, hedges, hadjoin, hincident, hcolor, hroute⟩
  · have hTnX := segTrans hTnA hAX
    have hrouteX := TashkinovAugmentationSequenceRestrict mu Tn X T hroute hTnX hXT
    exact ⟨Or.inl ⟨hkind, transportRoute Tn hrouteX⟩,
      TashkinovAugmentationSequenceSuffix mu Tn X T hroute hTnX hXT⟩
  · have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T hroute
    have hseedX : TreeSequenceInitialSegment seed X := commonPrefix hseedT hXT (by
      have hl := hadjoin.1
      have htn := hTnA.1
      change seed.length = Tn.length + 1 at hl
      omega)
    have hrouteX := TashkinovAugmentationSequenceRestrict mu seed X T hroute hseedX hXT
    exact ⟨Or.inr ⟨hkind, f, seed, hedges, hadjoin, transportRoute seed hrouteX⟩,
      TashkinovAugmentationSequenceSuffix mu seed X T hroute hseedX hXT⟩

private theorem helper_continuation_1607.{u_1, u_2} :
    helperContinuation1607Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha j hjLower hjUpper ej hej hfirst mu
      em bm Cm cm H q A ell B X y hprefix hj helem hAT hsum hBlen hXlen hAXstrict hXleB hBT hXT
      commonPrefix hAX hXB hAB ip x hx hxX hxB hinterval beta hbeta haA hne firstSpec ia ib a ha
      hia hib haInA haB hmissing hejX hxy hdisjoint hpath sigma hcase hbaseStable hsone hweak
      missingOther hmissingB hbetaNewY hfixedPrefix
  have hstoredFirst :=
    @helper_hstoredFirst_583 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@helem) (@hsum) (@hBlen) (@hXleB) (@hBT) (@hXT) (@hxB) (@beta) (@hbeta) (@haA)
        (@firstSpec) (@hib) (@missingOther) (@hmissingB)
  let n := Fin.last em.rounds
  let Tn := em.series.data.tree n.castSucc
  have segTrans := @helper_segTrans_616 (@V) (@E) (@G) (@e0)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have lastZero (hz : H.dividerCount = 0) : A = bm.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last, bm]
  have lastPositive := @helper_lastPositive_633 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@j) (@ej) (@hsum) (@hXT) (@beta)
  have coreToA :=
    @helper_coreToA_644 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hsum) (@hXT) (@beta) (@segTrans) (@stageSegment) (@lastZero) (@lastPositive)
  have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
    by_cases hp : em.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (bm.parallel hp).2.2).leftSegment
    · rw [bm.nonparallel hp]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hTnA := segTrans TnToCore coreToA
  have hbetaNotA :=
    @helper_hbetaNotA_656 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@helem) (@hAT) (@hsum) (@hAXstrict) (@hXT) (@hAB) (@hxB) (@beta) (@hbeta)
  have stageMissingSub :=
    @helper_stageMissingSub_670 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hTnA)
  have hgammaCutoff :=
    @helper_hgammaCutoff_684 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hej) (@hfirst) (@hsum) (@hXlen) (@hAXstrict) (@hXT) (@beta) (@hejX) (@hbetaNotA)
        (@stageMissingSub)
  have hfixedA :=
    @helper_hfixedA_709 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hsum) (@hXT) (@beta) (@hbaseStable) (@hsone) (@hweak)
  have hfixedX :=
    @helper_hfixedX_730 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hsum) (@hXT) (@hAX) (@beta) (@hfixedPrefix) (@hfixedA)
  -- Transport only the prefix route; the suffix is retained in the old coloring.
  have transportRoute := @helper_transportRoute_741 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@P) (@alpha) (@j) (@hXB) (@beta) (@hmissingB) (@segTrans) (@hfixedX)
  have routes :=
    @helper_routes_759 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hsum) (@hAXstrict) (@hXT) (@commonPrefix) (@hAX) (@beta) (@segTrans) (@hTnA)
        (@transportRoute)
  have hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧ beta ∈ TreeMissingColors sigma X := by
    constructor
    · exact Finset.mem_biUnion.mpr
        ⟨a, TreeSequenceInitialSegmentVertexSetSubset hAX haInA, (hmissingB a haB).symm ▸ ha⟩
    · exact Finset.mem_biUnion.mpr ⟨x, hxX, (hmissingB x hxB).symm ▸ hbeta⟩
  obtain ⟨_, _, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint X hAX hAXstrict hXB
      hfixedPrefix routes.1 routes.2 hsplitMissing hmissingB hstoredFirst hgammaCutoff
  have hxT : x ∈ TreeSequenceVertexSet T := TreeSequenceInitialSegmentVertexSetSubset hXT hxX
  have hyT : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  let Cs := @helperCs723 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j)  (@hsum)
      (@hXT) (@hxB) (@beta) (@hbeta) (@hxy) (@hmissingB) (@hbetaNewY) (@corr) (@hmax) (@bs) (@K)
      (@good) (@hxT) (@hyT)
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  apply Finset.mem_filter.mpr
  refine ⟨hinterval, Pnew, beta, ?_, ?_⟩
  · rw [hPnew, hprefix, hx, hmissingB x hxB]
    exact hbeta
  · rw [hPnew]
    exact hbetaNewY

private theorem helper_continuation_1420.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k), (
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) := Fin.last
        P.corresponding.replacementETT.rounds; (0 : ℕ) < H.dividerCount ∧ alpha ∈
        TreeMissingColors P.coloring (H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ alpha ∈ TreeMissingColors
        P.coloring (P.corresponding.replacementETT.series.data.tree n.castSucc)) →
    ∀ (j : ℕ), (2 : ℕ) ≤ j → j ≤ HierarchyFullTailLength C →
    ∀ (ej : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑ej : ℕ) = A.length + (j - (1 : ℕ))) →
        (P.coloring (T.edge ej) = some alpha ∧
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount);
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑ej : ℕ) → P.coloring (T.edge t) ≠
        some alpha) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let _ : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let _ : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix Cm (j - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); (
    ∀ (i : ℕ), HierarchyFullTailPrefix C i = HierarchyFullTailPrefix Cm i) → j ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        →
    ∀ (_ : A.length + ell = T.length), B.length = T.length - (1 : ℕ) → X.length = A.length + (j -
        (1 : ℕ)) → A.length < X.length → X.length ≤ B.length → TreeSequenceInitialSegment B T →
    ∀ (hXT : TreeSequenceInitialSegment X T), (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S W → TreeSequenceInitialSegment U W
        → S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment A X →
        TreeSequenceInitialSegment X B → TreeSequenceInitialSegment A B →
    let ip : Fin (T.length + (1 : ℕ)) := (⟨X.length,
    by have this : X.length ≤ T.length := hXT.1; omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let x : V := T.vertex ip; X.vertex (Fin.last X.length) = x → x ∈ TreeSequenceVertexSet X → x ∈
        TreeSequenceVertexSet B → y ∉ TreeSequenceVertexSet B → j - (1 : ℕ) ∈ Finset.Icc (1 : ℕ)
        (HierarchyFullTailLength C - (1 : ℕ)) →
    ∀ beta ∈ MissingColors G mu x, alpha ∈ TreeMissingColors mu A → alpha ∈ MissingColors G mu y →
        alpha ≠ beta → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T beta;
    let a : V := T.vertex ia; alpha ∈ MissingColors G mu a → (↑ia : ℕ) ≤ A.length → ib = ip → j -
        (1 : ℕ) ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha hnormalized j hjLower hjUpper ej
      hej hfirst mu em bm Cm cm H q A ell B X y hprefix hj helem hAT hsum hBlen hXlen hAXstrict
      hXleB hBT hXT commonPrefix hAX hXB hAB ip x hx hxX hxB hyNotB hinterval beta hbeta haA haY
      hne firstSpec ia ib a ha hia hib
  have haInA : a ∈ TreeSequenceVertexSet A := by
    let i : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ia := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (hAT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
  have haB : a ∈ TreeSequenceVertexSet B :=
    TreeSequenceInitialSegmentVertexSetSubset hAB haInA
  have hab : a ≠ x := by
    intro h
    have hv := congrArg Fin.val (T.vertex_injective h)
    change ia.val = X.length at hv
    omega
  have hmissing : alpha ∈ TreeMissingColors mu B ∧ beta ∈ TreeMissingColors mu B := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨a, haB, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨x, hxB, hbeta⟩
  have hejX : ej.val = X.length := hej.trans hXlen.symm
  have hordered :=
    @helper_hordered_369 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hej) (@hfirst) (@hsum) (@hXlen) (@hAXstrict) (@hXT) (@beta) (@hia) (@hib) (@hejX)
  have changeResult := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing hordered
  have hsame :=
    @helper_hsame_386 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hnormalized) (@j)
        (@ej) (@hsum) (@hXT) (@beta) (@hib) (@changeResult)
  let J := TwoColorIncidenceGraph G mu alpha beta
  let Q := TwoColorComponent G mu alpha beta (Sum.inl y)
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G mu alpha beta (Sum.inl v) := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl v)
    rfl
  have leaf := @helper_leaf_399 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej) (@hj)
      (@hsum) (@hXT) (@hx) (@beta) (@hne)
  have hay : a ≠ y := fun he => hyNotB (he ▸ haB)
  have hxy : x ≠ y := fun he => hyNotB (he ▸ hxB)
  have hdisjoint :=
    @helper_hdisjoint_416 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hsum) (@hXT) (@beta) (@hbeta) (@haY) (@ha) (@hab) (@hsame) (@self) (@leaf) (@hay) (@hxy)
  have hpath : TwoColorPathComponent G mu alpha beta (Sum.inl y) :=
    ⟨hne, Sum.inl y, self y, leaf y (Or.inl haY)⟩
  let sigma := TwoColorComponentSwap G mu alpha beta (Sum.inl y)
  have hcase :
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors mu
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors mu (em.series.data.tree (Fin.last em.rounds).castSucc) ∨
          (alpha ∈ TreeMissingColors mu A ∧
            alpha ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds) ∧
            beta ∉ TashkinovStoredColors em.series.data (Fin.last em.rounds)))) := by
    rcases hnormalized with hp | hz
    · exact Or.inl hp
    · exact Or.inr ⟨hz.1, Or.inl hz.2⟩
  obtain ⟨hbaseStable, hmissingA, hsproper, hsone, houtside⟩ :=
    P2813_T1_BaseControl G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      helem alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint
  have changed := StableChangeCasesOneTwo G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers cm.lexicographicMinimality
    helem cm.largeMissingSet alpha beta hne hmissing (Sum.inl y) hpath sigma rfl hcase hdisjoint
  have hweak : HierarchyWeaklyStable H q sigma := changed.1
  obtain ⟨missingOutside, missingAlphaToBeta, missingBetaToAlpha, missingOther⟩ :=
    TwoColorComponentSwapMissingBehavior G mu alpha beta hne cm.proper (Sum.inl y)
  have edgeOfVertex := @helper_edgeOfVertex_465 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta)
  have hmissingB :=
    @helper_hmissingB_473 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@helem) (@hsum) (@hXT) (@hxB) (@beta) (@hbeta) (@hne) (@ha) (@haB) (@hsame) (@self)
        (@hdisjoint) (@missingOutside) (@missingOther) (@edgeOfVertex)
  have hbetaNewY : beta ∈ MissingColors G sigma y :=
    missingAlphaToBeta y (self y) haY
  -- Recover the exact stored seed, the only possible beta edge before the split.
  have seedIncident := @helper_seedIncident_520 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
  have hfixedPrefix :=
    @helper_hfixedPrefix_556 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej)
        (@hej) (@hfirst) (@helem) (@hsum) (@hXlen) (@hAXstrict) (@hXT) (@hx) (@beta) (@hbeta)
        (@hejX) (@hbaseStable) (@seedIncident)
  exact @helper_continuation_1607 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@j) (@hjLower) (@hjUpper) (@ej) (@hej) (@hfirst) (@hprefix) (@hj) (@helem) (@hAT) (@hsum)
      (@hBlen) (@hXlen) (@hAXstrict) (@hXleB) (@hBT) (@hXT) (@commonPrefix) (@hAX) (@hXB) (@hAB)
      (@hx) (@hxX) (@hxB) (@hinterval) (@beta) (@hbeta) (@haA) (@hne) (@firstSpec) (@ha) (@hia)
      (@hib) (@haInA) (@haB) (@hmissing) (@hejX) (@hxy) (@hdisjoint) (@hpath) (@hcase)
      (@hbaseStable) (@hsone) (@hweak) (@missingOther) (@hmissingB) (@hbetaNewY) (@hfixedPrefix)
theorem HierarchyClaimNineFirstUseAfterSeed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (_ : HierarchyPathNumber P.counterexample.hierarchy = 1)
    (alpha : Fin k)
    (hstart :
      let H := P.counterexample.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      alpha ∈ TreeMissingColors P.coloring A ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hnormalized :
      let H := P.counterexample.hierarchy
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      (0 < H.dividerCount ∧
          alpha ∈ TreeMissingColors P.coloring
            (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧
          alpha ∈ TreeMissingColors P.coloring
            (P.corresponding.replacementETT.series.data.tree n.castSucc)))
    (hnoCommon : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (j : ℕ) (hjLower : 2 ≤ j) (hjUpper : j ≤ HierarchyFullTailLength C)
    (ej : Fin T.length)
    (hej :
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ej.val = A.length + (j - 1))
    (hfirst : P.coloring (T.edge ej) = some alpha ∧
      let A := HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < ej.val →
        P.coloring (T.edge t) ≠ some alpha) :
    j - 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  let mu := P.coloring
  let em := P.corresponding.replacementETT
  let bm := P.replacementBase
  let Cm := P.counterexample
  let cm := P.minimumContext
  let H := Cm.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength Cm
  let B := HierarchyFullTailPrefix Cm (ell - 1)
  let X := HierarchyFullTailPrefix Cm (j - 1)
  let y := T.vertex (Fin.last T.length)
  have hstar := (P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1).1
  have hell : HierarchyFullTailLength C = ell := by
    simp only [HierarchyFullTailLength, hstar]
    rfl
  have hprefix (i : ℕ) : HierarchyFullTailPrefix C i =
      HierarchyFullTailPrefix Cm i := by
    simp only [HierarchyFullTailPrefix, hstar]
    rfl
  have hj : j ≤ ell := by simpa only [hell] using hjUpper
  have htwo : 2 ≤ ell := by omega
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have hAT :=
    @helper_hAT_246 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
  have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAT.1
  have hBlen : B.length = T.length - 1 := by
    dsimp [B, HierarchyFullTailPrefix]
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hXlen : X.length = A.length + (j - 1) := by
    dsimp [X, HierarchyFullTailPrefix]
    change min (A.length + (j - 1)) T.length = A.length + (j - 1)
    omega
  have hAXstrict : A.length < X.length := by omega
  have hXleB : X.length ≤ B.length := by omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hXT : TreeSequenceInitialSegment X T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have commonPrefix := @helper_commonPrefix_268 (@V) (@E) (@G) (@e0)
  have hAX : TreeSequenceInitialSegment A X := commonPrefix hAT hXT (by omega)
  have hXB : TreeSequenceInitialSegment X B := commonPrefix hXT hBT hXleB
  have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT hBT (by omega)
  let ip : Fin (T.length + 1) := ⟨X.length, by have := hXT.1; omega⟩
  let x := T.vertex ip
  have hx : X.vertex (Fin.last X.length) = x := (hXT.2.1 _).symm
  have hxX : x ∈ TreeSequenceVertexSet X := by
    rw [← hx]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last X.length, rfl⟩
  have hxB : x ∈ TreeSequenceVertexSet B :=
    TreeSequenceInitialSegmentVertexSetSubset hXB hxX
  have hyNotB :=
    @helper_hyNotB_289 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j) (@ej) (@hej) (@hsum)
        (@hBlen) (@hXlen) (@hXleB) (@hBT)
  have hinterval : j - 1 ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1) := by
    rw [hell]
    simp only [Finset.mem_Icc]
    omega
  obtain ⟨beta, hbeta⟩ := hvertexMissing mu cm.proper cm.oneEdgeUncolored x
  have hbNotY : beta ∉ MissingColors G mu y := by
    have hd := hnoCommon (j - 1) hinterval
    rw [hprefix, hx] at hd
    exact Finset.disjoint_left.mp hd hbeta
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have haY : alpha ∈ MissingColors G mu y := hstart.2
  have hne : alpha ≠ beta := by
    intro he
    exact hbNotY (he ▸ haY)
  have firstSpec := @helper_firstSpec_312 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T)
      (@j)
  obtain ⟨va, hvaA, hava⟩ := Finset.mem_biUnion.mp haA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvaA
  obtain ⟨iaA, hiaA⟩ := hvaA
  let iaT := Fin.castLE (Nat.succ_le_succ hAT.1) iaA
  have haia : alpha ∈ MissingColors G mu (T.vertex iaT) := by
    rw [hAT.2.1 iaA, hiaA]
    exact hava
  let ia := HierarchyFirstMissingPosition mu T alpha
  let ib := HierarchyFirstMissingPosition mu T beta
  let a := T.vertex ia
  have ha : alpha ∈ MissingColors G mu a := (firstSpec mu alpha iaT haia).1
  have hia : ia.val ≤ A.length := by
    have hm := (firstSpec mu alpha iaT haia).2
    change ia.val ≤ iaA.val at hm
    have := iaA.isLt
    omega
  have hib :=
    @helper_hib_340 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@j) (@ej) (@helem)
        (@hsum) (@hBlen) (@hXleB) (@hBT) (@hXT) (@hxB) (@beta) (@hbeta) (@firstSpec)
  exact @helper_continuation_1420 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@hnormalized) (@j) (@hjLower) (@hjUpper) (@ej) (@hej) (@hfirst) (@hprefix) (@hj) (@helem)
      (@hAT) (@hsum) (@hBlen) (@hXlen) (@hAXstrict) (@hXleB) (@hBT) (@hXT) (@commonPrefix) (@hAX)
      (@hXB) (@hAB) (@hx) (@hxX) (@hxB) (@hyNotB) (@hinterval) (@beta) (@hbeta) (@haA) (@haY)
      (@hne) (@firstSpec) (@ha) (@hia) (@hib)
end GoldbergSeymour

end
