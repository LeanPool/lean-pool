/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TerminalKempeStageSwitch
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion

/-!
# Hierarchy Situation One Advance Inside Stored

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_tailException_322.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Y) (_ :
        TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A)) (_ : TreeSequenceInitialSegment A T) (hlen
        : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ),
        HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ :
        (1 : ℕ) ≤ j) (_ : j < T.length - A.length),
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i trans A starEq hAT hlen B hBT fullEq
      fullB elementary vertexMem R j hj hjlt c hc t hlo hhi hcol
  clear * - R j hj hjlt c hc t hlo hhi hcol starEq hAT hBT fullEq fullB elementary vertexMem
  let U := HierarchyFullTailPrefix R.counterexample j
  have hUlen : U.length = A.length + j := by
    simp only [U, HierarchyFullTailPrefix, TreeSequencePrefix]
    rw [starEq R]
    exact min_eq_left (by have := hAT.1; omega)
  have hUT : TreeSequenceInitialSegment U T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  let u : Fin U.length := ⟨t.val, by rw [hUlen]; omega⟩
  have hut : Fin.castLE hUT.1 u = t := Fin.ext rfl
  have hcU : c ∈ MissingColors G R.coloring (U.vertex (Fin.last U.length)) := by
    dsimp only [U]
    rw [fullEq R]
    exact hc
  have hcolU : R.coloring (U.edge u) = some c := by
    rw [← hUT.2.2 u, hut]; exact hcol
  have hex := HierarchyTailMissingColorExclusion G k e0 R.corresponding.replacementInput T
    R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample.hierarchy
    (by
      change ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet
        (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)))
      rw [fullB R]
      exact elementary R)
    j hj (by
      rw [starEq R]
      exact hjlt) c hcU u
    (by
      change (HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length ≤ t.val
      rw [starEq R]
      exact hlo)
    (by
      change t.val < (HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length + j
      rw [starEq R]
      exact hhi) hcolU
  obtain ⟨hzero, hcore, hval, f, hstep, hkind, hedges, hedge, hcF, hstored⟩ := hex
  have hAval : t.val = A.length := by
    change u.val = _ at hval
    rw [starEq R] at hval
    exact hval
  have hAn : A = R.corresponding.replacementETT.series.data.tree
      (Fin.last R.corresponding.replacementETT.rounds).castSucc := by
    rw [← starEq R]
    have hs : HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = R.replacementBase.core := by
      simp [HierarchyStarredStage, hzero, Fin.last]
    exact hs.trans hcore
  obtain ⟨i, hi⟩ := T.attaches t
  let a : Fin (A.length + 1) := ⟨i.val, by simpa only [hAval] using i.isLt⟩
  let old : Fin (T.length + 1) :=
    Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))
  have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a = old := Fin.ext rfl
  refine ⟨⟨T.vertex old, ?_, ?_⟩, hstored⟩
  · rw [← hAn, ← ha, hAT.2.1 a]
    exact vertexMem A a
  · rw [Incident, hi]
    exact Sym2.mem_mk_right _ _

private theorem helper_excM_401.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount);
    ∀ (_ : TreeSequenceInitialSegment A T) (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => (
    by first  | omega
    )) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => (
    by first  | omega
    ));
    ∀ (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ : (1 :
        ℕ) ≤ j) (_ : j < T.length - A.length),
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < A.length + j → R.coloring (T.edge t) =
        some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (_ : (
    ∀ (t : Fin T.length) (_ : A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ)), G.ends
        (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))) (m : ℕ) (hmLower : (1 : ℕ) ≤ m) (_
        : (1 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (m + (1 : ℕ))) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (m + (1 : ℕ))) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) =>
    by
          omega
    );
    let Y : TreeSequence G e0 := TreeSequencePrefix T (A.length + m) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + m) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬A.length + m ≤ T.length) =>
    by omega
    );
    let jm : Fin (B.length + (1 : ℕ)) := (⟨A.length + m, id (Decidable.byContradiction fun (a :
        ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) =>
    by omega
    )⟩ : Fin (B.length + (1 : ℕ)));
    let _ : Fin T.length := (⟨A.length + m,
    by omega
    ⟩ : Fin T.length);
    ∀ (_ : HierarchyFullTailPrefix C m = Y) (_ : Y.vertex (Fin.last Y.length) = B.vertex jm) (R :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) = some
        b → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation A hAT hlen B tailException
      consecutive m hmLower hm hmT X Y jm tnext hfullY hYvertex R b hb t hlo hhi hcol
  by_cases ht : t.val < A.length + m
  · exact tailException R m (by omega) (by have := hAT.1; omega) b
      (by rw [hfullY, hYvertex]; exact hb) t hlo ht hcol
  · have htEq : t = tnext := Fin.ext (by
      change t.val < A.length + (m + 1) at hhi
      dsimp [tnext]
      omega)
    subst t
    have he := consecutive tnext (by dsimp [tnext]; omega)
    have hv : T.vertex tnext.castSucc = B.vertex jm := rfl
    have hi : Incident G (B.vertex jm) (T.edge tnext) := by
      rw [Incident, he, hv]
      exact Sym2.mem_mk_left _ _
    exact ((Finset.mem_sdiff.mp hb).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge tnext, hi, hcol⟩)).elim

private theorem helper_advance_428.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ :
        HierarchyPathNumber C.hierarchy = (1 : ℕ)) (_ : (
    ∀ (mu : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G mu) (_ : IsOneEdgeUncolored mu
        e0) (v : V), (MissingColors G mu v).Nonempty)) (_ : ℕ) (_ :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k) (_ : (
    ∀ {X Y Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment X Z) (_ :
        TreeSequenceInitialSegment Y Z) (_ : X.length ≤ Y.length), TreeSequenceInitialSegment X
        Y)) (_ : TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) T) (hlen : (4 : ℕ) ≤ T.length),
    ∀ (_ : TreeSequenceInitialSegment (TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by
                omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by
                omega
    ) : TreeSequence G e0) T) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k) (j :
        Fin (((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 :
        ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ) : TreeSequence G e0)).length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring
        (((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ)
        ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ) : TreeSequence G e0)).vertex j)), (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) =
        (↑j : ℕ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (X : TreeSequence G
        e0) (_ : TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0) X) (_ : (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length < X.length) (_ :
        TreeSequenceInitialSegment X (TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by
                    omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by
                    omega
    ) : TreeSequence G e0)) (a_bound_0 b eta : Fin k) (_ : eta ∈ HierarchyStoredColorsAt
        R.counterexample.hierarchy (Fin.last R.counterexample.hierarchy.dividerCount)) (_ :
        a_bound_0 ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
        eta) (_ : (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length) (jb : Fin
        (((TreeSequencePrefix T (T.length - (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(1 : ℕ)
        ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ) : TreeSequence G e0)).length + (1 : ℕ))) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length < (↑jb : ℕ)) (_ : (↑jb : ℕ) ≤
        X.length) (_ : b ∈ MissingColors G R.coloring (((TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ) : TreeSequence G e0)).vertex jb)) (_ : a_bound_0 ∈ MissingColors G R.coloring (T.vertex
        (Fin.last T.length)) ∨ b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length))) (_ :
        (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length), R.coloring (T.edge t) ≠ some a_bound_0)) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) <
        X.length) (_ : R.coloring (T.edge t) = some b), TreeIncidentEdge
        (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ b ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))),
    ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (
    ∀ v ∈ TreeSequenceVertexSet (TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ) : TreeSequence G e0), MissingColors G S.coloring v = MissingColors G R.coloring v) ∧ (
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → S.coloring (T.edge t) =
        R.coloring (T.edge t)) ∧ (a_bound_0 ∈ MissingColors G R.coloring (T.vertex (Fin.last
        T.length)) → b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧ (b ∈
        MissingColors G R.coloring (T.vertex (Fin.last T.length)) → a_bound_0 ∈ MissingColors G
        S.coloring (T.vertex (Fin.last T.length))))) (_ : (
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta)) (_ :
        (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a_bound_1 :
        Fin k) (_ : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount)) (_ : a_bound_1 ∈ R.counterexample.good.gamma
        (Fin.last R.counterexample.hierarchy.dividerCount) eta) (t : Fin T.length) (_ :
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) : TreeSequence G
        e0).length ≤ (↑t : ℕ)) (_ : (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta)
        : ℕ)), R.coloring (T.edge t) ≠ some a_bound_1)) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (j : ℕ) (_ : (1 :
        ℕ) ≤ j) (_ : j < T.length - (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length),
    ∀ c ∈ MissingColors G R.coloring ((HierarchyFullTailPrefix C j).vertex (Fin.last
        (HierarchyFullTailPrefix C j).length)),
    ∀ (t : Fin T.length), (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) :
        TreeSequence G e0).length ≤ (↑t : ℕ) → (↑t : ℕ) < (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) : TreeSequence G e0).length + j → R.coloring (T.edge
        t) = some c → TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree (Fin.last
        R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧ c ∈ TashkinovStoredColors
        R.corresponding.replacementETT.series.data (Fin.last
        R.corresponding.replacementETT.rounds))) (_ : (
    ∀ (t : Fin T.length) (_ : (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) : TreeSequence G e0).length + HierarchyPathNumber C.hierarchy ≤
        (↑t : ℕ)), G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a_bound_2 ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
        eta, R.coloring f ≠ some a_bound_2)) (m : ℕ) (_ : (1 : ℕ) ≤ m) (_ : m <
        HierarchyFullTailLength C - (1 : ℕ)) (P : HierarchyReplacementPresentation G k e0 input T
        phi ett base C ctx),
    ∀ alpha ∈ MissingColors G P.coloring ((HierarchyFullTailPrefix C m).vertex (Fin.last
        (HierarchyFullTailPrefix C m).length)), alpha ∈ MissingColors G P.coloring (T.vertex
        (Fin.last T.length)) → alpha ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) → m + (1 : ℕ) ∈
        HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation hvertexMissing i P alpha common
  set A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  intro hAT hlen
  set B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) => by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) => by omega)
  intro hBT vertexMem firstAt stageSwitch gammaTransport gammaUnused tailException consecutive
      gammaChoice m hmLower hmUpper P alpha ha haLast hAlphaStored
  have hm : 1 ≤ m := hmLower
  have hmT : A.length + (m + 1) < T.length := by
    change m < (T.length - A.length) - 1 at hmUpper
    have := hAT.1
    omega
  let X := TreeSequencePrefix T (A.length + (m + 1)) (by have := A.positive; omega) (by omega)
  let Y := TreeSequencePrefix T (A.length + m) (by have := A.positive; omega) (by omega)
  have hXT : TreeSequenceInitialSegment X T := ⟨by exact le_of_lt hmT, fun _ => rfl, fun _ => rfl⟩
  have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by
      dsimp [X, TreeSequencePrefix]
      omega)
  have hXB : TreeSequenceInitialSegment X B :=
    common hXT hBT (by dsimp [X, B, TreeSequencePrefix]; omega)
  have hAXlt : A.length < X.length := by dsimp [X, TreeSequencePrefix]; omega
  let jm : Fin (B.length + 1) := ⟨A.length + m, by dsimp [B, TreeSequencePrefix]; omega⟩
  let jnext : Fin (B.length + 1) := ⟨A.length + (m + 1), by dsimp [B, TreeSequencePrefix]; omega⟩
  let tnext : Fin T.length := ⟨A.length + m, by omega⟩
  have hfullY : HierarchyFullTailPrefix C m = Y := by
    have hn : min (A.length + m) T.length = A.length + m := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + m) T.length) _ _ = Y
    simp only [hn]
    rfl
  have hfullX : HierarchyFullTailPrefix C (m + 1) = X := by
    have hn : min (A.length + (m + 1)) T.length = A.length + (m + 1) := min_eq_left (by omega)
    simp only [HierarchyFullTailPrefix]
    change TreeSequencePrefix T (min (A.length + (m + 1)) T.length) _ _ = X
    simp only [hn]
    rfl
  have hYvertex : Y.vertex (Fin.last Y.length) = B.vertex jm := rfl
  have hXvertex : X.vertex (Fin.last X.length) = B.vertex jnext := rfl
  have haM : alpha ∈ MissingColors G P.coloring (B.vertex jm) := by
    rw [hfullY, hYvertex] at ha
    exact ha
  obtain ⟨theta, htheta⟩ := hvertexMissing P.coloring P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored (B.vertex jnext)
  have nextMember (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (hc : c ∈ MissingColors G S.coloring (B.vertex jnext))
      (hcLast : c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) :
      m + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, S, c, ?_, hcLast⟩
    rw [hfullX, hXvertex]
    exact hc
  have excNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (b : Fin k) (hb : b ∈ MissingColors G R.coloring (B.vertex jnext))
      (t : Fin T.length) (hlo : A.length ≤ t.val) (hhi : t.val < X.length)
      (hcol : R.coloring (T.edge t) = some b) :
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) := by
    apply tailException R (m + 1) (by omega) (by have := hAT.1; omega) b
      (by rw [hfullX, hXvertex]; exact hb) t hlo
      (by exact hhi) hcol
  have excM := @helper_excM_401 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hsituation hAT hlen tailException consecutive m hmLower hm hmT
      hfullY hYvertex
  have avoidNext (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jnext)) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    apply gammaUnused R eta a heta ha t hlo
    rw [firstAt R eta jnext he]
    exact hhi
  have avoidM (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (eta a : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount))
      (ha : a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta)
      (he : eta ∈ MissingColors G R.coloring (B.vertex jm))
      (hgap : R.coloring (T.edge tnext) ≠ some a) :
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        R.coloring (T.edge t) ≠ some a := by
    intro t hlo hhi
    by_cases ht : t.val < A.length + m
    · apply gammaUnused R eta a heta ha t hlo
      rw [firstAt R eta jm he]
      exact ht
    · have htEq : t = tnext := Fin.ext (by
        change t.val < A.length + (m + 1) at hhi
        dsimp [tnext]
        omega)
      simpa only [htEq] using hgap
  obtain ⟨gamma, hgamma, hgap⟩ := gammaChoice P alpha hAlphaStored (T.edge tnext)
  obtain ⟨P1, hmissing1, hfixed1, _, hterminal1⟩ := stageSwitch P X hAX hAXlt hXB
    gamma alpha alpha hAlphaStored hgamma
    (by rw [firstAt P alpha jm haM]; dsimp [jm, X, TreeSequencePrefix]; omega)
    jm (by dsimp [jm]; omega) (by dsimp [jm, X, TreeSequencePrefix]; omega)
    haM (Or.inr haLast) (avoidM P alpha gamma hAlphaStored hgamma haM hgap)
    (excM P alpha haM)
  have hgLast : gamma ∈ MissingColors G P1.coloring (T.vertex (Fin.last T.length)) := hterminal1
      haLast
  have haM1 : alpha ∈ MissingColors G P1.coloring (B.vertex jm) := by
    rw [hmissing1 _ (vertexMem B jm)]; exact haM
  have htheta1 : theta ∈ MissingColors G P1.coloring (B.vertex jnext) := by
    rw [hmissing1 _ (vertexMem B jnext)]; exact htheta
  obtain ⟨hAlphaStored1, heqGamma⟩ := gammaTransport P P1 alpha hAlphaStored
  have hgamma1 : gamma ∈ P1.counterexample.good.gamma
      (Fin.last P1.counterexample.hierarchy.dividerCount) alpha := by
    rw [← heqGamma]; exact hgamma
  have hgap1 : P1.coloring (T.edge tnext) ≠ some gamma := by
    rw [hfixed1 tnext (by dsimp [tnext]; omega)
      (by dsimp [tnext, X, TreeSequencePrefix]; omega)]
    exact hgap
  obtain ⟨P2, hmissing2, _, hterminal2, _⟩ := stageSwitch P1 X hAX hAXlt hXB
    gamma theta alpha hAlphaStored1 hgamma1
    (by rw [firstAt P1 alpha jm haM1]; dsimp [jm, X, TreeSequencePrefix]; omega)
    jnext (by dsimp [jnext]; omega) (by rfl)
    htheta1 (Or.inl hgLast) (avoidM P1 alpha gamma hAlphaStored1 hgamma1 haM1 hgap1)
    (excNext P1 theta htheta1)
  exact nextMember P2 theta (by rw [hmissing2 _ (vertexMem B jnext)]; exact htheta1)
    (hterminal2 hgLast)

private theorem helper_firstAt_634.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ) (hlen : (4 :
        ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    );
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B))) (_ : (
    ∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))), U.vertex j ∈ TreeSequenceVertexSet
        U)) (_ : (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))) (_ : c ∈
        MissingColors G psi (T.vertex j)), HierarchyFirstMissingPosition psi T c ≤ j)) (_ : (
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (_ : (↑(HierarchyFirstMissingPosition psi T c) :
        ℕ) < T.length), c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T
        c)))) (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
        (j : Fin (B.length + (1 : ℕ))) (_ : c ∈ MissingColors G R.coloring (B.vertex j)),
        (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i hlen B hBT elementary vertexMem firstLe
      firstMem R c j hc
  clear * - G T B R c j hc elementary vertexMem firstLe firstMem hBT
  have hcT : c ∈ MissingColors G R.coloring
      (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j)) := by
    rw [hBT.2.1 j]; exact hc
  have hle := firstLe R.coloring c _ hcT
  have hlt : (HierarchyFirstMissingPosition R.coloring T c).val < T.length := by
    have := j.isLt
    change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
    have hblen : B.length = T.length - 1 := rfl
    omega
  let x : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T c).val, by
    change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
    omega⟩
  have hxT : Fin.castLE (Nat.succ_le_succ hBT.1) x =
      HierarchyFirstMissingPosition R.coloring T c := Fin.ext rfl
  have hcx : c ∈ MissingColors G R.coloring (B.vertex x) := by
    rw [← hBT.2.1 x, hxT]
    exact firstMem R.coloring c hlt
  have he : B.vertex x = B.vertex j := by
    by_contra hn
    exact Finset.disjoint_left.mp (elementary R (vertexMem B x) (vertexMem B j) hn) hcx hc
  exact congrArg Fin.val (B.vertex_injective he)

private theorem helper_firstMem_669.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (e0 : E) (T : TreeSequence G e0) (psi : PartialEdgeColoring E k) (c : Fin k),
    (↑(HierarchyFirstMissingPosition psi T c) : ℕ) < T.length →
    c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
  classical
  intro V E _ _ G k e0 T psi c hlt
  let _ := Fintype.ofFinite V
  let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
    c ∈ MissingColors G psi (T.vertex j)
  by_cases hn : candidates.Nonempty
  · unfold HierarchyFirstMissingPosition
    rw [dite_eq_left hn]
    exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  · have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
      unfold HierarchyFirstMissingPosition
      rw [dite_eq_right hn]
      rfl
    omega

private theorem helper_consecutive_751.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (_ : ℕ)
      (_ : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C),
    let A : TreeSequence G e0 :=
      HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
    ∀ (t : Fin T.length) (_ : A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ)),
    G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C i hpathUpper A t ht
  clear * - G T A C t ht hpathUpper
  let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  have hp : HierarchyPathNumber C.hierarchy =
      (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
  have hn : candidates.Nonempty := by
    by_contra hn
    rw [dite_eq_right hn] at hp
    have hu : HierarchyPathNumber C.hierarchy < T.length - A.length := hpathUpper
    omega
  have hm : candidates.min' hn = HierarchyPathNumber C.hierarchy := by
    simpa only [dite_eq_left hn] using hp.symm
  have hh := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  rw [hm] at hh
  exact hh t ht

private theorem helper_trans_785.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        HierarchyPathNumber C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hsituation i hiLower hiUpper X Y Z hXY hYZ
  clear * - hXY hYZ
  refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

private theorem helper_common_795.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        HierarchyPathNumber C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y Z
        → X.length ≤ Y.length → TreeSequenceInitialSegment X Y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hsituation i hiLower hiUpper trans X Y Z hXZ
      hYZ hXY
  clear * - hXZ hYZ hXY
  refine ⟨hXY, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)

private theorem helper_hAT_826.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        HierarchyPathNumber C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hsituation i hiLower hiUpper A
  have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
        (C.hierarchy.stage j.succ) :=
    Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
  simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
    starNext (Fin.last C.hierarchy.dividerCount)

private theorem helper_fullB_848.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → (3 : ℕ) ≤ T.length - A.length →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper A starEq htail
      hlen B R
  have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [starEq R]
    omega
  simp only [HierarchyFullTailPrefix, hn]
  rfl

private theorem helper_elementary_860.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper hlen B fullB R
  have h : ColoredVertexSetElementary G R.coloring
    (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - 1))) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0
      R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
      R.replacementBase R.counterexample R.minimumContext.proper
      R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
      R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
      R.minimumContext.largeMissingSet
  intro u hu v hv hne
  exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne

private theorem helper_firstLe_877.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        HierarchyPathNumber C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hsituation i hiLower hiUpper psi c j hj
  clear * - G T psi c j hj
  let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
    c ∈ MissingColors G psi (T.vertex j)
  have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hn : candidates.Nonempty := ⟨j, hm⟩
  unfold HierarchyFirstMissingPosition
  rw [dite_eq_left hn]
  exact Finset.min'_le candidates j hm

private theorem helper_lastData_900.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), C.good.gamma
        (Fin.last C.hierarchy.dividerCount) eta = R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper R
  clear * - R
  obtain ⟨hcount, hdata⟩ := R.sameGood.2
  have hh := hdata (Fin.last C.hierarchy.dividerCount)
  have hidx : Fin.cast (congrArg (fun q => q + 1) hcount)
      (Fin.last C.hierarchy.dividerCount) =
      Fin.last R.counterexample.hierarchy.dividerCount := Fin.ext hcount
  simpa only [hidx] using hh

private theorem helper_gammaTransport_914.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) → (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) ∧
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), C.good.gamma
        (Fin.last C.hierarchy.dividerCount) eta = R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta) →
    ∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount), eta ∈ HierarchyStoredColorsAt
        S.counterexample.hierarchy (Fin.last S.counterexample.hierarchy.dividerCount) ∧
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
        S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper trans lastData
      R S eta heta
  clear * - R S eta heta lastData
  have hOrig : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)
     := by
    rw [(lastData R).1]; exact heta
  refine ⟨?_, ((lastData R).2 eta hOrig).symm.trans ((lastData S).2 eta hOrig)⟩
  rw [← (lastData S).1]
  exact hOrig

private theorem helper_gammaUnused_930.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) →
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (eta a : Fin k),
        eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) → a ∈ R.counterexample.good.gamma (Fin.last
        R.counterexample.hierarchy.dividerCount) eta →
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < (↑(HierarchyFirstMissingPosition
        R.coloring T eta) : ℕ) → R.coloring (T.edge t) ≠ some a := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper A starEq R eta
      a heta ha t hlo hhi
  clear * - R eta a heta ha t hlo hhi starEq
  intro hc
  have hnot := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance
    (Fin.last R.counterexample.hierarchy.dividerCount) eta heta ha)).2
  apply hnot
  unfold HierarchySegmentColors
  dsimp only
  rw [starEq R, Fin.succ_last, R.counterexample.hierarchy.terminalStage]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo,
    lt_min hhi t.isLt, hc⟩

private theorem helper_gammaChoice_968.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), HierarchyPathNumber
        C.hierarchy = (1 : ℕ) →
    ∀ (i : ℕ), (1 : ℕ) ≤ i → i < HierarchyFullTailLength C - (1 : ℕ) → (
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount),
    ∀ (f : E),
    ∃ a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
        R.coloring f ≠ some a := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hsituation i hiLower hiUpper trans R eta
      heta f
  clear * - R eta heta f
  by_contra hn
  push Not at hn
  have hc : (R.counterexample.good.gamma
      (Fin.last R.counterexample.hierarchy.dividerCount) eta).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((hn a ha).symm.trans (hn b hb))
  rw [R.counterexample.good.twoColors _ eta heta] at hc
  omega

theorem HierarchySituationOneAdvanceInsideStored {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (i : ℕ) (hiLower : 1 ≤ i)
    (hiUpper : i < HierarchyFullTailLength C - 1)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hcommon :
      alpha ∈ MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)) ∧
        alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)))
    (hinside :
      let H := P.counterexample.hierarchy
      alpha ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount)) :
    i + 1 ∈ HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx := by
  classical
  have hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C := by
    rw [hsituation]
    omega
  classical
  open scoped Sym2 in
    have trans := @helper_trans_785 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hsituation) (@i)
        (@hiLower) (@hiUpper)
    have common := @helper_common_795 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hsituation) (@i)
        (@hiLower) (@hiUpper) (@trans)
    have sameLast :
    ∀ {a b : ℕ} (s : Fin (a + 2) → TreeSequence G e0) (t : Fin (b + 2) → TreeSequence G e0) (u v :
        TreeSequence G e0), a = b → HEq s t → u = v → Fin.cases (motive := fun _ => TreeSequence G
        e0) u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) = Fin.cases (motive := fun _ =>
        TreeSequence G e0) v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      clear * -
      intro a b s t u v hab hst huv
      cases hab
      have he : s = t := eq_of_heq hst
      cases he
      cases huv
      rfl
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
        HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
      (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
    have hAT :=
      @helper_hAT_826 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G) (@k)
          (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hsituation) (@i) (@hiLower) (@hiUpper)
    have htail : 3 ≤ T.length - A.length := by
      change i < (T.length - A.length) - 1 at hiUpper
      omega
    have hlen : 4 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    have hBT : TreeSequenceInitialSegment B T := ⟨by dsimp [B, TreeSequencePrefix]; omega,
      fun _ => rfl, fun _ => rfl⟩
    have hAB : TreeSequenceInitialSegment A B :=
      common hAT hBT (by dsimp [B, TreeSequencePrefix]; omega)
    have fullEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
        (j : ℕ) : HierarchyFullTailPrefix R.counterexample j = HierarchyFullTailPrefix C j := by
      unfold HierarchyFullTailPrefix
      dsimp only
      simp only [starEq R]
      rfl
    have fullB := @helper_fullB_848 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hsituation)
        (@i) (@hiLower) (@hiUpper) (@starEq) (@htail) (@hlen)
    have elementary := @helper_elementary_860 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hsituation)
        (@i) (@hiLower) (@hiUpper) (@hlen) (@fullB)
    have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
        U.vertex j ∈ TreeSequenceVertexSet U := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    have firstLe := @helper_firstLe_877 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hsituation) (@i)
        (@hiLower) (@hiUpper)
    have firstMem := @helper_firstMem_669 V E inferInstance inferInstance G k e0 T
    have firstAt := @helper_firstAt_634 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T phi ett base C ctx i hlen hBT elementary vertexMem firstLe firstMem
    have stageSwitch := P2963_T1_TerminalKempeStageSwitch G k e0 input T phi ett base C ctx
      A B (by omega) rfl rfl
    have lastData := @helper_lastData_900 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hsituation)
        (@i) (@hiLower) (@hiUpper)
    have gammaTransport := @helper_gammaTransport_914 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@hsituation) (@i) (@hiLower) (@hiUpper) (@trans) (@lastData)
    have gammaUnused := @helper_gammaUnused_930 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hsituation)
        (@i) (@hiLower) (@hiUpper) (@starEq)
    have tailException := @helper_tailException_322 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base C ctx i trans starEq hAT hlen hBT fullEq fullB
        elementary vertexMem
    have consecutive := @helper_consecutive_751 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base C i hpathUpper
    have gammaChoice := @helper_gammaChoice_968 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@hsituation)
        (@i) (@hiLower) (@hiUpper) (@trans)
    have advance := @helper_advance_428 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T phi ett base C ctx hsituation hvertexMissing i P alpha common hAT hlen hBT
        vertexMem firstAt stageSwitch gammaTransport gammaUnused tailException consecutive
        gammaChoice
    exact advance i hiLower hiUpper P alpha hcommon.1 hcommon.2 hinside

end GoldbergSeymour

end
