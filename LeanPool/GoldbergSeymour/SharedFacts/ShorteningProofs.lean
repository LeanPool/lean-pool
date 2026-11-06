/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Shared recolouring and shortened-hierarchy proofs

Shared proofs used by the Goldberg–Seymour construction branches.
Extracted from the credited Trellis port at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; the original branch contracts remain available.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ShorteningProofs

/-- The unique-refresh property transported between corresponding shortened hierarchies. -/
abbrev uniqueRefreshTransportStatement.{u_1, u_2} : Prop :=
open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (have _ : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (have _ : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (2 : ℕ))
    (have _ : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
    (have _ : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  let r : Fin T.length :=
   (⟨T.length - (1 : ℕ),
     have _ : (1 : ℕ) ≤ T.length := T.positive;
     Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
    Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (_ : ∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v)
   (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds,
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
         fun
          (a :
           ¬P.corresponding.replacementETT.rounds <
             P.corresponding.replacementETT.rounds + (2 : ℕ)) ↦
         by omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds,
         have _ : (1 : ℕ) ≤ T.length := T.positive;
         Decidable.byContradiction
          fun
           (a :
            ¬P.corresponding.replacementETT.rounds <
              P.corresponding.replacementETT.rounds + (2 : ℕ)) ↦
          by omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB)
   (goodB : GoodHierarchy HB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
   {
    rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
    series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
    strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
    ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
   (bs : HierarchyBase corr.replacementETT sigma)
   (baseStageK :
    HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
   (nestedK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
   (strictK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     (HB.stage j.castSucc).length < (HB.stage j.succ).length)
   (coreInsideK :
    TreeSequenceInitialSegment bs.core
     (HB.stage
      (⟨(1 : ℕ),
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ B.length := B.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) < HB.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
       Fin (HB.dividerCount + (2 : ℕ)))))
   (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
   (increasingK :
    ∀ (i j : Fin HB.dividerCount),
     (↑i : ℕ) < (↑j : ℕ) → (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
   (dividerStageK :
    ∀ (i : Fin HB.dividerCount),
     HB.stage
       (⟨(↑i : ℕ) + (1 : ℕ),
         have _ : (1 : ℕ) ≤ T.length := T.positive;
         have _ : (1 : ℕ) ≤ B.length := B.positive;
         Decidable.byContradiction fun (a : ¬(↑i : ℕ) + (1 : ℕ) < HB.dividerCount + (2 : ℕ)) ↦ by
          omega⟩ :
        Fin (HB.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
       (have _ : (1 : ℕ) ≤ T.length := T.positive;
       have _ : (1 : ℕ) ≤ B.length := B.positive;
       Decidable.byContradiction fun (a : ¬(↑(HB.dividerPosition i) : ℕ) ≤ B.length) ↦ by
        omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
   { dividerCount := HB.dividerCount,
     stage := HB.stage,
     baseStage := baseStageK,
     terminalStage := terminalStageK,
     nested := nestedK,
     strict := strictK,
     dividerPosition := HB.dividerPosition,
     dividerPositive := positiveK,
     dividerIncreasing := increasingK,
     dividerStage := dividerStageK,
     coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  ∀
   (_ :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStarredStage KF j = HierarchyStarredStage HB j)
   (_ :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (HB.stage j.castSucc) X)
   (_ :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j)
   (i : Fin KF.dividerCount),
  ∃! eta : Fin k,
   eta ∈ HierarchyStoredColorsAt KF i.succ ∧
    (goodB.gamma i.succ eta ⊆
      (TreeSequenceVertexSet (KF.stage i.succ.castSucc) \
         TreeSequenceVertexSet (HierarchyStarredStage KF i.castSucc)).biUnion
       fun (v : V) ↦ MissingColors G sigma v) ∧
     ∀ theta ∈ HierarchyStoredColorsAt KF i.succ,
      theta ≠ eta → goodB.gamma i.succ theta = goodB.gamma i.castSucc theta

theorem properRecoloring.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  alpha ∈ MissingColors G mu (B.vertex (Fin.last B.length)) →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  let w : V := T.vertex (Fin.last T.length);
  G.ends f = s(y, w) →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  IsProperEdgeColoring G sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha haT mu trans hlenT B halphaB r f y
      w hends sigma fixed e g c heg hadj he hg
  by_cases hef : e = f
  · subst e
    have hgf : g ≠ f := heg.symm
    have hc : c = alpha := by simpa [sigma] using he.symm
    subst c
    rw [fixed g hgf] at hg
    obtain ⟨v, hvf, hvg⟩ := hadj
    have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
    rcases hv with rfl | rfl
    · exact (Finset.mem_sdiff.mp halphaB).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
    · exact (Finset.mem_sdiff.mp haT).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hvg, hg⟩)
  · by_cases hgf : g = f
    · subst g
      have hc : c = alpha := by simpa [sigma] using hg.symm
      subst c
      rw [fixed e hef] at he
      obtain ⟨v, hve, hvf⟩ := hadj
      have hv : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hvf
      rcases hv with rfl | rfl
      · exact (Finset.mem_sdiff.mp halphaB).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
      · exact (Finset.mem_sdiff.mp haT).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, hve, he⟩)
    · exact P.minimumContext.proper heg hadj ((fixed e hef).symm.trans he)
        ((fixed g hgf).symm.trans hg)

theorem terminalStoredColors.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (U : TreeSequence G e0),
      TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
        TreeMissingColors sigma U = TreeMissingColors mu U) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B),
  MaximumProperty corr.replacementETT →
  ∀ (bs : HierarchyBase corr.replacementETT sigma),
  baseB.core = bs.core →
  ({ rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
              series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
              strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := generatingB :
              ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                mu }.series.data.kind
          (Fin.last
            { rounds := P.corresponding.replacementETT.rounds,
                roundsPositive := positiveB,
                series := P.corresponding.replacementETT.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := generatingB :
                ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                  mu }.rounds) =
        some TashkinovExtensionKind.PE ↔
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        some TashkinovExtensionKind.PE) →
  ({ rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
              series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
              strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := generatingB :
              ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                mu }.series.data.kind
          (Fin.last
            { rounds := P.corresponding.replacementETT.rounds,
                roundsPositive := positiveB,
                series := P.corresponding.replacementETT.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := generatingB :
                ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                  mu }.rounds) =
        some TashkinovExtensionKind.PE →
      baseB.closure = bs.closure) →
  ∀
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  HB.stage ≍
      { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
          terminalStage := terminalStageK, nested := nestedK, strict := strictK,
          dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
          dividerIncreasing := increasingK, dividerStage := dividerStageK,
          coreInsideFirst := coreInsideK :
          TashkinovHierarchy corr.replacementETT bs }.stage →
  HB.dividerPosition ≍
      { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
          terminalStage := terminalStageK, nested := nestedK, strict := strictK,
          dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
          dividerIncreasing := increasingK, dividerStage := dividerStageK,
          coreInsideFirst := coreInsideK :
          TashkinovHierarchy corr.replacementETT bs }.dividerPosition →
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HierarchyStarredStage KF j = HierarchyStarredStage HB j) →
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
      Tn →
  TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) =
    TashkinovStoredColors EB.series.data (Fin.last EB.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha n Tn mu hlenT B X hTnX r f
      S hSBlen sigma missingTree positiveB aboveB strictB belowB generatingB baseB HB EB corr
      hmaximum bs hcore hpe hclosure baseStageK terminalStageK nestedK strictK coreInsideK
      positiveK increasingK dividerStageK KF hstage hposition starredEq terminalTree
  rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
  rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
  cases hr
  have hs : data = rs := eq_of_heq hp
  cases hs
  let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
  have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
    dsimp [j]; have := EB.roundsPositive; omega)
  have ht : rs.data.tree (Fin.last EB.rounds).castSucc = Tn := by
    change rs.data.tree (Fin.last EB.rounds).castSucc =
      EB.series.data.tree (Fin.last EB.rounds).castSucc
    rw [← hj]; exact hl j
  have hm : TreeMissingColors (rs.data.coloring (Fin.last EB.rounds))
      (rs.data.tree (Fin.last EB.rounds).castSucc) = TreeMissingColors mu Tn := by
    rw [← hc, ht]
    exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX)
  have hmOld : TreeMissingColors (EB.series.data.coloring (Fin.last EB.rounds))
      (EB.series.data.tree (Fin.last EB.rounds).castSucc) = TreeMissingColors mu Tn := by
    rw [← EB.generatingColoring]
  change TashkinovStoredColors rs.data (Fin.last EB.rounds) =
    TashkinovStoredColors EB.series.data (Fin.last EB.rounds)
  simp only [TashkinovStoredColors, hstored, hm, hmOld]


/-- The unique-refresh condition is preserved by the shared hierarchy transport. -/
theorem uniqueRefreshTransport.{u_1, u_2} :
    uniqueRefreshTransportStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu hlenT B X r f sigma missingFixed
      positiveB aboveB strictB belowB generatingB baseB HB goodB EB corr bs baseStageK
      terminalStageK nestedK strictK coreInsideK positiveK increasingK dividerStageK KF starredEq
      stageBX storedEq i
  have hnew :
      ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun v => MissingColors G sigma v) =
      ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun v => MissingColors G mu v) := by
    apply Finset.biUnion_congr rfl
    intro v hv
    exact missingFixed v (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ)
      (Finset.mem_sdiff.mp hv).1)
  change ∃! c : Fin k,
    c ∈ HierarchyStoredColorsAt KF i.succ ∧
      goodB.gamma i.succ c ⊆
        ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage KF i.castSucc)).biUnion
            fun v => MissingColors G sigma v) ∧
      ∀ d ∈ HierarchyStoredColorsAt KF i.succ, d ≠ c →
        goodB.gamma i.succ d = goodB.gamma i.castSucc d
  rw [starredEq i.castSucc, hnew]
  simp only [storedEq]
  exact goodB.uniqueRefresh i

end GoldbergSeymour.SharedFacts.ShorteningProofs

end
