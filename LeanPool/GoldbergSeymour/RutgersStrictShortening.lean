/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTransTrees
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.RutgersCounterexampleMeasure
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosureExists
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TreeExitComponentMeetsTreeOnlyAtExit
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.ClosedColorExitPathBoundaryEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Rutgers Strict Shortening

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperFinish912Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (gamma : Fin k) (_ : gamma ≠ counterexample.beta),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀ (i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let newPresentation : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀
       (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (_ : counterexample.beta ∈ TreeMissingColors mu4 W) (_ : gamma ∉ TreeMissingColors mu4 W),
       let Package : Type (max u_1 u_1 u_2) :=
        (a : V) ×
         (b : V) ×
          (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) × E;
       let Good : Package → Prop := fun (p : Package) ↦
        TreeExitPath W mu4 counterexample.beta gamma p.fst p.snd.fst p.snd.snd.1 ∧
         p.snd.snd.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
          Incident G p.snd.fst p.snd.snd.2 ∧ Sum.inr p.snd.snd.2 ∈ p.snd.snd.1.support;
       ∀ (p q r : Package) (_ : Good p) (_ : Good q) (_ : Good r)
        (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ q.snd.snd.1.support))
        (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ r.snd.snd.1.support))
        (_ : (∀ x ∈ q.snd.snd.1.support, x ∉ r.snd.snd.1.support))
        (_ : TreeVertexOrder W p.snd.fst q.snd.fst) (_ : TreeVertexOrder W q.snd.fst r.snd.fst),
        ∃ (C' : RutgersCounterexample G k e0 original newPresentation),
         RutgersCounterexampleMeasure C' =
          p.snd.snd.1.length + q.snd.snd.1.length + r.snd.snd.1.length

private abbrev helperBranch871Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀ (i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let newPresentation : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀
       (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (Q3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (c1 : V) (hc1 : Sum.inl c1 ∈ Q1.support) (g1 : E) (c2 : V) (hc2 : Sum.inl c2 ∈ Q2.support)
       (g2 : E) (c3 : V) (hc3 : Sum.inl c3 ∈ Q3.support) (g3 : E),
       let L1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl c1) :=
        Q1.takeUntil (Sum.inl c1) hc1;
       let L2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl c2) :=
        Q2.takeUntil (Sum.inl c2) hc2;
       let L3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl c3) :=
        Q3.takeUntil (Sum.inl c3) hc3;
       ∀ (_ : (∀ x ∈ L1.support, x ∉ L2.support)) (_ : (∀ x ∈ L1.support, x ∉ L3.support))
        (_ : (∀ x ∈ L2.support, x ∉ L3.support))
        (_ : L1.length + L2.length + L3.length < RutgersCounterexampleMeasure counterexample),
        let Package : Type (max u_1 u_2) :=
         (a : V) ×
          (b : V) ×
           (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
            E;
        let Good : Package → Prop := fun (p : Package) ↦
         TreeExitPath W mu4 counterexample.beta gamma p.fst p.snd.fst p.snd.snd.1 ∧
          p.snd.snd.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
           Incident G p.snd.fst p.snd.snd.2 ∧ Sum.inr p.snd.snd.2 ∈ p.snd.snd.1.support;
        let pack1 : Package :=
         (⟨counterexample.a1,
           (⟨c1, (L1, g1)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a1) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack2 : Package :=
         (⟨counterexample.a2,
           (⟨c2, (L2, g2)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a2) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack3 : Package :=
         (⟨counterexample.a3,
           (⟨c3, (L3, g3)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a3) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        ∀ (_ : Good pack1) (_ : Good pack2) (_ : Good pack3)
         (_ :
          (∀ (p q r : Package) (_ : Good p) (_ : Good q) (_ : Good r)
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ q.snd.snd.1.support))
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : (∀ x ∈ q.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : TreeVertexOrder W p.snd.fst q.snd.fst) (_ : TreeVertexOrder W q.snd.fst r.snd.fst),
           ∃ (C' : RutgersCounterexample G k e0 original newPresentation),
            RutgersCounterexampleMeasure C' =
             p.snd.snd.1.length + q.snd.snd.1.length + r.snd.snd.1.length))
         (j1 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j1 = c1) (j2 : Fin (W.length + (1 : ℕ)))
         (_ : W.vertex j2 = c2) (j3 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j3 = c3)
         (_ : (↑j1 : ℕ) ≠ (↑j2 : ℕ)) (_ : (↑j1 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j2 : ℕ) ≠ (↑j3 : ℕ))
         (_ : ¬(↑j1 : ℕ) < (↑j2 : ℕ)) (_ : ¬(↑j1 : ℕ) < (↑j3 : ℕ)),
         ∃ (newCounterexample : RutgersCounterexample G k e0 original newPresentation),
          RutgersCounterexampleMeasure newCounterexample <
           RutgersCounterexampleMeasure counterexample

private abbrev helperBranch1326Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a1)
       (Sum.inl counterexample.b1))
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a2)
       (Sum.inl counterexample.b2))
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a3)
       (Sum.inl counterexample.b3))
     (_ _ i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length) (_ : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let newPresentation : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀
       (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (Q3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (c1 : V) (hc1 : Sum.inl c1 ∈ Q1.support) (g1 : E) (c2 : V) (hc2 : Sum.inl c2 ∈ Q2.support)
       (g2 : E) (c3 : V) (hc3 : Sum.inl c3 ∈ Q3.support) (g3 : E),
       let L1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl c1) :=
        Q1.takeUntil (Sum.inl c1) hc1;
       let L2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl c2) :=
        Q2.takeUntil (Sum.inl c2) hc2;
       let L3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl c3) :=
        Q3.takeUntil (Sum.inl c3) hc3;
       ∀ (_ : (∀ x ∈ L1.support, x ∉ L2.support)) (_ : (∀ x ∈ L1.support, x ∉ L3.support))
        (_ : (∀ x ∈ L2.support, x ∉ L3.support))
        (_ : L1.length + L2.length + L3.length < RutgersCounterexampleMeasure counterexample),
        let Package : Type (max u_1 u_1 u_2) :=
         (a : V) ×
          (b : V) ×
           (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
            E;
        let Good : Package → Prop := fun (p : Package) ↦
         TreeExitPath W mu4 counterexample.beta gamma p.fst p.snd.fst p.snd.snd.1 ∧
          p.snd.snd.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
           Incident G p.snd.fst p.snd.snd.2 ∧ Sum.inr p.snd.snd.2 ∈ p.snd.snd.1.support;
        let pack1 : Package :=
         (⟨counterexample.a1,
           (⟨c1, (L1, g1)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a1) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack2 : Package :=
         (⟨counterexample.a2,
           (⟨c2, (L2, g2)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a2) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack3 : Package :=
         (⟨counterexample.a3,
           (⟨c3, (L3, g3)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a3) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        ∀ (_ : Good pack1) (_ : Good pack2) (_ : Good pack3)
         (_ :
          (∀ (p q r : Package) (_ : Good p) (_ : Good q) (_ : Good r)
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ q.snd.snd.1.support))
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : (∀ x ∈ q.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : TreeVertexOrder W p.snd.fst q.snd.fst) (_ : TreeVertexOrder W q.snd.fst r.snd.fst),
           ∃ (C' : RutgersCounterexample G k e0 original newPresentation),
            RutgersCounterexampleMeasure C' =
             p.snd.snd.1.length + q.snd.snd.1.length + r.snd.snd.1.length))
         (j1 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j1 = c1) (j2 : Fin (W.length + (1 : ℕ)))
         (_ : W.vertex j2 = c2) (j3 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j3 = c3)
         (_ : (↑j1 : ℕ) ≠ (↑j2 : ℕ)) (_ : (↑j1 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j2 : ℕ) ≠ (↑j3 : ℕ))
         (_ : ¬(↑j1 : ℕ) < (↑j2 : ℕ)),
         ∃ (newCounterexample : RutgersCounterexample G k e0 original newPresentation),
          RutgersCounterexampleMeasure newCounterexample <
           RutgersCounterexampleMeasure counterexample

private abbrev helperBranch1689Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀ (i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let newPresentation : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀
       (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (Q3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (c1 : V) (hc1 : Sum.inl c1 ∈ Q1.support) (g1 : E) (c2 : V) (hc2 : Sum.inl c2 ∈ Q2.support)
       (g2 : E) (c3 : V) (hc3 : Sum.inl c3 ∈ Q3.support) (g3 : E),
       let L1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl c1) :=
        Q1.takeUntil (Sum.inl c1) hc1;
       let L2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl c2) :=
        Q2.takeUntil (Sum.inl c2) hc2;
       let L3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl c3) :=
        Q3.takeUntil (Sum.inl c3) hc3;
       ∀ (_ : (∀ x ∈ L1.support, x ∉ L2.support)) (_ : (∀ x ∈ L1.support, x ∉ L3.support))
        (_ : (∀ x ∈ L2.support, x ∉ L3.support))
        (_ : L1.length + L2.length + L3.length < RutgersCounterexampleMeasure counterexample),
        let Package : Type (max u_1 u_2) :=
         (a : V) ×
          (b : V) ×
           (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
            E;
        let Good : Package → Prop := fun (p : Package) ↦
         TreeExitPath W mu4 counterexample.beta gamma p.fst p.snd.fst p.snd.snd.1 ∧
          p.snd.snd.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
           Incident G p.snd.fst p.snd.snd.2 ∧ Sum.inr p.snd.snd.2 ∈ p.snd.snd.1.support;
        let pack1 : Package :=
         (⟨counterexample.a1,
           (⟨c1, (L1, g1)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a1) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack2 : Package :=
         (⟨counterexample.a2,
           (⟨c2, (L2, g2)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a2) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack3 : Package :=
         (⟨counterexample.a3,
           (⟨c3, (L3, g3)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a3) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        ∀ (_ : Good pack1) (_ : Good pack2) (_ : Good pack3)
         (_ :
          (∀ (p q r : Package) (_ : Good p) (_ : Good q) (_ : Good r)
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ q.snd.snd.1.support))
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : (∀ x ∈ q.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : TreeVertexOrder W p.snd.fst q.snd.fst) (_ : TreeVertexOrder W q.snd.fst r.snd.fst),
           ∃ (C' : RutgersCounterexample G k e0 original newPresentation),
            RutgersCounterexampleMeasure C' =
             p.snd.snd.1.length + q.snd.snd.1.length + r.snd.snd.1.length))
         (j1 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j1 = c1) (j2 : Fin (W.length + (1 : ℕ)))
         (_ : W.vertex j2 = c2) (j3 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j3 = c3)
         (_ : (↑j1 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j2 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j1 : ℕ) < (↑j2 : ℕ))
         (_ : ¬(↑j2 : ℕ) < (↑j3 : ℕ)),
         ∃ (newCounterexample : RutgersCounterexample G k e0 original newPresentation),
          RutgersCounterexampleMeasure newCounterexample <
           RutgersCounterexampleMeasure counterexample

private abbrev helperBranch1588Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a1)
       (Sum.inl counterexample.b1))
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a2)
       (Sum.inl counterexample.b2))
     (_ :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a3)
       (Sum.inl counterexample.b3))
     (_ _ i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length) (_ : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let newPresentation : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀
       (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (Q3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (c1 : V) (hc1 : Sum.inl c1 ∈ Q1.support) (g1 : E) (c2 : V) (hc2 : Sum.inl c2 ∈ Q2.support)
       (g2 : E) (c3 : V) (hc3 : Sum.inl c3 ∈ Q3.support) (g3 : E),
       let L1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl c1) :=
        Q1.takeUntil (Sum.inl c1) hc1;
       let L2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl c2) :=
        Q2.takeUntil (Sum.inl c2) hc2;
       let L3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl c3) :=
        Q3.takeUntil (Sum.inl c3) hc3;
       ∀ (_ : (∀ x ∈ L1.support, x ∉ L2.support)) (_ : (∀ x ∈ L1.support, x ∉ L3.support))
        (_ : (∀ x ∈ L2.support, x ∉ L3.support))
        (_ : L1.length + L2.length + L3.length < RutgersCounterexampleMeasure counterexample),
        let Package : Type (max u_1 u_1 u_2) :=
         (a : V) ×
          (b : V) ×
           (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
            E;
        let Good : Package → Prop := fun (p : Package) ↦
         TreeExitPath W mu4 counterexample.beta gamma p.fst p.snd.fst p.snd.snd.1 ∧
          p.snd.snd.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
           Incident G p.snd.fst p.snd.snd.2 ∧ Sum.inr p.snd.snd.2 ∈ p.snd.snd.1.support;
        let pack1 : Package :=
         (⟨counterexample.a1,
           (⟨c1, (L1, g1)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a1) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack2 : Package :=
         (⟨counterexample.a2,
           (⟨c2, (L2, g2)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a2) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        let pack3 : Package :=
         (⟨counterexample.a3,
           (⟨c3, (L3, g3)⟩ :
            (b : V) ×
             (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
               (Sum.inl counterexample.a3) (Sum.inl b) ×
              E)⟩ :
          (a : V) ×
           (b : V) ×
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) ×
             E);
        ∀ (_ : Good pack1) (_ : Good pack2) (_ : Good pack3)
         (_ :
          (∀ (p q r : Package) (_ : Good p) (_ : Good q) (_ : Good r)
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ q.snd.snd.1.support))
           (_ : (∀ x ∈ p.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : (∀ x ∈ q.snd.snd.1.support, x ∉ r.snd.snd.1.support))
           (_ : TreeVertexOrder W p.snd.fst q.snd.fst) (_ : TreeVertexOrder W q.snd.fst r.snd.fst),
           ∃ (C' : RutgersCounterexample G k e0 original newPresentation),
            RutgersCounterexampleMeasure C' =
             p.snd.snd.1.length + q.snd.snd.1.length + r.snd.snd.1.length))
         (j1 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j1 = c1) (j2 : Fin (W.length + (1 : ℕ)))
         (_ : W.vertex j2 = c2) (j3 : Fin (W.length + (1 : ℕ))) (_ : W.vertex j3 = c3)
         (_ : (↑j1 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j2 : ℕ) ≠ (↑j3 : ℕ)) (_ : (↑j1 : ℕ) < (↑j2 : ℕ)),
         ∃ (newCounterexample : RutgersCounterexample G k e0 original newPresentation),
          RutgersCounterexampleMeasure newCounterexample <
           RutgersCounterexampleMeasure counterexample

private abbrev helperContinuation2244Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   ∀ (seed : TreeSequence G e0)
    (hseed :
     R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed)
    (_ : counterexample.b1 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b2 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b3 ∈ TreeSequenceVertexSet U) (gamma : Fin k)
    (_ : gamma ≠ counterexample.beta),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
     (_ :
      (∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
       (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v)) (_ : p.IsPath) {f : E}
       (_ : Sum.inr f ∈ p.support),
       ∃ (j : ℕ) (x : V) (y : V),
        (0 : ℕ) < j ∧
         j < p.length ∧
          p.getVert j = Sum.inr f ∧
           p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
            p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
             Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y)))
     (P1 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a1)
       (Sum.inl counterexample.b1))
     (_ : P1.support = counterexample.Q1.support) (_ : P1.length = counterexample.Q1.length)
     (P2 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a2)
       (Sum.inl counterexample.b2))
     (_ : P2.support = counterexample.Q2.support) (_ : P2.length = counterexample.Q2.length)
     (P3 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a3)
       (Sum.inl counterexample.b3))
     (_ : P3.support = counterexample.Q3.support) (_ : P3.length = counterexample.Q3.length)
     (_ _ i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
     (hi3le : (↑i3 : ℕ) ≤ U.length) (_ : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
     ∀ (W : TreeSequence G e0) (hW : TashkinovClosure mu4 C W)
      (route4W : TashkinovAugmentationSequence mu4 seed W)
      (A40 : CorrespondingExtendedTashkinovTree G k e0 original mu4 W)
      (max40 : MaximumProperty A40.replacementETT)
      (agree40 :
       A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds))
      (agree0 :
       presentation.corresponding.replacementETT.series.data.tree
          (Fin.last presentation.corresponding.replacementETT.rounds).castSucc =
         original.series.data.tree (Fin.last original.rounds).castSucc ∧
        presentation.corresponding.replacementETT.series.data.kind
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.kind (Fin.last original.rounds) ∧
         presentation.corresponding.replacementETT.series.data.connectingEdges
           (Fin.last presentation.corresponding.replacementETT.rounds) =
          original.series.data.connectingEdges (Fin.last original.rounds)),
      let _ : RutgersClosedPresentation G k e0 original :=
       {
        sigma := mu4, U := W, corresponding := A40, maximum := max40,
        terminalRoute :=
         id
          (have htree :
           A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc = Tn :=
           Eq.trans agree40.left (Eq.symm agree0.left);
          have hkind :
           A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
            R.series.data.kind n :=
           Eq.trans agree40.right.left (Eq.symm agree0.right.left);
          have hedges :
           A40.replacementETT.series.data.connectingEdges (Fin.last A40.replacementETT.rounds) =
            R.series.data.connectingEdges n :=
           Eq.trans agree40.right.right (Eq.symm agree0.right.right);
          Or.casesOn hseed
           (fun (hPE : R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ↦
            Or.inl
             (⟨Eq.trans hkind hPE.left,
               Eq.mpr
                (id (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W) htree))
                (Eq.mpr
                 (id
                  (congrArg (fun (_a : TreeSequence G e0) ↦ TashkinovClosure mu4 _a W)
                   (Eq.symm hPE.right)))
                 (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                  TashkinovAugmentationSequence mu4 seed W ∧
                   ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W)))⟩ :
              A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                some TashkinovExtensionKind.PE ∧
               TashkinovClosure mu4
                (A40.replacementETT.series.data.tree (Fin.last A40.replacementETT.rounds).castSucc)
                W))
           fun
            (hSER :
             (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
               R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
              ∃ (f : E),
               R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
           Exists.casesOn hSER.right
            fun (f : E)
             (h : R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed) ↦
            And.casesOn h
             fun (he : R.series.data.connectingEdges n = { f })
              (ha : TreeSequenceAdjoinEdge Tn f seed) ↦
             Or.inr
              (⟨Eq.mpr
                 (id
                  (congr
                   (congrArg Or (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.SE)))
                   (congrFun' (congrArg Eq hkind) (some TashkinovExtensionKind.RE))))
                 hSER.left,
                Exists.intro f
                 (Exists.intro seed
                  (⟨Eq.trans hedges he,
                    (⟨Eq.mpr
                       (id (congrFun' (congrFun' (congrArg TreeSequenceAdjoinEdge htree) f) seed))
                       ha,
                      (⟨route4W, fun {_ : E} {_ : Fin k} {_ : V} ↦ hW.right⟩ :
                       TashkinovAugmentationSequence mu4 seed W ∧
                        ColoredVertexSetClosed G mu4 (TreeSequenceVertexSet W))⟩ :
                     TreeSequenceAdjoinEdge
                       (A40.replacementETT.series.data.tree
                        (Fin.last A40.replacementETT.rounds).castSucc)
                       f seed ∧
                      TashkinovClosure mu4 seed W)⟩ :
                   A40.replacementETT.series.data.connectingEdges
                      (Fin.last A40.replacementETT.rounds) =
                     { f } ∧
                    TreeSequenceAdjoinEdge
                      (A40.replacementETT.series.data.tree
                       (Fin.last A40.replacementETT.rounds).castSucc)
                      f seed ∧
                     TashkinovClosure mu4 seed W))⟩ :
               (A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.SE ∨
                 A40.replacementETT.series.data.kind (Fin.last A40.replacementETT.rounds) =
                  some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed : TreeSequence G e0),
                 A40.replacementETT.series.data.connectingEdges
                    (Fin.last A40.replacementETT.rounds) =
                   { f } ∧
                  TreeSequenceAdjoinEdge
                    (A40.replacementETT.series.data.tree
                     (Fin.last A40.replacementETT.rounds).castSucc)
                    f seed ∧
                   TashkinovClosure mu4 seed W)) :
        RutgersClosedPresentation G k e0 original };
      ∀ (_ : ColoredVertexSetElementary G mu4 (TreeSequenceVertexSet W))
       (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a1)
         (Sum.inl counterexample.b1))
       (_ : TreeExitPath U mu4 counterexample.beta gamma counterexample.a1 counterexample.b1 Q1)
       (_ : Q1.support = P1.support) (_ : Q1.length = P1.length)
       (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a2)
         (Sum.inl counterexample.b2))
       (_ : TreeExitPath U mu4 counterexample.beta gamma counterexample.a2 counterexample.b2 Q2)
       (_ : Q2.support = P2.support) (_ : Q2.length = P2.length)
       (Q3 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl counterexample.a3)
         (Sum.inl counterexample.b3))
       (_ : TreeExitPath U mu4 counterexample.beta gamma counterexample.a3 counterexample.b3 Q3)
       (_ : Q3.support = P3.support) (_ : Q3.length = P3.length)
       (_ : counterexample.b1 ∈ TreeSequenceVertexSet W)
       (_ : counterexample.b2 ∈ TreeSequenceVertexSet W)
       (_ : counterexample.b3 ∈ TreeSequenceVertexSet W)
       (_ : counterexample.beta ∈ MissingColors G mu4 counterexample.b3)
       (_ : counterexample.beta ∈ TreeMissingColors mu4 W)
       (_ :
        (∀ {b : V} {f : E} (_ : b ∈ TreeSequenceVertexSet U) (_ : b ≠ counterexample.b3)
         (_ : Incident G b f) (_ : sigma f = some counterexample.beta),
         mu4 f = some counterexample.beta)),
       ∃ (newPresentation : RutgersClosedPresentation G k e0 original) (newCounterexample :
        RutgersCounterexample G k e0 original newPresentation),
        RutgersCounterexampleMeasure newCounterexample < RutgersCounterexampleMeasure counterexample

private abbrev helperContinuation2163Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (current : ExtendedTashkinovTree G k e0 input' T' generating')
     (_ : current.rounds = original.rounds) (_ : MaximumProperty current),
     ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation)
   (_ :
    (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
     (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C))
   (_ :
    (∀ {i : PartialEdgeColoring E k} {A : TreeSequence G e0} {phi : PartialEdgeColoring E k}
     (base : ExtendedTashkinovTree G k e0 i A phi) {psi : PartialEdgeColoring E k}
     {B : TreeSequence G e0} (corr : CorrespondingExtendedTashkinovTree G k e0 base psi B),
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
       base.series.data.tree (Fin.last base.rounds).castSucc ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        base.series.data.kind (Fin.last base.rounds) ∧
       corr.replacementETT.series.data.connectingEdges (Fin.last corr.replacementETT.rounds) =
        base.series.data.connectingEdges (Fin.last base.rounds))),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
   ∀ (seed : TreeSequence G e0)
    (_ :
     (R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed))
    (_ : counterexample.b1 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b2 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b3 ∈ TreeSequenceVertexSet U) (gamma : Fin k)
    (_ : gamma ≠ counterexample.beta),
    let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
     (_ :
      (IsProperEdgeColoring G mu3 ∧
       IsOneEdgeUncolored mu3 e0 ∧
        StableColoring U Dn sigma mu3 ∧ ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f))
     (_ : TashkinovAugmentationSequence mu3 seed U)
     (A3 : CorrespondingExtendedTashkinovTree G k e0 R mu3 U)
     (_ : MaximumProperty A3.replacementETT)
     (_ :
      (∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
       (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v)) (_ : p.IsPath) {f : E}
       (_ : Sum.inr f ∈ p.support),
       ∃ (j : ℕ) (x : V) (y : V),
        (0 : ℕ) < j ∧
         j < p.length ∧
          p.getVert j = Sum.inr f ∧
           p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
            p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
             Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y)))
     (P1 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a1)
       (Sum.inl counterexample.b1))
     (_ : TreeExitPath U mu3 gamma counterexample.beta counterexample.a1 counterexample.b1 P1)
     (_ : P1.support = counterexample.Q1.support) (_ : P1.length = counterexample.Q1.length)
     (P2 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a2)
       (Sum.inl counterexample.b2))
     (_ : TreeExitPath U mu3 gamma counterexample.beta counterexample.a2 counterexample.b2 P2)
     (_ : P2.support = counterexample.Q2.support) (_ : P2.length = counterexample.Q2.length)
     (P3 :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl counterexample.a3)
       (Sum.inl counterexample.b3))
     (_ : TreeExitPath U mu3 gamma counterexample.beta counterexample.a3 counterexample.b3 P3)
     (_ : P3.support = counterexample.Q3.support) (_ : P3.length = counterexample.Q3.length)
     (_ i2 i3 : Fin (presentation.U.length + (1 : ℕ))) (_ : (↑i2 : ℕ) < (↑i3 : ℕ))
     (_ : Tn.length < (↑i2 : ℕ)) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤ U.length)
     (hi3prevpos : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
     let B : TreeSequence G e0 :=
      TreeSequencePrefix U ((↑i3 : ℕ) - (1 : ℕ)) hi3prevpos
       (Decidable.byContradiction fun (a : ¬(↑i3 : ℕ) - (1 : ℕ) ≤ U.length) ↦ by omega);
     let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
     ∀ (_ : C.length = (↑i3 : ℕ)) (_ : TreeSequenceInitialSegment C U)
      (_ : TreeSequenceInitialSegment B C) (_ : C.length = B.length + (1 : ℕ))
      (_ : TreeSequenceInitialSegment Tn B) (_ : TreeSequenceInitialSegment seed C)
      (_ : counterexample.b3 ∈ TreeSequenceVertexSet C)
      (_ : counterexample.b1 ∈ TreeSequenceVertexSet C)
      (_ : counterexample.b2 ∈ TreeSequenceVertexSet C),
      let K : Set (V ⊕ E) :=
       TwoColorComponent G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
      let mu4 : PartialEdgeColoring E k :=
       TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
      ∀ (_ : gamma ∈ MissingColors G mu3 counterexample.b3)
       (_ : (∀ w ∈ TreeSequenceVertexSet U, Sum.inl w ∈ K ↔ w = counterexample.b3))
       (_ : (∀ {v : V} (_ : Sum.inl v ∉ K) {f : E} (_ : Incident G v f), mu4 f = mu3 f))
       (_ :
        (have C : Set (V ⊕ E) :=
         TwoColorComponent G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
        have phi' : PartialEdgeColoring E k :=
         TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
        (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G mu3 v) ∧
         (∀ (v : V),
           Sum.inl v ∈ C →
            gamma ∈ MissingColors G mu3 v → counterexample.beta ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
            Sum.inl v ∈ C →
             counterexample.beta ∈ MissingColors G mu3 v → gamma ∈ MissingColors G phi' v) ∧
           ∀ (v : V) (c : Fin k),
            c ≠ gamma →
             c ≠ counterexample.beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G mu3 v)))
       (_ : (∀ v ∈ TreeSequenceVertexSet B, MissingColors G mu4 v = MissingColors G mu3 v))
       (_ :
        A3.replacementETT.series.data.tree (Fin.last A3.replacementETT.rounds).castSucc =
          R.series.data.tree (Fin.last R.rounds).castSucc ∧
         A3.replacementETT.series.data.kind (Fin.last A3.replacementETT.rounds) =
           R.series.data.kind (Fin.last R.rounds) ∧
          A3.replacementETT.series.data.connectingEdges (Fin.last A3.replacementETT.rounds) =
           R.series.data.connectingEdges (Fin.last R.rounds))
       (_ : ModColoring A3.replacementETT mu4)
       (_ : (∀ (j : Fin C.length), mu4 (C.edge j) = mu3 (C.edge j))),
       ∃ (newPresentation : RutgersClosedPresentation G k e0 original) (newCounterexample :
        RutgersCounterexample G k e0 original newPresentation),
        RutgersCounterexampleMeasure newCounterexample < RutgersCounterexampleMeasure counterexample

private abbrev helperContinuation2093Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (original : ExtendedTashkinovTree G k e0 input T generating)
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (current : ExtendedTashkinovTree G k e0 input' T' generating')
     (_ : current.rounds = original.rounds) (_ : MaximumProperty current),
     ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
   (_ :
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (current : ExtendedTashkinovTree G k e0 input' T' generating')
     (_ : current.rounds = original.rounds) (_ : MaximumProperty current),
     let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
     let Tterminal : TreeSequence G e0 := current.series.data.tree terminal.castSucc;
     ∀ (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma)
      (_ : IsOneEdgeUncolored sigma e0)
      (_ :
       StableColoring Tterminal (TashkinovStoredColors current.series.data terminal)
        (current.series.data.coloring terminal) sigma),
      ModColoring current sigma))
   (presentation : RutgersClosedPresentation G k e0 original)
   (counterexample : RutgersCounterexample G k e0 original presentation)
   (_ :
    (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
     (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C))
   (_ :
    (∀ {i : PartialEdgeColoring E k} {A : TreeSequence G e0} {phi : PartialEdgeColoring E k}
     (base : ExtendedTashkinovTree G k e0 i A phi) {psi : PartialEdgeColoring E k}
     {B : TreeSequence G e0} (corr : CorrespondingExtendedTashkinovTree G k e0 base psi B),
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
       base.series.data.tree (Fin.last base.rounds).castSucc ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        base.series.data.kind (Fin.last base.rounds) ∧
       corr.replacementETT.series.data.connectingEdges (Fin.last corr.replacementETT.rounds) =
        base.series.data.connectingEdges (Fin.last base.rounds))),
   let R :
    ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput presentation.U
     presentation.sigma :=
    presentation.corresponding.replacementETT;
   let U : TreeSequence G e0 := presentation.U;
   let sigma : PartialEdgeColoring E k := presentation.sigma;
   let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
   let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
   let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
   ∀ (seed : TreeSequence G e0)
    (_ :
     (R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
      (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
       ∃ (f : E), R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed))
    (_ : counterexample.b1 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b2 ∈ TreeSequenceVertexSet U)
    (_ : counterexample.b3 ∈ TreeSequenceVertexSet U),
    ∀ gamma ∈ MissingColors G sigma counterexample.b3,
     gamma ≠ counterexample.beta →
      let mu3 : PartialEdgeColoring E k := OutsideTreeColorSwap U sigma counterexample.alpha gamma;
      (IsProperEdgeColoring G mu3 ∧
        IsOneEdgeUncolored mu3 e0 ∧
         StableColoring U Dn sigma mu3 ∧ ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f) →
       TashkinovAugmentationSequence mu3 seed U →
        ∀ (A3 : CorrespondingExtendedTashkinovTree G k e0 R mu3 U),
         MaximumProperty A3.replacementETT →
          (∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
            (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v)),
            p.IsPath →
             ∀ {f : E},
              Sum.inr f ∈ p.support →
               ∃ (j : ℕ) (x : V) (y : V),
                (0 : ℕ) < j ∧
                 j < p.length ∧
                  p.getVert j = Sum.inr f ∧
                   p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
                    p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
                     Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y)) →
           ∀
            (P1 :
             (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
              (Sum.inl counterexample.a1) (Sum.inl counterexample.b1)),
            TreeExitPath U mu3 gamma counterexample.beta counterexample.a1 counterexample.b1 P1 →
             P1.support = counterexample.Q1.support →
              P1.length = counterexample.Q1.length →
               ∀
                (P2 :
                 (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
                  (Sum.inl counterexample.a2) (Sum.inl counterexample.b2)),
                TreeExitPath U mu3 gamma counterexample.beta counterexample.a2 counterexample.b2
                  P2 →
                 P2.support = counterexample.Q2.support →
                  P2.length = counterexample.Q2.length →
                   ∀
                    (P3 :
                     (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
                      (Sum.inl counterexample.a3) (Sum.inl counterexample.b3)),
                    TreeExitPath U mu3 gamma counterexample.beta counterexample.a3 counterexample.b3
                      P3 →
                     P3.support = counterexample.Q3.support →
                      P3.length = counterexample.Q3.length →
                       ∀ (i1 i2 : Fin (presentation.U.length + (1 : ℕ))),
                        presentation.U.vertex i1 = counterexample.b1 →
                         presentation.U.vertex i2 = counterexample.b2 →
                          (↑i1 : ℕ) < (↑i2 : ℕ) →
                           ∀ (i3 : Fin (presentation.U.length + (1 : ℕ))),
                            presentation.U.vertex i3 = counterexample.b3 →
                             (↑i2 : ℕ) < (↑i3 : ℕ) →
                              Tn.length < (↑i2 : ℕ) →
                               ∀ (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ)) (hi3le : (↑i3 : ℕ) ≤ U.length)
                                (hi3prevpos : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
                                let B : TreeSequence G e0 :=
                                 TreeSequencePrefix U ((↑i3 : ℕ) - (1 : ℕ)) hi3prevpos
                                  (Decidable.byContradiction
                                   fun (a : ¬(↑i3 : ℕ) - (1 : ℕ) ≤ U.length) ↦ by omega);
                                let C : TreeSequence G e0 :=
                                 TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
                                C.length = (↑i3 : ℕ) →
                                 TreeSequenceInitialSegment B U →
                                  TreeSequenceInitialSegment C U →
                                   TreeSequenceInitialSegment B C →
                                    C.length = B.length + (1 : ℕ) →
                                     TreeSequenceInitialSegment Tn B →
                                      TreeSequenceInitialSegment seed B →
                                       ∃ (newPresentation :
                                        RutgersClosedPresentation G k e0 original)
                                        (newCounterexample :
                                        RutgersCounterexample G k e0 original newPresentation),
                                        RutgersCounterexampleMeasure newCounterexample <
                                         RutgersCounterexampleMeasure counterexample

private theorem helper_edgeVertices_296.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (_ : RutgersClosedPresentation G k e0 original) {phi : PartialEdgeColoring E k}
      {a b : Fin k} {u v : V}
      (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v)),
    p.IsPath →
    ∀ {f : E},
    Sum.inr f ∈ p.support →
    ∃ (j : ℕ) (x : V) (y : V),
    (0 : ℕ) < j ∧
      j < p.length ∧
        p.getVert j = Sum.inr f ∧
          p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
            p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
              Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y) := by
  classical
  intro V E _ _ _ G k e0 input T generating original presentation phi a b u v p hp f hf
  obtain ⟨j, hj, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hjpos : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    simp [this] at hj
  have hjlt : j < p.length := by
    by_contra h
    have : j = p.length := by omega
    simp [this] at hj
  have hl := p.adj_getVert_succ (i := j - 1) (by omega)
  have hr := p.adj_getVert_succ hjlt
  rw [show j - 1 + 1 = j by omega, hj] at hl
  rw [hj] at hr
  cases hx : p.getVert (j - 1) with
  | inr g => rw [hx] at hl; exact hl.elim
  | inl x =>
    rw [hx] at hl
    cases hy : p.getVert (j + 1) with
    | inr g => rw [hy] at hr; exact hr.elim
    | inl y =>
      rw [hy] at hr
      have hxf : Incident G x f := hl.1
      have hyf : Incident G y f := hr.1
      have hxy : x ≠ y := by
        intro h
        have heq : p.getVert (j - 1) = p.getVert (j + 1) := by rw [hx, hy, h]
        have := hp.getVert_injOn (by omega : j - 1 ≤ p.length)
          (by omega : j + 1 ≤ p.length) heq
        omega
      exact ⟨j, x, y, hjpos, hjlt, hj, hx, hy, hxf, hyf, hxy,
        (Sym2.mem_and_mem_iff hxy).mp ⟨hxf, hyf⟩⟩

private theorem helper_remote3_362.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let R :
      ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput
        presentation.U presentation.sigma :=
      presentation.corresponding.replacementETT;
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
    ∀ (seed : TreeSequence G e0) (_ : TashkinovClosure sigma seed U)
      (_ : counterexample.b3 ∈ TreeSequenceVertexSet U),
    ∀ gamma ∈ MissingColors G sigma counterexample.b3,
    gamma ≠ counterexample.beta →
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    (IsProperEdgeColoring G mu3 ∧
        IsOneEdgeUncolored mu3 e0 ∧
          StableColoring U Dn sigma mu3 ∧
            ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f) →
    ∀ (A3 : CorrespondingExtendedTashkinovTree G k e0 R mu3 U)
      (A30 : CorrespondingExtendedTashkinovTree G k e0 original mu3 U),
    A30.replacementInput = A3.replacementInput →
    A30.replacementSeries ≍ A3.replacementSeries →
    (∀ {u : V} {f : E},
        u ∉ TreeSequenceVertexSet U →
          Incident G u f →
            TreeIncidentEdge U f → f ∈ BoundaryEdges G (TreeSequenceVertexSet U)) →
    ∀ {u : V},
    u ∉ TreeSequenceVertexSet U →
    counterexample.alpha ∈ MissingColors G sigma u ∨
        counterexample.beta ∈ MissingColors G sigma u →
    gamma ∈ MissingColors G mu3 u ∨ counterexample.beta ∈ MissingColors G mu3 u := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Dn
      seed hclosure hb3 gamma hgamma hgammaBeta mu3 hswap3 A3 A30 _ _ outsideBoundary u hu hm
  by_cases hag : counterexample.alpha = gamma
  · have heq : mu3 = sigma := by
      funext f
      by_cases ht : TreeIncidentEdge U f
      · simp [mu3, OutsideTreeColorSwap, ht]
      · by_cases hc : sigma f = some gamma <;>
          simp [mu3, OutsideTreeColorSwap, ht, hag, hc]
    simpa [heq, hag] using hm
  rcases hm with ha | hb
  · left
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter] at ha ⊢
    rintro ⟨f, huf, hnew⟩
    by_cases ht : TreeIncidentEdge U f
    · have hold := (hswap3.2.2.2 f ht).symm.trans hnew
      exact (hclosure.2 (outsideBoundary hu huf ht) hb3 hold) hgamma
    · by_cases hfa : sigma f = some counterexample.alpha
      · exact ha ⟨f, huf, hfa⟩
      · by_cases hfg : sigma f = some gamma
        · have heq : counterexample.alpha = gamma := by
            simpa [mu3, OutsideTreeColorSwap, ht, hfa, hfg, Ne.symm hag] using hnew
          exact hag heq
        · exact hfg (by simp [mu3, OutsideTreeColorSwap, ht, hfa, hfg] at hnew)
  · right
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter] at hb ⊢
    rintro ⟨f, huf, hnew⟩
    apply hb
    refine ⟨f, huf, ?_⟩
    by_cases ht : TreeIncidentEdge U f
    · exact (hswap3.2.2.2 f ht).symm.trans hnew
    · by_cases hfa : sigma f = some counterexample.alpha
      · have : gamma = counterexample.beta := by
          simpa [mu3, OutsideTreeColorSwap, ht, hfa] using hnew
        exact (hgammaBeta this).elim
      · by_cases hfg : sigma f = some gamma
        · have : counterexample.alpha = counterexample.beta := by
            simpa [mu3, OutsideTreeColorSwap, ht, hfa, hfg, Ne.symm hag] using hnew
          exact (counterexample.colorsDistinct this).elim
        · simpa [mu3, OutsideTreeColorSwap, ht, hfa, hfg] using hnew

private theorem helper_transfer3_406.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let R :
      ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput
        presentation.U presentation.sigma :=
      presentation.corresponding.replacementETT;
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
    ∀ (seed : TreeSequence G e0) (_ : TashkinovClosure sigma seed U) (gamma : Fin k)
      (_ : gamma ≠ counterexample.beta),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
      (_ :
        (IsProperEdgeColoring G mu3 ∧
          IsOneEdgeUncolored mu3 e0 ∧
            StableColoring U Dn sigma mu3 ∧
              ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f))
      (_ :
        (∀ {u v : V}
          (p :
            (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Walk
              (Sum.inl u) (Sum.inl v))
          (_ : TreeExitPath U sigma counterexample.alpha counterexample.beta u v p) {f : E}
          (_ : Sum.inr f ∈ p.support) (_ : TreeIncidentEdge U f),
          f ∈ BoundaryEdges G (TreeSequenceVertexSet U)))
      (_ :
        (∀ {u : V} (_ : u ∉ TreeSequenceVertexSet U)
          (_ :
            counterexample.alpha ∈ MissingColors G sigma u ∨
              counterexample.beta ∈ MissingColors G sigma u),
          gamma ∈ MissingColors G mu3 u ∨ counterexample.beta ∈ MissingColors G mu3 u))
      {u v : V}
      (p :
        (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Walk
          (Sum.inl u) (Sum.inl v))
      (_ : TreeExitPath U sigma counterexample.alpha counterexample.beta u v p),
    ∃ (q :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl u)
        (Sum.inl v)),
    TreeExitPath U mu3 gamma counterexample.beta u v q ∧
      q.support = p.support ∧ q.length = p.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Dn
      seed hclosure gamma hgammaBeta mu3 hswap3 pathBoundary remote3 u v p hexit
  have preserve {w : V} {f : E} (hf : Sum.inr f ∈ p.support)
      (hadj : (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Adj
        (Sum.inl w) (Sum.inr f)) :
      (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Adj
        (Sum.inl w) (Sum.inr f) := by
    refine ⟨hadj.1, ?_⟩
    by_cases ht : TreeIncidentEdge U f
    · have hfBound := pathBoundary p hexit hf ht
      have hfNotAlpha : sigma f ≠ some counterexample.alpha := by
        intro h
        obtain ⟨x, hx, hc⟩ := Finset.mem_biUnion.mp counterexample.alphaMissing
        exact (hclosure.2 hfBound hx h) hc
      exact Or.inr ((hswap3.2.2.2 f ht).trans (hadj.2.resolve_left hfNotAlpha))
    · rcases hadj.2 with hfa | hfb
      · exact Or.inl (by simp [mu3, OutsideTreeColorSwap, ht, hfa])
      · exact Or.inr (by simp [mu3, OutsideTreeColorSwap, ht, hfb,
          counterexample.colorsDistinct.symm, hgammaBeta.symm])
  have hedges : ∀ z, z ∈ p.edges →
      z ∈ (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).edgeSet := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hadj := (SimpleGraph.mem_edgeSet _).mp (p.edges_subset_edgeSet hz)
      have hx := p.fst_mem_support_of_mem_edges hz
      have hy := p.snd_mem_support_of_mem_edges hz
      apply (SimpleGraph.mem_edgeSet _).mpr
      cases x <;> cases y
      · exact hadj.elim
      · exact preserve hy hadj
      · exact (preserve hx hadj.symm).symm
      · exact hadj.elim
  let q := p.transfer (TwoColorIncidenceGraph G mu3 gamma counterexample.beta) hedges
  refine ⟨q, ⟨hexit.1.transfer hedges, ?_, hexit.2.2.1, hexit.2.2.2.1,
    remote3 hexit.2.2.1 hexit.2.2.2.2.1, ?_⟩, by simp [q], by simp [q]⟩
  · simpa [q] using hexit.2.1
  · intro w hw
    simpa [q] using hexit.2.2.2.2.2 w hw

private theorem helper_finish_912.{u_1, u_2} :
    helperFinish912Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed gamma hgammaBeta mu3 i3 hi3pos hi3le C mu4 W hW route4W A40 max40 agree40 agree0
      newPresentation Q1 Q2 Q3 betaTree gammaNotTree Package Good p q r hp hq hr hdpq hdpr hdqr
      hopq hoqr
  have distinctOutside {p q : Package}
      (hd : ∀ x, x ∈ p.2.2.1.support → x ∉ q.2.2.1.support) : p.1 ≠ q.1 := by
    intro h
    apply hd (Sum.inl p.1) p.2.2.1.start_mem_support
    rw [h]
    exact q.2.2.1.start_mem_support
  have distinctInside {p q : Package}
      (hd : ∀ x, x ∈ p.2.2.1.support → x ∉ q.2.2.1.support) : p.2.1 ≠ q.2.1 := by
    intro h
    apply hd (Sum.inl p.2.1) p.2.2.1.end_mem_support
    rw [h]
    exact q.2.2.1.end_mem_support
  let C' : RutgersCounterexample G k e0 original newPresentation := {
    alpha := counterexample.beta
    beta := gamma
    colorsDistinct := hgammaBeta.symm
    alphaMissing := betaTree
    betaPresent := gammaNotTree
    a1 := p.1
    b1 := p.2.1
    a2 := q.1
    b2 := q.2.1
    a3 := r.1
    b3 := r.2.1
    Q1 := p.2.2.1
    Q2 := q.2.2.1
    Q3 := r.2.2.1
    f1 := p.2.2.2
    f2 := q.2.2.2
    f3 := r.2.2.2
    exit1 := hp.1
    exit2 := hq.1
    exit3 := hr.1
    supportDisjoint12 := hdpq
    supportDisjoint13 := hdpr
    supportDisjoint23 := hdqr
    outsideDistinct12 := distinctOutside hdpq
    outsideDistinct13 := distinctOutside hdpr
    outsideDistinct23 := distinctOutside hdqr
    insideDistinct12 := distinctInside hdpq
    insideDistinct13 := distinctInside hdpr
    insideDistinct23 := distinctInside hdqr
    insideOrder12 := hopq
    insideOrder23 := hoqr
    boundary1 := hp.2.1
    boundary2 := hq.2.1
    boundary3 := hr.2.1
    incident1 := hp.2.2.1
    incident2 := hq.2.2.1
    incident3 := hr.2.2.1
    edgeOnWalk1 := hp.2.2.2
    edgeOnWalk2 := hq.2.2.2
    edgeOnWalk3 := hr.2.2.2 }
  exact ⟨C', rfl⟩

private theorem helper_walkContained_1125.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    ∀ (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀ (i3 : Fin (presentation.U.length + (1 : ℕ))) (hi3pos : (1 : ℕ) ≤ (↑i3 : ℕ))
      (hi3le : (↑i3 : ℕ) ≤ U.length),
    let C : TreeSequence G e0 := TreeSequencePrefix U (↑i3 : ℕ) hi3pos hi3le;
    let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
    ∀ (W : TreeSequence G e0) (_ : TashkinovClosure mu4 C W)
      (_ : counterexample.b3 ∈ TreeSequenceVertexSet W)
      (_ : counterexample.beta ∈ MissingColors G mu4 counterexample.b3) {u v : V}
      (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl u)
          (Sum.inl v))
      (_ : v ∈ TreeSequenceVertexSet W) (_ : gamma ∈ TreeMissingColors mu4 W),
    u ∈ TreeSequenceVertexSet W := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample U sigma gamma
      mu3 i3 hi3pos hi3le C mu4 W hW hb3W betaMissing u v p hv hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  let H := TwoColorIncidenceGraph G mu4 counterexample.beta gamma
  let inside : Sum V E → Prop := fun z => match z with
    | Sum.inl x => x ∈ TreeSequenceVertexSet W
    | Sum.inr f => ∀ x, Incident G x f → x ∈ TreeSequenceVertexSet W
  have neighborClosed {x y : Sum V E} (hx : inside x) (hxy : H.Adj x y) : inside y := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hxy.elim
      | inr f =>
        intro y hyf
        by_contra hy
        have hne : x ≠ y := by intro h; exact hy (h ▸ hx)
        have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet W) := by
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x, hx, y, hy, (Sym2.mem_and_mem_iff hne).mp ⟨hxy.1, hyf⟩⟩
        rcases hxy.2 with hb | hg
        · exact (hW.2 hboundary hb3W hb) betaMissing
        · exact (hW.2 hboundary hw hg) hgw
    | inr f =>
      cases y with
      | inl y => exact hx y hxy.1
      | inr g => exact hxy.elim
  have walkClosed {x y : Sum V E} (q : H.Walk x y) : inside x → inside y := by
    induction q with
    | nil => exact id
    | cons hadj q ih => exact fun hx => ih (neighborClosed hx hadj)
  exact walkClosed p.reverse hv

private theorem helper_branch_871.{u_1, u_2} :
    helperBranch871Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed gamma mu3 i3 hi3pos hi3le C mu4 W hW route4W A40 max40 agree40 agree0
      newPresentation Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 L1 L2 L3 hdis12 hdis13 hdis23
      hmeasure Package Good pack1 pack2 pack3 good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj12
      hj13 hj23 h12 h13
  by_cases h23 : j2.val < j3.val
  · obtain ⟨C', heq⟩ := finish pack2 pack3 pack1 good2 good3 good1
      hdis23 (fun x hx hy => hdis12 x hy hx) (fun x hx hy => hdis13 x hy hx)
      ⟨j2, j3, hj2, hj3, h23⟩ ⟨j3, j1, hj3, hj1, by omega⟩
    refine ⟨C', ?_⟩
    simp only [pack1, pack2, pack3] at heq
    omega
  · obtain ⟨C', heq⟩ := finish pack3 pack2 pack1 good3 good2 good1
      (fun x hx hy => hdis23 x hy hx) (fun x hx hy => hdis13 x hy hx)
      (fun x hx hy => hdis12 x hy hx)
      ⟨j3, j2, hj3, hj2, by omega⟩ ⟨j2, j1, hj2, hj1, by omega⟩
    refine ⟨C', ?_⟩
    simp only [pack1, pack2, pack3] at heq
    omega

private theorem helper_branch_1326.{u_1, u_2} :
    helperBranch1326Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed gamma mu3 P1 P2 P3 i1 i2 i3 hi3pos hi3le hi3prevpos C mu4 W hW route4W A40 max40
      agree40 agree0 newPresentation Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 L1 L2 L3 hdis12
      hdis13 hdis23 hmeasure Package Good pack1 pack2 pack3 good1 good2 good3 finish j1 hj1 j2
      hj2 j3 hj3 hj12 hj13 hj23 h12
  by_cases h13 : j1.val < j3.val
  · obtain ⟨C', heq⟩ := finish pack2 pack1 pack3 good2 good1 good3
      (fun x hx hy => hdis12 x hy hx) hdis23 hdis13
      ⟨j2, j1, hj2, hj1, by omega⟩ ⟨j1, j3, hj1, hj3, h13⟩
    refine ⟨C', ?_⟩
    simp only [pack1, pack2, pack3] at heq
    omega
  · exact @helper_branch_871 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating original presentation counterexample seed hseed gamma i3 hi3pos hi3le W
      hW route4W A40 max40 agree40 agree0 Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 hdis12 hdis13
      hdis23 hmeasure good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj12 hj13 hj23 h12 h13
private theorem helper_commonPrefix_945.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {A B X : TreeSequence G e0},
    TreeSequenceInitialSegment A X →
    TreeSequenceInitialSegment B X →
    A.length ≤ B.length →
    TreeSequenceInitialSegment A B := by
  classical
  intro V E G e0 A B X hAX hBX hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    calc
      B.vertex (Fin.castLE _ i) =
          X.vertex (Fin.castLE _ (Fin.castLE _ i)) := (hBX.2.1 _).symm
      _ = X.vertex (Fin.castLE _ i) := by congr 1
      _ = A.vertex i := hAX.2.1 _
  · intro i
    calc
      B.edge (Fin.castLE _ i) =
          X.edge (Fin.castLE _ (Fin.castLE _ i)) := (hBX.2.2 _).symm
      _ = X.edge (Fin.castLE _ i) := by congr 1
      _ = A.edge i := hAX.2.2 _

private theorem helper_transportRoute_1070.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation)
      (_ :
        (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
          (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)),
    let R :
      ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput
        presentation.U presentation.sigma :=
      presentation.corresponding.replacementETT;
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
    ∀ (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
      (_ :
        (IsProperEdgeColoring G mu3 ∧
          IsOneEdgeUncolored mu3 e0 ∧
            StableColoring U Dn sigma mu3 ∧
              ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f))
      (A B : TreeSequence G e0) (_ : TashkinovAugmentationSequence sigma A B)
      (_ : TreeSequenceInitialSegment B U),
    TashkinovAugmentationSequence mu3 A B := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample segmentTrans R
      U sigma n Dn gamma mu3 hswap3 A B hAB hBU
  induction hAB with
  | refl => exact Relation.ReflTransGen.refl
  | @tail B C hAB hBC ih =>
    have hBU' := segmentTrans hBC.2.1 hBU
    refine (ih hBU').tail ?_
    rcases hBC with ⟨hlen, hBC, c, hcolor, hmissing⟩
    refine ⟨hlen, hBC, c, ?_, ?_⟩
    · apply Eq.trans (hswap3.2.2.2 _ ?_) hcolor
      obtain ⟨v, hv⟩ := C.attaches (Fin.cast hlen.symm (Fin.last B.length))
      refine ⟨C.vertex (Fin.cast hlen.symm (Fin.last B.length)).succ,
        TreeSequenceInitialSegmentVertexSetSubset hBU (by simp [TreeSequenceVertexSet]), ?_⟩
      simp [Incident, hv]
    · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmissing
      exact Finset.mem_biUnion.mpr ⟨v, hv, by
        rw [hswap3.2.2.1.2 v (TreeSequenceInitialSegmentVertexSetSubset hBU' hv)]
        exact hc⟩

private theorem helper_pathBoundary_1116.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    ∀
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
          (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v))
          (_ : p.IsPath) {f : E} (_ : Sum.inr f ∈ p.support),
          ∃ (j : ℕ) (x : V) (y : V),
            (0 : ℕ) < j ∧
              j < p.length ∧
                p.getVert j = Sum.inr f ∧
                  p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
                    p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
                      Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y)))
      {u v : V}
      (p :
        (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Walk
          (Sum.inl u) (Sum.inl v))
      (_ : TreeExitPath U sigma counterexample.alpha counterexample.beta u v p) {f : E}
      (_ : Sum.inr f ∈ p.support) (_ : TreeIncidentEdge U f),
    f ∈ BoundaryEdges G (TreeSequenceVertexSet U) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample U sigma
      edgeVertices u v p hexit f hf hti
  obtain ⟨j, x, y, _, _, _, hx, hy, hxf, hyf, hxy, hends⟩ := edgeVertices p hexit.1 hf
  have hxP : Sum.inl x ∈ p.support := by rw [← hx]; exact p.getVert_mem_support _
  have hyP : Sum.inl y ∈ p.support := by rw [← hy]; exact p.getVert_mem_support _
  have hnBoth : ¬ (x ∈ TreeSequenceVertexSet U ∧ y ∈ TreeSequenceVertexSet U) := by
    rintro ⟨hxU, hyU⟩
    exact hxy (((hexit.2.2.2.2.2 x hxU).mp hxP).trans
      ((hexit.2.2.2.2.2 y hyU).mp hyP).symm)
  obtain ⟨w, hw, hwf⟩ := hti
  have hwxy : w = x ∨ w = y := by simpa [Incident, hends] using hwf
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hwxy with hwx | hwy
  · subst w
    exact ⟨x, hw, y, fun hy => hnBoth ⟨hw, hy⟩, hends⟩
  · subst w
    exact ⟨y, hw, x, fun hx => hnBoth ⟨hx, hw⟩, by simpa [Sym2.eq_swap] using hends⟩

private theorem helper_transfer4_1373.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    ∀ (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    let _ : Set (V ⊕ E) :=
      TwoColorComponent G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
    let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
    ∀
      (_ :
        (have C : Set (V ⊕ E) :=
          TwoColorComponent G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
        have phi' : PartialEdgeColoring E k :=
          TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
        (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G mu3 v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                gamma ∈ MissingColors G mu3 v →
                  counterexample.beta ∈ MissingColors G phi' v) ∧
            (∀ (v : V),
                Sum.inl v ∈ C →
                  counterexample.beta ∈ MissingColors G mu3 v →
                    gamma ∈ MissingColors G phi' v) ∧
              ∀ (v : V) (c : Fin k),
                c ≠ gamma →
                  c ≠ counterexample.beta →
                    (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G mu3 v)))
      (_ :
        TwoColorIncidenceGraph G mu4 counterexample.beta gamma =
          TwoColorIncidenceGraph G mu3 gamma counterexample.beta)
      {u v : V}
      (p :
        (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl u)
          (Sum.inl v))
      (_ : TreeExitPath U mu3 gamma counterexample.beta u v p),
    ∃ (q :
      (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl u)
        (Sum.inl v)),
    TreeExitPath U mu4 counterexample.beta gamma u v q ∧
      q.support = p.support ∧ q.length = p.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample U sigma gamma
      mu3 K mu4 behavior4 graph4 u v p hexit
  have hremote : counterexample.beta ∈ MissingColors G mu4 u ∨
      gamma ∈ MissingColors G mu4 u := by
    by_cases huK : Sum.inl u ∈ K
    · rcases hexit.2.2.2.2.1 with hg | hb
      · exact Or.inl (behavior4.2.1 u huK hg)
      · exact Or.inr (behavior4.2.2.1 u huK hb)
    · rw [behavior4.1 u huK]
      exact hexit.2.2.2.2.1.symm
  have hedges : ∀ z, z ∈ p.edges →
      z ∈ (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).edgeSet := by
    intro z hz
    rw [graph4]
    exact p.edges_subset_edgeSet hz
  let q := p.transfer (TwoColorIncidenceGraph G mu4 counterexample.beta gamma) hedges
  refine ⟨q, ⟨hexit.1.transfer hedges, ?_, hexit.2.2.1,
    hexit.2.2.2.1, hremote, ?_⟩, by simp [q], by simp [q]⟩
  · simpa [q] using hexit.2.1
  · intro w hw
    simpa [q] using hexit.2.2.2.2.2 w hw

private theorem helper_outside4_1441.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    ∀ (_ : counterexample.b3 ∈ TreeSequenceVertexSet U) (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
    ∀ (W : TreeSequence G e0)
      (_ : ColoredVertexSetElementary G mu4 (TreeSequenceVertexSet W))
      (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl counterexample.a1) (Sum.inl counterexample.b1))
      (_ :
        TreeExitPath U mu4 counterexample.beta gamma counterexample.a1 counterexample.b1 Q1)
      (Q2 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl counterexample.a2) (Sum.inl counterexample.b2))
      (_ :
        TreeExitPath U mu4 counterexample.beta gamma counterexample.a2 counterexample.b2 Q2)
      (_ : counterexample.b1 ∈ TreeSequenceVertexSet W)
      (_ : counterexample.b2 ∈ TreeSequenceVertexSet W)
      (_ :
        (∀ {u v : V}
          (_ :
            (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl u)
              (Sum.inl v))
          (_ : v ∈ TreeSequenceVertexSet W) (_ : gamma ∈ TreeMissingColors mu4 W),
          u ∈ TreeSequenceVertexSet W))
      (_ :
        (∀ {a : V} (_ : a ∈ TreeSequenceVertexSet W) (_ : a ≠ counterexample.b3),
          counterexample.beta ∉ MissingColors G mu4 a))
      {a : V} (_ : a ∉ TreeSequenceVertexSet U)
      (_ : counterexample.beta ∈ MissingColors G mu4 a ∨ gamma ∈ MissingColors G mu4 a),
    a ∉ TreeSequenceVertexSet W := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample U sigma hb3
      gamma mu3 mu4 W elementary4 Q1 hQ1 Q2 hQ2 hb1W hb2W walkContained notBeta a haU hm haW
  have hab3 : a ≠ counterexample.b3 := by intro h; exact haU (h ▸ hb3)
  have hga := hm.resolve_left (notBeta haW hab3)
  have hgTree : gamma ∈ TreeMissingColors mu4 W := Finset.mem_biUnion.mpr ⟨a, haW, hga⟩
  have ha1W := walkContained Q1 hb1W hgTree
  have ha2W := walkContained Q2 hb2W hgTree
  have ha13 : counterexample.a1 ≠ counterexample.b3 := by
    intro h; exact counterexample.exit1.2.2.1 (h ▸ hb3)
  have ha23 : counterexample.a2 ≠ counterexample.b3 := by
    intro h; exact counterexample.exit2.2.2.1 (h ▸ hb3)
  have hg1 := hQ1.2.2.2.2.1.resolve_left (notBeta ha1W ha13)
  have hg2 := hQ2.2.2.2.2.1.resolve_left (notBeta ha2W ha23)
  exact Finset.disjoint_left.mp
    (elementary4 ha1W ha2W counterexample.outsideDistinct12) hg1 hg2

private theorem helper_hL1strict_1522.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation),
    let R :
      ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput
        presentation.U presentation.sigma :=
      presentation.corresponding.replacementETT;
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    let _ : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
    ∀ (gamma : Fin k),
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    ∀
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
          (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v))
          (_ : p.IsPath) {f : E} (_ : Sum.inr f ∈ p.support),
          ∃ (j : ℕ) (x : V) (y : V),
            (0 : ℕ) < j ∧
              j < p.length ∧
                p.getVert j = Sum.inr f ∧
                  p.getVert (j - (1 : ℕ)) = Sum.inl x ∧
                    p.getVert (j + (1 : ℕ)) = Sum.inl y ∧
                      Incident G x f ∧ Incident G y f ∧ x ≠ y ∧ G.ends f = s(x, y)))
      (P1 :
        (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
          (Sum.inl counterexample.a1) (Sum.inl counterexample.b1))
      (_ : P1.support = counterexample.Q1.support)
      (_ :
        (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
          (Sum.inl counterexample.a2) (Sum.inl counterexample.b2))
      (_ :
        (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
          (Sum.inl counterexample.a3) (Sum.inl counterexample.b3))
      (_ _ i3 : Fin (presentation.U.length + (1 : ℕ))) (_ : (1 : ℕ) ≤ (↑i3 : ℕ))
      (_ : (↑i3 : ℕ) ≤ U.length) (_ : (1 : ℕ) ≤ (↑i3 : ℕ) - (1 : ℕ)),
    let mu4 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3);
    ∀ (W : TreeSequence G e0)
      (Q1 :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl counterexample.a1) (Sum.inl counterexample.b1))
      (_ : Q1.support = P1.support)
      (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl counterexample.a2) (Sum.inl counterexample.b2))
      (_ :
        (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl counterexample.a3) (Sum.inl counterexample.b3))
      (_ : (∀ (v : V) (_ : Incident G v counterexample.f1), v ∈ TreeSequenceVertexSet W))
      (c1 : V) (hc1 : Sum.inl c1 ∈ Q1.support)
      (_ :
        TreeExitPath W mu4 counterexample.beta gamma counterexample.a1 c1
          (Q1.takeUntil (Sum.inl c1) hc1)),
    let L1 :
      (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
        (Sum.inl counterexample.a1) (Sum.inl c1) :=
      Q1.takeUntil (Sum.inl c1) hc1;
    L1.length < Q1.length := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n
      gamma mu3 edgeVertices P1 hsP1 P2 P3 i1 i2 i3 hi3pos hi3le hi3prevpos mu4 W Q1 hsQ1 Q2 Q3
      hf1ends c1 hc1 hL1 L1
  have hf1P : Sum.inr counterexample.f1 ∈ Q1.support := by
    rw [hsQ1, hsP1]
    exact counterexample.edgeOnWalk1
  have hf1notL : Sum.inr counterexample.f1 ∉ L1.support := by
    intro hf
    obtain ⟨j, x, y, _, _, _, hx, hy, hxf, hyf, hxy, _⟩ := edgeVertices L1 hL1.1 hf
    have hxW := hf1ends x hxf
    have hyW := hf1ends y hyf
    have hxc := (hL1.2.2.2.2.2 x hxW).mp (by rw [← hx]; exact L1.getVert_mem_support _)
    have hyc := (hL1.2.2.2.2.2 y hyW).mp (by rw [← hy]; exact L1.getVert_mem_support _)
    exact hxy (hxc.trans hyc.symm)
  have hle : L1.length ≤ Q1.length := Q1.length_takeUntil_le_length hc1
  by_contra h
  have heq : L1.length = Q1.length := by omega
  have hsEq : L1.support = Q1.support := by
    have hpref := Q1.support_takeUntil_prefix_support hc1
    apply hpref.eq_of_length
    simpa only [SimpleGraph.Walk.length_support] using congrArg (fun n => n + 1) heq
  exact hf1notL (hsEq.symm ▸ hf1P)

private theorem helper_branch_1689.{u_1, u_2} :
    helperBranch1689Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed gamma mu3 i3 hi3pos hi3le C mu4 W hW route4W A40 max40 agree40 agree0
      newPresentation Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 L1 L2 L3 hdis12 hdis13 hdis23
      hmeasure Package Good pack1 pack2 pack3 good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj13
      hj23 h12 h23
  by_cases h13 : j1.val < j3.val
  · obtain ⟨C', heq⟩ := finish pack1 pack3 pack2 good1 good3 good2
      hdis13 hdis12 (fun x hx hy => hdis23 x hy hx)
      ⟨j1, j3, hj1, hj3, h13⟩ ⟨j3, j2, hj3, hj2, by omega⟩
    refine ⟨C', ?_⟩
    simp only [pack1, pack2, pack3] at heq
    omega
  · obtain ⟨C', heq⟩ := finish pack3 pack1 pack2 good3 good1 good2
      (fun x hx hy => hdis13 x hy hx) (fun x hx hy => hdis23 x hy hx) hdis12
      ⟨j3, j1, hj3, hj1, by omega⟩ ⟨j1, j2, hj1, hj2, h12⟩
    refine ⟨C', ?_⟩
    simp only [pack1, pack2, pack3] at heq
    omega

private theorem helper_branch_1588.{u_1, u_2} :
    helperBranch1588Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed gamma mu3 P1 P2 P3 i1 i2 i3 hi3pos hi3le hi3prevpos C mu4 W hW route4W A40 max40
      agree40 agree0 newPresentation Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 L1 L2 L3 hdis12
      hdis13 hdis23 hmeasure Package Good pack1 pack2 pack3 good1 good2 good3 finish j1 hj1 j2
      hj2 j3 hj3 hj13 hj23 h12
  by_cases h23 : j2.val < j3.val
  · obtain ⟨C', heq⟩ := finish pack1 pack2 pack3 good1 good2 good3
      hdis12 hdis13 hdis23 ⟨j1, j2, hj1, hj2, h12⟩ ⟨j2, j3, hj2, hj3, h23⟩
    exact ⟨C', by simpa [pack1, pack2, pack3, heq] using hmeasure⟩
  · exact @helper_branch_1689 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating original presentation counterexample seed hseed gamma i3 hi3pos hi3le W
      hW route4W A40 max40 agree40 agree0 Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2 c3 hc3 g3 hdis12 hdis13
      hdis23 hmeasure good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj13 hj23 h12 h23
private theorem helper_continuation_2244.{u_1, u_2} :
    helperContinuation2244Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original presentation counterexample R U sigma n Tn
      seed hseed hb1 hb2 hb3 gamma hgammaBeta mu3 edgeVertices P1 hsP1 hlP1 P2 hsP2 hlP2 P3 hsP3
      hlP3 i1 i2 i3 hi3pos hi3le hi3prevpos C mu4 W hW route4W A40 max40 agree40 agree0
      newPresentation elementary4 Q1 hQ1 hsQ1 hlQ1 Q2 hQ2 hsQ2 hlQ2 Q3 hQ3 hsQ3 hlQ3 hb1W hb2W
      hb3W betaMissing betaTree fixedRetained
  have hf1color : mu4 counterexample.f1 = some counterexample.beta :=
    fixedRetained hb1 counterexample.insideDistinct13 counterexample.incident1
      (Finset.mem_filter.mp counterexample.boundary1).2
  have hf2color : mu4 counterexample.f2 = some counterexample.beta :=
    fixedRetained hb2 counterexample.insideDistinct23 counterexample.incident2
      (Finset.mem_filter.mp counterexample.boundary2).2
  have retainedEnds {b : V} {f : E} (hb : b ∈ TreeSequenceVertexSet W)
      (hbf : Incident G b f) (hf : mu4 f = some counterexample.beta) :
      ∀ v, Incident G v f → v ∈ TreeSequenceVertexSet W := by
    intro v hv
    by_contra hvW
    have hbv : b ≠ v := by intro h; exact hvW (h ▸ hb)
    have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet W) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b, hb, v, hvW, (Sym2.mem_and_mem_iff hbv).mp ⟨hbf, hv⟩⟩
    exact (hW.2 hboundary hb3W hf) betaMissing
  have hf1ends := retainedEnds hb1W counterexample.incident1 hf1color
  have hf2ends := retainedEnds hb2W counterexample.incident2 hf2color
  have walkContained {u v : V}
      (p : (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl u) (Sum.inl v))
      (hv : v ∈ TreeSequenceVertexSet W) (hg : gamma ∈ TreeMissingColors mu4 W) :
      u ∈ TreeSequenceVertexSet W := by
    exact @helper_walkContained_1125 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating original presentation counterexample gamma i3 hi3pos hi3le W hW
        hb3W betaMissing u v p hv hg
  have notBeta {a : V} (ha : a ∈ TreeSequenceVertexSet W)
      (hab : a ≠ counterexample.b3) : counterexample.beta ∉ MissingColors G mu4 a := by
    intro hm
    exact Finset.disjoint_left.mp (elementary4 ha hb3W hab) hm betaMissing
  have outside4 {a : V} (haU : a ∉ TreeSequenceVertexSet U)
      (hm : counterexample.beta ∈ MissingColors G mu4 a ∨ gamma ∈ MissingColors G mu4 a) :
      a ∉ TreeSequenceVertexSet W := by
    exact @helper_outside4_1441 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating original presentation counterexample hb3 gamma W elementary4 Q1 hQ1
        Q2 hQ2 hb1W hb2W walkContained notBeta a haU hm
  have ha1W := outside4 counterexample.exit1.2.2.1 hQ1.2.2.2.2.1
  have ha2W := outside4 counterexample.exit2.2.2.1 hQ2.2.2.2.2.1
  have ha3W := outside4 counterexample.exit3.2.2.1 hQ3.2.2.2.2.1
  have betaClosed : TreeColorSetClosed G mu4 W {counterexample.beta} := by
    intro c hc
    have heq : c = counterexample.beta := by simpa using hc
    subst c
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hd := Finset.mem_filter.mp hf
    exact (hW.2 hd.1 hb3W hd.2) betaMissing
  have firstEntry {u v : V}
      (p : (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl u) (Sum.inl v))
      (hp : p.IsPath) (hu : u ∉ TreeSequenceVertexSet W) (hv : v ∈ TreeSequenceVertexSet W)
      (hm : counterexample.beta ∈ MissingColors G mu4 u ∨ gamma ∈ MissingColors G mu4 u) :
      ∃ (c : V) (hc : Sum.inl c ∈ p.support),
        TreeExitPath W mu4 counterexample.beta gamma u c (p.takeUntil (Sum.inl c) hc) ∧
        ∃ f, f ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
          Incident G c f ∧ Sum.inr f ∈ (p.takeUntil (Sum.inl c) hc).support := by
    obtain ⟨c, _, member, exit⟩ :=
      TreeExitPath.firstEntry W p hp hm hu ⟨v, hv, p.end_mem_support⟩
    obtain ⟨edge, _, boundary, incident, support⟩ := exit.closedLastBoundaryEdge betaClosed
    exact ⟨c, member, exit, edge, boundary, incident, support⟩
  obtain ⟨c1, hc1, hL1, g1, hg1, hiG1, hsG1⟩ :=
    firstEntry Q1 hQ1.1 ha1W hb1W hQ1.2.2.2.2.1
  obtain ⟨c2, hc2, hL2, g2, hg2, hiG2, hsG2⟩ :=
    firstEntry Q2 hQ2.1 ha2W hb2W hQ2.2.2.2.2.1
  obtain ⟨c3, hc3, hL3, g3, hg3, hiG3, hsG3⟩ :=
    firstEntry Q3 hQ3.1 ha3W hb3W hQ3.2.2.2.2.1
  let L1 := Q1.takeUntil (Sum.inl c1) hc1
  let L2 := Q2.takeUntil (Sum.inl c2) hc2
  let L3 := Q3.takeUntil (Sum.inl c3) hc3
  have hdis12 : ∀ x, x ∈ L1.support → x ∉ L2.support := by
    intro x hx1 hx2
    apply counterexample.supportDisjoint12 x
    · rw [← hsP1, ← hsQ1]
      exact Q1.support_takeUntil_subset_support hc1 hx1
    · rw [← hsP2, ← hsQ2]
      exact Q2.support_takeUntil_subset_support hc2 hx2
  have hdis13 : ∀ x, x ∈ L1.support → x ∉ L3.support := by
    intro x hx1 hx3
    apply counterexample.supportDisjoint13 x
    · rw [← hsP1, ← hsQ1]
      exact Q1.support_takeUntil_subset_support hc1 hx1
    · rw [← hsP3, ← hsQ3]
      exact Q3.support_takeUntil_subset_support hc3 hx3
  have hdis23 : ∀ x, x ∈ L2.support → x ∉ L3.support := by
    intro x hx2 hx3
    apply counterexample.supportDisjoint23 x
    · rw [← hsP2, ← hsQ2]
      exact Q2.support_takeUntil_subset_support hc2 hx2
    · rw [← hsP3, ← hsQ3]
      exact Q3.support_takeUntil_subset_support hc3 hx3
  have hc12 : c1 ≠ c2 := by
    intro h
    exact hdis12 _ L1.end_mem_support (h ▸ L2.end_mem_support)
  have hc13 : c1 ≠ c3 := by
    intro h
    exact hdis13 _ L1.end_mem_support (h ▸ L3.end_mem_support)
  have hc23 : c2 ≠ c3 := by
    intro h
    exact hdis23 _ L2.end_mem_support (h ▸ L3.end_mem_support)
  have gammaNotTree : gamma ∉ TreeMissingColors mu4 W := by
    intro hg
    obtain ⟨v, hv, hgv⟩ := Finset.mem_biUnion.mp hg
    have hd := Finset.mem_filter.mp hg1
    exact (hW.2 hd.1 hv hd.2) hgv
  have hL1strict : L1.length < Q1.length := by
    exact @helper_hL1strict_1522 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating original presentation counterexample gamma edgeVertices P1 hsP1 P2
        P3 i1 i2 i3 hi3pos hi3le hi3prevpos W Q1 hsQ1 Q2 Q3 hf1ends c1 hc1 hL1
  have hmeasure : L1.length + L2.length + L3.length <
      RutgersCounterexampleMeasure counterexample := by
    have hle2 : L2.length ≤ Q2.length := Q2.length_takeUntil_le_length hc2
    have hle3 : L3.length ≤ Q3.length := Q3.length_takeUntil_le_length hc3
    unfold RutgersCounterexampleMeasure
    rw [← hlP1, ← hlP2, ← hlP3, ← hlQ1, ← hlQ2, ← hlQ3]
    omega
  let Package := Σ a : V, Σ b : V,
    (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk (Sum.inl a) (Sum.inl b) × E
  let Good : Package → Prop := fun p =>
    TreeExitPath W mu4 counterexample.beta gamma p.1 p.2.1 p.2.2.1 ∧
      p.2.2.2 ∈ BoundaryColorEdges G mu4 (TreeSequenceVertexSet W) gamma ∧
      Incident G p.2.1 p.2.2.2 ∧ Sum.inr p.2.2.2 ∈ p.2.2.1.support
  let pack1 : Package := ⟨counterexample.a1, c1, L1, g1⟩
  let pack2 : Package := ⟨counterexample.a2, c2, L2, g2⟩
  let pack3 : Package := ⟨counterexample.a3, c3, L3, g3⟩
  have good1 : Good pack1 := ⟨hL1, hg1, hiG1, hsG1⟩
  have good2 : Good pack2 := ⟨hL2, hg2, hiG2, hsG2⟩
  have good3 : Good pack3 := ⟨hL3, hg3, hiG3, hsG3⟩
  have finish (p q r : Package) (hp : Good p) (hq : Good q) (hr : Good r)
      (hdpq : ∀ x, x ∈ p.2.2.1.support → x ∉ q.2.2.1.support)
      (hdpr : ∀ x, x ∈ p.2.2.1.support → x ∉ r.2.2.1.support)
      (hdqr : ∀ x, x ∈ q.2.2.1.support → x ∉ r.2.2.1.support)
      (hopq : TreeVertexOrder W p.2.1 q.2.1)
      (hoqr : TreeVertexOrder W q.2.1 r.2.1) :
      ∃ C' : RutgersCounterexample G k e0 original newPresentation,
        RutgersCounterexampleMeasure C' =
          p.2.2.1.length + q.2.2.1.length + r.2.2.1.length := by
    exact @helper_finish_912 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating original presentation counterexample seed hseed gamma hgammaBeta i3
        hi3pos hi3le W hW route4W A40 max40 agree40 agree0 Q1 Q2 Q3 betaTree gammaNotTree p q r
        hp hq hr hdpq hdpr hdqr hopq hoqr
  obtain ⟨j1, hj1⟩ : ∃ j, W.vertex j = c1 := by
    simpa [TreeSequenceVertexSet] using hL1.2.2.2.1
  obtain ⟨j2, hj2⟩ : ∃ j, W.vertex j = c2 := by
    simpa [TreeSequenceVertexSet] using hL2.2.2.2.1
  obtain ⟨j3, hj3⟩ : ∃ j, W.vertex j = c3 := by
    simpa [TreeSequenceVertexSet] using hL3.2.2.2.1
  have hj12 : j1.val ≠ j2.val := by
    intro h
    exact hc12 (hj1.symm.trans ((congrArg W.vertex (Fin.ext h)).trans hj2))
  have hj13 : j1.val ≠ j3.val := by
    intro h
    exact hc13 (hj1.symm.trans ((congrArg W.vertex (Fin.ext h)).trans hj3))
  have hj23 : j2.val ≠ j3.val := by
    intro h
    exact hc23 (hj2.symm.trans ((congrArg W.vertex (Fin.ext h)).trans hj3))
  refine ⟨newPresentation, ?_⟩
  by_cases h12 : j1.val < j2.val
  · exact @helper_branch_1588 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating original presentation counterexample seed hseed gamma P1 P2 P3 i1 i2 i3
      hi3pos hi3le hi3prevpos W hW route4W A40 max40 agree40 agree0 Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2
      c3 hc3 g3 hdis12 hdis13 hdis23 hmeasure good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj13
      hj23 h12
  · exact @helper_branch_1326 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating original presentation counterexample seed hseed gamma P1 P2 P3 i1 i2 i3
      hi3pos hi3le hi3prevpos W hW route4W A40 max40 agree40 agree0 Q1 Q2 Q3 c1 hc1 g1 c2 hc2 g2
      c3 hc3 g3 hdis12 hdis13 hdis23 hmeasure good1 good2 good3 finish j1 hj1 j2 hj2 j3 hj3 hj12
      hj13 hj23 h12

private theorem helper_continuation_2163.{u_1, u_2} :
    helperContinuation2163Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original hcurrentOne presentation counterexample
      segmentTrans terminalAgreement R U sigma n Tn Dn seed hseed hb1 hb2 hb3 gamma hgammaBeta
      mu3 hswap3 route3 A3 max3 edgeVertices P1 hP1 hsP1 hlP1 P2 hP2 hsP2 hlP2 P3 hP3 hsP3 hlP3
      i1 i2 i3 hi23 hTni2 hi3pos hi3le hi3prevpos B C hClen hCU hBC hpenultimate hTnB hseedC hb3C
      hb1C hb2C K mu4 hgamma3 hKU fixedOutsideVertex behavior4 missingB agree3 M4 fixedC
  have route3C : TashkinovAugmentationSequence mu3 seed C :=
    TashkinovAugmentationSequenceRestrict mu3 seed C U route3 hseedC hCU
  have route4C : TashkinovAugmentationSequence mu4 seed C :=
    TashkinovAugmentationSequenceColoringTransport mu3 mu4 seed B C route3C
      hBC hpenultimate (fun j _ => fixedC j) missingB
  obtain ⟨W, hW⟩ := TashkinovClosureExists mu4 C
  have hCW := TashkinovAugmentationSequenceInitialSegment mu4 C W hW.1
  have hTnW := segmentTrans (segmentTrans hTnB hBC) hCW
  have hstrictW : Tn.length < W.length := by have := hCW.1; omega
  have route4W : TashkinovAugmentationSequence mu4 seed W := route4C.trans hW.1
  obtain ⟨A4⟩ : Nonempty (CorrespondingExtendedTashkinovTree
      G k e0 A3.replacementETT mu4 W) := by
    apply M4.2.2 W (by rwa [agree3.1]) (by simpa [agree3.1] using hstrictW)
    rcases hseed with hPE | hSER
    · refine Or.inl ⟨by simpa [agree3.2.1] using hPE.1, ?_⟩
      rw [agree3.1]
      change TashkinovAugmentationSequence mu4 Tn W
      rwa [← hPE.2]
    · obtain ⟨f, he, ha⟩ := hSER.2
      exact Or.inr ⟨by simpa [agree3.2.1] using hSER.1, f, seed,
        by simpa [agree3.2.2] using he, by simpa [agree3.1] using ha, route4W⟩
  have max4 : MaximumProperty A4.replacementETT :=
    MaximumPropertyTransport G k e0 A3.replacementETT mu4 M4 W A4 max3
  obtain ⟨A4R, h4input, _, h4ETT⟩ := CorrespondingExtendedTashkinovTreeTransTrees
    G k e0 presentation.corresponding.replacementInput U U W sigma mu3 mu4 R A3 A4
  obtain ⟨A40, h40input, _, h40ETT⟩ := CorrespondingExtendedTashkinovTreeTransTrees
    G k e0 input T U W generating sigma mu4 original presentation.corresponding A4R
  have maximumHEq {i j : PartialEdgeColoring E k} {A : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      {F : ExtendedTashkinovTree G k e0 i A phi}
      {F' : ExtendedTashkinovTree G k e0 j A phi}
      (hij : i = j) (hFF' : HEq F F') (hm : MaximumProperty F') : MaximumProperty F := by
    subst j
    rw [eq_of_heq hFF']
    exact hm
  have max40 : MaximumProperty A40.replacementETT :=
    maximumHEq h40input h40ETT (maximumHEq h4input h4ETT max4)
  have agree40 := terminalAgreement original A40
  have agree0 := terminalAgreement original presentation.corresponding
  have elementary4 : ColoredVertexSetElementary G mu4 (TreeSequenceVertexSet W) :=
    hcurrentOne A40.replacementETT A40.rungAgreement max40
  have colorPair4 (f : E) :
      (mu4 f = some counterexample.beta ∨ mu4 f = some gamma) ↔
        (mu3 f = some gamma ∨ mu3 f = some counterexample.beta) := by
    by_cases hK : Sum.inr f ∈ K
    · by_cases hg : mu3 f = some gamma
      · simp [mu4, TwoColorComponentSwap, K, hK, hg]
      · by_cases hb : mu3 f = some counterexample.beta
        · simp [mu4, TwoColorComponentSwap, K, hK, hb]
        · simp [mu4, TwoColorComponentSwap, K, hK, hg, hb]
    · simp [mu4, TwoColorComponentSwap, K, hK, or_comm]
  have graph4 : TwoColorIncidenceGraph G mu4 counterexample.beta gamma =
      TwoColorIncidenceGraph G mu3 gamma counterexample.beta := by
    ext x y
    cases x <;> cases y <;> simp only [TwoColorIncidenceGraph]
    all_goals first  | rw [colorPair4]
  have transfer4 {u v : V}
      (p : (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk (Sum.inl u) (Sum.inl v))
      (hexit : TreeExitPath U mu3 gamma counterexample.beta u v p) :
      ∃ q : (TwoColorIncidenceGraph G mu4 counterexample.beta gamma).Walk
          (Sum.inl u) (Sum.inl v),
        TreeExitPath U mu4 counterexample.beta gamma u v q ∧
          q.support = p.support ∧ q.length = p.length := by
    exact @helper_transfer4_1373 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating original presentation counterexample gamma behavior4 graph4 u v p
        hexit
  obtain ⟨Q1, hQ1, hsQ1, hlQ1⟩ := transfer4 P1 hP1
  obtain ⟨Q2, hQ2, hsQ2, hlQ2⟩ := transfer4 P2 hP2
  obtain ⟨Q3, hQ3, hsQ3, hlQ3⟩ := transfer4 P3 hP3
  have hb1W := TreeSequenceInitialSegmentVertexSetSubset hCW hb1C
  have hb2W := TreeSequenceInitialSegmentVertexSetSubset hCW hb2C
  have hb3W := TreeSequenceInitialSegmentVertexSetSubset hCW hb3C
  have betaMissing : counterexample.beta ∈ MissingColors G mu4 counterexample.b3 :=
    behavior4.2.1 counterexample.b3 (by rfl) hgamma3
  have betaTree : counterexample.beta ∈ TreeMissingColors mu4 W :=
    Finset.mem_biUnion.mpr ⟨counterexample.b3, hb3W, betaMissing⟩
  have fixedRetained {b : V} {f : E} (hb : b ∈ TreeSequenceVertexSet U)
      (hb3 : b ≠ counterexample.b3) (hbf : Incident G b f)
      (hcolor : sigma f = some counterexample.beta) : mu4 f = some counterexample.beta := by
    have hbK : Sum.inl b ∉ K := fun h => hb3 ((hKU b hb).mp h)
    exact (fixedOutsideVertex hbK hbf).trans ((hswap3.2.2.2 f ⟨b, hb, hbf⟩).trans hcolor)
  exact @helper_continuation_2244 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating original presentation counterexample seed hseed hb1 hb2 hb3 gamma
      hgammaBeta edgeVertices P1 hsP1 hlP1 P2 hsP2 hlP2 P3 hsP3 hlP3 i1 i2 i3 hi3pos hi3le
      hi3prevpos W hW route4W A40 max40 agree40 agree0 elementary4 Q1 hQ1 hsQ1 hlQ1 Q2 hQ2 hsQ2
      hlQ2 Q3 hQ3 hsQ3 hlQ3 hb1W hb2W hb3W betaMissing betaTree fixedRetained
private theorem helper_continuation_2093.{u_1, u_2} :
    helperContinuation2093Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original hcurrentOne hcurrentSix presentation
      counterexample segmentTrans terminalAgreement R U sigma n Tn Dn seed hseed hb1 hb2 hb3
      gamma hgamma hgammaBeta mu3 hswap3 route3 A3 max3 edgeVertices P1 hP1 hsP1 hlP1 P2 hP2 hsP2
      hlP2 P3 hP3 hsP3 hlP3 i1 i2 hi1 hi2 hi12 i3 hi3 hi23 hTni2 hi3pos hi3le hi3prevpos B C
      hClen hBU hCU hBC hpenultimate hTnB hseedB
  have hseedC := segmentTrans hseedB hBC
  have hb3C : counterexample.b3 ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨Fin.last C.length, ?_⟩
    apply (hCU.2.1 _).symm.trans
    calc
      U.vertex (Fin.castLE _ (Fin.last C.length)) = U.vertex i3 := by
        congr 1
      _ = counterexample.b3 := hi3
  have hb1C : counterexample.b1 ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i1.val, by omega⟩, ?_⟩
    exact (hCU.2.1 _).symm.trans hi1
  have hb2C : counterexample.b2 ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i2.val, by omega⟩, ?_⟩
    exact (hCU.2.1 _).symm.trans hi2
  have hb3notB : counterexample.b3 ∉ TreeSequenceVertexSet B := by
    intro h
    obtain ⟨j, hj⟩ : ∃ j, B.vertex j = counterexample.b3 := by
      simpa [TreeSequenceVertexSet] using h
    have heq := U.vertex_injective ((hBU.2.1 j).trans (hj.trans hi3.symm))
    have hval := congrArg Fin.val heq
    have := j.isLt
    simp only [Fin.val_castLE] at hval
    omega
  let K := TwoColorComponent G mu3 gamma counterexample.beta (Sum.inl counterexample.b3)
  let mu4 := TwoColorComponentSwap G mu3 gamma counterexample.beta (Sum.inl counterexample.b3)
  have hgamma3 : gamma ∈ MissingColors G mu3 counterexample.b3 := by
    rw [hswap3.2.2.1.2 _ hb3]
    exact hgamma
  have hKU : ∀ w, w ∈ TreeSequenceVertexSet U →
      (Sum.inl w ∈ K ↔ w = counterexample.b3) :=
    TreeExitComponentMeetsTreeOnlyAtExit U mu3 gamma counterexample.beta
      counterexample.b3 hswap3.1 hgamma3 ⟨counterexample.a3, P3, hP3⟩
  have hKB : ∀ w, w ∈ TreeSequenceVertexSet B → Sum.inl w ∉ K := by
    intro w hw hK
    have hw3 := (hKU w (TreeSequenceInitialSegmentVertexSetSubset hBU hw)).mp hK
    exact hb3notB (hw3 ▸ hw)
  have fixedOutsideVertex {v : V} (hv : Sum.inl v ∉ K) {f : E}
      (hf : Incident G v f) : mu4 f = mu3 f := by
    by_cases hK : Sum.inr f ∈ K
    · have hnot : ¬ (mu3 f = some gamma ∨ mu3 f = some counterexample.beta) := by
        intro hcolor
        have hadj : (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Adj
            (Sum.inl v) (Sum.inr f) := ⟨hf, hcolor⟩
        apply hv
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hK
      simp only [not_or] at hnot
      simp [mu4, TwoColorComponentSwap, K, hK, hnot.1, hnot.2]
    · simp [mu4, TwoColorComponentSwap, K, hK]
  have fixedB : ∀ f, TreeIncidentEdge B f → mu4 f = mu3 f := by
    rintro f ⟨v, hv, hf⟩
    exact fixedOutsideVertex (hKB v hv) hf
  have behavior4 := TwoColorComponentSwapMissingBehavior G mu3 gamma
    counterexample.beta hgammaBeta hswap3.1 (Sum.inl counterexample.b3)
  have missingB : ∀ v, v ∈ TreeSequenceVertexSet B →
      MissingColors G mu4 v = MissingColors G mu3 v := by
    intro v hv
    exact behavior4.1 v (hKB v hv)
  have proper4 : IsProperEdgeColoring G mu4 :=
    TwoColorComponentSwapProper G mu3 gamma counterexample.beta hgammaBeta hswap3.1 _
  have one4 : IsOneEdgeUncolored mu4 e0 := by
    constructor
    · simp [mu4, TwoColorComponentSwap, hswap3.2.1.1]
    · intro f hf
      obtain ⟨c, hc⟩ := hswap3.2.1.2 f hf
      by_cases hK : Sum.inr f ∈ K
      · by_cases hcg : c = gamma
        · exact ⟨counterexample.beta, by simp [mu4, TwoColorComponentSwap, K, hK, hc, hcg]⟩
        · by_cases hcb : c = counterexample.beta
          · exact ⟨gamma, by simp [mu4, TwoColorComponentSwap, K, hK, hc, hcb, hgammaBeta.symm]⟩
          · exact ⟨c, by simp [mu4, TwoColorComponentSwap, K, hK, hc, hcg, hcb]⟩
      · exact ⟨c, by simp [mu4, TwoColorComponentSwap, K, hK, hc]⟩
  have agree3 := terminalAgreement R A3
  have stable4 : StableColoring
      (A3.replacementETT.series.data.tree (Fin.last A3.replacementETT.rounds).castSucc)
      (TashkinovStoredColors A3.replacementETT.series.data (Fin.last A3.replacementETT.rounds))
      (A3.replacementETT.series.data.coloring (Fin.last A3.replacementETT.rounds)) mu4 := by
    rw [agree3.1, ← A3.replacementETT.generatingColoring]
    refine ⟨?_, ?_⟩
    · rintro f ⟨v, hv, hf⟩ _
      exact fixedB f ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnB hv, hf⟩
    · intro v hv
      exact missingB v (TreeSequenceInitialSegmentVertexSetSubset hTnB hv)
  have M4 : ModColoring A3.replacementETT mu4 :=
    hcurrentSix A3.replacementETT
      (A3.rungAgreement.trans presentation.corresponding.rungAgreement) max3
      mu4 proper4 one4 stable4
  have fixedC : ∀ j : Fin C.length, mu4 (C.edge j) = mu3 (C.edge j) := by
    intro j
    obtain ⟨i, hi⟩ := C.attaches j
    have hiB : i.val < B.length + 1 := by have := i.isLt; have := j.isLt; omega
    let q : Fin (B.length + 1) := ⟨i.val, hiB⟩
    have hiEq : C.vertex (Fin.castLT i (by omega)) = B.vertex q := by
      exact hBC.2.1 q
    apply fixedB
    refine ⟨B.vertex q, by simp [TreeSequenceVertexSet], ?_⟩
    rw [Incident, hi, hiEq]
    simp
  exact @helper_continuation_2163 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating original hcurrentOne presentation counterexample segmentTrans
      terminalAgreement seed hseed hb1 hb2 hb3 gamma hgammaBeta hswap3 route3 A3 max3
      edgeVertices P1 hP1 hsP1 hlP1 P2 hP2 hsP2 hlP2 P3 hP3 hsP3 hlP3 i1 i2 i3 hi23 hTni2 hi3pos
      hi3le hi3prevpos hClen hCU hBC hpenultimate hTnB hseedC hb3C hb1C hb2C hgamma3 hKU
      fixedOutsideVertex behavior4 missingB agree3 M4 fixedC
private theorem helper_continuation_2062.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 input T generating)
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (current : ExtendedTashkinovTree G k e0 input' T' generating')
          (_ : current.rounds = original.rounds) (_ : MaximumProperty current),
          ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')))
      (_ :
        (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
          {generating' : PartialEdgeColoring E k}
          (current : ExtendedTashkinovTree G k e0 input' T' generating')
          (_ : current.rounds = original.rounds) (_ : MaximumProperty current),
          let terminal : Fin (current.rounds + (1 : ℕ)) := Fin.last current.rounds;
          let Tterminal : TreeSequence G e0 := current.series.data.tree terminal.castSucc;
          ∀ (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigma)
            (_ : IsOneEdgeUncolored sigma e0)
            (_ :
              StableColoring Tterminal (TashkinovStoredColors current.series.data terminal)
                (current.series.data.coloring terminal) sigma),
            ModColoring current sigma))
      (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample : RutgersCounterexample G k e0 original presentation)
      (_ :
        (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
          (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C))
      (_ :
        (∀ {A B X : TreeSequence G e0} (_ : TreeSequenceInitialSegment A X)
          (_ : TreeSequenceInitialSegment B X) (_ : A.length ≤ B.length),
          TreeSequenceInitialSegment A B))
      (_ :
        (∀ {i : PartialEdgeColoring E k} {A : TreeSequence G e0}
          {phi : PartialEdgeColoring E k} (base : ExtendedTashkinovTree G k e0 i A phi)
          {psi : PartialEdgeColoring E k} {B : TreeSequence G e0}
          (corr : CorrespondingExtendedTashkinovTree G k e0 base psi B),
          corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc =
              base.series.data.tree (Fin.last base.rounds).castSucc ∧
            corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
                base.series.data.kind (Fin.last base.rounds) ∧
              corr.replacementETT.series.data.connectingEdges
                  (Fin.last corr.replacementETT.rounds) =
                base.series.data.connectingEdges (Fin.last base.rounds))),
    let R :
      ExtendedTashkinovTree G k e0 presentation.corresponding.replacementInput
        presentation.U presentation.sigma :=
      presentation.corresponding.replacementETT;
    let U : TreeSequence G e0 := presentation.U;
    let sigma : PartialEdgeColoring E k := presentation.sigma;
    let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
    let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors R.series.data n;
    ∀ (seed : TreeSequence G e0)
      (_ :
        (R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn ∨
          (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
              R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E),
              R.series.data.connectingEdges n = { f } ∧ TreeSequenceAdjoinEdge Tn f seed))
      (_ : TashkinovClosure sigma seed U) (_ : TreeSequenceInitialSegment seed U)
      (_ : TreeSequenceInitialSegment Tn U)
      (_ : counterexample.b1 ∈ TreeSequenceVertexSet U)
      (_ : counterexample.b2 ∈ TreeSequenceVertexSet U)
      (_ : counterexample.b3 ∈ TreeSequenceVertexSet U)
      (_ : counterexample.b2 ∉ TreeSequenceVertexSet Tn) (_ : Tn.length < U.length),
    ∀ gamma ∈ MissingColors G sigma counterexample.b3,
    gamma ≠ counterexample.beta →
    let mu3 : PartialEdgeColoring E k :=
      OutsideTreeColorSwap U sigma counterexample.alpha gamma;
    (IsProperEdgeColoring G mu3 ∧
        IsOneEdgeUncolored mu3 e0 ∧
          StableColoring U Dn sigma mu3 ∧
            ∀ (f : E), TreeIncidentEdge U f → mu3 f = sigma f) →
    StableColoring Tn Dn (R.series.data.coloring n) mu3 →
    ∃ (newPresentation : RutgersClosedPresentation G k e0 original) (newCounterexample :
      RutgersCounterexample G k e0 original newPresentation),
    RutgersCounterexampleMeasure newCounterexample <
      RutgersCounterexampleMeasure counterexample := by
  classical
  intro V E _ _ _ _ G k e0 input T generating original hcurrentOne hcurrentSix presentation
      counterexample segmentTrans commonPrefix terminalAgreement R U sigma n Tn Dn seed hseed
      hclosure hseedU hTnU hb1 hb2 hb3 hmiddle' hstrict gamma hgamma hgammaBeta mu3 hswap3 hstable3
  have M3 : ModColoring R mu3 :=
    hcurrentSix R presentation.corresponding.rungAgreement presentation.maximum
      mu3 hswap3.1 hswap3.2.1 hstable3
  have transportRoute (A B : TreeSequence G e0)
      (hAB : TashkinovAugmentationSequence sigma A B)
      (hBU : TreeSequenceInitialSegment B U) :
      TashkinovAugmentationSequence mu3 A B := by
    exact @helper_transportRoute_1070 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating original presentation counterexample segmentTrans gamma hswap3
        A B hAB hBU
  have route3 : TashkinovAugmentationSequence mu3 seed U :=
    transportRoute seed U hclosure.1 ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have closed3 : ColoredVertexSetClosed G mu3 (TreeSequenceVertexSet U) := by
    intro f c v hf hv hfc hc
    obtain ⟨x, hx, y, hy, hends⟩ := by simpa [BoundaryEdges] using hf
    have hfi : TreeIncidentEdge U f := ⟨x, hx, by simp [Incident, hends]⟩
    exact (hclosure.2 hf hv ((hswap3.2.2.2 f hfi).symm.trans hfc))
      (by rwa [hswap3.2.2.1.2 v hv] at hc)
  obtain ⟨A3⟩ : Nonempty (CorrespondingExtendedTashkinovTree G k e0 R mu3 U) := by
    apply M3.2.2 U hTnU hstrict
    rcases hseed with hPE | hSER
    · exact Or.inl ⟨hPE.1, by simpa [hPE.2] using route3⟩
    · obtain ⟨f, he, ha⟩ := hSER.2
      exact Or.inr ⟨hSER.1, f, seed, he, ha, route3⟩
  have max3 : MaximumProperty A3.replacementETT :=
    MaximumPropertyTransport G k e0 R mu3 M3 U A3 presentation.maximum
  obtain ⟨A30, _, _, hA30⟩ := CorrespondingExtendedTashkinovTreeTransTrees
    G k e0 input T U U generating sigma mu3 original presentation.corresponding A3
  have edgeVertices {phi : PartialEdgeColoring E k} {a b : Fin k}
      {u v : V} (p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v))
      (hp : p.IsPath) {f : E} (hf : Sum.inr f ∈ p.support) :
      ∃ (j : Nat) (x y : V), 0 < j ∧ j < p.length ∧
        p.getVert j = Sum.inr f ∧ p.getVert (j - 1) = Sum.inl x ∧
        p.getVert (j + 1) = Sum.inl y ∧ Incident G x f ∧ Incident G y f ∧
        x ≠ y ∧ G.ends f = s(x, y) := by
    exact @helper_edgeVertices_296 V E inferInstance inferInstance inferInstance G k e0 input T
        generating original presentation phi a b u v p hp f hf
  have pathBoundary {u v : V}
      (p : (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Walk
        (Sum.inl u) (Sum.inl v))
      (hexit : TreeExitPath U sigma counterexample.alpha counterexample.beta u v p)
      {f : E} (hf : Sum.inr f ∈ p.support) (hti : TreeIncidentEdge U f) :
      f ∈ BoundaryEdges G (TreeSequenceVertexSet U) := by
    exact @helper_pathBoundary_1116 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T generating original presentation counterexample edgeVertices u v p hexit f
        hf hti
  have outsideBoundary {u : V} {f : E} (hu : u ∉ TreeSequenceVertexSet U)
      (huf : Incident G u f) (hti : TreeIncidentEdge U f) :
      f ∈ BoundaryEdges G (TreeSequenceVertexSet U) := by
    obtain ⟨x, hx, hxf⟩ := hti
    have hxu : x ≠ u := by intro h; exact hu (h ▸ hx)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hx, u, hu, (Sym2.mem_and_mem_iff hxu).mp ⟨hxf, huf⟩⟩
  have remote3 {u : V} (hu : u ∉ TreeSequenceVertexSet U)
      (hm : counterexample.alpha ∈ MissingColors G sigma u ∨
        counterexample.beta ∈ MissingColors G sigma u) :
      gamma ∈ MissingColors G mu3 u ∨ counterexample.beta ∈ MissingColors G mu3 u := by
    exact @helper_remote3_362 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating original presentation counterexample seed hclosure hb3 gamma hgamma
        hgammaBeta hswap3 A3 A30 (by assumption) (by assumption) outsideBoundary u hu hm
  have transfer3 {u v : V}
      (p : (TwoColorIncidenceGraph G sigma counterexample.alpha counterexample.beta).Walk
        (Sum.inl u) (Sum.inl v))
      (hexit : TreeExitPath U sigma counterexample.alpha counterexample.beta u v p) :
      ∃ q : (TwoColorIncidenceGraph G mu3 gamma counterexample.beta).Walk
          (Sum.inl u) (Sum.inl v),
        TreeExitPath U mu3 gamma counterexample.beta u v q ∧
        q.support = p.support ∧ q.length = p.length := by
    exact @helper_transfer3_406 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T generating original presentation counterexample seed hclosure gamma hgammaBeta
        hswap3 pathBoundary remote3 u v p hexit
  obtain ⟨P1, hP1, hsP1, hlP1⟩ := transfer3 counterexample.Q1 counterexample.exit1
  obtain ⟨P2, hP2, hsP2, hlP2⟩ := transfer3 counterexample.Q2 counterexample.exit2
  obtain ⟨P3, hP3, hsP3, hlP3⟩ := transfer3 counterexample.Q3 counterexample.exit3
  obtain ⟨i1, i2, hi1, hi2, hi12⟩ := counterexample.insideOrder12
  obtain ⟨i2', i3, hi2', hi3, hi23⟩ := counterexample.insideOrder23
  have hi2eq : i2' = i2 := U.vertex_injective (hi2'.trans hi2.symm)
  subst i2'
  have hTni2 : Tn.length < i2.val := by
    by_contra h
    have hilt : i2.val < Tn.length + 1 := by omega
    apply hmiddle'
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i2.val, hilt⟩, ?_⟩
    exact (hTnU.2.1 ⟨i2.val, hilt⟩).symm.trans hi2
  have hi3pos : 1 ≤ i3.val := by omega
  have hi3le : i3.val ≤ U.length := Nat.lt_succ_iff.mp i3.isLt
  have hi3prevpos : 1 ≤ i3.val - 1 := by have := Tn.positive; omega
  let B := TreeSequencePrefix U (i3.val - 1) hi3prevpos (by omega)
  let C := TreeSequencePrefix U i3.val hi3pos hi3le
  have hBlen : B.length = i3.val - 1 := rfl
  have hClen : C.length = i3.val := rfl
  have hBU : TreeSequenceInitialSegment B U :=
    ⟨by dsimp [B, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have hCU : TreeSequenceInitialSegment C U :=
    ⟨hi3le, fun _ => rfl, fun _ => rfl⟩
  have hBC : TreeSequenceInitialSegment B C := commonPrefix hBU hCU (by omega)
  have hpenultimate : C.length = B.length + 1 := by omega
  have hTnB : TreeSequenceInitialSegment Tn B := commonPrefix hTnU hBU (by omega)
  have hseedB : TreeSequenceInitialSegment seed B := by
    apply commonPrefix hseedU hBU
    rcases hseed with hPE | hSER
    · rw [hPE.2]
      omega
    · obtain ⟨f, _, ha⟩ := hSER.2
      have := ha.1
      omega
  exact @helper_continuation_2093 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating original hcurrentOne hcurrentSix presentation counterexample
      segmentTrans terminalAgreement seed hseed hb1 hb2 hb3 gamma hgamma hgammaBeta hswap3 route3
      A3 max3 edgeVertices P1 hP1 hsP1 hlP1 P2 hP2 hsP2 hlP2 P3 hP3 hsP3 hlP3 i1 i2 hi1 hi2 hi12
      i3 hi3 hi23 hTni2 hi3pos hi3le hi3prevpos hClen hBU hCU hBC hpenultimate hTnB hseedB
theorem RutgersStrictShortening
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentOne : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hcurrentSix : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tterminal
          (TashkinovStoredColors current.series.data terminal)
          (current.series.data.coloring terminal) sigma ->
        ModColoring current sigma)
    (presentation : RutgersClosedPresentation G k e0 original)
    (counterexample : RutgersCounterexample G k e0 original presentation)
    (hmiddle :
      let replacement := presentation.corresponding.replacementETT
      let terminal : Fin (replacement.rounds + 1) :=
        Fin.last replacement.rounds
      counterexample.b2 ∉ TreeSequenceVertexSet
        (replacement.series.data.tree terminal.castSucc)) :
    exists (newPresentation : RutgersClosedPresentation G k e0 original) (newCounterexample
      : RutgersCounterexample G k e0 original newPresentation),
      RutgersCounterexampleMeasure newCounterexample <
        RutgersCounterexampleMeasure counterexample := by
  classical
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact @TreeSequenceInitialSegment.trans V E G e0 A B C hAB hBC
  have commonPrefix {A B X : TreeSequence G e0}
      (hAX : TreeSequenceInitialSegment A X)
      (hBX : TreeSequenceInitialSegment B X) (hlen : A.length ≤ B.length) :
      TreeSequenceInitialSegment A B := by
    exact @helper_commonPrefix_945 V E G e0 A B X hAX hBX hlen
  have terminalAgreement {i : PartialEdgeColoring E k}
      {A : TreeSequence G e0} {phi : PartialEdgeColoring E k}
      (base : ExtendedTashkinovTree G k e0 i A phi)
      {psi : PartialEdgeColoring E k} {B : TreeSequence G e0}
      (corr : CorrespondingExtendedTashkinovTree G k e0 base psi B) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc =
        base.series.data.tree (Fin.last base.rounds).castSucc ∧
      corr.replacementETT.series.data.kind
          (Fin.last corr.replacementETT.rounds) =
        base.series.data.kind (Fin.last base.rounds) ∧
      corr.replacementETT.series.data.connectingEdges
          (Fin.last corr.replacementETT.rounds) =
        base.series.data.connectingEdges (Fin.last base.rounds) := by
    exact ⟨corr.terminalData.1, corr.terminalData.2.1, corr.terminalConnectingEdges⟩
  let R := presentation.corresponding.replacementETT
  let U := presentation.U
  let sigma := presentation.sigma
  let n : Fin (R.rounds + 1) := Fin.last R.rounds
  let Tn := R.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors R.series.data n
  have hproper : IsProperEdgeColoring G sigma := by
    rw [show sigma = presentation.corresponding.replacementSeries.data.coloring
      (Fin.last original.rounds) from presentation.corresponding.finalGeneratingColoring]
    exact presentation.corresponding.replacementProper _
  have hone : IsOneEdgeUncolored sigma e0 := by
    rw [show sigma = presentation.corresponding.replacementSeries.data.coloring
      (Fin.last original.rounds) from presentation.corresponding.finalGeneratingColoring]
    exact presentation.corresponding.replacementOneUncolored _
  obtain ⟨seed, hseed, hclosure⟩ : ∃ seed : TreeSequence G e0,
      ((R.series.data.kind n = some TashkinovExtensionKind.PE ∧ seed = Tn) ∨
        ((R.series.data.kind n = some TashkinovExtensionKind.SE ∨
          R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ f, R.series.data.connectingEdges n = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed)) ∧
      TashkinovClosure sigma seed U := by
    rcases presentation.terminalRoute with hPE | hSER
    · exact ⟨Tn, Or.inl ⟨hPE.1, rfl⟩, hPE.2⟩
    · rcases hSER with ⟨hkind, f, seed, hedges, hadjoin, hcl⟩
      exact ⟨seed, Or.inr ⟨hkind, f, hedges, hadjoin⟩, hcl⟩
  have hseedU : TreeSequenceInitialSegment seed U :=
    TashkinovAugmentationSequenceInitialSegment sigma seed U hclosure.1
  have hTnSeed : TreeSequenceInitialSegment Tn seed := by
    rcases hseed with hPE | hSER
    · rw [hPE.2]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨f, _, hadjoin⟩ := hSER.2
      exact hadjoin.2.1
  have hTnU := segmentTrans hTnSeed hseedU
  have hTnSubset := TreeSequenceInitialSegmentVertexSetSubset hTnU
  have hb1 : counterexample.b1 ∈ TreeSequenceVertexSet U := counterexample.exit1.2.2.2.1
  have hb2 : counterexample.b2 ∈ TreeSequenceVertexSet U := counterexample.exit2.2.2.2.1
  have hb3 : counterexample.b3 ∈ TreeSequenceVertexSet U := counterexample.exit3.2.2.2.1
  have hmiddle' : counterexample.b2 ∉ TreeSequenceVertexSet Tn := hmiddle
  have hstrict : Tn.length < U.length := by
    by_contra hn
    obtain ⟨i, hi⟩ : ∃ i, U.vertex i = counterexample.b2 := by
      simpa [TreeSequenceVertexSet] using hb2
    have hil : i.val < Tn.length + 1 := by have := i.isLt; omega
    apply hmiddle'
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨i.val, hil⟩, ?_⟩
    exact (hTnU.2.1 ⟨i.val, hil⟩).symm.trans hi
  obtain ⟨gamma, hgamma⟩ := MissingColorsNonemptyOfMaximumDegree G sigma hdegree counterexample.b3
  have hgammaTree : gamma ∈ TreeMissingColors sigma U :=
    Finset.mem_biUnion.mpr ⟨counterexample.b3, hb3, hgamma⟩
  have hgammaBeta : gamma ≠ counterexample.beta := by
    intro h
    exact counterexample.betaPresent (h ▸ hgammaTree)
  let mu3 := OutsideTreeColorSwap U sigma counterexample.alpha gamma
  have hswap3 : IsProperEdgeColoring G mu3 ∧ IsOneEdgeUncolored mu3 e0 ∧
      StableColoring U Dn sigma mu3 ∧
      ∀ f, TreeIncidentEdge U f → mu3 f = sigma f := by
    by_cases h : counterexample.alpha = gamma
    · have heq : mu3 = sigma := by
        funext f
        by_cases hf : TreeIncidentEdge U f
        · simp [mu3, OutsideTreeColorSwap, hf]
        · by_cases hc : sigma f = some gamma <;>
            simp [mu3, OutsideTreeColorSwap, hf, h, hc]
      rw [heq]
      exact ⟨hproper, hone, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    · exact OutsideTreeColorSwapStable U Dn sigma counterexample.alpha gamma
        hproper hone hclosure.2 counterexample.alphaMissing hgammaTree h
  have hstable3 : StableColoring Tn Dn (R.series.data.coloring n) mu3 := by
    rw [← R.generatingColoring]
    refine ⟨fun f hf _ => hswap3.2.2.2 f ?_, ?_⟩
    · obtain ⟨v, hv, hf⟩ := hf
      exact ⟨v, hTnSubset hv, hf⟩
    · intro v hv
      exact hswap3.2.2.1.2 v (hTnSubset hv)
  exact @helper_continuation_2062 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating original hcurrentOne hcurrentSix presentation counterexample
      segmentTrans commonPrefix terminalAgreement seed hseed hclosure hseedU hTnU hb1 hb2 hb3
      hmiddle' hstrict gamma hgamma hgammaBeta hswap3 hstable3
end GoldbergSeymour

end
