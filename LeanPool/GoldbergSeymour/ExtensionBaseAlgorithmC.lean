/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.TwoColorComponentSwapPresentColors

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmCInvariant
public import LeanPool.GoldbergSeymour.StrongInterchangeabilityKempePreserved

/-!
# Extension Base Algorithm C

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch527Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
   {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
   (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (terminalSlot : Fin ett.rounds)
   (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
   (gamma delta : Fin (p + (1 : ℕ)) → Fin k)
   (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
   (hsupport :
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
   (hkind :
    ∀ (a : Fin (p + (1 : ℕ))),
     ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
   (hgamma : ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
   (hdelta : ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
   (hterminalInClass :
    terminalSlot ∈
     (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
      Finset (Fin ett.rounds))),
   let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
   let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
   let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
   let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
   let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
    fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
    if ha : a < p then
     TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p)) (traceDelta (⟨a, ha⟩ : Fin p))
      (Sum.inl u)
    else phi;
   let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
    Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
   let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k := fun (a : Fin (p + (1 : ℕ))) ↦
    coloringNat (↑a : ℕ);
   ∀
    (hslotEnumerates :
     Finset.image slot Finset.univ =
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
         Finset (Fin ett.rounds)).erase
       terminalSlot)
    (hslotDescending : ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
    (htransition :
     ∀ (a : Fin p),
      coloring a.succ =
       TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a) (Sum.inl u)),
    let trace :
     ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u :=
     {
      steps := p, slot := slot, gamma := traceGamma, delta := traceDelta, coloring := coloring,
      initialColoring := of_eq_true (eq_self mu0), terminalAtEnd := hterminalAtEnd,
      terminalInClass := hterminalInClass, enumerates := hslotEnumerates,
      strictlyDescending := hslotDescending,
      chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
      extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
      gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
      deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a), transition := htransition :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u };
    ∀ (_ : (∀ (a : Fin p), trace.gamma a ≠ trace.delta a))
     (_ :
      (∀ (a b : Fin p) (_ : (↑a : ℕ) < (↑b : ℕ)),
       trace.gamma b ≠ trace.gamma a ∧ trace.gamma b ≠ trace.delta a)),
     let U : Finset (Fin k) :=
      ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
            Finset (Fin ett.rounds)).erase
          terminalSlot :
         Finset (Fin ett.rounds)).biUnion
       fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
     ∀
      (_ :
       (∀ (a : Fin p),
        trace.slot a ∈
         ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
             Finset (Fin ett.rounds)).erase
           terminalSlot :
          Finset (Fin ett.rounds))))
      (_ : (∀ (a : Fin p), trace.gamma a ∈ U)) (_ : (∀ (a : Fin p), trace.delta a ∈ U))
      (_ : (∀ (a c : Fin p) (_ : (↑c : ℕ) = (↑a : ℕ) + (1 : ℕ)), trace.delta c = trace.gamma a))
      (_ :
       (∀ (t : Fin ett.rounds) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
        (_ : IsProperEdgeColoring G phi)
        (_ : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
        (_ : beta ∈ MissingColors G phi u) (_ : alpha ∈ PresentColors G phi u)
        (_ : alpha ∈ PresentColors G phi terminalSupport)
        (_ : beta ∈ PresentColors G phi terminalSupport),
        TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
         (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc),
           Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) → w = terminalSupport) ∧
          (Sum.inl terminalSupport ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
           ¬((TwoColorIncidenceGraph G phi alpha beta).neighborSet
              (Sum.inl terminalSupport)).Subsingleton)))
      (_ :
       (∀ {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}
        (_ : IsOneEdgeUncolored phi e0),
        IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0))
      (_ :
       (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta c : Fin k} {z : V ⊕ E}
        (_ : c ∈ PresentColors G phi v) (_ : c ≠ alpha) (_ : c ≠ beta),
        c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v))
      (_ :
       (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} (_ : alpha ≠ beta)
        (_ : beta ∈ MissingColors G phi v) (_ : alpha ∈ PresentColors G phi v),
        alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧
         beta ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v))
      (_ :
       (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} {z : V ⊕ E}
        (_ : alpha ≠ beta) (_ : alpha ∈ PresentColors G phi v) (_ : beta ∈ PresentColors G phi v),
        ∀ c ∈ PresentColors G phi v,
         c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v))
      (a : Fin trace.steps)
      (_ :
       ((IsProperEdgeColoring G (trace.coloring a.castSucc) ∧
         IsOneEdgeUncolored (trace.coloring a.castSucc) e0) ∧
        (∀ c ∈ U, c ∈ PresentColors G (trace.coloring a.castSucc) terminalSupport) ∧
         (∀ (a_1 : Fin trace.steps),
           (↑a.castSucc : ℕ) ≤ (↑a_1 : ℕ) →
            trace.gamma a_1 ∈ PresentColors G (trace.coloring a.castSucc) u) ∧
          (∀ (a_1 : Fin trace.steps),
            (↑a_1 : ℕ) = (↑a.castSucc : ℕ) →
             trace.delta a_1 ∈ MissingColors G (trace.coloring a.castSucc) u) ∧
           ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
            s ∈
              ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
                  Finset (Fin ett.rounds)).erase
                terminalSlot :
               Finset (Fin ett.rounds)) →
             (∀ (a_2 : Fin trace.steps), (↑a_2 : ℕ) < (↑a.castSucc : ℕ) → trace.slot a_2 ≠ s) →
              ett.series.data.chosenVertex s.succ = some terminalSupport →
               ett.series.data.gamma s.succ = some gammaS →
                ett.series.data.delta s.succ = some deltaS →
                 ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.castSucc) gammaS
                  deltaS)),
      (IsProperEdgeColoring G (trace.coloring a.succ) ∧
        IsOneEdgeUncolored (trace.coloring a.succ) e0) ∧
       (∀ c ∈ U, c ∈ PresentColors G (trace.coloring a.succ) terminalSupport) ∧
        (∀ (a_1 : Fin trace.steps),
          (↑a.succ : ℕ) ≤ (↑a_1 : ℕ) →
           trace.gamma a_1 ∈ PresentColors G (trace.coloring a.succ) u) ∧
         (∀ (a_1 : Fin trace.steps),
           (↑a_1 : ℕ) = (↑a.succ : ℕ) →
            trace.delta a_1 ∈ MissingColors G (trace.coloring a.succ) u) ∧
          ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
           s ∈
             ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
                 Finset (Fin ett.rounds)).erase
               terminalSlot :
              Finset (Fin ett.rounds)) →
            (∀ (a_2 : Fin trace.steps), (↑a_2 : ℕ) < (↑a.succ : ℕ) → trace.slot a_2 ≠ s) →
             ett.series.data.chosenVertex s.succ = some terminalSupport →
              ett.series.data.gamma s.succ = some gammaS →
               ett.series.data.delta s.succ = some deltaS →
                ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.succ) gammaS deltaS

private abbrev helperContinuation1280Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
   {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
   (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
   (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
   (terminalSlot jSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
   (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma delta : Fin (p + (1 : ℕ)) → Fin k)
   (_ : IsProperEdgeColoring G mu0) (_ : IsOneEdgeUncolored mu0 e0)
   (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
   (hsupport :
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
   (hkind :
    ∀ (a : Fin (p + (1 : ℕ))),
     ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
   (hgamma : ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
   (hdelta : ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
   (_ : (∀ (a : Fin p), gamma a.succ = delta a.castSucc))
   (_ :
    (∀
     s ∈
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
       terminalSlot,
     TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree s.succ.castSucc)))
   (_ : gamma (Fin.last p) ∈ MissingColors G mu0 u)
   (_ : (∀ (a : Fin p), gamma a.castSucc ∈ PresentColors G mu0 u))
   (_ :
    (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k)
     (_ :
      s ∈
       (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
        terminalSlot)
     (_ : ett.series.data.gamma s.succ = some gammaS)
     (_ : ett.series.data.delta s.succ = some deltaS),
     ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS))
   (_ :
    (MissingColors G mu0 terminalSupport ∩
      ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
         terminalSlot).biUnion
       fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) =
     ∅),
   ∀
    (hterminalInClass :
     terminalSlot ∈
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
       Finset (Fin ett.rounds))),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
     fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
     if ha : a < p then
      TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p)) (traceDelta (⟨a, ha⟩ : Fin p))
       (Sum.inl u)
     else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
     Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k := fun (a : Fin (p + (1 : ℕ))) ↦
     coloringNat (↑a : ℕ);
    ∀
     (hslotEnumerates :
      Finset.image slot Finset.univ =
       (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
          Finset (Fin ett.rounds)).erase
        terminalSlot)
     (hslotDescending : ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
     (htransition :
      ∀ (a : Fin p),
       coloring a.succ =
        TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a) (Sum.inl u)),
     let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u :=
      {
       steps := p, slot := slot, gamma := traceGamma, delta := traceDelta, coloring := coloring,
       initialColoring := of_eq_true (eq_self mu0), terminalAtEnd := hterminalAtEnd,
       terminalInClass := hterminalInClass, enumerates := hslotEnumerates,
       strictlyDescending := hslotDescending,
       chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
       extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
       gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
       deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a), transition := htransition :
       ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u };
     ∀ (_ : (∀ (a : Fin p), trace.gamma a ≠ trace.delta a))
      (_ :
       (∀ (a b : Fin p) (_ : (↑a : ℕ) < (↑b : ℕ)),
        trace.gamma b ≠ trace.gamma a ∧ trace.gamma b ≠ trace.delta a)),
      let U : Finset (Fin k) :=
       ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
             Finset (Fin ett.rounds)).erase
           terminalSlot :
          Finset (Fin ett.rounds)).biUnion
        fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
      ∀ (_ : (∀ (a : Fin p), (↑(reversePosition a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = p))
       (_ : (∀ (a : Fin p), trace.gamma a = gamma (reversePosition a)))
       (_ : (∀ (a : Fin p), trace.delta a = delta (reversePosition a)))
       (_ :
        (∀ (a : Fin p),
         trace.slot a ∈
          ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport :
              Finset (Fin ett.rounds)).erase
            terminalSlot :
           Finset (Fin ett.rounds))))
       (_ : (∀ (a : Fin p), trace.gamma a ∈ U)) (_ : (∀ (a : Fin p), trace.delta a ∈ U)),
       ExtensionBaseAlgorithmCInvariant ett terminalSupport hterminalSupport terminalSlot jSlot mu0
        u trace

private noncomputable abbrev helperTrace1922.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [Fintype V] →
            [Fintype E] →
              [DecidableEq E] →
                {G : LooplessMultigraph V E} →
                  {k : ℕ} →
                    {e0 : E} →
                      {input : PartialEdgeColoring E k} →
                        {T : TreeSequence G e0} →
                          {generating : PartialEdgeColoring E k} →
                            (ett : ExtendedTashkinovTree G k e0 input T generating) →
                              (terminalSupport : V) →
                                (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) →
                                  (terminalSlot : Fin ett.rounds) →
                                    (mu0 : PartialEdgeColoring E k) →
                                      (u : V) →
                                        (p : ℕ) →
                                          (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) →
                                            (gamma delta : Fin (p + (1 : ℕ)) → Fin k) →
                                              (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds →
                                                (∀ (a : Fin (p + (1 : ℕ))),
                                                    ett.series.data.chosenVertex (indices a).succ =
                                                      some terminalSupport) →
                                                  (∀ (a : Fin (p + (1 : ℕ))),
                                                      ett.series.data.kind (indices a).succ =
                                                        some TashkinovExtensionKind.PE) →
                                                    (∀ (a : Fin (p + (1 : ℕ))),
                                                        ett.series.data.gamma (indices a).succ =
                                                          some (gamma a)) →
                                                      (∀ (a : Fin (p + (1 : ℕ))),
                                                          ett.series.data.delta (indices a).succ =
                                                            some (delta a)) →
                                                        let supportClass :
                                                          Finset (Fin ett.rounds) :=
                                                          ExtensionBaseSupportClass ett
                                                            terminalSupport hterminalSupport
                                                            terminalSupport;
                                                        terminalSlot ∈ supportClass →
                                                          let reversePosition :
                                                            Fin p → Fin (p + (1 : ℕ)) :=
                                                            fun (a : Fin p) ↦ a.rev.castSucc;
                                                          let slot : Fin p → Fin ett.rounds :=
                                                            fun (a : Fin p) ↦
                                                            indices (reversePosition a);
                                                          let traceGamma : Fin p → Fin k :=
                                                            fun (a : Fin p) ↦
                                                            gamma (reversePosition a);
                                                          let traceDelta : Fin p → Fin k :=
                                                            fun (a : Fin p) ↦
                                                            delta (reversePosition a);
                                                          let nextColoring :
                                                            ℕ →
                                                              PartialEdgeColoring E k →
                                                                PartialEdgeColoring E k :=
                                                            fun (a : ℕ)
                                                              (phi : PartialEdgeColoring E k) ↦
                                                            if ha : a < p then
                                                              TwoColorComponentSwap G phi
                                                                (traceGamma (⟨a, ha⟩ : Fin p))
                                                                (traceDelta (⟨a, ha⟩ : Fin p))
                                                                (Sum.inl u)
                                                            else phi;
                                                          let coloringNat :
                                                            ℕ → PartialEdgeColoring E k :=
                                                            fun (t : ℕ) ↦
                                                            Nat.rec mu0
                                                              (fun (a : ℕ)
                                                                  (phi : PartialEdgeColoring E k) ↦
                                                                nextColoring a phi)
                                                              t;
                                                          let coloring :
                                                            Fin (p + (1 : ℕ)) →
                                                              PartialEdgeColoring E k :=
                                                            fun (a : Fin (p + (1 : ℕ))) ↦
                                                            coloringNat (↑a : ℕ);
                                                          Finset.image slot Finset.univ =
                                                              supportClass.erase terminalSlot →
                                                            (∀ (a b : Fin p),
                                                                (↑a : ℕ) < (↑b : ℕ) →
                                                                  (↑(slot b) : ℕ) <
                                                                    (↑(slot a) : ℕ)) →
                                                              (∀ (a : Fin p),
                                                                  coloring a.succ =
                                                                    TwoColorComponentSwap G
                                                                      (coloring a.castSucc)
                                                                      (traceGamma a) (traceDelta a)
                                                                      (Sum.inl u)) →
                                                                ExtensionBaseAlgorithmCTrace ett
                                                                  terminalSupport hterminalSupport
                                                                  terminalSlot mu0 u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta supportClass
      hterminalInClass reversePosition slot traceGamma traceDelta nextColoring coloringNat
      coloring hslotEnumerates hslotDescending htransition
  exact {
    steps := p
    slot := slot
    gamma := traceGamma
    delta := traceDelta
    coloring := coloring
    initialColoring := by simp [coloring, coloringNat]
    terminalAtEnd := hterminalAtEnd
    terminalInClass := hterminalInClass
    enumerates := hslotEnumerates
    strictlyDescending := hslotDescending
    chosenSupport := fun a => hsupport (reversePosition a)
    extensionKind := fun a => hkind (reversePosition a)
    gammaField := fun a => hgamma (reversePosition a)
    deltaField := fun a => hdelta (reversePosition a)
    transition := htransition }

private theorem helper_herased_110.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot : Fin ett.rounds) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (_ :
        (∀ (a c : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) < (↑c : ℕ)),
          (↑(indices a) : ℕ) < (↑(indices c) : ℕ)))
      (_ :
        (∀ (s : Fin ett.rounds),
          s ∈
              ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                terminalSupport ↔
            ∃ (a : Fin (p + (1 : ℕ))), indices a = s))
      (_ : indices (Fin.last p) = terminalSlot),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    supportClass.erase terminalSlot =
      Finset.image (fun (a : Fin p) ↦ indices a.castSucc) Finset.univ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot p
      indices hincreasing hclass hterminalIndex supportClass
  ext s
  constructor
  · intro hs
    have hsClass : s ∈ supportClass := (Finset.mem_erase.mp hs).2
    obtain ⟨a, ha⟩ := (hclass s).mp hsClass
    have haLast : a ≠ Fin.last p := by
      intro h
      apply (Finset.mem_erase.mp hs).1
      rw [← ha, h, hterminalIndex]
    have haLt : a.val < p := by
      have haLe : a.val ≤ p := Nat.le_of_lt_succ a.isLt
      rcases lt_or_eq_of_le haLe with hlt | heq
      · exact hlt
      · exact False.elim (haLast (Fin.ext heq))
    let b : Fin p := ⟨a.val, haLt⟩
    have hb : b.castSucc = a := Fin.ext rfl
    rw [Finset.mem_image]
    exact ⟨b, Finset.mem_univ b, by simpa [hb] using ha⟩
  · intro hs
    rw [Finset.mem_image] at hs
    obtain ⟨a, -, ha⟩ := hs
    rw [Finset.mem_erase]
    refine ⟨?_, (hclass s).2 ⟨a.castSucc, ha⟩⟩
    intro hsTerminal
    have hindexEq : indices a.castSucc = indices (Fin.last p) := by
      rw [ha, hsTerminal, hterminalIndex]
    have hvalLt : a.castSucc.val < (Fin.last p).val := by
      simp
    exact (Nat.ne_of_lt (hincreasing a.castSucc (Fin.last p) hvalLt))
      (congrArg Fin.val hindexEq)

private theorem helper_single_step_295.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
        (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport u : V)
        (t : Fin ett.rounds) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
        (_ : IsProperEdgeColoring G phi)
        (_ : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
        (_ : beta ∈ MissingColors G phi u) (_ : alpha ∈ PresentColors G phi u)
        (_ : alpha ∈ PresentColors G phi terminalSupport)
        (_ : beta ∈ PresentColors G phi terminalSupport),
        TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
          (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc),
              Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                w = terminalSupport) ∧
            (Sum.inl terminalSupport ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
              ¬((TwoColorIncidenceGraph G phi alpha beta).neighborSet
                    (Sum.inl terminalSupport)).Subsingleton) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport u t phi alpha beta hproperPhi hSI
      hbetaMissing halphaPresent hterminalAlphaPresent hterminalBetaPresent
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := TwoColorComponent G phi alpha beta (Sum.inl u)
  have hne : alpha ≠ beta := hSI.1
  obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using halphaPresent
  have heAlphaAdj : H.Adj (Sum.inl u) (Sum.inr eAlpha) := by
    simpa [H, TwoColorIncidenceGraph] using
      And.intro heAlphaIncident (Or.inl heAlphaColor)
  have heAlphaComponent : Sum.inr eAlpha ∈ C := by
    change H.connectedComponentMk (Sum.inr eAlpha) =
      H.connectedComponentMk (Sum.inl u)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      heAlphaAdj).symm
  have huComponent : Sum.inl u ∈ C := by rfl
  have huSubsingleton : Set.Subsingleton (H.neighborSet (Sum.inl u)) := by
    exact TwoColorIncidenceGraph.neighborSet_subsingleton_of_missing hproperPhi
      (Or.inr hbetaMissing)
  have hpath : TwoColorPathComponent G phi alpha beta (Sum.inl u) := by
    refine ⟨hne, Sum.inl u, huComponent, ?_⟩
    simpa [H] using huSubsingleton
  have hnontrivial : TwoColorNontrivialPathComponent G phi alpha beta
      (Sum.inl u) := ⟨hpath, eAlpha, heAlphaComponent⟩
  refine ⟨hnontrivial, ?_, ?_⟩
  · intro w hwTree hwComponent
    by_contra hwne
    obtain ⟨hcycle, -, -⟩ :=
      hSI.2.2.2.choose_spec.2.2.2 w hwTree hwne
    have huInW : Sum.inl u ∈
        TwoColorComponent G phi alpha beta (Sum.inl w) := by
      change H.connectedComponentMk (Sum.inl u) =
        H.connectedComponentMk (Sum.inl w)
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl u) at hwComponent
      exact hwComponent.symm
    have hpathW : TwoColorPathComponent G phi alpha beta (Sum.inl w) := by
      refine ⟨hne, Sum.inl u, huInW, ?_⟩
      simpa [H] using huSubsingleton
    exact (TwoColorPathComponentNotCycle G phi alpha beta (Sum.inl w)
      hpathW) hcycle
  · intro _ hsub
    obtain ⟨eAlphaN, heAlphaNIncident, heAlphaNColor⟩ := by
      simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] using hterminalAlphaPresent
    obtain ⟨eBetaN, heBetaNIncident, heBetaNColor⟩ := by
      simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] using hterminalBetaPresent
    have hedgeNe : eAlphaN ≠ eBetaN := by
      intro heq
      subst eBetaN
      exact hne (Option.some.inj (heAlphaNColor.symm.trans heBetaNColor))
    have hAlphaNeighbor : Sum.inr eAlphaN ∈
        H.neighborSet (Sum.inl terminalSupport) := by
      simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
        And.intro heAlphaNIncident (Or.inl heAlphaNColor)
    have hBetaNeighbor : Sum.inr eBetaN ∈
        H.neighborSet (Sum.inl terminalSupport) := by
      simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
        And.intro heBetaNIncident (Or.inr heBetaNColor)
    exact hedgeNe (Sum.inr.inj (hsub hAlphaNeighbor hBetaNeighbor))

private theorem helper_branch_509.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k) (_ : IsProperEdgeColoring G mu0)
      (_ : IsOneEdgeUncolored mu0 e0)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
      (_ : (∀ (a : Fin p), gamma a.succ = delta a.castSucc))
      (_ : gamma (Fin.last p) ∈ MissingColors G mu0 u),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    let L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot;
    let U : Finset (Fin k) :=
      L.biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
    ∀ (_ : (∀ (a : Fin p), (↑(reversePosition a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = p))
      (_ : (∀ (a : Fin p), trace.delta a = delta (reversePosition a)))
      (_ : (∀ c ∈ U, c ∈ PresentColors G mu0 terminalSupport))
      (_ : (∀ (a : Fin p), trace.gamma a ∈ PresentColors G mu0 u))
      (_ :
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ L)
          (_ : ett.series.data.gamma s.succ = some gammaS)
          (_ : ett.series.data.delta s.succ = some deltaS),
          ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS)),
    (IsProperEdgeColoring G (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) ∧
      IsOneEdgeUncolored (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) e0) ∧
    (∀ c ∈ U,
      c ∈
        PresentColors G (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) terminalSupport) ∧
    (∀ (a : Fin trace.steps),
      (↑(0 : Fin (trace.steps + (1 : ℕ))) : ℕ) ≤ (↑a : ℕ) →
        trace.gamma a ∈
          PresentColors G (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) u) ∧
    (∀ (a : Fin trace.steps),
      (↑a : ℕ) = (↑(0 : Fin (trace.steps + (1 : ℕ))) : ℕ) →
        trace.delta a ∈
          MissingColors G (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
    s ∈ L →
    (∀ (a : Fin trace.steps),
        (↑a : ℕ) < (↑(0 : Fin (trace.steps + (1 : ℕ))) : ℕ) → trace.slot a ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport →
    ett.series.data.gamma s.succ = some gammaS →
    ett.series.data.delta s.succ = some deltaS →
    ETTStrongInterchangeable ett s terminalSupport
      (trace.coloring (0 : Fin (trace.steps + (1 : ℕ)))) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
      hterminalGammaMissing supportClass hterminalInClass reversePosition slot traceGamma
      traceDelta nextColoring coloringNat coloring hslotEnumerates hslotDescending htransition
      trace L U hposition htraceDelta initial_terminal_present initial_gamma_present
      initial_survivor
  rw [trace.initialColoring]
  refine ⟨⟨hproper, hone⟩, initial_terminal_present,
    (fun a _ => initial_gamma_present a), ?_, ?_⟩
  · intro a ha
    let q : Fin p := a.rev
    have hpos : reversePosition a = q.castSucc := Fin.ext rfl
    have hlast : Fin.last p = q.succ := by
      apply Fin.ext
      have hpa := hposition a
      change p = a.rev.val + 1
      change a.rev.val + a.val + 1 = p at hpa
      simp at ha
      omega
    rw [htraceDelta a, hpos, ← hchain q, ← hlast]
    exact hterminalGammaMissing
  · intro s gammaS deltaS hs _ _ hgs hds
    exact initial_survivor s gammaS deltaS hs hgs hds

private theorem helper_branch_654.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a)),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    let L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot;
    ∀ (a : Fin trace.steps)
      (_ :
        IsProperEdgeColoring G (trace.coloring a.castSucc) ∧
          IsOneEdgeUncolored (trace.coloring a.castSucc) e0)
      (_ :
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ L)
          (_ :
            (∀ (a_2 : Fin trace.steps) (_ : (↑a_2 : ℕ) < (↑a.castSucc : ℕ)),
              trace.slot a_2 ≠ s))
          (_ : ett.series.data.chosenVertex s.succ = some terminalSupport)
          (_ : ett.series.data.gamma s.succ = some gammaS)
          (_ : ett.series.data.delta s.succ = some deltaS),
          ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.castSucc) gammaS
            deltaS))
      (_ :
        ETTStrongInterchangeable ett (trace.slot a) terminalSupport
          (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a))
      (_ :
        TwoColorNontrivialPathComponent G (trace.coloring a.castSucc) (trace.gamma a)
            (trace.delta a) (Sum.inl u) ∧
          (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc),
              Sum.inl w ∈
                  TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a)
                    (trace.delta a) (Sum.inl u) →
                w = terminalSupport) ∧
            (Sum.inl terminalSupport ∈
                TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a)
                  (trace.delta a) (Sum.inl u) →
              ¬((TwoColorIncidenceGraph G (trace.coloring a.castSucc) (trace.gamma a)
                        (trace.delta a)).neighborSet
                    (Sum.inl terminalSupport)).Subsingleton))
      (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ L)
      (_ : (∀ (a_2 : Fin trace.steps) (_ : (↑a_2 : ℕ) < (↑a.succ : ℕ)), trace.slot a_2 ≠ s))
      (_ : ett.series.data.chosenVertex s.succ = some terminalSupport)
      (_ : ett.series.data.gamma s.succ = some gammaS)
      (_ : ett.series.data.delta s.succ = some deltaS),
    ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.succ) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta supportClass
      hterminalInClass reversePosition slot traceGamma traceDelta nextColoring coloringNat
      coloring hslotEnumerates hslotDescending htransition trace L a hgood hsurvivor hcurrentSI
      hstep s gammaS deltaS hs hnot hsupportS hgammaS hdeltaS
  have hsOld : ETTStrongInterchangeable ett s terminalSupport
      (trace.coloring a.castSucc) gammaS deltaS := by
    apply hsurvivor s gammaS deltaS hs
    · intro c hc
      apply hnot c
      change c.val < a.val at hc
      change c.val < a.val + 1
      omega
    · exact hsupportS
    · exact hgammaS
    · exact hdeltaS
  have hsImage : s ∈ Finset.univ.image trace.slot := by
    rw [trace.enumerates]
    exact hs
  rcases Finset.mem_image.mp hsImage with ⟨c, -, hc⟩
  have hac : a.val < c.val := by
    by_contra hle
    have hca : c.val < a.succ.val := by
      simp
      omega
    exact hnot c hca hc
  have hslt : s.val < (trace.slot a).val := by
    have hdesc := trace.strictlyDescending a c hac
    simpa [hc] using hdesc
  have hpreserved := StrongInterchangeabilityKempePreserved ett s
    (trace.slot a) terminalSupport terminalSupport gammaS deltaS
    (trace.gamma a) (trace.delta a) (trace.coloring a.castSucc)
    (Sum.inl u) hgood.1 hgood.2 hgammaS hdeltaS
    (trace.gammaField a) (trace.deltaField a) (Or.inr hslt)
    (by intro hneSupport; exact (hneSupport rfl).elim) hstep.1
    hcurrentSI hsOld
  rw [trace.transition a]
  exact hpreserved.2.2

private theorem helper_branch_527.{u_1, u_2} :
    helperBranch527Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta
  set supportClass : Finset (Fin ett.rounds) := ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport terminalSupport
  intro hterminalInClass reversePosition slot traceGamma traceDelta nextColoring coloringNat
      coloring hslotEnumerates hslotDescending htransition trace trace_colors_ne surviving_gamma_ne
  set L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot
  intro U slot_mem gamma_mem_U delta_mem_U next_delta_eq_gamma single_step swap_preserves_one
      swap_present_other root_swap_exchange swap_preserves_present a ih
  rcases ih with ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
  have hgammaPresent : trace.gamma a ∈
      PresentColors G (trace.coloring a.castSucc) u :=
    hfuture a (by rfl)
  have hdeltaMissing : trace.delta a ∈
      MissingColors G (trace.coloring a.castSucc) u :=
    hnext a rfl
  have hcurrentSI : ETTStrongInterchangeable ett (trace.slot a)
      terminalSupport (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a) := by
    apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
        (slot_mem a)
    · intro c hc hca
      have hdesc := trace.strictlyDescending c a hc
      rw [hca] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
    · exact trace.chosenSupport a
    · exact trace.gammaField a
    · exact trace.deltaField a
  have hterminalGamma : trace.gamma a ∈
      PresentColors G (trace.coloring a.castSucc) terminalSupport :=
    hterminal (trace.gamma a) (gamma_mem_U a)
  have hterminalDelta : trace.delta a ∈
      PresentColors G (trace.coloring a.castSucc) terminalSupport :=
    hterminal (trace.delta a) (delta_mem_U a)
  have hstep := single_step (trace.slot a)
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
    hgood.1 hcurrentSI hdeltaMissing hgammaPresent hterminalGamma
    hterminalDelta
  have hproperNext :
      IsProperEdgeColoring G (trace.coloring a.succ) := by
    rw [trace.transition a]
    exact TwoColorComponentSwapProper G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a) (trace_colors_ne a) hgood.1
      (Sum.inl u)
  have honeNext : IsOneEdgeUncolored (trace.coloring a.succ) e0 := by
    rw [trace.transition a]
    exact swap_preserves_one hgood.2
  have hexchange := root_swap_exchange (trace_colors_ne a)
    hdeltaMissing hgammaPresent
  rw [← trace.transition a] at hexchange
  refine ⟨⟨hproperNext, honeNext⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hpresent := swap_preserves_present (z := Sum.inl u)
      (trace_colors_ne a) hterminalGamma hterminalDelta c
      (hterminal c hc)
    rw [← trace.transition a] at hpresent
    exact hpresent
  · intro c hac
    have hac' : a.val < c.val := by
      change a.val + 1 ≤ c.val at hac
      omega
    have hne := surviving_gamma_ne a c hac'
    have hpresent := swap_present_other (z := Sum.inl u)
      (hfuture c (Nat.le_of_lt hac')) hne.1 hne.2
    rw [← trace.transition a] at hpresent
    exact hpresent
  · intro c hca
    rw [next_delta_eq_gamma a c (by simpa using hca)]
    exact hexchange.1
  · exact @helper_branch_654 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport terminalSlot mu0 u p indices gamma
      delta hterminalAtEnd hsupport hkind hgamma hdelta hterminalInClass hslotEnumerates
      hslotDescending htransition a hgood hsurvivor hcurrentSI hstep
private theorem helper_invariant_596.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k) (_ : IsProperEdgeColoring G mu0)
      (_ : IsOneEdgeUncolored mu0 e0)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
      (_ : (∀ (a : Fin p), gamma a.succ = delta a.castSucc))
      (_ : gamma (Fin.last p) ∈ MissingColors G mu0 u),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    ∀ (_ : (∀ (a : Fin p), trace.gamma a ≠ trace.delta a))
      (_ :
        (∀ (a b : Fin p) (_ : (↑a : ℕ) < (↑b : ℕ)),
          trace.gamma b ≠ trace.gamma a ∧ trace.gamma b ≠ trace.delta a)),
    let L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot;
    let U : Finset (Fin k) :=
      L.biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
    ∀ (_ : (∀ (a : Fin p), (↑(reversePosition a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = p))
      (_ : (∀ (a : Fin p), trace.delta a = delta (reversePosition a)))
      (_ : (∀ (a : Fin p), trace.slot a ∈ L)) (_ : (∀ (a : Fin p), trace.gamma a ∈ U))
      (_ : (∀ (a : Fin p), trace.delta a ∈ U))
      (_ : (∀ c ∈ U, c ∈ PresentColors G mu0 terminalSupport))
      (_ : (∀ (a : Fin p), trace.gamma a ∈ PresentColors G mu0 u))
      (_ :
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ L)
          (_ : ett.series.data.gamma s.succ = some gammaS)
          (_ : ett.series.data.delta s.succ = some deltaS),
          ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS))
      (_ :
        (∀ (a c : Fin p) (_ : (↑c : ℕ) = (↑a : ℕ) + (1 : ℕ)),
          trace.delta c = trace.gamma a))
      (_ :
        (∀ (t : Fin ett.rounds) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
          (_ : IsProperEdgeColoring G phi)
          (_ : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
          (_ : beta ∈ MissingColors G phi u) (_ : alpha ∈ PresentColors G phi u)
          (_ : alpha ∈ PresentColors G phi terminalSupport)
          (_ : beta ∈ PresentColors G phi terminalSupport),
          TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
            (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc),
                Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                  w = terminalSupport) ∧
              (Sum.inl terminalSupport ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                ¬((TwoColorIncidenceGraph G phi alpha beta).neighborSet
                      (Sum.inl terminalSupport)).Subsingleton)))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}
          (_ : IsOneEdgeUncolored phi e0),
          IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta c : Fin k} {z : V ⊕ E}
          (_ : c ∈ PresentColors G phi v) (_ : c ≠ alpha) (_ : c ≠ beta),
          c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} (_ : alpha ≠ beta)
          (_ : beta ∈ MissingColors G phi v) (_ : alpha ∈ PresentColors G phi v),
          alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧
            beta ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} {z : V ⊕ E}
          (_ : alpha ≠ beta) (_ : alpha ∈ PresentColors G phi v)
          (_ : beta ∈ PresentColors G phi v),
          ∀ c ∈ PresentColors G phi v,
            c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v))
      (n : Fin (trace.steps + (1 : ℕ))),
    (IsProperEdgeColoring G (trace.coloring n) ∧ IsOneEdgeUncolored (trace.coloring n) e0) ∧
    (∀ c ∈ U, c ∈ PresentColors G (trace.coloring n) terminalSupport) ∧
    (∀ (a : Fin trace.steps),
      (↑n : ℕ) ≤ (↑a : ℕ) → trace.gamma a ∈ PresentColors G (trace.coloring n) u) ∧
    (∀ (a : Fin trace.steps),
      (↑a : ℕ) = (↑n : ℕ) → trace.delta a ∈ MissingColors G (trace.coloring n) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
    s ∈ L →
    (∀ (a : Fin trace.steps), (↑a : ℕ) < (↑n : ℕ) → trace.slot a ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport →
    ett.series.data.gamma s.succ = some gammaS →
    ett.series.data.delta s.succ = some deltaS →
    ETTStrongInterchangeable ett s terminalSupport (trace.coloring n) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
      hterminalGammaMissing supportClass hterminalInClass reversePosition slot traceGamma
      traceDelta nextColoring coloringNat coloring hslotEnumerates hslotDescending htransition
      trace trace_colors_ne surviving_gamma_ne L U hposition htraceDelta slot_mem gamma_mem_U
      delta_mem_U initial_terminal_present initial_gamma_present initial_survivor
      next_delta_eq_gamma single_step swap_preserves_one swap_present_other root_swap_exchange
      swap_preserves_present n
  induction n using Fin.induction with
  | zero =>
      exact @helper_branch_509 V E inferInstance inferInstance inferInstance G k e0 input T
          generating ett terminalSupport hterminalSupport terminalSlot mu0 u p indices gamma
          delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
          hterminalGammaMissing hterminalInClass hslotEnumerates hslotDescending htransition
          hposition htraceDelta initial_terminal_present initial_gamma_present initial_survivor
  | succ a ih =>
      exact @helper_branch_527 V E inferInstance inferInstance inferInstance G k e0
          input T generating ett terminalSupport hterminalSupport terminalSlot mu0 u p indices
          gamma delta hterminalAtEnd hsupport hkind hgamma hdelta hterminalInClass
          hslotEnumerates hslotDescending htransition trace_colors_ne surviving_gamma_ne slot_mem
          gamma_mem_U delta_mem_U next_delta_eq_gamma single_step swap_preserves_one
          swap_present_other root_swap_exchange swap_preserves_present a ih
private theorem helper_branch_732.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot jSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
      (_ :
        (∀
          s ∈
            (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                  terminalSupport).erase
              terminalSlot,
          TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree s.succ.castSucc))),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    let L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot;
    let U : Finset (Fin k) :=
      L.biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
    ∀ (_ : (∀ (a : Fin p), trace.slot a ∈ L)) (_ : (∀ (a : Fin p), trace.gamma a ∈ U))
      (_ : (∀ (a : Fin p), trace.delta a ∈ U))
      (_ :
        (∀ (t : Fin ett.rounds) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
          (_ : IsProperEdgeColoring G phi)
          (_ : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
          (_ : beta ∈ MissingColors G phi u) (_ : alpha ∈ PresentColors G phi u)
          (_ : alpha ∈ PresentColors G phi terminalSupport)
          (_ : beta ∈ PresentColors G phi terminalSupport),
          TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
            (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc),
                Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                  w = terminalSupport) ∧
              (Sum.inl terminalSupport ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                ¬((TwoColorIncidenceGraph G phi alpha beta).neighborSet
                      (Sum.inl terminalSupport)).Subsingleton)))
      (_ :
        (∀ (n : Fin (trace.steps + (1 : ℕ))),
          (IsProperEdgeColoring G (trace.coloring n) ∧
              IsOneEdgeUncolored (trace.coloring n) e0) ∧
            (∀ c ∈ U, c ∈ PresentColors G (trace.coloring n) terminalSupport) ∧
              (∀ (a : Fin trace.steps),
                  (↑n : ℕ) ≤ (↑a : ℕ) →
                    trace.gamma a ∈ PresentColors G (trace.coloring n) u) ∧
                (∀ (a : Fin trace.steps),
                    (↑a : ℕ) = (↑n : ℕ) →
                      trace.delta a ∈ MissingColors G (trace.coloring n) u) ∧
                  ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
                    s ∈ L →
                      (∀ (a : Fin trace.steps), (↑a : ℕ) < (↑n : ℕ) → trace.slot a ≠ s) →
                        ett.series.data.chosenVertex s.succ = some terminalSupport →
                          ett.series.data.gamma s.succ = some gammaS →
                            ett.series.data.delta s.succ = some deltaS →
                              ETTStrongInterchangeable ett s terminalSupport
                                (trace.coloring n) gammaS deltaS))
      (a : Fin trace.steps),
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree (trace.slot a).succ.castSucc) ∧
    trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) u ∧
    TwoColorNontrivialPathComponent G (trace.coloring a.castSucc) (trace.gamma a)
      (trace.delta a) (Sum.inl u) ∧
    (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc),
      Sum.inl w ∈
          TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
            (Sum.inl u) →
        w = terminalSupport) ∧
    (Sum.inl terminalSupport ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
          (Sum.inl u) →
      ¬((TwoColorIncidenceGraph G (trace.coloring a.castSucc) (trace.gamma a)
                (trace.delta a)).neighborSet
            (Sum.inl terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
    s ∈
        (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
              terminalSupport).erase
          terminalSlot →
    (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport →
    ett.series.data.gamma s.succ = some gammaS →
    ett.series.data.delta s.succ = some deltaS →
    ETTStrongInterchangeable ett s terminalSupport (trace.coloring a.succ) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot
      jSlot mu0 u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta hTjInitial
      supportClass hterminalInClass reversePosition slot traceGamma traceDelta nextColoring
      coloringNat coloring hslotEnumerates hslotDescending htransition trace L U slot_mem
      gamma_mem_U delta_mem_U single_step invariant a
  rcases invariant a.castSucc with
    ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
  have hmissing := hnext a rfl
  have hpresent := hfuture a (by rfl)
  have hterminalGamma := hterminal (trace.gamma a) (gamma_mem_U a)
  have hterminalDelta := hterminal (trace.delta a) (delta_mem_U a)
  have hsi : ETTStrongInterchangeable ett (trace.slot a) terminalSupport
      (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) := by
    apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
        (slot_mem a)
    · intro c hc hca
      have hdesc := trace.strictlyDescending c a hc
      rw [hca] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
    · exact trace.chosenSupport a
    · exact trace.gammaField a
    · exact trace.deltaField a
  have hstep := single_step (trace.slot a)
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
    hgood.1 hsi hmissing hpresent hterminalGamma hterminalDelta
  refine ⟨?_, hmissing, hstep.1, hstep.2.1, hstep.2.2, ?_⟩
  · exact hTjInitial (trace.slot a) (slot_mem a)
  · intro s gammaS deltaS hs hnot hsupportS hgammaS hdeltaS
    have hnextInvariant := invariant a.succ
    exact hnextInvariant.2.2.2.2 s gammaS deltaS hs (by
      intro c hc
      apply hnot c
      change c.val < a.val + 1 at hc
      omega) hsupportS hgammaS hdeltaS

private theorem helper_surviving_gamma_ne_883.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
      (_ : Function.Injective (Fin.cons (gamma (0 : Fin (p + (1 : ℕ)))) delta)),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    let colorChain : Fin (p + (2 : ℕ)) → Fin k :=
      Fin.cons (gamma (0 : Fin (p + (1 : ℕ)))) delta;
    ∀ (_ : (∀ (q : Fin (p + (1 : ℕ))), gamma q = colorChain q.castSucc))
      (_ : (∀ (q : Fin (p + (1 : ℕ))), delta q = colorChain q.succ)) (a b : Fin p)
      (_ : (↑a : ℕ) < (↑b : ℕ)),
    trace.gamma b ≠ trace.gamma a ∧
    trace.gamma b ≠ trace.delta a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta hdistinct supportClass
      hterminalInClass reversePosition slot traceGamma traceDelta nextColoring coloringNat
      coloring hslotEnumerates hslotDescending htransition trace colorChain gamma_eq_chain
      delta_eq_chain a b hab
  change gamma (reversePosition b) ≠ gamma (reversePosition a) ∧
    gamma (reversePosition b) ≠ delta (reversePosition a)
  rw [gamma_eq_chain, gamma_eq_chain, delta_eq_chain]
  constructor <;> intro h
  · have hi := hdistinct h
    have hv := congrArg Fin.val hi
    change b.rev.val = a.rev.val at hv
    have := Fin.rev_lt_rev.mpr hab
    omega
  · have hi := hdistinct h
    have hv := congrArg Fin.val hi
    change b.rev.val = a.rev.val + 1 at hv
    have := Fin.rev_lt_rev.mpr hab
    omega

private theorem helper_swap_preserves_one_984.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
      {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}
      (_ : IsOneEdgeUncolored phi e0),
    IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0 := by
  classical
  intro V E G k e0 phi alpha beta z h
  constructor
  · simp [TwoColorComponentSwap, h.1]
  · intro e he0
    obtain ⟨c, hc⟩ := h.2 e he0
    by_cases heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · by_cases heAlpha : phi e = some alpha
      · exact ⟨beta, by simp [TwoColorComponentSwap, heK, heAlpha]⟩
      · by_cases heBeta : phi e = some beta
        · exact ⟨alpha, by
            simp [TwoColorComponentSwap, heK, heBeta]⟩
        · exact ⟨c, by
            simpa [TwoColorComponentSwap, heK, heAlpha, heBeta] using hc⟩
    · exact ⟨c, by simpa [TwoColorComponentSwap, heK] using hc⟩

private theorem helper_continuation_1578.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot jSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k) (_ : IsProperEdgeColoring G mu0)
      (_ : IsOneEdgeUncolored mu0 e0)
      (hterminalAtEnd : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (hsupport :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
      (hkind :
        ∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE)
      (hgamma :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a))
      (hdelta :
        ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a))
      (_ : (∀ (a : Fin p), gamma a.succ = delta a.castSucc))
      (_ :
        (∀
          s ∈
            (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                  terminalSupport).erase
              terminalSlot,
          TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree s.succ.castSucc)))
      (_ : gamma (Fin.last p) ∈ MissingColors G mu0 u),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (hterminalInClass : terminalSlot ∈ supportClass),
    let reversePosition : Fin p → Fin (p + (1 : ℕ)) := fun (a : Fin p) ↦ a.rev.castSucc;
    let slot : Fin p → Fin ett.rounds := fun (a : Fin p) ↦ indices (reversePosition a);
    let traceGamma : Fin p → Fin k := fun (a : Fin p) ↦ gamma (reversePosition a);
    let traceDelta : Fin p → Fin k := fun (a : Fin p) ↦ delta (reversePosition a);
    let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
      fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦
      if ha : a < p then
        TwoColorComponentSwap G phi (traceGamma (⟨a, ha⟩ : Fin p))
          (traceDelta (⟨a, ha⟩ : Fin p)) (Sum.inl u)
      else phi;
    let coloringNat : ℕ → PartialEdgeColoring E k := fun (t : ℕ) ↦
      Nat.rec mu0 (fun (a : ℕ) (phi : PartialEdgeColoring E k) ↦ nextColoring a phi) t;
    let coloring : Fin (p + (1 : ℕ)) → PartialEdgeColoring E k :=
      fun (a : Fin (p + (1 : ℕ))) ↦ coloringNat (↑a : ℕ);
    ∀ (hslotEnumerates : Finset.image slot Finset.univ = supportClass.erase terminalSlot)
      (hslotDescending :
        ∀ (a b : Fin p), (↑a : ℕ) < (↑b : ℕ) → (↑(slot b) : ℕ) < (↑(slot a) : ℕ))
      (htransition :
        ∀ (a : Fin p),
          coloring a.succ =
            TwoColorComponentSwap G (coloring a.castSucc) (traceGamma a) (traceDelta a)
              (Sum.inl u)),
    let trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
        u :=
      { steps := p, slot := slot, gamma := traceGamma, delta := traceDelta,
        coloring := coloring, initialColoring := of_eq_true (eq_self mu0),
        terminalAtEnd := hterminalAtEnd, terminalInClass := hterminalInClass,
        enumerates := hslotEnumerates, strictlyDescending := hslotDescending,
        chosenSupport := fun (a : Fin p) ↦ hsupport (reversePosition a),
        extensionKind := fun (a : Fin p) ↦ hkind (reversePosition a),
        gammaField := fun (a : Fin p) ↦ hgamma (reversePosition a),
        deltaField := fun (a : Fin p) ↦ hdelta (reversePosition a),
        transition := htransition :
        ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0
          u };
    ∀ (_ : (∀ (a : Fin p), trace.gamma a ≠ trace.delta a))
      (_ :
        (∀ (a b : Fin p) (_ : (↑a : ℕ) < (↑b : ℕ)),
          trace.gamma b ≠ trace.gamma a ∧ trace.gamma b ≠ trace.delta a)),
    let L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot;
    let U : Finset (Fin k) :=
      L.biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
    ∀ (_ : (∀ (a : Fin p), (↑(reversePosition a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = p))
      (_ : (∀ (a : Fin p), trace.delta a = delta (reversePosition a)))
      (_ : (∀ (a : Fin p), trace.slot a ∈ L)) (_ : (∀ (a : Fin p), trace.gamma a ∈ U))
      (_ : (∀ (a : Fin p), trace.delta a ∈ U))
      (_ : (∀ c ∈ U, c ∈ PresentColors G mu0 terminalSupport))
      (_ : (∀ (a : Fin p), trace.gamma a ∈ PresentColors G mu0 u))
      (_ :
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ L)
          (_ : ett.series.data.gamma s.succ = some gammaS)
          (_ : ett.series.data.delta s.succ = some deltaS),
          ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS))
      (_ :
        (∀ (a c : Fin p) (_ : (↑c : ℕ) = (↑a : ℕ) + (1 : ℕ)),
          trace.delta c = trace.gamma a))
      (_ :
        (∀ (t : Fin ett.rounds) (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
          (_ : IsProperEdgeColoring G phi)
          (_ : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
          (_ : beta ∈ MissingColors G phi u) (_ : alpha ∈ PresentColors G phi u)
          (_ : alpha ∈ PresentColors G phi terminalSupport)
          (_ : beta ∈ PresentColors G phi terminalSupport),
          TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
            (∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc),
                Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                  w = terminalSupport) ∧
              (Sum.inl terminalSupport ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
                ¬((TwoColorIncidenceGraph G phi alpha beta).neighborSet
                      (Sum.inl terminalSupport)).Subsingleton)))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}
          (_ : IsOneEdgeUncolored phi e0),
          IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta c : Fin k} {z : V ⊕ E}
          (_ : c ∈ PresentColors G phi v) (_ : c ≠ alpha) (_ : c ≠ beta),
          c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} (_ : alpha ≠ beta)
          (_ : beta ∈ MissingColors G phi v) (_ : alpha ∈ PresentColors G phi v),
          alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧
            beta ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v))
      (_ :
        (∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} {z : V ⊕ E}
          (_ : alpha ≠ beta) (_ : alpha ∈ PresentColors G phi v)
          (_ : beta ∈ PresentColors G phi v),
          ∀ c ∈ PresentColors G phi v,
            c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v)),
    ExtensionBaseAlgorithmCInvariant ett terminalSupport hterminalSupport terminalSlot jSlot
      mu0 u trace := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot jSlot
      mu0 u p indices gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
      hTjInitial hterminalGammaMissing supportClass hterminalInClass reversePosition slot traceGamma
      traceDelta nextColoring coloringNat coloring hslotEnumerates hslotDescending htransition trace
      trace_colors_ne surviving_gamma_ne L U hposition htraceDelta slot_mem gamma_mem_U delta_mem_U
      initial_terminal_present initial_gamma_present initial_survivor next_delta_eq_gamma
      single_step swap_preserves_one swap_present_other root_swap_exchange swap_preserves_present
  have invariant :=
    @helper_invariant_596 V E inferInstance inferInstance inferInstance G k
        e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0 u p indices
        gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
        hterminalGammaMissing hterminalInClass hslotEnumerates hslotDescending htransition
        trace_colors_ne surviving_gamma_ne hposition htraceDelta slot_mem gamma_mem_U delta_mem_U
        initial_terminal_present initial_gamma_present initial_survivor next_delta_eq_gamma
        single_step swap_preserves_one swap_present_other root_swap_exchange swap_preserves_present
  unfold ExtensionBaseAlgorithmCInvariant
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (invariant a).1
  · exact @helper_branch_732 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport hterminalSupport terminalSlot jSlot mu0 u p indices gamma
      delta hterminalAtEnd hsupport hkind hgamma hdelta hTjInitial hterminalInClass
      hslotEnumerates hslotDescending htransition slot_mem gamma_mem_U delta_mem_U single_step
      invariant
  · intro s gammaS deltaS hs hnot _ _ _
    have hsImage : s ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hs
    rcases Finset.mem_image.mp hsImage with ⟨a, -, ha⟩
    exact False.elim (hnot a ha)

private theorem helper_continuation_1280.{u_1, u_2} :
    helperContinuation1280Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot
      jSlot mu0 u p indices gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta
      hchain hTjInitial hterminalGammaMissing hinitialGammaPresent hinitialSI hterminalNoMissing
  set supportClass : Finset (Fin ett.rounds) := ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport terminalSupport
  intro hterminalInClass reversePosition slot traceGamma traceDelta nextColoring coloringNat
      coloring hslotEnumerates hslotDescending htransition trace trace_colors_ne surviving_gamma_ne
  set L : Finset (Fin ett.rounds) := supportClass.erase terminalSlot
  intro U hposition htraceGamma htraceDelta slot_mem gamma_mem_U delta_mem_U
  have initial_terminal_present (c : Fin k) (hc : c ∈ U) :
      c ∈ PresentColors G mu0 terminalSupport := by
    have hn : c ∉ MissingColors G mu0 terminalSupport := by
      intro hm
      have hi : c ∈ MissingColors G mu0 terminalSupport ∩ U :=
        Finset.mem_inter.mpr ⟨hm, hc⟩
      change c ∈ MissingColors G mu0 terminalSupport ∩
        ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot).biUnion
            (fun t => ett.series.data.stored t.succ) at hi
      rw [hterminalNoMissing] at hi
      simp at hi
    simpa [MissingColors] using hn
  have initial_gamma_present (a : Fin p) :
      trace.gamma a ∈ PresentColors G mu0 u := by
    rw [htraceGamma]
    exact hinitialGammaPresent a.rev
  have initial_survivor (s : Fin ett.rounds) (gammaS deltaS : Fin k)
      (hs : s ∈ L)
      (hgs : ett.series.data.gamma s.succ = some gammaS)
      (hds : ett.series.data.delta s.succ = some deltaS) :
      ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS := by
    exact hinitialSI s gammaS deltaS hs hgs hds
  have next_delta_eq_gamma (a c : Fin p)
      (hca : c.val = a.val + 1) : trace.delta c = trace.gamma a := by
    have ha := hposition a
    have hc := hposition c
    let q : Fin p := c.rev
    have hpc : reversePosition c = q.castSucc := Fin.ext rfl
    have hpa : reversePosition a = q.succ := by
      apply Fin.ext
      simp [q]
      omega
    rw [htraceDelta c, htraceGamma a, hpc, hpa]
    exact (hchain q).symm
  have single_step := @helper_single_step_295 V E inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSupport u
  have swap_preserves_one := @helper_swap_preserves_one_984 V E G k e0
  have swap_present_other {phi : PartialEdgeColoring E k} {v : V}
      {alpha beta c : Fin k} {z : Sum V E}
      (hc : c ∈ PresentColors G phi v) (hca : c ≠ alpha)
      (hcb : c ≠ beta) :
      c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
    exact TwoColorComponentSwapPreservesOther hc hca hcb
  have root_swap_exchange := @TwoColorComponentSwapExchangesRootColors V E inferInstance G k
  have swap_preserves_present {phi : PartialEdgeColoring E k} {v : V}
      {alpha beta : Fin k} {z : Sum V E}
      (hne : alpha ≠ beta)
      (halpha : alpha ∈ PresentColors G phi v)
      (hbeta : beta ∈ PresentColors G phi v) :
      ∀ c : Fin k, c ∈ PresentColors G phi v →
        c ∈ PresentColors G
          (TwoColorComponentSwap G phi alpha beta z) v := by
    exact TwoColorComponentSwapPreservesPresent halpha hbeta
  exact @helper_continuation_1578 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport)
      (@hterminalSupport) (@terminalSlot) (@jSlot) (@mu0) (@u) (@p) (@indices) (@gamma) (@delta)
      (@hproper) (@hone) (@hterminalAtEnd) (@hsupport) (@hkind) (@hgamma) (@hdelta) (@hchain)
      (@hTjInitial) (@hterminalGammaMissing) (@hterminalInClass) (@hslotEnumerates)
      (@hslotDescending) (@htransition) (@trace_colors_ne) (@surviving_gamma_ne) (@hposition)
      (@htraceDelta) (@slot_mem) (@gamma_mem_U) (@delta_mem_U) (@initial_terminal_present)
      (@initial_gamma_present) (@initial_survivor) (@next_delta_eq_gamma) (@single_step)
      (@swap_preserves_one) (@swap_present_other) (@root_swap_exchange) (@swap_preserves_present)

private theorem helper_branch_170.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (terminalSlot jSlot : Fin ett.rounds) (mu0 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
      (gamma delta : Fin (p + (1 : ℕ)) → Fin k) (_ : IsProperEdgeColoring G mu0)
      (_ : IsOneEdgeUncolored mu0 e0) (_ : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds)
      (_ :
        (∀ (a c : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) < (↑c : ℕ)),
          (↑(indices a) : ℕ) < (↑(indices c) : ℕ)))
      (_ :
        (∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.chosenVertex (indices a).succ = some terminalSupport))
      (_ :
        (∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE))
      (_ :
        (∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.gamma (indices a).succ = some (gamma a)))
      (_ :
        (∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.delta (indices a).succ = some (delta a)))
      (_ :
        (∀ (a : Fin (p + (1 : ℕ))),
          ett.series.data.stored (indices a).succ = {gamma a, delta a}))
      (_ : (∀ (a : Fin p), gamma a.succ = delta a.castSucc))
      (_ : Function.Injective (Fin.cons (gamma (0 : Fin (p + (1 : ℕ)))) delta))
      (_ :
        (∀
          s ∈
            (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                  terminalSupport).erase
              terminalSlot,
          TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
            (ett.series.data.tree s.succ.castSucc)))
      (_ : gamma (Fin.last p) ∈ MissingColors G mu0 u)
      (_ : (∀ (a : Fin p), gamma a.castSucc ∈ PresentColors G mu0 u))
      (_ :
        (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k)
          (_ :
            s ∈
              (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                    terminalSupport).erase
                terminalSlot)
          (_ : ett.series.data.gamma s.succ = some gammaS)
          (_ : ett.series.data.delta s.succ = some deltaS),
          ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS))
      (_ :
        (MissingColors G mu0 terminalSupport ∩
            ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                      terminalSupport).erase
                  terminalSlot).biUnion
              fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) =
          ∅),
    let supportClass : Finset (Fin ett.rounds) :=
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport;
    ∀ (_ : terminalSlot ∈ supportClass)
      (_ :
        supportClass.erase terminalSlot =
          Finset.image (fun (a : Fin p) ↦ indices a.castSucc) Finset.univ)
      (_ : ¬p = (0 : ℕ)),
    ∃ (trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u),
    ExtensionBaseAlgorithmCInvariant ett terminalSupport hterminalSupport terminalSlot jSlot
      mu0 u trace := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot jSlot
      mu0 u p indices gamma delta hproper hone hterminalAtEnd hincreasing hsupport hkind hgamma
      hdelta hstored hchain hdistinct hTjInitial hterminalGammaMissing hinitialGammaPresent
      hinitialSI hterminalNoMissing supportClass hterminalInClass herased hp
  have hpPos : 0 < p := Nat.pos_of_ne_zero hp
  let reversePosition : Fin p → Fin (p + 1) := fun a => a.rev.castSucc
  let slot : Fin p → Fin ett.rounds := fun a => indices (reversePosition a)
  let traceGamma : Fin p → Fin k := fun a => gamma (reversePosition a)
  let traceDelta : Fin p → Fin k := fun a => delta (reversePosition a)
  let nextColoring : ℕ → PartialEdgeColoring E k → PartialEdgeColoring E k :=
    fun a phi => if ha : a < p then
      TwoColorComponentSwap G phi
        (traceGamma ⟨a, ha⟩) (traceDelta ⟨a, ha⟩) (Sum.inl u)
    else phi
  let coloringNat : ℕ → PartialEdgeColoring E k :=
    Nat.rec mu0 (fun a phi => nextColoring a phi)
  let coloring : Fin (p + 1) → PartialEdgeColoring E k :=
    fun a => coloringNat a.val
  have hslotEnumerates : Finset.univ.image slot = supportClass.erase terminalSlot := by
    rw [herased]
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp [slot, reversePosition]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp [slot, reversePosition]⟩
  have hslotDescending : ∀ a b : Fin p, a.val < b.val →
      (slot b).val < (slot a).val := by
    intro a b hab
    apply hincreasing
    change b.rev.val < a.rev.val
    exact Fin.rev_lt_rev.mpr hab
  have htransition : ∀ a : Fin p,
      coloring a.succ = TwoColorComponentSwap G (coloring a.castSucc)
        (traceGamma a) (traceDelta a) (Sum.inl u) := by
    intro a
    simp [coloring, coloringNat, nextColoring, a.isLt]
  let trace := @helperTrace1922 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
      (@terminalSlot) (@mu0) (@u) (@p) (@indices) (@gamma) (@delta) (@hterminalAtEnd) (@hsupport)
      (@hkind) (@hgamma) (@hdelta) (@hterminalInClass) (@hslotEnumerates) (@hslotDescending)
      (@htransition)
  let colorChain : Fin (p + 2) → Fin k := Fin.cons (gamma 0) delta
  have gamma_eq_chain (q : Fin (p + 1)) :
      gamma q = colorChain q.castSucc := by
    cases q using Fin.cases with
    | zero => simp [colorChain]
    | succ a => simpa [colorChain] using hchain a
  have delta_eq_chain (q : Fin (p + 1)) :
      delta q = colorChain q.succ := by
    simp [colorChain]
  have trace_colors_ne (a : Fin p) :
      trace.gamma a ≠ trace.delta a := by
    change gamma (reversePosition a) ≠ delta (reversePosition a)
    rw [gamma_eq_chain, delta_eq_chain]
    intro h
    have hi := hdistinct h
    have hv := congrArg Fin.val hi
    simp at hv
  have surviving_gamma_ne := @helper_surviving_gamma_ne_883 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u p indices gamma delta hterminalAtEnd hsupport hkind hgamma hdelta hdistinct hterminalInClass
      hslotEnumerates hslotDescending htransition gamma_eq_chain delta_eq_chain
  refine ⟨trace, ?_⟩
  let L := supportClass.erase terminalSlot
  let U := L.biUnion fun t => ett.series.data.stored t.succ
  have hposition (a : Fin p) :
      (reversePosition a).val + a.val + 1 = p := by
    simp [reversePosition, Fin.rev]
    omega
  have htraceGamma (a : Fin p) :
      trace.gamma a = gamma (reversePosition a) := rfl
  have htraceDelta (a : Fin p) :
      trace.delta a = delta (reversePosition a) := rfl
  have hslotIdentity (a : Fin p) :
      trace.slot a = indices (reversePosition a) := rfl
  have slot_mem (a : Fin p) : trace.slot a ∈ L := by
    change trace.slot a ∈ supportClass.erase terminalSlot
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have gamma_mem_U (a : Fin p) : trace.gamma a ∈ U := by
    apply Finset.mem_biUnion.mpr
    refine ⟨trace.slot a, slot_mem a, ?_⟩
    rw [hslotIdentity a, hstored (reversePosition a),
      ← htraceGamma a]
    simp
  have delta_mem_U (a : Fin p) : trace.delta a ∈ U := by
    apply Finset.mem_biUnion.mpr
    refine ⟨trace.slot a, slot_mem a, ?_⟩
    rw [hslotIdentity a, hstored (reversePosition a),
      ← htraceDelta a]
    simp
  exact @helper_continuation_1280 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSupport hterminalSupport terminalSlot jSlot mu0 u p
      indices gamma delta hproper hone hterminalAtEnd hsupport hkind hgamma hdelta hchain
      hTjInitial hterminalGammaMissing hinitialGammaPresent hinitialSI hterminalNoMissing
      hterminalInClass hslotEnumerates hslotDescending htransition trace_colors_ne
      surviving_gamma_ne hposition htraceGamma htraceDelta slot_mem gamma_mem_U delta_mem_U
private noncomputable abbrev helperTrace2072.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [Fintype V] →
            [Fintype E] →
              [DecidableEq E] →
                {G : LooplessMultigraph V E} →
                  {k : ℕ} →
                    {e0 : E} →
                      {input : PartialEdgeColoring E k} →
                        {T : TreeSequence G e0} →
                          {generating : PartialEdgeColoring E k} →
                            (ett : ExtendedTashkinovTree G k e0 input T generating) →
                              (terminalSupport : V) →
                                (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) →
                                  (terminalSlot : Fin ett.rounds) →
                                    (mu0 : PartialEdgeColoring E k) →
                                      (u : V) →
                                        (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds →
                                          let supportClass : Finset (Fin ett.rounds) :=
                                            ExtensionBaseSupportClass ett terminalSupport
                                              hterminalSupport terminalSupport;
                                          terminalSlot ∈ supportClass →
                                            (indices : Fin ((0 : ℕ) + (1 : ℕ)) → Fin ett.rounds) →
                                              (Fin ((0 : ℕ) + (1 : ℕ)) → Fin k) →
                                                (Fin ((0 : ℕ) + (1 : ℕ)) → Fin k) →
                                                  supportClass.erase terminalSlot =
                                                      Finset.image
                                                        (fun (a : Fin (0 : ℕ)) ↦ indices a.castSucc)
                                                        Finset.univ →
                                                    ExtensionBaseAlgorithmCTrace ett terminalSupport
                                                      hterminalSupport terminalSlot mu0 u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport terminalSlot mu0
      u hterminalAtEnd supportClass hterminalInClass indices gamma delta herased
  exact {
    steps := 0
    slot := fun a => Fin.elim0 a
    gamma := fun a => Fin.elim0 a
    delta := fun a => Fin.elim0 a
    coloring := fun _ => mu0
    initialColoring := rfl
    terminalAtEnd := hterminalAtEnd
    terminalInClass := hterminalInClass
    enumerates := by simpa [supportClass] using herased.symm
    strictlyDescending := fun a => Fin.elim0 a
    chosenSupport := fun a => Fin.elim0 a
    extensionKind := fun a => Fin.elim0 a
    gammaField := fun a => Fin.elim0 a
    deltaField := fun a => Fin.elim0 a
    transition := fun a => Fin.elim0 a }

theorem ExtensionBaseAlgorithmC {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (terminalSlot jSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k)
    (hproper : IsProperEdgeColoring G mu0)
    (hone : IsOneEdgeUncolored mu0 e0)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ s : Fin ett.rounds,
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = s)
    (hterminalIndex : indices (Fin.last p) = terminalSlot)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hTjInitial : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
        TreeSequenceInitialSegment
          (ett.series.data.tree jSlot.succ.castSucc)
          (ett.series.data.tree s.succ.castSucc))
    (hterminalGammaMissing :
      gamma (Fin.last p) ∈ MissingColors G mu0 u)
    (hinitialGammaPresent : ∀ a : Fin p,
      gamma a.castSucc ∈ PresentColors G mu0 u)
    (hinitialSI : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS)
    (hterminalNoMissing :
      MissingColors G mu0 terminalSupport ∩
        ((ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot).biUnion
            (fun s => ett.series.data.stored s.succ) = ∅) :
    ∃ trace :
      ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot mu0 u,
    ExtensionBaseAlgorithmCInvariant ett terminalSupport hterminalSupport terminalSlot jSlot
      mu0 u trace := by
  classical
  let supportClass :=
    ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport
  have hterminalInClass : terminalSlot ∈ supportClass := by
    rw [hclass]
    exact ⟨Fin.last p, hterminalIndex⟩
  have herased :=
    @helper_herased_110 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSupport hterminalSupport terminalSlot p indices hincreasing hclass
        hterminalIndex
  by_cases hp : p = 0
  · subst p
    let trace := @helperTrace2072 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
        (@terminalSlot) (@mu0) (@u) (@hterminalAtEnd) (@hterminalInClass) (@indices) (@gamma)
        (@delta) (@herased)
    refine ⟨trace, ?_⟩
    unfold ExtensionBaseAlgorithmCInvariant
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨hproper, hone⟩
    · intro a
      exact Fin.elim0 a
    · intro s gammaS deltaS hs _ hsupportS hgammaS hdeltaS
      exact hinitialSI s gammaS deltaS hs hgammaS hdeltaS
  · exact @helper_branch_170 V E inferInstance inferInstance  inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport terminalSlot jSlot mu0 u p indices
      gamma delta hproper hone hterminalAtEnd hincreasing hsupport hkind hgamma hdelta hstored
      hchain hdistinct hTjInitial hterminalGammaMissing hinitialGammaPresent hinitialSI
      hterminalNoMissing hterminalInClass herased hp
end GoldbergSeymour

end
