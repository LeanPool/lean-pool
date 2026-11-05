/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelSupportClosureProperties
public import LeanPool.GoldbergSeymour.ParallelTerminalAwayInterchangeable
public import LeanPool.GoldbergSeymour.ParallelTerminalPEPreprocessing
public import LeanPool.GoldbergSeymour.ParallelTwoConstituentPathContradiction

public import LeanPool.GoldbergSeymour.Td

/-!
# Parallel Closure Union Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ParallelClosureUnionElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (baseSigma : HierarchyBase ett sigma) :
    ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet baseSigma.core) := by
  classical
  have ctx : TechnicalInductionContext G k e0 ett.rounds := by
    refine {
      lowerOne := ?_
      lowerTwo := ?_
      lowerThree := ?_
      lowerFour := ?_
      lowerFive := ?_
      lowerSix := ?_
      currentThree := ?_
      currentFour := ?_
      currentFive := ?_
      currentSix := ?_ }
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.2.2
    · intro input' T' generating' current hround hmax
      apply ExtensionRules G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply ExtensionBase G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply Basic2 G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply Td G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hpre := ParallelTerminalPEPreprocessing G k e0 input T phi ett ctx
    hMP hpositive hPE sigma hproper hone hstable baseSigma
  dsimp at hpre
  rcases hpre with
    ⟨support, common, gamma, delta, hsupport, hgamma, hdelta,
      hsupportT, hsupportJ, hcommonT, hcommonJ, hcommonNe,
      hdeltaMissing, hgammaNotMissing, hcommonMissing, hTElementary⟩
  have hclosure := ParallelSupportClosureProperties G k e0 input T phi ett
    ctx hMP hpositive hPE sigma hproper hone hstable baseSigma
  rcases hclosure with ⟨hJElementary, hJClosed, hJInterchangeable⟩
  have hTInterchangeable :=
    ParallelTerminalAwayInterchangeable G k e0 input T phi ett ctx hMP
      hpositive hPE sigma hproper hone hstable support gamma delta
      hsupport hgamma hdelta
  dsimp at hTInterchangeable
  have hunion : Nonempty (OrderedTreeUnion Tn baseSigma.closure baseSigma.core) := by
    simpa [n, Tn] using (baseSigma.parallel hPE).2.2
  apply ParallelTwoConstituentPathContradiction G k e0 sigma Tn
    baseSigma.closure baseSigma.core hunion hproper hTElementary
    hJElementary hJClosed support common gamma delta hsupportT hsupportJ
    hcommonT hcommonJ hcommonNe hdeltaMissing hgammaNotMissing
    hcommonMissing
  · intro alpha beta halpha hbeta halphaGamma halphaDelta hbetaGamma
      hbetaDelta
    exact hTInterchangeable alpha beta halpha hbeta halphaGamma halphaDelta
      hbetaGamma hbetaDelta
  · exact hJInterchangeable

end GoldbergSeymour

end
