/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.FinalModel
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.Lemma4Pinch
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.InputsBridge
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.PinchCoefficientClassification
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.CoefficientShapes
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.CoefficientSigns

/-!
# Borisov's converse from the published normal-form inputs

This file is the assembly point for the converse direction of Borisov's
criterion.  The presentation-level Assertions IV--V and the coefficient
classification in Assertion V supply every input used by the iterated-HNN
proof.
-/

@[expose] public section

namespace Undecidability
namespace BorisovConverseClassified

open BorisovCStage
open BorisovContextNormalForm
open BorisovFinalModel
open BorisovLemma4Pinch

noncomputable section

/-- The converse simulation theorem with the required `Gamma3` normal-form
inputs displayed explicitly.  All `c`, `t`, and `k` HNN stages, the ordered
double-coset extraction, and the full Lemma-4 induction are discharged. -/
theorem criterion_converse_of_classification
    (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum)
    (hinter : BaseIntersections datum)
    (hclass : PinchClassification datum hfree)
    (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  criterion_converse_of_borisov_inputs datum hfree hinter
    (borisovLemma4_of_classification datum hfree hclass) Q

end

end BorisovConverseClassified
end Undecidability

namespace Undecidability
namespace BorisovConditionalConverse

open BorisovCStage
open BorisovConverseClassified
open BorisovInputsBridge
open BorisovIntersections
open BorisovLemma4Pinch
open BorisovHNNModel
open BorisovPinchCoefficientClassification
open BorisovCoefficientShapes
open BorisovCoefficientSignComparison

noncomputable section

/-- Minimal semantic boundary for the converse: rank-five freeness, the two
base intersections, and the literal coefficient shapes. -/
theorem criterion_converse_of_shapes
    (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum)
    (hinter : BorisovContextNormalForm.BaseIntersections datum)
    (hsource : ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ U datum →
        SourceCoefficientShape datum Q f r)
    (htarget : ∀ (Q : List (Fin 2)) (f r : ℤ),
      d3 ^ f * positive3 Q * e3 ^ r ∈ V datum →
        TargetCoefficientShape datum Q f r)
    (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  criterion_converse_of_classification datum hfree hinter
    (pinchClassification_of_shapes datum hfree hsource htarget) Q

/-- Parser-facing form of `criterion_converse_of_shapes`: positivity and the absence of two
displayed rule letters are the exact two facts consumed from the
coefficient-by-coefficient comparison of flat HNN normal forms. -/
theorem criterion_converse_of_positive_sparse_parsers
    (datum : Thue.StandingDatum)
    (hsourcePositive : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        AllPositive w.toWord)
    (hsourceSparse : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1)
    (htargetPositive : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        AllPositive w.toWord)
    (htargetSparse : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1)
    (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  criterion_converse_of_shapes datum (rankFiveFree datum)
    (baseIntersections datum)
    (sourceCoefficientShape_of_positive_sparse_parser datum
      hsourcePositive hsourceSparse)
    (targetCoefficientShape_of_positive_sparse_parser datum
      htargetPositive htargetSparse) Q

/-- Flat-signature uniqueness supplies positivity automatically.  Thus the
page-771 parser input used here is that a canonical rank-five preimage
contains at most one displayed rule letter. -/
theorem criterion_converse_of_sparse_parsers
    (datum : Thue.StandingDatum)
    (hsourceSparse : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      uLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1)
    (htargetSparse : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (w : FreeGroup BorisovCStage.RuleBasis),
      vLift datum w = d3 ^ f * positive3 Q * e3 ^ r →
        ruleCount w.toWord ≤ 1)
    (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  criterion_converse_of_positive_sparse_parsers datum
    (u_allPositive_of_coefficient_eq datum) hsourceSparse
    (v_allPositive_of_coefficient_eq datum) htargetSparse Q

end

end BorisovConditionalConverse
end Undecidability
