/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.DistinctDistances.S4CertificateSummaryElab
meta import Lean.Meta.Closure

/-!
# Kernel replay of packed certificate checks

A proposed summary contains literal packed tries. Direct kernel conversion against
these literals avoids running the derived decidable equality for tries. For heavier
cases, verify the four quarters independently and combine their exact summaries.
-/

namespace Esgk.S4

open Lean Elab Tactic FarkasPackedCheck

/-- Check a computed equality by submitting reflexivity on its proposed right-hand side
as an auxiliary theorem. Kernel conversion checks that the two sides agree. -/
elab (name := certificateEquality) "s4_check_equality" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, _, expected) := target.eq?
    | throwError "expected a packed certificate equality"
  let reflexivity ← Meta.mkEqRefl expected
  let verified ← Meta.mkAuxTheorem target reflexivity
  goal.assign verified
  replaceMainGoal []

@[expose] public section

/-- Calculate the exact packed quantities from the original tree and row builder. -/
noncomputable def replaySummary {T : Type} (width : Nat) (box : Box)
    (build : T → Option Row) (rows : WTree T) : PackedSummary :=
  let length := chunkLen box.nv 4
  ⟨rows.sumNat (leafCost width box.nv build), rows.sumInt (leafRhs build),
    rows.sumTrie (leafPack width length 4 build Row.pos),
    rows.sumTrie (leafPack width length 4 build Row.neg)⟩

/-- A replay equality certifies the four projected quantities. -/
theorem summaryValidOfReplay {T : Type} {width : Nat} {box : Box} {build : T → Option Row}
    {rows : WTree T} {summary : PackedSummary}
    (verified : replaySummary width box build rows = summary) :
    SummaryValid width box build rows summary :=
  ⟨congrArg PackedSummary.cost verified, congrArg PackedSummary.rhs verified,
    congrArg PackedSummary.positive verified, congrArg PackedSummary.negative verified⟩

/-- Compute an integer row while forcing its common denominator before scaling the coefficients.
A case split on the natural number lets kernel reduction share the resulting numeral. -/
noncomputable def buildIntWithSharedDenominator
    (parameters : Params) (lower upper : ℚ) (tag : Tag) : Option Row :=
  (parameters.build lower upper tag).bind fun row ↦
    let scale (denominator : Nat) : Option Row :=
      some ⟨QRow.signedEntries (fun value ↦ decide (0 < value))
          (QRow.scaleNumerator denominator) row.ent,
        QRow.signedEntries (fun value ↦ decide (value < 0))
          (fun value ↦ -QRow.scaleNumerator denominator value) row.ent,
        QRow.scaleNumerator denominator row.rhs⟩
    Nat.casesOn row.den (scale 0) (fun predecessor ↦ scale predecessor.succ)

private theorem buildIntWithSharedDenominator_eq
    (parameters : Params) (lower upper : ℚ) :
    buildIntWithSharedDenominator parameters lower upper = parameters.buildInt lower upper := by
  funext tag
  unfold buildIntWithSharedDenominator Params.buildInt
  cases parameters.build lower upper tag with
  | none => rfl
  | some row =>
    simp only [Option.bind_some, QRow.toRow]
    generalize row.den = denominator
    cases denominator <;> rfl

/-- Exact replay with a shared denominator verifies the original integer-row builder. -/
theorem summaryValidOfSharedDenominatorReplay (parameters : Params) (lower upper : ℚ)
    {width : Nat} {rows : WTree Tag} {summary : PackedSummary}
    (verified : replaySummary width parameters.box (buildIntWithSharedDenominator parameters
      lower upper) rows = summary) :
    SummaryValid width parameters.box (parameters.buildInt lower upper) rows summary := by
  rw [← buildIntWithSharedDenominator_eq]
  exact summaryValidOfReplay verified

end

/-- Check one quarter of the weighted row tree against its proposed packed summary. -/
macro "s4_verify_quarter " summary:ident ", " valid:ident ", " caseIndex:num ", "
    rows:ident ", " builder:ident ", " quarter:num : command =>
  `(private noncomputable def subtree : WTree Tag := s4_subtree% $rows 2 $quarter
    private noncomputable def $summary : PackedSummary := s4_summary% $caseIndex, subtree
    private theorem $valid : SummaryValid 256 params.box $builder subtree $summary :=
      summaryValidOfReplay (by s4_check_equality))

/-- Verify each quarter separately, then check the combined summary. -/
macro "s4_verify_quarters " verified:ident ", " caseIndex:num ", " rows:ident : command => do
  let upperIndex := Syntax.mkNumLit (toString (caseIndex.getNat + 1))
  `(private noncomputable def certificateBuild :=
      params.buildInt (caseY.get $caseIndex) (caseY.get $upperIndex)
    s4_verify_quarter firstSummary, firstValid, $caseIndex, $rows, certificateBuild, 0
    s4_verify_quarter secondSummary, secondValid, $caseIndex, $rows, certificateBuild, 1
    s4_verify_quarter thirdSummary, thirdValid, $caseIndex, $rows, certificateBuild, 2
    s4_verify_quarter fourthSummary, fourthValid, $caseIndex, $rows, certificateBuild, 3
    private theorem combinedCheck : checkSummary 256 params.box
        ((firstSummary.combine secondSummary).combine (thirdSummary.combine fourthSummary)) =
      true := by decide +kernel
    private theorem $verified : check 256 params.box certificateBuild $rows = true :=
      ((firstValid.node secondValid).node (thirdValid.node fourthValid)).checked combinedCheck)

end Esgk.S4
