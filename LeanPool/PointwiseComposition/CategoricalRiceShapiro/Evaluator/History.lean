/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Cell

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The evaluator-history codes

The evaluation table is extended one row at a time.  `codeEvaluatorRow` builds
the row of a table by primitive recursion on the fuel read from the table
length, `codeEvaluatorTableStep` appends that row, and `codeEvaluatorHistory`
iterates the step from the empty table.  `codeHistoryEvaluator` looks one entry
up in the history one step past the pair of its first two arguments, and
`codeEvaluatorHistoryBeforeCell` names the history one step earlier.

Only the code constructions are given here.  The standard computation theorems
over the natural numbers are not part of this migration, and no arithmetic
property of the encoding is asserted.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

/-- The recursion that builds one row of the evaluation table: at recursion
argument `i` the cell at index `k - (i + 1)` is consed onto the row built so
far, where `k` is the fuel read from the table length. -/
def codeEvaluatorRowCore {r : ℕ} (dtable : Code r) : Code (r + 1) :=
  codePrec (codeListNil (n := r))
    (codeListCons
      (codeEvaluatorCell (codeLift (codeLift dtable))
        (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift dtable))))
          (codeSucc (Code.proj (0 : Fin (r + 2))))))
      (Code.proj (1 : Fin (r + 2))))

/-- One row of the evaluation table of `dtable`. -/
def codeEvaluatorRow {r : ℕ} (dtable : Code r) : Code r :=
  codeBind (codeUnpair₁ (codeListLength dtable)) (codeEvaluatorRowCore dtable)

/-- `codeEvaluatorRow` binds the fuel read from the table length as the
recursion argument of one fixed arity-`r + 1` code.

The recursion is an implementation detail and stays private; a proof reaches it
by rewriting with this equation. -/
theorem codeEvaluatorRow_eq_bind {r : ℕ} (dtable : Code r) :
    codeEvaluatorRow dtable =
      codeBind (codeUnpair₁ (codeListLength dtable))
        (codePrec (codeListNil (n := r))
          (codeListCons
            (codeEvaluatorCell (codeLift (codeLift dtable))
              (codeSub (codeUnpair₁ (codeListLength (codeLift (codeLift dtable))))
                (codeSucc (Code.proj (0 : Fin (r + 2))))))
            (Code.proj (1 : Fin (r + 2))))) :=
  rfl

/-- Extend the evaluation table by one row. -/
def codeEvaluatorTableStep {r : ℕ} (dtable : Code r) : Code r :=
  codeListSnoc dtable (codeEvaluatorRow dtable)

/-- The evaluation table after the number of steps given by the argument. -/
def codeEvaluatorHistory : Code 1 :=
  codePrec (codeListNil (n := 0)) (codeEvaluatorTableStep (Code.proj (1 : Fin 2)))

/-- The evaluation history one step before the one `codeHistoryEvaluator`
reads: the history at the pair of the first two arguments. -/
def codeEvaluatorHistoryBeforeCell : Code 3 :=
  codeEvaluatorHistory.comp ![codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3))]

/-- Look up entry `n` of the row of `k` and `q` in the history one step past
the pair of `k` and `q`. -/
def codeHistoryEvaluator : Code 3 :=
  codeTableLookup
    (codeEvaluatorHistory.comp
      ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])
    (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)) (Code.proj (2 : Fin 3))

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
