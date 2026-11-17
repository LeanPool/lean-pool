/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.TableLookup
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.PartialRecursive

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The evaluator-cell code

One cell of the evaluation table.  The table length names the pair `(k, q)`:
`k` is the fuel and `q` the partial-recursive index under evaluation.  For
positive fuel the constructor number of `q` selects a branch — `4` pairing,
`5` composition, `6` primitive recursion, `7` minimization — and every other
constructor number falls through to `codeBaseEvaluatorCell`, which decides the
four base constructors.  Branches `6` and `7` receive predecessor fuel and the
whole index `q`; branch `7` reads the entire payload rather than its first
component.  No comparison of the argument with the fuel occurs.

The conditional is arithmetic and eager: `codeIfPos` evaluates both branches.
Only the code constructions are given here.  The standard computation theorems
over the natural numbers are not part of this migration.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

/-- The cell for one of the four base constructors. -/
def codeBaseEvaluatorCell {r : ℕ} (dtable dn : Code r) : Code r :=
  let dp := codeListLength dtable
  let dk := codeUnpair₁ dp
  let dq := codeUnpair₂ dp
  let dtag := codePartrecTag dq
  codeIfPos dk
    (codeIfPos (codeEq dtag (codeConst 0)) (codeConst 1)
      (codeIfPos (codeEq dtag (codeConst 1)) (codeSucc (codeSucc dn))
        (codeIfPos (codeEq dtag (codeConst 2)) (codeSucc (codeUnpair₁ dn))
          (codeIfPos (codeEq dtag (codeConst 3)) (codeSucc (codeUnpair₂ dn)) (codeConst 0)))))
    (codeConst 0)

/-- The cell for the pairing constructor. -/
def codePairEvaluatorCell {r : ℕ} (dtable dk dcf dcg dn : Code r) : Code r :=
  codeOptionBind (codeTableLookup dtable dk dcf dn)
    (codeOptionBind
      (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcg) (codeLift dn))
      (codeSucc (codePair (Code.proj (1 : Fin (r + 2))) (Code.proj (0 : Fin (r + 2))))))

/-- The cell for the composition constructor: the inner index `dcg` is applied
to the argument, and the outer index `dcf` to the result. -/
def codeCompEvaluatorCell {r : ℕ} (dtable dk dcf dcg dn : Code r) : Code r :=
  codeOptionBind (codeTableLookup dtable dk dcg dn)
    (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcf) codeHead)

/-- The cell for the primitive-recursion constructor. -/
def codePrecEvaluatorCell {r : ℕ} (dtable dk' dq dcf dcg dn : Code r) : Code r :=
  let dk := codeSucc dk'
  let dz := codeUnpair₁ dn
  let dt := codeUnpair₂ dn
  let dy := codeSub dt (codeConst 1)
  codeIfPos dt
    (codeOptionBind (codeTableLookup dtable dk' dq (codePair dz dy))
      (codeTableLookup (codeLift dtable) (codeLift dk) (codeLift dcg)
        (codePair (codeLift dz) (codePair (codeLift dy) codeHead))))
    (codeTableLookup dtable dk dcf dz)

/-- The cell for the minimization constructor. -/
def codeRfindEvaluatorCell {r : ℕ} (dtable dk' dq dcf dn : Code r) : Code r :=
  let dk := codeSucc dk'
  let dz := codeUnpair₁ dn
  let dm := codeUnpair₂ dn
  codeOptionBind (codeTableLookup dtable dk dcf (codePair dz dm))
    (codeIfPos codeHead
      (codeTableLookup (codeLift dtable) (codeLift dk') (codeLift dq)
        (codePair (codeLift dz) (codeSucc (codeLift dm))))
      (codeSucc (codeLift dm)))

/-- One evaluator cell: fuel and index are read from the table length, and the
constructor number of the index selects the branch. -/
def codeEvaluatorCell {r : ℕ} (dtable dn : Code r) : Code r :=
  let dp := codeListLength dtable
  let dk := codeUnpair₁ dp
  let dk' := codeSub dk (codeConst 1)
  let dq := codeUnpair₂ dp
  let dtag := codePartrecTag dq
  let dcf := codePartrecPayload₁ dq
  let dcg := codePartrecPayload₂ dq
  let drfind := codePartrecPayload dq
  codeIfPos dk
    (codeIfPos (codeEq dtag (codeConst 4)) (codePairEvaluatorCell dtable dk dcf dcg dn)
      (codeIfPos (codeEq dtag (codeConst 5)) (codeCompEvaluatorCell dtable dk dcf dcg dn)
        (codeIfPos (codeEq dtag (codeConst 6)) (codePrecEvaluatorCell dtable dk' dq dcf dcg dn)
          (codeIfPos (codeEq dtag (codeConst 7))
            (codeRfindEvaluatorCell dtable dk' dq drfind dn)
            (codeBaseEvaluatorCell dtable dn)))))
    (codeConst 0)

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
