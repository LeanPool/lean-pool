/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EncodedList
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Pairing

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The table-lookup code

`codeTableLookup dtable dk dq dn` reads entry `dn` of the row of the encoded
table `dtable` indexed by the Cantor pair of `dk` and `dq`.

A row is stored as an encoded `Option (List (Option ℕ))`, so the row read out
of the table is an encoded `Option (Option ℕ)`, and the two layers are
flattened by `codeOptionJoin`.  Subtracting `1` before the second lookup
replaces an absent row by the empty row.

The literal construction matters: later results reason about this code itself,
not only about the function it realizes over the natural numbers, so it must not
be replaced by an extensionally equivalent one.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

/-- Flatten an encoded `Option (Option ℕ)` to an encoded `Option ℕ`. -/
def codeOptionJoin {r : ℕ} (d : Code r) : Code r :=
  codeSub d (codeConst 1)

/-- Entry `dn` of the row of `dtable` indexed by the pair of `dk` and `dq`. -/
def codeTableLookup {r : ℕ} (dtable dk dq dn : Code r) : Code r :=
  codeOptionJoin
    (codeListGetOptional (codeSub (codeListGetOptional dtable (codePair dk dq)) (codeConst 1))
      dn)

/-- The table-lookup code written out without the private flattening helper. -/
theorem codeTableLookup_eq {r : ℕ} (dtable dk dq dn : Code r) :
    codeTableLookup dtable dk dq dn =
      codeSub
        (codeListGetOptional
          (codeSub (codeListGetOptional dtable (codePair dk dq)) (codeConst 1)) dn)
        (codeConst 1) :=
  rfl

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
