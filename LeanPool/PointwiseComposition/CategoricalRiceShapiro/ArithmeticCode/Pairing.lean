/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.Conditional

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Cantor pairing

The pairing construction inverted by `codeUnpair₁` and `codeUnpair₂` in
`CategoricalRiceShapiro.ArithmeticCode.Arithmetic`.  It needs only the
conditional, not minimization, and so does not depend on that module.

Only the code construction is given here.  The standard computation theorem
over the natural numbers is not part of this migration.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

/-- Cantor pairing of `d₀` and `d₁`. -/
def codePair {n : ℕ} (d₀ d₁ : Code n) : Code n :=
  codeIfPos (codeLt d₀ d₁) (codeAdd (codeMul d₁ d₁) d₀)
    (codeAdd (codeAdd (codeMul d₀ d₀) d₀) d₁)

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
