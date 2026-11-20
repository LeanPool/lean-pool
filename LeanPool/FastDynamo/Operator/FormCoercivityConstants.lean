/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Analysis.ComplexForm

/-!
# Explicit coercivity constants for complex forms

This file names a positive lower constant for a complex form,
`HasComplexCoercivityConstant q c`, and derives from it the lower bound of the real
part of `q` and coercivity in the sense of `IsComplexCoercive`.  Keeping the constant
explicit is convenient for uniform perturbation estimates.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

universe u v

variable {V : Type u} {X : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-! ## Explicit coercivity constants -/

/-- A named positive lower constant for a complex form.  Keeping the
constant explicit is convenient for uniform perturbation estimates. -/
def HasComplexCoercivityConstant (q : ComplexForm V) (c : ℝ) : Prop :=
  0 < c ∧ ∀ u : V, c * ‖u‖ * ‖u‖ ≤ (q u u).re

namespace HasComplexCoercivityConstant

omit [CompleteSpace V] in
/--
The defining lower bound of a named coercivity constant: `c ‖u‖² ≤ re (q u u)` for every `u` in
the form domain.
-/
theorem lower {q : ComplexForm V} {c : ℝ}
    (hq : HasComplexCoercivityConstant q c) (u : V) :
    c * ‖u‖ * ‖u‖ ≤ (q u u).re :=
  hq.2 u

omit [CompleteSpace V] in
/--
A form with a named coercivity constant is coercive in the unquantified sense `IsComplexCoercive`,
so complex Lax--Milgram applies to it.
-/
theorem isComplexCoercive {q : ComplexForm V} {c : ℝ}
    (hq : HasComplexCoercivityConstant q c) : IsComplexCoercive q :=
  ⟨c, hq.1, hq.2⟩

end HasComplexCoercivityConstant

end

end FastDynamo
