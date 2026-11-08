/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LeanPool.AaronsonAmbainis.Chain
public import LeanPool.AaronsonAmbainis.Bridge.PrintedRow
public import LeanPool.AaronsonAmbainis.Bridge.PrintedAA
public import LeanPool.AaronsonAmbainis.Conjecture

/-!
# From the statements of the project to the Mathlib-only statements of `Conjecture.lean`

`Conjecture.lean` states the conjecture, and the hypothesis `FbsDegreeBound`, with nothing but
Mathlib. Here the theorems of `Chain.lean` are carried over to its propositions:

* `explicitBound : ExplicitBound`, `printedConjecture : PrintedConjecture`,
  `explicitBoundPM : ExplicitBoundPM`
  from `AaronsonAmbainis.mainTheorem : MainTheorem`, which has no hypothesis;
* `explicitBoundImproved_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved`
  from `AaronsonAmbainis.mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved`.
  The hypothesis `FbsDegreeBound` is Theorem 1.7 of arXiv:2410.19062 as printed; it gives
  `RowBound` (`rowBound_of_printed` in `PrintedRow.lean`). Nothing here says that it holds.

The theorems of `Main.lean` are these four theorems under their final names. The same bounds
without square roots are `explicitBound_sq`, `explicitBoundPM_sq` and
`explicitBoundImproved_sq_of_fbsDegreeBound`. The passage from the statements on the cube of
`Defs.lean` to polynomials, and from the bounds without square roots to the printed forms, is in
`PrintedAA.lean`. `PrintedAA.lean` also gives two steps used in some of the proofs below: the
real power `ε ^ ((5 : ℝ) / 2)` of `Conjecture.lean` equals `ε² √ε` (`rpow_five_halves`), and the
encoding `true ↦ 1`, `false ↦ -1` of `ExplicitBoundPM` is reached from the encoding
`true ↦ -1`, `false ↦ 1` of `Defs.lean` by negating every bit (`pmt_sq_of_mainTheorem`,
`pmt_sqrt_of_mainTheorem`). The axioms on which the theorems depend are printed at the end.
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-! ### The theorems with no hypothesis -/

/-- Conjecture 6 of arXiv:0911.0996 with `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, no hypothesis. -/
theorem explicitBound_sq (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Conjecture 6 of arXiv:0911.0996 with `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`, no
hypothesis. -/
theorem explicitBound : ExplicitBound := by
  intro N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Conjecture 6 of arXiv:0911.0996 as printed with `Inf_i[p] ≥ (ε/d)^7`, no hypothesis. -/
theorem printedConjecture : PrintedConjecture :=
  fun N d p hp hrange ε hε hvar =>
    zo_pow_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Theorem 1.1 of the paper of this repository on `{-1,1}^n` (`true ↦ 1`, `false ↦ -1`), without
square roots: `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, no hypothesis. -/
theorem explicitBoundPM_sq (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pmt_sq_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar

/-- Theorem 1.1 of the paper of this repository on `{-1,1}^n` (`true ↦ 1`, `false ↦ -1`):
`Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`, no hypothesis. -/
theorem explicitBoundPM : ExplicitBoundPM := by
  intro n d p hp hbd ε hε hvar
  rw [rpow_five_halves hε.le]
  exact pmt_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar

/-! ### The conditional theorem, both ends Mathlib-only -/

/-- Theorem 1.7 of arXiv:2410.19062 as printed ⟹ Conjecture 6 of arXiv:0911.0996 with
`3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`. -/
theorem explicitBoundImproved_sq_of_fbsDegreeBound (h : FbsDegreeBound) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar

/-- Theorem 1.7 of arXiv:2410.19062 as printed ⟹ Conjecture 6 of arXiv:0911.0996 with
`Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`. -/
theorem explicitBoundImproved_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved := by
  intro h N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar

end AaronsonAmbainis.Bridge

/-! Types and axioms. -/
