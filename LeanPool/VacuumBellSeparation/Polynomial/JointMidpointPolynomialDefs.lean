/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateCauchyPolynomial
public import LeanPool.VacuumBellSeparation.Polynomial.MultivariateSelector
public import LeanPool.VacuumBellSeparation.Polynomial.SelectorTaylorBounds

/-!
# Literal statement construction extracted from Polynomial/JointMidpointPolynomial

The moved declarations retain their original text. Later target proofs remain separate.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace VacuumBellSeparation
open Gaussian MvPolynomial

/-- Joint midpoint shift defined as `if j = 0 then 1 / 2 else if j = 3 then -(1 / 2) else 0`. -/
def jointMidpointShift (j : Fin 6) : ℂ :=
  if j = 0 then 1 / 2 else if j = 3 then -(1 / 2) else 0

/-- Joint midpoint left given by `C 1 * X 0 + C (1 / 2)`. -/
def jointMidpointLeft : MvPolynomial (Fin 6) ℂ := C 1 * X 0 + C (1 / 2)

/-- Joint midpoint right given by `C (-1) * X 3 + C (1 / 2)`. -/
def jointMidpointRight : MvPolynomial (Fin 6) ℂ := C (-1) * X 3 + C (1 / 2)

/-- Joint midpoint oriented. -/
def jointMidpointOriented (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) : MvPolynomial (Fin 6) ℂ :=
  realPolynomialSubstitution (selector (2 * n)) jointMidpointLeft *
    realPolynomialSubstitution (selector (2 * n)) jointMidpointRight *
      cauchyTaylorPolynomial 6 n (1 / 100) F (fun _ => 1) jointMidpointShift

/-- Swap the actual two triples. -/
def swapSpatialSix (j : Fin 6) : Fin 6 :=
  Fin.addCases (fun i : Fin 3 => Fin.natAdd 3 i) (fun i : Fin 3 => Fin.castAdd 3 i) j


/-- Product-minus-joint sign and the actual transpose. -/
def jointMidpointPolynomial (F : (Fin 6 → ℂ) → ℂ) (n : ℕ) : MvPolynomial (Fin 6) ℂ :=
  -(jointMidpointOriented F n + rename swapSpatialSix (jointMidpointOriented F n))


end VacuumBellSeparation
