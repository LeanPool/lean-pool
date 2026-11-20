/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneScalarLeibniz

/-!
# The weak form of the constant-coefficient equation

This module defines `constantCoefficientWeakForm`, the sesquilinear weak form of the
constant-coefficient operator `-epsilon Delta + mu` on the repository's whole-plane weak
`H¹` graph.  It is the form of the scalar resolvent equation of the constant-coefficient
background operator: `ConstantCoefficientBackgroundResolvent` states the weak resolvent
equation with it, and `WholePlaneEllipticRegularity` turns that equation into an
identity of tempered distributions.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace ConstantCoefficientBackground

/-- The weak form of `(-epsilon Delta + mu) g` on the whole plane.  The inner
product convention is Mathlib's: it is conjugate-linear in the test field
and linear in the solution field. -/
def constantCoefficientWeakForm (epsilon : ℝ) (mu : ℂ)
    (g phi : WholePlaneScalarH1) : ℂ :=
  (epsilon : ℂ) *
      ∑ j : Fin 2,
        inner ℂ (wholePlaneH1FirstDerivative ℂ j phi)
          (wholePlaneH1FirstDerivative ℂ j g) +
    mu * inner ℂ (wholePlaneH1Embedding ℂ phi)
      (wholePlaneH1Embedding ℂ g)

end ConstantCoefficientBackground

end

end FastDynamo
