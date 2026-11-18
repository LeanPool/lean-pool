/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.LetwinApproximation
public import LeanPool.KLS.FunctionalInequalities.KLS.Letwin.RegularClass
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic

/-!
# The compact Letwin constant-eight bound

`KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`: for every `n > 0`, every
compactly supported isotropic
log-concave probability law on `EuclideanSpace ℝ (Fin n)` and every self-adjoint real operator
(singular and indefinite included), the
variance of the quadratic form is at most `8` times its squared Hilbert–Schmidt norm. It follows
from the regular-class bound through the
existing compact reduction `letwinCompactBound_of_regularClass`.

This is the exact compact counterpart of Letwin (arXiv:2607.24164v1), Theorem 1.2, as used by
Bizeul–Klartag–Lehec
(arXiv:2610.05474v1), Lemma 4.2. It does not state the noncompact theorem; this module provides only
that compact
bound.
-/

@[expose] public section

section
open MeasureTheory Set
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

theorem letwinCompactBound : LetwinCompactBound := by
  apply letwinCompactBound_of_regularClass
  intro n hn K W κ hκ hK hKc hKint hW hstrong μ hμ hiso
  exact regularClass_letwinQuadraticBound hn hκ hK hKc hKint hW hstrong μ hμ hiso

end FunctionalInequalities.KLS.LogConcave.Suspension

end
