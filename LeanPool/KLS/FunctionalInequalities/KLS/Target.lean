/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Poincare
/-!
# The KLS conjecture

`KLS.Conjecture` (`KLS/Statement.lean`) is a `def … : Prop` that names the sentence: there is a
universal
`C < ∞` such that every log-concave probability law with finite second moment on every
finite-dimensional
Euclidean space satisfies `C_P^lit(μ) ≤ C ‖Cov_μ‖_op`. This module proves it.

The proof is the Bizeul–Klartag–Lehec route (arXiv:2610.05474v1):
- the compact Letwin constant-8 bound (`letwinCompactBound`);
- the cutoff stochastic-localization cumulant bound (Theorem 4.1);
- the Taylor criterion (Theorem 3.1) and the suspension (Proposition 7.1);
- the regular approximation and the affine/isotropic reduction.

These are assembled in `KLS.BKL.Localization.conjecture` (`KLS/BKL/Poincare.lean`). The statement of
`KLS.Conjecture` is unchanged. Proof modules do not import this endpoint; the aggregate root exports
it.
-/

@[expose] public section

namespace FunctionalInequalities.KLS

/--
**The KLS conjecture**, covariance-normalized literature form (Blueprint `conj:kls`): there is a
universal `C < ∞` such that every log-concave probability law with finite second moment on every
finite-dimensional Euclidean space satisfies `C_P^lit(μ) ≤ C ‖Cov_μ‖_op`. Proved through the BKL
route. -/
theorem kls : Conjecture :=
  FunctionalInequalities.KLS.BKL.Localization.conjecture

end FunctionalInequalities.KLS
