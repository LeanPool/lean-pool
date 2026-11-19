/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/DynamicalFactorization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianProjection
public import LeanPool.GinibrePoincare.Analysis.GinibreDynamicsGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRRealization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticFullTwoRadiusRealization
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalIndependentInitial
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianStateTransitionKernel
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianEquilibriumProductLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticStationaryTwoRadiusLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionSemigroupIdentification

/-! # Reading route through stochastic dynamical factorization

This import facade collects the endpoints for the original singular
Brownian SDE. For a proof-oriented reading order:

1. `GinibreDrivenPathFactorization`: project the deterministic Volterra
   equation to the center OU equation and the relative equation.
2. `GinibreBrownianProjection`: prove orthogonality and independence of
   the projected Brownian noises.
3. `GinibreStochasticNoncollision` (imported transitively): construct the
   Hamiltonian martingales and conclude infinite lifetime and noncollision.
4. `BrownianOrthogonalIndependentInitial`: transfer independent input
   pairs through the measurable solution maps to independent entire paths.
5. `GinibreStochasticFullTwoRadiusRealization`: construct independent
   scalar drivers and both localized CIR equations, including zero speed
   and zero initial center.
6. `GinibreHamiltonianStateTransitionKernel`: assemble the genuine
   transition kernels and their Markov properties.
7. `GinibreHamiltonianEquilibriumProductLaw` and
   `GinibreStochasticStationaryTwoRadiusLaw`: obtain invariance of the
   original process and the independent Gamma law of the two radii at each time.
8. `GinibreStochasticTransitionSemigroupIdentification`: identify the
   original stochastic evolution with the analytic paper-speed evolution
   on the full symmetric L² space.

The deterministic and stochastic endpoints keep their individual domains:
noncollision and path factorization need a positive particle count; the
relative-radius CIR endpoints require at least two particles. Speed is
nonnegative in the global original-process assertions. Integral identities
are localized by bounded Hamiltonian stops, with exhaustion established in
`GinibreStochasticLocalizationExhaustion`. -/

@[expose] public section
