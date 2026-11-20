/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FullPaper.lean.
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

public import LeanPool.GinibrePoincare.Endgame.FullMainAnalyticProof
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionEndpoints
public import LeanPool.GinibrePoincare.Analysis.GaussianCanonicalDbarSolution
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireDistance
public import LeanPool.GinibrePoincare.Analysis.GaussianGinibreProjectionIntertwining
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionGeometry
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionDistance
public import LeanPool.GinibrePoincare.Analysis.EntireVandermondeFactorization
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarEqualitySpace
public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionClasses
public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionGaussian
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionBridge
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireReconstruction
public import LeanPool.GinibrePoincare.Analysis.GinibreCenterProjectionEquality
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarCompactCore
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireHilbertIdentification
public import LeanPool.GinibrePoincare.Analysis.GaussianClosedFormVolume
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakEquality
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexProjectionGeometry
public import LeanPool.GinibrePoincare.Analysis.GaussianFirstModeCreation
public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesHolomorphicLowering
public import LeanPool.GinibrePoincare.Analysis.GinibreRadiusNotHolomorphic
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNine
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneTen
public import LeanPool.GinibrePoincare.Endgame.FullMatrixLift
public import LeanPool.GinibrePoincare.Endgame.FullNonQuadraticPotential
public import LeanPool.GinibrePoincare.Analysis.DynamicalFactorization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCapacity
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseCurvatureTangent
public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorIncompleteness
public import LeanPool.GinibrePoincare.Analysis.GinibreNonsymmetricCounterexample
public import LeanPool.GinibrePoincare.Analysis.GinibreLinearStatisticPoincare
public import LeanPool.GinibrePoincare.Analysis.HermiteRodriguesMultivariate
public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorGradientCommutation
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochner
public import LeanPool.GinibrePoincare.Analysis.GinibreEquilibriumProcessStationarityPath
public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreOneParticleSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreGraphNormEquivalence
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarCombinatorics
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreRealCoreClosureEquivalence
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexCoreClosureEquivalence
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarDistributionalClosure

public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralDifferentialFactorization
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralPoincare
public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterPoincare
public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterOrbits
public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterLowering

public import LeanPool.GinibrePoincare.Endgame.BochnerKodairaTheoremOneTen
public import LeanPool.GinibrePoincare.Endgame.CorrespondenceEndpoints

/-! # Public full-paper entry point

The concrete paper results are exported on their stated domains:

For a mathematical reading order, follow these modules, each under the
`LeanPool.GinibrePoincare` prefix:

1. Theorem 1.1, sharp inequality and equality cases:
   `Endgame.FullMainAnalyticProof`, then `Analysis.GaussianDbarEqualitySpace`
   and `Analysis.GaussianEntireHilbertIdentification`.
2. Theorems 1.2 and 1.3, equilibrium coordinates, dynamics and CIR:
   `Analysis.EquilibriumFactorization`, `Analysis.DynamicalFactorization`, and
   `Analysis.CorrespondenceDynamicsGlobalCIR`.
3. Theorem 1.4 and Corollary 1.5, polynomial sector and spectrum:
   `Analysis.PolynomialEigenfunctions`, `Analysis.PolynomialGeneratorSpectrum`,
   and `Analysis.CorrespondenceOperatorNumberSpectrum`.
4. Lemma 1.7 and Remark 1.8, curvature unbounded below and constant mean
   curvature: `Analysis.GinibrePointwiseCurvature`.
5. Theorems 1.9 and 1.10, exact deficits: `Endgame.FullTheoremOneNine`,
   `Endgame.FullTheoremOneNinePointwiseGamma`, and `Endgame.FullTheoremOneTen`.
6. Theorems 1.12 to 1.14, radial LSI, matrix lift and general potentials:
   `Analysis.LogSobolevInequality`, `Endgame.FullMatrixLift`, and
   `Endgame.FullNonQuadraticPotential`.
7. Section 2 and Appendices A and B, domains, cores and dbar foundations:
   `Analysis.GaussianDbarCompactCore`, `Analysis.CorrespondenceCollisionCutoff`,
   `Analysis.GinibreCollisionCapacity` for the collision capacity of Lemma A.3,
   and `Analysis.CorrespondenceAuxiliaryHermiteLeading`.

The pinned [upstream reading guide][reading-guide] and its four topic guides
give longer routes, under the upstream module names.

To consume large conclusions without positional projections,
use `fullTheoremOneNine_named`, `fullTheoremOneTen_named`,
`fullMatrixLift_named`, `correspondenceOperatorNumber_has_bochner_data`, and
`ginibreBrownianMaximalProcess_CIR_realization_named`. Their result records
give named access to the same proved identities and domain facts.

[reading-guide]:
  <https://github.com/djalilchafai/ginibre-poincare/blob/a1b2ba84e7dad8ba11b5c49a18b986a762a00a41/HUMAN_READABILITY.md>

* `fullTheoremOneNine`: both exact deficits on the full real generator graph,
  with sharp equality classification on the entire symmetric weak domain.
* `fullTheoremOneNinePointwiseGamma`: both deficits on the compact smooth
  collision-free core, with the second written as the literal pointwise Γ₂ integral.
* `fullTheoremOneTen`: both differential deficits, with the actual projected
  inverse square root and genuine weak second Wirtinger derivatives. Their
  energy is the literal Gaussian integral of the squared derivatives.
* `fullMatrixLift_functional_inequalities`: variance and entropy bounds under
  the actual Gaussian matrix law and its genuine finite overlap energy.
* `correspondenceMatrix_theorem_1_13`: the matrix H¹ hypothesis internally
  identifies the weak derivative and proves finite overlap energy.
* `fullNonQuadraticPotentialTheorem`: symmetric Poincaré under the
  actual Laplacian bound, and radial log-Sobolev under actual strong convexity.
* `ginibreBrownian_full_two_radius_independent_CIR_realization`: the original
  singular Brownian process, two independent drivers and both localized CIR
  equations with genuine exhausting stops.
* `correspondence_ginibre_global_independent_CIR_equations`: both unstopped
  radius equations with the same independent drivers and actual stochastic integrals.
* `correspondence_ginibre_continuous_strongMarkov`: continuous strong Markov
  paths, including restart at almost surely finite stopping times.
* `correspondenceOperatorEvolution_ergodic`: strong L² ergodicity without a
  symmetry restriction on the observable.
* `correspondenceFriedrichsSquareRoot_domain_ordinary_H1`: the positive
  self-adjoint square root of the nonnegative Friedrichs operator `−A` has the ordinary
  weak-H¹ domain, where `A` is the unrestricted generator.
* `correspondenceOperatorNumber_spectrum_iff`: the exact spectrum of the
  maximal Gaussian number operator, using actual bounded two-sided inverses.
* `correspondenceOperatorNumber_ginibre_shifted_root_deficit`: the literal
  shifted-square-root deficit on the symmetric ordinary weak-H¹ domain.
* `ginibreBrownian_equilibrium_original_invariant`: exact Ginibre marginals
  of the literal equilibrium-initialized original Brownian process.
* `ginibreOriginalStochasticL2Resolvent_eq_analytic`: identification of the
  literal stochastic normalized Laplace integral and the analytic unit resolvent.
* `ginibreOriginalSymmetricStochasticL2Operator_eq_paper`: the actual original
  Brownian transition semigroup equals the analytic paper evolution for every
  nonnegative speed, time and symmetric L² input.
* `polynomialSector_incomplete`: the actual closed polynomial sector is proper,
  witnessed by the nonzero centered quadratic and genuine relative-phase invariance.
* `ginibre_nonsymmetric_poincare_constant_lower_bound`: the actual coordinate
  counterexample gives the nonsymmetric lower bound (n+1)/4 for n≥2.
* `ginibreLinearStatistic_poincare`: sharp dimension-free transfer to the actual
  C¹ Lipschitz linear-statistic pushforward law.
* `ComplexHermite.multivariateNormalized_rodrigues`: the literal sequential
  Wirtinger derivatives of the actual Gaussian, with exact factorial constants.
* `ginibrePregenerator_gradient_commutation`: the actual differential operator
  commutes with directional differentiation up to the genuine Hamiltonian Hessian.
* `ginibrePointwiseGammaTwo_bochner`: the actual pointwise Bochner formula;
  `ginibrePointwiseGammaTwo_eq_iterated` identifies the literal iterated carré du champ.
* `ginibreEquilibriumPositivePath_shift_law`: true whole-path equilibrium
  stationarity, also exported as literal original-process finite-dimensional laws.
* `ginibreCollisionSet_capacity_zero`: zero capacity for the literal weighted
  ordinary weak-H¹ capacity infimum.
* `ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment`: Corollary 1.5
  for every n > 0, using the bounded two-sided resolvent spectrum of the actual
  unbounded full generator at arbitrary positive speed.
* `ginibre_gradient_graph_norm_equivalence`: the positive-speed norm comparison
  in Lemma A.2, on actual weighted L² value/gradient pairs.
* `ginibreComplexSmoothCore_closure_equivalence`: the equality of the global
  and collision-free compact smooth complex gradient graph closures in Lemma A.2.

The finite and infinite second-Wirtinger energy formulas are exported along
with their independently defined compact-test weak derivative graphs.
* `ginibre_pointwise_bakry_emery_curvature_unbounded_below` and
  `ginibre_pointwise_mean_curvature`: genuine Hamiltonian Hessian conclusions.

These exports use the actual measures, domains, processes and operators. Their
analytic constructions and regularity conclusions are proved in the imported
modules rather than supplied as completion assumptions.
-/

@[expose] public section
