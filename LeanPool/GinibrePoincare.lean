/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexGibbsLSI
public import LeanPool.GinibrePoincare.Analysis.AlternativeMatrixPoincare
public import LeanPool.GinibrePoincare.Analysis.AlternativeSlaterPoincare
public import LeanPool.GinibrePoincare.Analysis.AlternativeSpectralPoincare
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceMatrixWeakClosure
public import LeanPool.GinibrePoincare.Analysis.DynamicalFactorization
public import LeanPool.GinibrePoincare.Analysis.EntireVandermondeFactorization
public import LeanPool.GinibrePoincare.Analysis.FullRadialLSIReduction
public import LeanPool.GinibrePoincare.Analysis.GaussianCanonicalDbarSolution
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCapacity
public import LeanPool.GinibrePoincare.Analysis.GinibreComplexCoreClosureEquivalence
public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionGeometry
public import LeanPool.GinibrePoincare.Analysis.GinibreEquilibriumProcessStationarityPath
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreNonsymmetricCounterexample
public import LeanPool.GinibrePoincare.Analysis.GinibreOneParticleSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import LeanPool.GinibrePoincare.Analysis.GinibreRadialGamma
public import LeanPool.GinibrePoincare.Analysis.GinibreRadiusNotHolomorphic
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticFullTwoRadiusRealization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticNoncollision
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticStationaryTwoRadiusLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionSemigroupIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreTwoRadiusEquilibriumLaw
public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianPoincare
public import LeanPool.GinibrePoincare.Analysis.PolynomialEigenfunctionGenerator
public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorIncompleteness
public import LeanPool.GinibrePoincare.Endgame.BochnerKodairaTheoremOneTen
public import LeanPool.GinibrePoincare.Endgame.FullMainAnalyticProof
public import LeanPool.GinibrePoincare.Endgame.FullMatrixLift
public import LeanPool.GinibrePoincare.Endgame.FullNonQuadraticPotential
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNine
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneTen

/-!
# Sharp symmetric Poincaré inequality for the complex Ginibre log-gas

Source: arxiv:2608.19358v2, url:https://github.com/djalilchafai/ginibre-poincare/tree/a1b2ba84e7dad8ba11b5c49a18b986a762a00a41
Authors: Djalil Chafaï
Status: verified
Main declarations: `GinibrePoincare.ginibre_symmetric_weak_poincare`,
  `GinibrePoincare.ginibreEquality_full_weak_affine_iff`,
  `GinibrePoincare.fullTheoremOneNine_named`, `GinibrePoincare.fullMainAnalyticProof`,
  `GinibrePoincare.spectral_ginibre_symmetric_weak_poincare`,
  `GinibrePoincare.slater_ginibre_symmetric_weak_poincare`,
  `GinibrePoincare.fullTheoremOneTenSchwartz`, `GinibrePoincare.bochnerKodairaTheoremOneTen`,
  `GinibrePoincare.radialObservable_ginibre_gamma`,
  `GinibrePoincare.polynomialEigenfunction_eigenvalue_equation_atSpeed`,
  `GinibrePoincare.ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment`,
  `GinibrePoincare.polynomialSector_incomplete`,
  `GinibrePoincare.ginibre_pointwise_bakry_emery_curvature_unbounded_below`,
  `GinibrePoincare.ginibre_pointwise_mean_curvature`, `GinibrePoincare.radial_sobolev_lsi`,
  `GinibrePoincare.gaussianSchwartzDbar_entire_gap`,
  `GinibrePoincare.gaussianVolumeClosedForm_canonicalSolvability`,
  `GinibrePoincare.entire_alternating_vandermonde_factorization`,
  `GinibrePoincare.ginibreDivisibleEntire_real_centered_geometry`,
  `GinibrePoincare.ginibreComplexSmoothCore_closure_equivalence`,
  `GinibrePoincare.ginibreCollisionSet_capacity_zero`,
  `GinibrePoincare.correspondenceMatrix_theorem_1_13`,
  `GinibrePoincare.fullMatrixLift_functional_inequalities`,
  `GinibrePoincare.matrixSpectralLift_finite_overlap_gaussian_poincare`,
  `GinibrePoincare.matrixGaussian_poincare_compactC1`,
  `GinibrePoincare.ginibreTwoRadius_equilibrium_gamma_product`,
  `GinibrePoincare.ginibre_nonsymmetric_poincare_constant_lower_bound`,
  `GinibrePoincare.ginibreSquaredNormL2_not_holomorphic`,
  `GinibrePoincare.ginibreBrownian_equilibrium_original_whole_future_stationary`,
  `GinibrePoincare.ginibreOriginalStochasticL2Resolvent_eq_analytic`,
  `GinibrePoincare.ginibreBrownianMaximalProcess_global_original_solution`,
  `GinibrePoincare.ginibreBrownian_full_two_radius_independent_CIR_realization`,
  `GinibrePoincare.ginibreBrownian_original_transition_eq_paper_ae`,
  `GinibrePoincare.ginibreOriginalEquilibrium_two_radius_gamma_product`,
  `GinibrePoincare.fullNonQuadraticPotentialTheorem`,
  `GinibrePoincare.bakryEmeryConfigurationGibbs_square_lsi`
Tags: ginibre-ensemble, poincare-inequality, weak-gradients, hermite-polynomials, equality-cases
MSC: 60E15, 60B20, 46E35
-/
