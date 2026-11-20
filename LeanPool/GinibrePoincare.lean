/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

module

public import LeanPool.GinibrePoincare.Endgame.FullPaper

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
  `GinibrePoincare.bakryEmeryConfigurationGibbs_square_lsi`,
  `GinibrePoincare.fullTheoremOneNinePointwiseGamma`,
  `GinibrePoincare.correspondence_poincare_iff_integrated_pointwise_curvature`,
  `GinibrePoincare.spectral_ginibre_full_generator_spectrum_support`,
  `GinibrePoincare.correspondence_ginibre_global_independent_CIR_equations`,
  `GinibrePoincare.correspondence_ginibre_continuous_strongMarkov`,
  `GinibrePoincare.correspondenceOperatorEvolution_ergodic`,
  `GinibrePoincare.correspondenceFriedrichsSquareRoot_domain_ordinary_H1`,
  `GinibrePoincare.correspondenceOperatorNumber_spectrum_iff`,
  `GinibrePoincare.correspondenceBrascampLieb_weak_probability_variance`,
  `GinibrePoincare.gueFull_C1_H1_inequalities`, `GinibrePoincare.localDolbeault_locallyL2`,
  `GinibrePoincare.positiveWeightEntire_tendstoLocallyUniformly`,
  `GinibrePoincare.gaussian_tensor_mixed_monomial_gramSchmidt`,
  `GinibrePoincare.gaussianGapEqualitySpace_real_analytic_representative`
Tags: ginibre-ensemble, poincare-inequality, weak-gradients, hermite-polynomials, equality-cases
MSC: 60E15, 60B20, 46E35
-/
