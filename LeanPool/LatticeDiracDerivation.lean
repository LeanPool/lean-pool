/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac030

/-!
# Cubical lattice Dirac factorization and its continuum limit

Source: doi:10.5281/zenodo.24150001, url:https://github.com/gpartin/LeanDiracDerivation/tree/867004142ada3eec464d5bd3088d7313fdad1613
Authors: G. D. Partin
Status: verified
Main declarations: `LeanDirac.restricted_action_variation_is_native_variation`,
  `LeanDirac.native_prepared_modal_potential_expansion`,
  `LeanDirac.native_psi_tangent_symbol_is_exact_scalar_coefficient`,
  `LeanDirac.c19_spatial_remainder_bound`,
  `LeanDirac.standard_c19_hamiltonian_square_is_continuum_dispersion`,
  `LeanDirac.interpreted_hamiltonian_intertwines_minus`,
  `LeanDirac.interpreted_hamiltonian_intertwines_plus`,
  `LeanDirac.native_branch_defect_is_spatial_remainder`,
  `LeanDirac.recurrence_branch_generator_defect_tends_to_zero`,
  `LeanDirac.native_tangent_local_continuity`,
  `LeanDirac.native_cell4_flux_continuum_limit_is_dirac_current`,
  `LeanDirac.normalized_finite_fourier_basis_orthonormal`,
  `LeanDirac.exists_unique_admissible_spin_scale`, `LeanDirac.cube_spin_casimir`,
  `LeanDirac.cube_continuous_turn_two_pi`, `LeanDirac.admissible_two_copy_native_root_is_canonical`,
  `LeanDirac.c19_first_brillouin_zone_zero_unique`, `LeanDirac.pauli_lubanski_mass_shell_spin_half`,
  `LeanDirac.gordon_current_decomposition`
Tags: mathematical-physics, dirac-operator, clifford-algebra, lattice, klein-gordon
MSC: 81Q05, 15A66, 65M06, 81R20
-/
