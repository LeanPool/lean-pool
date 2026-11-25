/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.SophieGermainArchives.Algebra.BigOperators.Naf4073PowerSums
public import LeanPool.SophieGermainArchives.Exercises
public import LeanPool.SophieGermainArchives.Fr9118
public import LeanPool.SophieGermainArchives.Geometry.Fr9115Curvature
public import LeanPool.SophieGermainArchives.Mechanics.Fr9115Elasticity
public import LeanPool.SophieGermainArchives.NumberTheory.Fr9115Arithmetic
public import LeanPool.SophieGermainArchives.NumberTheory.Naf4073Gersonides
public import LeanPool.SophieGermainArchives.NumberTheory.Naf4073Note
public import LeanPool.SophieGermainArchives.NumberTheory.Naf4073Triangular

/-!
# Statements read in Sophie Germain's manuscripts

Source: url:https://gallica.bnf.fr/ark:/12148/btv1b90724875
Authors: Michel Hua
Status: verified
Main declarations: `LeanPool.SophieGermainArchives.Naf4073.triangular_of_square`,
  `LeanPool.SophieGermainArchives.Naf4073.lagrange_unique`,
  `LeanPool.SophieGermainArchives.Fr9115Arithmetic.manuscriptC_odd`,
  `LeanPool.SophieGermainArchives.Fr9115Arithmetic.dvd_n_of_dvd_both`,
  `LeanPool.SophieGermainArchives.Fr9115Arithmetic.exists_prime_nonresidue`,
  `LeanPool.SophieGermainArchives.Fr9115Arithmetic.three_primitive_root`,
  `LeanPool.SophieGermainArchives.Fr9115Arithmetic.fermat_primitive_root`,
  `LeanPool.SophieGermainArchives.Fr9118.generalisation`,
  `LeanPool.SophieGermainArchives.Fr9118.p4_add_four_prime_iff`,
  `LeanPool.SophieGermainArchives.Fr9115Elasticity.exists_mode_iff`,
  `LeanPool.SophieGermainArchives.Fr9115Elasticity.first_root_free_free`,
  `LeanPool.SophieGermainArchives.Fr9115Elasticity.second_family_is_mode`,
  `LeanPool.SophieGermainArchives.Fr9115Elasticity.free_stylet_iff`,
  `LeanPool.SophieGermainArchives.Fr9115Curvature.euler_principal`,
  `LeanPool.SophieGermainArchives.Fr9115Curvature.integral_kappa`
Tags: sophie-germain, history-of-mathematics, quadratic-residues, triangular-numbers, elasticity
MSC: 11A15, 11D41, 11B83, 74K20, 74H45, 53A05, 01A50
-/
