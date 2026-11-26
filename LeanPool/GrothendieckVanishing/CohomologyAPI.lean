/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import LeanPool.GrothendieckVanishing.ClosedImmersion
public import LeanPool.GrothendieckVanishing.CohomologyCalculus
public import LeanPool.GrothendieckVanishing.CohomologyVanishing

/-!
# Sheaf Cohomology API

Centralizes results about sheaf cohomology `Sheaf.H`, keeping the underlying `Ext`
calculations internal so downstream files never need to unfold `Sheaf.H` directly.

## Main results

* `subsingleton_sheafH_of_shortExact_middle`: middle-term cohomology vanishing
* `sheafH_subsingleton_of_isEmpty`: empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero`: bundled zero-sheaf vanishing
* `stalk_zero_of_ses_g_iso`: stalk vanishing from SES with iso on `g`
* `stalk_zero_of_shortExact_kernel`: stalk vanishing from SES kernel
* `stalk_zero_of_g_is_cokernel_of_stalk_epi`: sheaf-level stalk
  vanishing from a cokernel and stalk-epi hypothesis
* `cokernel_stalk_zero_of_stalk_surj`: actual-cokernel specialization of the same stalk
  vanishing under stalk-surjectivity
* `sheafHSuccMap`: successor connecting morphism
* `sheafH_succ_map_exists_preimage_of_subsingleton_middle`: successor-map
  preimage wrapper
* `sheafH0EquivSections`: sheaf-level wrapper for `H^0(F) ≃+ F(⊤)`
* `sheafH0EquivSections_natural`: sheaf-level naturality of the above
* `sheafH1CokernelIsoOfSubsingletonMiddle`: sheaf-level form of the
  `H¹` cokernel identification
* `sheafH1_cokernel_iso_of_subsingleton_middle_natural`: sheaf-level
  naturality for the same `H¹` cokernel identification
* `sheafHSuccIsoOfSubsingletonMiddle`: sheaf-level form of the
  higher-degree connecting isomorphism
* `sheafH_succ_iso_of_subsingleton_middle_natural`: sheaf-level
  naturality for the same connecting isomorphism
* `sheafH0_surj_of_epi_app_top`: sheaf-level surjectivity on top sections
  gives H^0 surjectivity
* `sheafH_subsingleton_H1_via_surj`: sheaf-level H^1 vanishing via
  H^0-surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top`: sheaf-level H^1 vanishing via
  surjective top sections
* `sheafH_subsingleton_of_injective`: positive-degree cohomology of an injective sheaf
  is subsingleton
* `sheafH_subsingleton_H1_of_injective_of_epi_app_top`: sheaf-level
  injective-middle-term `H¹` vanishing
* `sheafH_dimension_shift_of_both`: sheaf-level forward dimension shift
  for short exact sequences
* `sheafH_dimension_shift_of_mono`: forward dimension shift for a monomorphism
* `sheafH_dimension_shift_of_injective`: forward dimension shift with injective middle term
* `sheafH_dimension_shift_X₃_of_locallySurjective`: reverse dimension shift for locally
  surjective morphisms
-/
