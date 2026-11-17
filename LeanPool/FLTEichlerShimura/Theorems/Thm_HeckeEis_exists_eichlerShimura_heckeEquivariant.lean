/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_HeckeEis_BinaryFormRep
public import LeanPool.FLTEichlerShimura.Definitions.Def_Gamma0CoeffCohomology
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularForm_HeckeOperatorForms

import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime
import LeanPool.FLTEichlerShimura.Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj

/-!
# Eichler–Shimura decomposition with Hecke operators at every prime

For every nonzero level and weight at least two, the holomorphic and antiholomorphic
Eichler–Shimura maps are injective and have complementary images in parabolic cohomology.
The cohomological Hecke operators are supplied, together with their action on arbitrary
parabolic cocycle representatives. Both maps intertwine these operators with `T_ℓ` away
from the level and `U_ℓ` at primes dividing the level.

This combines the FLT decomposition theorem with general Hecke descent and the intertwining
identity for binary-form coefficients; no descent hypothesis is required from the caller.
-/

public section publicSection

open scoped MatrixGroups
open CongruenceSubgroup

namespace HeckeEis

/-- The Eichler–Shimura decomposition, with descended Hecke operators and compatibility
at every prime, including primes dividing the level. -/
theorem exists_eichlerShimura_heckeEquivariant (N : ℕ) [NeZero N] (n : ℕ) :
    ∃ (ES : CuspForm (Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ]
          coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
      (ESbar : CuspForm (Gamma0 N) ((n : ℤ) + 2) →ₛₗ[starRingEnd ℂ]
          coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))
      (T : (ℓ : ℕ) → ℓ.Prime →
        coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) →ₗ[ℂ]
          coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
      Function.Injective ES ∧ Function.Injective ESbar ∧
      IsCompl (LinearMap.range ES) (LinearMap.range ESbar) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
        (z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype))),
        ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
          letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          (w : Gamma0 N → ↥(BinaryForm ℂ n)) =
              coeffHeckeFun N ℓ ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)
                (binaryFormAlphaAdj ℂ n ℓ) z ∧
            T ℓ hℓ (coeffH1parMk _ z) = coeffH1parMk _ w) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        (∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2),
          T ℓ hℓ (ES f) = ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f)) ∧
        (∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2),
          T ℓ hℓ (ESbar f) = ESbar (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f))) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N),
        (∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2),
          T ℓ hℓ (ES f) = ES (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f)) ∧
        (∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2),
          T ℓ hℓ (ESbar f) = ESbar (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f))) := by
  classical
  obtain ⟨ES, ESbar, hinj, hinjbar, hcompl, hgood, hbad⟩ :=
    exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime N n
  have descent := fun (ℓ : ℕ) (hℓ : ℓ.Prime) =>
    letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exists_coeffH1par_linearMap_coeffHeckeFun N ℓ
      ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj ℂ n ℓ)
      (binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ)
  choose T hT using descent
  refine ⟨ES, ESbar, T, hinj, hinjbar, hcompl, hT, ?_, ?_⟩
  · intro ℓ hℓ hℓN
    exact hgood ℓ hℓ hℓN (T ℓ hℓ) (hT ℓ hℓ)
  · intro ℓ hℓ hℓN
    exact hbad ℓ hℓ hℓN (T ℓ hℓ) (hT ℓ hℓ)

end HeckeEis

end publicSection
