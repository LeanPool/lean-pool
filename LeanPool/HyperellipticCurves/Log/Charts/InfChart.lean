/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansionInf
public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart

import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The infinity-disk pipeline and its chart coordinates (chart coverage)

The analogue of `LeanPool.HyperellipticCurves.Log.Charts.PhiChart`'s disk pipeline for the residue
disk of
the point at infinity. The disk centre is `∞` itself, so the class to expand is `[P_z - ∞] + [τ]` —
no auxiliary point, no pair blocks, and no certificates: one Cantor composition and one reduction
step, both in closed form. The moving point `P_z = (1/û, 1/(ûᵍ·z))` has non-integral
coordinates (`û = ChabautyColeman.infSeries` is the infinity coordinate series, `û(0) = 0`),
so all data are carried in *scaled* integral form:

* the composed square root is `v_check = z·v_c` (`ChabautyColeman.infV`), built from the scaled
  interpolation coefficient `c_hat` (`ChabautyColeman.infC`), integral because
  `1/uτ(1/û) = ûᵍ/(reflect g uτ)(û)` with `(reflect g uτ)(û)` a *unit*;
* the moving factor of the composed `u`-part is the reversed-normalized `1 - û·X` (degree
  drops at `z = 0`: the moving point leaves through infinity, matching `[P_0] = 0`);
* the two defining identities become *reflected* polynomial identities:
  `û^g·v_check(1/û) = 1` (`ChabautyColeman.aeval_reflect_infV`) and
  `û^(2g+1)·(v_check² - z²·f)(1/û) = û - z²·(reverse f)(û) = 0`
  (`ChabautyColeman.aeval_reflect_infV_sq_sub`, by the defining equation of `infSeries`).

From these, the master factorization `v_check² - z²·f = (1 - û·X)·uτ·Q` is obtained by two exact
divisions (the second one reflected, dividing by the monic `X - û`), and the reduced `u`-part
`U = F(û)·Q` (`ChabautyColeman.infU`) is monic of degree `g` with `U(0) = uτ`
(`ChabautyColeman.map_constantCoeff_infU`); its chart coordinates `ζ(z)`
(`ChabautyColeman.infZeta`) are integral with `ζ(0) = 0`. The reduced `v`-part exists after
unscaling by `z` (`ChabautyColeman.exists_infVred`).

Blueprint node: `thm:glue` (infinity chart) / `lem:global-generic` environment.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section InfData

variable {O : Type*} [CommRing O] {f : O[X]} (hf : f.Monic) (uτ vτ : O[X])

/-- The inverse of the reversed `τ`-value `A₁ = (reflect g uτ)(û)` at the infinity
coordinate series `û`; a unit since `A₁(0) = 1` for monic `uτ`. -/
noncomputable def infTauInv : O⟦X⟧ :=
  PowerSeries.invOfUnit (aeval (infSeries hf) uτ.reverse) 1

/-- The scaled interpolation coefficient `c_hat = z·(y - vτ(x))/uτ(x)` of the infinity-disk
composition, in closed integral form. -/
noncomputable def infC : O⟦X⟧ :=
  (1 - PowerSeries.X * infSeries hf * aeval (infSeries hf) (reflect (uτ.natDegree - 1) vτ))
    * infTauInv hf uτ

/-- The scaled composed `v`-polynomial `v_check = z·v_c` of the infinity-disk pipeline:
`v_check = z·vτ + c_hat·uτ`, interpolating (after unscaling) `vτ` on `τ` and the moving point. -/
noncomputable def infV : (O⟦X⟧)[X] :=
  C PowerSeries.X * vτ.map PowerSeries.C + C (infC hf uτ vτ) * uτ.map PowerSeries.C

variable {uτ vτ}

theorem constantCoeff_aeval_infSeries (p : O[X]) :
    PowerSeries.constantCoeff (aeval (infSeries hf) p) = p.coeff 0 := by
  rw [aeval_def, Polynomial.hom_eval₂, constantCoeff_infSeries, eval₂_at_zero]
  change (RingHom.id O) (p.coeff 0) = p.coeff 0
  exact RingHom.id_apply _

theorem aeval_infSeries_reverse_mul_infTauInv (huτ : uτ.Monic) :
    aeval (infSeries hf) uτ.reverse * infTauInv hf uτ = 1 := by
  refine PowerSeries.mul_invOfUnit _ 1 ?_
  rw [constantCoeff_aeval_infSeries, coeff_zero_reverse, huτ.leadingCoeff, Units.val_one]

/-- **The reflected interpolation identity**: `û^g·v_check(1/û) = 1` — the moving point's
interpolation condition in integral form. -/
theorem aeval_reflect_infV (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree) :
    aeval (infSeries hf) (reflect uτ.natDegree (infV hf uτ vτ)) = 1 := by
  have hmap : ∀ p : O[X], aeval (infSeries hf) (p.map PowerSeries.C)
      = aeval (infSeries hf) p := fun p ↦ by
    rw [← PowerSeries.algebraMap_eq, aeval_map_algebraMap]
  set B := aeval (infSeries hf) (reflect (uτ.natDegree - 1) vτ)
  set A := aeval (infSeries hf) uτ.reverse
  have h1 : aeval (infSeries hf) (reflect uτ.natDegree (C PowerSeries.X * vτ.map PowerSeries.C))
      = PowerSeries.X * infSeries hf * B := by
    obtain ⟨g, hg⟩ : ∃ g, uτ.natDegree = g + 1 := ⟨uτ.natDegree - 1, by lia⟩
    rw [reflect_C_mul, show reflect uτ.natDegree (vτ.map PowerSeries.C)
        = X * reflect (uτ.natDegree - 1) (vτ.map PowerSeries.C) by
      rw [hg, Nat.add_sub_cancel]
      exact reflect_succ (le_trans natDegree_map_le (by lia)),
      reflect_map, map_mul, map_mul, aeval_C, aeval_X, hmap]
    change PowerSeries.X * (infSeries hf * B) = _
    ring
  have h2 : aeval (infSeries hf)
        (reflect uτ.natDegree (C (infC hf uτ vτ) * uτ.map PowerSeries.C))
      = infC hf uτ vτ * A := by
    rw [reflect_C_mul, reflect_map, map_mul, aeval_C, hmap]
    change infC hf uτ vτ * aeval (infSeries hf) (reflect uτ.natDegree uτ) = _
    rw [show reflect uτ.natDegree uτ = uτ.reverse from rfl]
  rw [infV, reflect_add, map_add, h1, h2, infC]
  have hAinv : A * infTauInv hf uτ = 1 := aeval_infSeries_reverse_mul_infTauInv hf huτ
  linear_combination (1 - PowerSeries.X * infSeries hf * B) * hAinv

theorem natDegree_infV_le (hvτ : vτ.natDegree ≤ uτ.natDegree) :
    (infV hf uτ vτ).natDegree ≤ uτ.natDegree := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_map_le hvτ)
  · exact le_trans (natDegree_C_mul_le _ _) natDegree_map_le

/-- **The reflected on-curve identity**: `û^(2g+1)·(v_check² - z²·f)(1/û) = û - z²·F(û) = 0`. -/
theorem aeval_reflect_infV_sq_sub (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    aeval (infSeries hf) (reflect (2 * uτ.natDegree + 1)
      (infV hf uτ vτ ^ 2 - C (PowerSeries.X ^ 2) * f.map PowerSeries.C)) = 0 := by
  have hmap : ∀ p : O[X], aeval (infSeries hf) (p.map PowerSeries.C)
      = aeval (infSeries hf) p := fun p ↦ by
    rw [← PowerSeries.algebraMap_eq, aeval_map_algebraMap]
  rw [reflect_sub, reflect_C_mul, map_sub, map_mul, aeval_C]
  have h2 : reflect (2 * uτ.natDegree + 1) (f.map PowerSeries.C)
      = (f.reverse).map PowerSeries.C := by
    rw [reflect_map]
    congr 1
    rw [reverse, hdeg]
  have h1 : reflect (2 * uτ.natDegree + 1) (infV hf uτ vτ ^ 2)
      = X * reflect uτ.natDegree (infV hf uτ vτ) ^ 2 := by
    rw [reflect_succ (le_trans natDegree_pow_le (by lia [natDegree_infV_le hf hvτ.le])),
      sq, sq, two_mul uτ.natDegree,
      reflect_mul _ _ (natDegree_infV_le hf hvτ.le) (natDegree_infV_le hf hvτ.le)]
  rw [h1, h2, hmap, map_mul, aeval_X, map_pow, aeval_reflect_infV hf huτ hvτ, one_pow, mul_one,
    Algebra.algebraMap_self, RingHom.id_apply]
  linear_combination infSeries_eq hf

variable (uτ vτ) in
/-- The cofactor `W = (v_check² - z²·f)/uτ` of the infinity-disk reduction step. -/
noncomputable def infW : (O⟦X⟧)[X] :=
  (infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C) /ₘ uτ.map PowerSeries.C

variable (uτ vτ) in
/-- The un-normalized reduced `u`-part of the infinity-disk pipeline: the second cofactor
in `v_check² - z²·f = (1 - û·X)·uτ·Q`, obtained by reflected division by the moving factor. -/
noncomputable def infQ : (O⟦X⟧)[X] :=
  reflect uτ.natDegree
    ((reflect (uτ.natDegree + 1) (infW hf uτ vτ)) /ₘ (X - C (infSeries hf)))

variable (uτ vτ) in
/-- **The reduced `u`-part of the infinity-disk pipeline**: the monic degree-`g`
representative of `[P_z - ∞] + [τ]`, normalized by the unit `F(û) = (reverse f)(û)`. -/
noncomputable def infU : (O⟦X⟧)[X] :=
  C (aeval (infSeries hf) f.reverse) * infQ hf uτ vτ

/-- Exactness of the first division: `v_check² - z²·f = uτ·W`. -/
theorem infV_sq_sub_eq_infW (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C
      = uτ.map PowerSeries.C * infW hf uτ vτ := by
  obtain ⟨w, hw⟩ := hdvdτ
  have hwm : vτ.map PowerSeries.C ^ 2 - f.map PowerSeries.C
      = uτ.map PowerSeries.C * w.map PowerSeries.C := by
    rw [← Polynomial.map_pow, ← Polynomial.map_sub, hw, Polynomial.map_mul]
  have hdvd : uτ.map PowerSeries.C
      ∣ infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C := by
    refine ⟨C PowerSeries.X ^ 2 * w.map PowerSeries.C
      + 2 * C PowerSeries.X * C (infC hf uτ vτ) * vτ.map PowerSeries.C
      + C (infC hf uτ vτ) ^ 2 * uτ.map PowerSeries.C, ?_⟩
    rw [infV]
    linear_combination (C PowerSeries.X ^ 2 : (O⟦X⟧)[X]) * hwm
  conv_lhs => rw [← modByMonic_add_div
    (infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C) (uτ.map PowerSeries.C)]
  rw [(modByMonic_eq_zero_iff_dvd (huτ.map PowerSeries.C)).mpr hdvd, zero_add, infW]

theorem natDegree_infV_sq_sub_le (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    (infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C).natDegree
      ≤ 2 * uτ.natDegree + 1 := by
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans natDegree_pow_le (by lia [natDegree_infV_le hf hvτ.le])
  · rw [← map_pow]
    exact le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_map_le hdeg.le)

theorem natDegree_infW_le (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    (infW hf uτ vτ).natDegree ≤ uτ.natDegree + 1 := by
  rw [infW, natDegree_divByMonic _ (huτ.map PowerSeries.C),
    natDegree_map_eq_of_injective (PowerSeries.C_injective)]
  lia [natDegree_infV_sq_sub_le hf hvτ hdeg]

/-- **The master factorization** of the infinity-disk reduction:
`v_check² - z²·f = (1 - û·X)·uτ·Q`, an identity in `O⟦z⟧[X]`. -/
theorem infV_sq_sub_factor [IsDomain O] (huτ : uτ.Monic)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C
      = (1 - C (infSeries hf) * X) * uτ.map PowerSeries.C * infQ hf uτ vτ := by
  have hmap : ∀ p : O[X], aeval (infSeries hf) (p.map PowerSeries.C)
      = aeval (infSeries hf) p := fun p ↦ by
    rw [← PowerSeries.algebraMap_eq, aeval_map_algebraMap]
  -- the reflected cofactor has the moving root
  have hfac : reflect (2 * uτ.natDegree + 1)
        (infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C)
      = reflect uτ.natDegree (uτ.map PowerSeries.C)
          * reflect (uτ.natDegree + 1) (infW hf uτ vτ) := by
    rw [infV_sq_sub_eq_infW hf huτ hdvdτ,
      show 2 * uτ.natDegree + 1 = uτ.natDegree + (uτ.natDegree + 1) by lia]
    exact reflect_mul _ _ (le_trans natDegree_map_le le_rfl) (natDegree_infW_le hf huτ hvτ hdeg)
  have hAunit : IsUnit (aeval (infSeries hf) uτ.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨_, aeval_infSeries_reverse_mul_infTauInv hf huτ⟩
  have hroot : aeval (infSeries hf) (reflect (uτ.natDegree + 1) (infW hf uτ vτ)) = 0 := by
    have h0 := aeval_reflect_infV_sq_sub hf huτ hvτ hdeg
    rw [show C PowerSeries.X ^ 2 = C (PowerSeries.X ^ 2 : O⟦X⟧) by rw [map_pow]] at hfac
    rw [hfac, map_mul, reflect_map, hmap,
      show reflect uτ.natDegree uτ = uτ.reverse from rfl] at h0
    exact (hAunit.mul_right_eq_zero).mp h0
  -- exact division by the reflected moving factor
  have hWrev : reflect (uτ.natDegree + 1) (infW hf uτ vτ)
      = (X - C (infSeries hf))
          * ((reflect (uτ.natDegree + 1) (infW hf uτ vτ)) /ₘ (X - C (infSeries hf))) :=
    (mul_divByMonic_eq_iff_isRoot.mpr (by
      rw [IsRoot, ← eval₂_id, ← Algebra.algebraMap_self (R := O⟦X⟧), ← aeval_def, hroot])).symm
  -- unreflect
  have hW : infW hf uτ vτ = (1 - C (infSeries hf) * X) * infQ hf uτ vτ := by
    have h1 := congrArg (reflect (uτ.natDegree + 1)) hWrev
    rw [reflect_reflect] at h1
    have hXdeg : (X - C (infSeries hf) : (O⟦X⟧)[X]).natDegree ≤ 1 := (natDegree_X_sub_C _).le
    have hQdeg : ((reflect (uτ.natDegree + 1) (infW hf uτ vτ))
        /ₘ (X - C (infSeries hf))).natDegree ≤ uτ.natDegree := by
      rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
      have h2 : (reflect (uτ.natDegree + 1) (infW hf uτ vτ)).natDegree
          ≤ max (uτ.natDegree + 1) (infW hf uτ vτ).natDegree := natDegree_reflect_le
      lia [le_trans h2 (max_le le_rfl (natDegree_infW_le hf huτ hvτ hdeg))]
    have h1' : infW hf uτ vτ = reflect (1 + uτ.natDegree) ((X - C (infSeries hf))
        * (reflect (uτ.natDegree + 1) (infW hf uτ vτ) /ₘ (X - C (infSeries hf)))) := by
      rwa [add_comm 1 uτ.natDegree]
    rw [h1', reflect_mul _ _ hXdeg hQdeg, infQ]
    congr 1
    rw [reflect_sub, reflect_C, pow_one, show (X : (O⟦X⟧)[X]) = X ^ 1 from (pow_one _).symm,
      reflect_monomial, show revAt 1 1 = 0 by rw [revAt_le le_rfl], pow_zero]
  rw [infV_sq_sub_eq_infW hf huτ hdvdτ, hW]
  ring

section Domain

variable [IsDomain O]

theorem infSeries_ne_zero : infSeries hf ≠ 0 := by
  intro h0
  have h := infSeries_eq hf
  rw [h0, aeval_def, eval₂_at_zero, coeff_zero_reverse, hf.leadingCoeff, map_one,
    mul_one] at h
  exact pow_ne_zero 2 PowerSeries.X_ne_zero h.symm

/-- The leading structure of the un-normalized reduced `u`-part: its degree is `g` and its
leading coefficient is inverse to the unit `F(û)`. -/
theorem infQ_leadingCoeff_natDegree (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    aeval (infSeries hf) f.reverse * (infQ hf uτ vτ).leadingCoeff = 1
      ∧ (infQ hf uτ vτ).natDegree = uτ.natDegree := by
  set L := infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C with hL
  -- the top coefficient of the left side is `-z²`
  have hcoeff : L.coeff (2 * uτ.natDegree + 1) = -(PowerSeries.X ^ 2) := by
    rw [hL, coeff_sub, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt natDegree_pow_le
      (by lia [natDegree_infV_le hf hvτ.le])), ← map_pow, coeff_C_mul, coeff_map,
      ← hdeg, hf.coeff_natDegree, map_one, mul_one, zero_sub]
  have hX2 : (PowerSeries.X : O⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 PowerSeries.X_ne_zero
  have hLdeg : L.natDegree = 2 * uτ.natDegree + 1 :=
    le_antisymm (natDegree_infV_sq_sub_le hf hvτ hdeg)
      (le_natDegree_of_ne_zero (by rw [hcoeff]; exact neg_ne_zero.mpr hX2))
  have hLne : L ≠ 0 := fun h0 ↦ by
    rw [h0] at hcoeff
    exact hX2 (neg_eq_zero.mp hcoeff.symm)
  -- the moving factor has degree `1` with leading coefficient `-û`
  have hune : infSeries hf ≠ 0 := infSeries_ne_zero hf
  have hMeq : (1 - C (infSeries hf) * X : (O⟦X⟧)[X]) = C (-infSeries hf) * X + C 1 := by
    rw [map_neg, C_1]; ring
  have hMdeg : (1 - C (infSeries hf) * X : (O⟦X⟧)[X]).natDegree = 1 := by
    rw [hMeq, natDegree_linear (neg_ne_zero.mpr hune)]
  have hMlc : (1 - C (infSeries hf) * X : (O⟦X⟧)[X]).leadingCoeff = -infSeries hf := by
    rw [hMeq, leadingCoeff_linear (neg_ne_zero.mpr hune)]
  have hMne : (1 - C (infSeries hf) * X : (O⟦X⟧)[X]) ≠ 0 := fun h0 ↦ by
    simp [h0] at hMdeg
  -- factor degrees and leading coefficients over the domain
  have hfac := infV_sq_sub_factor hf huτ hvτ hdeg hdvdτ
  have hQne : infQ hf uτ vτ ≠ 0 := fun h0 ↦ hLne (by rw [hL, hfac, h0, mul_zero])
  have hdegs := congrArg natDegree hfac
  rw [← hL, hLdeg, natDegree_mul (mul_ne_zero hMne (huτ.map _).ne_zero) hQne,
    natDegree_mul hMne (huτ.map _).ne_zero, hMdeg,
    natDegree_map_eq_of_injective PowerSeries.C_injective] at hdegs
  have hQdeg : (infQ hf uτ vτ).natDegree = uτ.natDegree := by lia
  have hlcs := congrArg leadingCoeff hfac
  rw [← hL, leadingCoeff, hLdeg, hcoeff, leadingCoeff_mul, leadingCoeff_mul, hMlc,
    (huτ.map (PowerSeries.C : O →+* O⟦X⟧)).leadingCoeff, mul_one] at hlcs
  -- cancel `z²` against `û = z²·F(û)`
  have hcancel : PowerSeries.X ^ 2
      * (aeval (infSeries hf) f.reverse * (infQ hf uτ vτ).leadingCoeff - 1) = 0 := by
    have hu := infSeries_eq hf
    linear_combination hlcs - (infQ hf uτ vτ).leadingCoeff * hu
  refine ⟨sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hX2), hQdeg⟩

/-- **The reduced `u`-part is monic of degree `g`.** -/
theorem infU_monic (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    (infU hf uτ vτ).Monic := by
  have hlc := (infQ_leadingCoeff_natDegree hf huτ hvτ hdeg hdvdτ).1
  rw [Monic, infU, leadingCoeff_mul, leadingCoeff_C, hlc]

theorem natDegree_infU (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    (infU hf uτ vτ).natDegree = uτ.natDegree := by
  obtain ⟨hlc, hQdeg⟩ := infQ_leadingCoeff_natDegree hf huτ hvτ hdeg hdvdτ
  have hD : aeval (infSeries hf) f.reverse ≠ 0 := fun h0 ↦ by
    rw [h0, zero_mul] at hlc
    exact zero_ne_one hlc
  rw [infU, natDegree_C_mul hD, hQdeg]

end Domain

section CenterZero

@[simp] theorem constantCoeff_infC :
    PowerSeries.constantCoeff (infC hf uτ vτ) = 1 := by
  rw [infC, map_mul, map_sub, map_one, map_mul, map_mul, PowerSeries.constantCoeff_X,
    zero_mul, zero_mul, sub_zero, one_mul, infTauInv, PowerSeries.constantCoeff_invOfUnit,
    inv_one, Units.val_one]

/-- At `z = 0` the scaled composed `v`-polynomial degenerates to the centre: `v_check(0) = uτ`. -/
theorem map_constantCoeff_infV :
    (infV hf uτ vτ).map (PowerSeries.constantCoeff (R := O)) = uτ := by
  rw [infV, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C,
    PowerSeries.constantCoeff_X, C_0, zero_mul, Polynomial.map_map,
    PowerSeries.constantCoeff_comp_C, map_id,
    constantCoeff_infC hf, C_1, one_mul, zero_add]

/-- **The centre of the infinity-disk pipeline is the `τ`-datum**: at `z = 0` the reduced
`u`-part returns `uτ` exactly (the moving point has left through infinity). -/
theorem map_constantCoeff_infU [IsDomain O] (huτ : uτ.Monic)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    (infU hf uτ vτ).map (PowerSeries.constantCoeff (R := O)) = uτ := by
  have h := congrArg (Polynomial.map (PowerSeries.constantCoeff (R := O)))
    (infV_sq_sub_factor hf huτ hvτ hdeg hdvdτ)
  rw [Polynomial.map_sub, Polynomial.map_pow, map_constantCoeff_infV hf, Polynomial.map_mul,
    Polynomial.map_pow, map_C, PowerSeries.constantCoeff_X, C_0, zero_pow two_ne_zero,
    zero_mul, sub_zero, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_mul, map_C, constantCoeff_infSeries, C_0, zero_mul,
    sub_zero, one_mul, Polynomial.map_map, PowerSeries.constantCoeff_comp_C, map_id] at h
  have hQ : (infQ hf uτ vτ).map (PowerSeries.constantCoeff (R := O)) = uτ :=
    mul_left_cancel₀ huτ.ne_zero (by rw [← h]; ring)
  rw [infU, Polynomial.map_mul, map_C, constantCoeff_aeval_infSeries, coeff_zero_reverse,
    hf.leadingCoeff, C_1, one_mul, hQ]

variable (uτ vτ) in
/-- **The infinity-disk chart coordinates `ζ(z)`**: the coefficients of the perturbation of
the reduced `u`-part relative to the `τ`-centre. -/
noncomputable def infZeta (j : Fin uτ.natDegree) : O⟦X⟧ :=
  chartCoords PowerSeries.C uτ (infU hf uτ vτ) j

theorem constantCoeff_infZeta [IsDomain O] (huτ : uτ.Monic)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hdvdτ : uτ ∣ vτ ^ 2 - f) (j : Fin uτ.natDegree) :
    PowerSeries.constantCoeff (infZeta hf uτ vτ j) = 0 := by
  rw [infZeta, map_chartCoords, PowerSeries.constantCoeff_comp_C,
    map_constantCoeff_infU hf huτ hvτ hdeg hdvdτ,
    chartCoords, Polynomial.map_id, sub_self, coeff_zero]

end CenterZero

section Vpart

variable [IsDomain O]

/-- The reduced `u`-part divides the scaled on-curve expression. -/
theorem infU_dvd (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    infU hf uτ vτ ∣ infV hf uτ vτ ^ 2 - C PowerSeries.X ^ 2 * f.map PowerSeries.C := by
  obtain ⟨hlc, -⟩ := infQ_leadingCoeff_natDegree hf huτ hvτ hdeg hdvdτ
  have hDunit : IsUnit (C (aeval (infSeries hf) f.reverse) : (O⟦X⟧)[X]) :=
    isUnit_C.mpr (isUnit_iff_exists_inv.mpr ⟨_, hlc⟩)
  obtain ⟨E, hE⟩ := hDunit.exists_left_inv
  refine ⟨E * ((1 - C (infSeries hf) * X) * uτ.map PowerSeries.C), ?_⟩
  rw [infV_sq_sub_factor hf huτ hvτ hdeg hdvdτ, infU]
  linear_combination ((1 - C (infSeries hf) * X) * uτ.map PowerSeries.C
    * infQ hf uτ vτ) * hE.symm

/-- **Existence of the reduced `v`-part**: the scaled remainder `v_check mod U` is divisible by
`z`, and its unscaled negative `V` completes `(U, V)` to a reduced Mumford datum. -/
theorem exists_infVred (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f) :
    ∃ V : (O⟦X⟧)[X], C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ)
      ∧ V.degree < (infU hf uτ vτ).degree
      ∧ infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C := by
  have hUm : (infU hf uτ vτ).Monic := infU_monic hf huτ hvτ hdeg hdvdτ
  -- the remainder is divisible by `z`
  have hmod0 : (infV hf uτ vτ %ₘ infU hf uτ vτ).map (PowerSeries.constantCoeff (R := O))
      = 0 := by
    rw [map_modByMonic _ hUm, map_constantCoeff_infV hf,
      map_constantCoeff_infU hf huτ hvτ hdeg hdvdτ, modByMonic_self huτ]
  obtain ⟨V', hV'⟩ : (C PowerSeries.X : (O⟦X⟧)[X]) ∣ infV hf uτ vτ %ₘ infU hf uτ vτ := by
    refine (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ PowerSeries.X_dvd_iff.mpr ?_
    simpa [coeff_map] using congrArg (fun p ↦ Polynomial.coeff p i) hmod0
  refine ⟨-V', by rw [hV']; ring, ?_, ?_⟩
  · rw [degree_neg]
    rcases eq_or_ne V' 0 with rfl | hne
    · rw [degree_zero]
      exact bot_lt_iff_ne_bot.mpr (mt degree_eq_bot.mp hUm.ne_zero)
    · have hd := degree_modByMonic_lt (infV hf uτ vτ) hUm
      rwa [hV', degree_mul, degree_C (PowerSeries.X_ne_zero (R := O)), zero_add] at hd
  · -- `z²·(V² - f) ≡ v_check² - z²·f ≡ 0 mod U`, then cancel `z²`
    have hcong : infU hf uτ vτ ∣ C (PowerSeries.X ^ 2 : O⟦X⟧) * ((-V') ^ 2
        - f.map PowerSeries.C) := by
      have h1 : infV hf uτ vτ - infV hf uτ vτ %ₘ infU hf uτ vτ
          = infU hf uτ vτ * (infV hf uτ vτ /ₘ infU hf uτ vτ) := by
        linear_combination -modByMonic_add_div (infV hf uτ vτ) (infU hf uτ vτ)
      have h2 := infU_dvd hf huτ hvτ hdeg hdvdτ
      obtain ⟨q₂, hq₂⟩ := h2
      refine ⟨q₂ - (infV hf uτ vτ + infV hf uτ vτ %ₘ infU hf uτ vτ)
        * (infV hf uτ vτ /ₘ infU hf uτ vτ), ?_⟩
      have hsq : (C PowerSeries.X * -V') ^ 2 = (infV hf uτ vτ %ₘ infU hf uτ vτ) ^ 2 := by
        rw [hV']
        ring
      rw [map_pow]
      linear_combination hsq + hq₂ - (infV hf uτ vτ + infV hf uτ vτ %ₘ infU hf uτ vτ) * h1
    exact Monic.dvd_of_C_mul_dvd hUm (pow_ne_zero 2 PowerSeries.X_ne_zero) hcong

end Vpart

end InfData

end ChabautyColeman
