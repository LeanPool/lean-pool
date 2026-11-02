/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DisplacementScale
public import Mathlib.Data.Int.Log

/-!
# AuxiliaryScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The auxiliary scale of the displacement tail bound

The tail bound on the displacement compares the maximal scale `m` with an
auxiliary scale `n`, chosen so that `3^n` straddles

`max{ν t / (δ 3^m), (c⋆ γ^{-1})^{1/2} (t / (δ 3^m))^{1/(1-γ)}}`,

and the chains-of-good-cubes estimate is then applied at that `n`.  Its
hypothesis `n ≤ m - Y_m(ε)` is exactly what the minimal-scale condition

`min{3^{2m} / (ν t), (c⋆^{-1} γ)^{1/2} ((3^m)^{2-γ} / t)^{1/(1-γ)}} ≥ S_m`

delivers, through the definition `S_m = δ^{-1/(1-γ)} 3^{Y_m(ε)}`.

The two halves of the comparison behave differently.  On the first term the
powers of `δ` do not cancel and the argument uses `δ ≤ 1`: what is left over is
`δ^{1 - 1/(1-γ)} ≥ 1`, an inequality that fails for `δ > 1`.  On the second term
every factor cancels exactly — the powers of `c⋆` and `γ` because the two
expressions are reciprocal, the powers of `δ` because the exponent `1/(1-γ)` is
the same on both sides, and the powers of three because
`((3^m)^{1-γ})^{1/(1-γ)} = 3^m`.  This is the bookkeeping that fixes the exponent
`-1/(1-γ)` of `δ` in `S_m`.

## Main definitions

* `auxiliaryScaleBound nu cstar gamma delta t m` — the quantity `3^n` straddles.
* `displacementMinScale nu cstar gamma t m` — the left side of the minimal-scale
  condition.

## References

* ABK26, the displacement tail bound of Section 5.3.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3

noncomputable section

/-! ## 1. The two quantities -/

/-- **The quantity the auxiliary scale straddles**,
`max{ν t / (δ 3^m), (c⋆ γ^{-1})^{1/2} (t / (δ 3^m))^{1/(1-γ)}}`. -/
def auxiliaryScaleBound (nu cstar gamma delta t : ℝ) (m : ℤ) : ℝ :=
  max (nu * t / (delta * (3 : ℝ) ^ m))
    ((cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * (t / (delta * (3 : ℝ) ^ m)) ^ (1 - gamma)⁻¹)

/-- **The left side of the minimal-scale condition**,
`min{3^{2m} / (ν t), (c⋆^{-1} γ)^{1/2} ((3^m)^{2-γ} / t)^{1/(1-γ)}}`. -/
def displacementMinScale (nu cstar gamma t : ℝ) (m : ℤ) : ℝ :=
  min ((3 : ℝ) ^ (2 * m) / (nu * t))
    ((cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
      (((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹)

theorem auxiliaryScaleBound_pos {nu cstar gamma delta t : ℝ} (hnu : 0 < nu)
    (hdelta : 0 < delta) (ht : 0 < t) (m : ℤ) :
    0 < auxiliaryScaleBound nu cstar gamma delta t m := by
  have hX : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

/-! ## 2. The choice of the auxiliary scale -/

/-- **Every positive quantity is straddled by two consecutive powers of three.**
The base-three integer logarithm is such a scale, which is the choice the
displacement tail bound makes. -/
theorem exists_auxiliaryScale {v : ℝ} (hv : 0 < v) :
    ∃ n : ℤ, (3 : ℝ) ^ n ≤ v ∧ v < (3 : ℝ) ^ (n + 1) := by
  refine ⟨Int.log 3 v, ?_, ?_⟩
  · simpa using Int.zpow_log_le_self (b := 3) (r := v) (by norm_num) hv
  · simpa using Int.lt_zpow_succ_log_self (b := 3) (by norm_num) v

/-! ## 3. The comparison with the scale of the chains estimate -/

section Comparison

variable {nu cstar gamma delta t : ℝ} {m : ℤ} {N : ℕ}

/-- The first term of the maximum, where the powers of `δ` leave `δ^{1-1/(1-γ)}`
behind.  This is the half that uses `δ ≤ 1`. -/
private theorem firstTerm_le (hnu : 0 < nu) (ht : 0 < t) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hmin : displacementScale delta gamma N ≤ (3 : ℝ) ^ (2 * m) / (nu * t)) :
    nu * t / (delta * (3 : ℝ) ^ m) ≤ (3 : ℝ) ^ (m - (N : ℤ)) := by
  have h1g : (0 : ℝ) < 1 - gamma := by linarith only [hgamma1]
  have hX : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hT : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hnut : 0 < nu * t := mul_pos hnu ht
  have hS : 0 < displacementScale delta gamma N := displacementScale_pos hdelta gamma N
  -- the two rewritings of powers of three
  have hsq : (3 : ℝ) ^ (2 * m) = (3 : ℝ) ^ m * (3 : ℝ) ^ m := by
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hdiff : (3 : ℝ) ^ (m - (N : ℤ)) = (3 : ℝ) ^ m / (3 : ℝ) ^ N := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  -- `3^N ≤ delta * S`, the only place `delta ≤ 1` is used
  have hexp : (1 : ℝ) - (1 - gamma)⁻¹ ≤ 0 := by
    have hge : (1 : ℝ) ≤ (1 - gamma)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) h1g]
      linarith only [hgamma]
    linarith only [hge]
  have hdpow : (1 : ℝ) ≤ delta ^ ((1 : ℝ) - (1 - gamma)⁻¹) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1 hexp
  have hdmul : delta * delta ^ (-(1 - gamma)⁻¹) = delta ^ ((1 : ℝ) - (1 - gamma)⁻¹) := by
    rw [show (1 : ℝ) - (1 - gamma)⁻¹ = 1 + -(1 - gamma)⁻¹ by ring,
      Real.rpow_add hdelta, Real.rpow_one]
  have hTle : (3 : ℝ) ^ N ≤ delta * displacementScale delta gamma N := by
    have hrw : delta * displacementScale delta gamma N =
        delta ^ ((1 : ℝ) - (1 - gamma)⁻¹) * (3 : ℝ) ^ N := by
      rw [displacementScale, ← mul_assoc, hdmul]
    rw [hrw]
    calc (3 : ℝ) ^ N = 1 * (3 : ℝ) ^ N := (one_mul _).symm
      _ ≤ delta ^ ((1 : ℝ) - (1 - gamma)⁻¹) * (3 : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right hdpow hT.le
  -- `S * (nu t) ≤ 3^{2m}`
  have hSnut : displacementScale delta gamma N * (nu * t) ≤ (3 : ℝ) ^ m * (3 : ℝ) ^ m := by
    have hmul := mul_le_mul_of_nonneg_right hmin hnut.le
    rw [div_mul_cancel₀ _ hnut.ne', hsq] at hmul
    exact hmul
  rw [hdiff, div_le_div_iff₀ (by positivity) hT]
  calc nu * t * (3 : ℝ) ^ N
      ≤ nu * t * (delta * displacementScale delta gamma N) :=
        mul_le_mul_of_nonneg_left hTle hnut.le
    _ = delta * (displacementScale delta gamma N * (nu * t)) := by ring
    _ ≤ delta * ((3 : ℝ) ^ m * (3 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left hSnut hdelta.le
    _ = (3 : ℝ) ^ m * (delta * (3 : ℝ) ^ m) := by ring

/-- The second term of the maximum, where every factor cancels exactly: the
powers of `c⋆` and `γ` because the two expressions are reciprocal, the powers of
`δ` because both carry the exponent `1/(1-γ)`, and the powers of three because
`((3^m)^{1-γ})^{1/(1-γ)} = 3^m`. -/
private theorem secondTerm_le (ht : 0 < t) (hdelta : 0 < delta) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hmin : displacementScale delta gamma N ≤ (cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) *
      (((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹) :
    (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * (t / (delta * (3 : ℝ) ^ m)) ^ (1 - gamma)⁻¹ ≤
      (3 : ℝ) ^ (m - (N : ℤ)) := by
  have h1g : (0 : ℝ) < 1 - gamma := by linarith only [hgamma1]
  have hX : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hT : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hd : (0 : ℝ) < delta ^ (-(1 - gamma)⁻¹) := Real.rpow_pos_of_pos hdelta _
  have hA : (0 : ℝ) < (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpow : (0 : ℝ) < ((3 : ℝ) ^ m) ^ (2 - gamma) := Real.rpow_pos_of_pos hX _
  have hP : (0 : ℝ) < (((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  -- the reciprocal pair of constants
  have hAinv : (cstar⁻¹ * gamma) ^ (1 / 2 : ℝ) = ((cstar * gamma⁻¹) ^ (1 / 2 : ℝ))⁻¹ := by
    have hrec : cstar⁻¹ * gamma = (cstar * gamma⁻¹)⁻¹ := by
      field_simp
    rw [hrec, Real.inv_rpow (by positivity)]
  -- the factorization of the power of the ratio
  have hsplit : (t / (delta * (3 : ℝ) ^ m)) ^ (1 - gamma)⁻¹ =
      ((((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹)⁻¹ *
        ((3 : ℝ) ^ m * delta ^ (-(1 - gamma)⁻¹)) := by
    have hprod : t / (delta * (3 : ℝ) ^ m) =
        t / ((3 : ℝ) ^ m) ^ (2 - gamma) *
          (((3 : ℝ) ^ m) ^ (2 - gamma) / (delta * (3 : ℝ) ^ m)) := by
      field_simp
    have hfirst : (t / ((3 : ℝ) ^ m) ^ (2 - gamma)) ^ (1 - gamma)⁻¹ =
        ((((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹)⁻¹ := by
      rw [← Real.inv_rpow (by positivity), inv_div]
    have hsecond : (((3 : ℝ) ^ m) ^ (2 - gamma) / (delta * (3 : ℝ) ^ m)) ^ (1 - gamma)⁻¹ =
        (3 : ℝ) ^ m * delta ^ (-(1 - gamma)⁻¹) := by
      have hbase : ((3 : ℝ) ^ m) ^ (2 - gamma) / (delta * (3 : ℝ) ^ m) =
          ((3 : ℝ) ^ m) ^ (1 - gamma) / delta := by
        have hadd : ((3 : ℝ) ^ m) ^ (2 - gamma) =
            ((3 : ℝ) ^ m) ^ (1 - gamma) * (3 : ℝ) ^ m := by
          rw [show (2 : ℝ) - gamma = 1 - gamma + 1 by ring, Real.rpow_add hX, Real.rpow_one]
        rw [hadd]
        field_simp
      rw [hbase, Real.div_rpow (Real.rpow_pos_of_pos hX _).le hdelta.le,
        ← Real.rpow_mul hX.le, mul_inv_cancel₀ h1g.ne', Real.rpow_one,
        Real.rpow_neg hdelta.le, div_eq_mul_inv]
    rw [hprod, Real.mul_rpow (by positivity) (by positivity), hfirst, hsecond]
  -- the hypothesis in product form
  have hAS : (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * displacementScale delta gamma N ≤
      (((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hmin hA.le
    rw [hAinv, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at hmul
    exact hmul
  have hSpos : 0 < displacementScale delta gamma N := displacementScale_pos hdelta gamma N
  have hASpos : 0 < (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * displacementScale delta gamma N :=
    mul_pos hA hSpos
  have hPinv : ((((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹)⁻¹ ≤
      ((cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * displacementScale delta gamma N)⁻¹ :=
    inv_anti₀ hASpos hAS
  have hdiff : (3 : ℝ) ^ (m - (N : ℤ)) = (3 : ℝ) ^ m / (3 : ℝ) ^ N := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hsplit, hdiff]
  calc (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) *
        (((((3 : ℝ) ^ m) ^ (2 - gamma) / t) ^ (1 - gamma)⁻¹)⁻¹ *
          ((3 : ℝ) ^ m * delta ^ (-(1 - gamma)⁻¹)))
      ≤ (cstar * gamma⁻¹) ^ (1 / 2 : ℝ) *
          (((cstar * gamma⁻¹) ^ (1 / 2 : ℝ) * displacementScale delta gamma N)⁻¹ *
            ((3 : ℝ) ^ m * delta ^ (-(1 - gamma)⁻¹))) := by
        gcongr
    _ = (3 : ℝ) ^ m / (3 : ℝ) ^ N := by
        rw [displacementScale]
        field_simp

/-- **The minimal-scale condition supplies the hypothesis of the chains
estimate.**  If `3^n` is below the straddled quantity and the scale
`S_m = δ^{-1/(1-γ)} 3^N` is below the minimal-scale quantity, then
`n ≤ m - N`. -/
theorem auxiliaryScale_le_sub_of_displacementScale_le {n : ℤ}
    (hnu : 0 < nu) (ht : 0 < t) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcstar : 0 < cstar) (hgamma : 0 < gamma) (hgamma1 : gamma < 1)
    (hn : (3 : ℝ) ^ n ≤ auxiliaryScaleBound nu cstar gamma delta t m)
    (hmin : displacementScale delta gamma N ≤ displacementMinScale nu cstar gamma t m) :
    n ≤ m - (N : ℤ) := by
  have hbound : auxiliaryScaleBound nu cstar gamma delta t m ≤ (3 : ℝ) ^ (m - (N : ℤ)) :=
    max_le (firstTerm_le hnu ht hdelta hdelta1 hgamma hgamma1
        (hmin.trans (min_le_left _ _)))
      (secondTerm_le ht hdelta hcstar hgamma hgamma1 (hmin.trans (min_le_right _ _)))
  have hzpow : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (m - (N : ℤ)) := hn.trans hbound
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hzpow

end Comparison

end

end Algsuperdiff.Section5.Support
