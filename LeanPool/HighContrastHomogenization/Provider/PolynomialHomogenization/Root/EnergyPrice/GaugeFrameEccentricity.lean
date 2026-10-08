/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeCubeEnergyPriceWitness
public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalNorm
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeFrameEccentricity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gauge frame factor is a power of the witness eccentricity

The frozen `boundaryEnergy` is pinned in the **physical** frame
(`hsNormSq U s (fun x ↦ matVecMul (matSqrt (symmPart abar)) (g₀.grad x))`,
`168:68-74`), while the law-free cube price of
`HCPoly.Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeCubeEnergyPriceWitness`
lives in the **gauge** frame on
`matImage (matSqrt (symmPart abar))⁻¹ U`.  The change of variables is the
`hsNormSq_matImage_le`, whose constant is

```
hsAffineFactor L⁻¹ s N = max (|det L⁻¹| ^ (-(2s)/d)) (|det L⁻¹| · N ^ (d + 2s)).
```

This file proves that this constant, **multiplied by the gauge cube side**,
collapses to a dimension-only constant times a power of
`witnessEccentricity (symmPart abar)`:

```
hsAffineFactor L⁻¹ s ‖L‖ · ell ^ (2s)
  ≤ d ^ (d/2) · 2 ^ (2s) · witnessEccentricity (symmPart abar) ^ (d + 2s)
```

whenever `ell ≤ 2 ‖L⁻¹‖`, which the inner-ellipsoid normalization premise
`U ⊆ ellipsoid abar 1` supplies (the gauge image of `ellipsoid abar 1` is the
ball of radius `‖L⁻¹‖`, because `ellipsoid` is normalized by
`specBound (symmPart abar)⁻¹`).

**So the exponent is `p = d + 2s`**, and no factor of `‖L‖` alone survives:
the absolute scale of `abar` cancels between the frame distortion (`‖L‖ ^ 2s`)
and the gauge cube side (`ell ^ 2s ≤ (2‖L⁻¹‖) ^ 2s`).  This is paid by the
eccentricity fold.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03
open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The gauge condition number -/

/-- The operator norm of the matrix square root is the square root of the
spectral bound. -/
theorem norm_matSqrt_eq_sqrt_specBound {A : Mat d} (hA : A.PosDef) :
    ‖matSqrt A‖ = Real.sqrt (specBound A) := by
  have hherm : (matSqrt A)ᴴ = matSqrt A :=
    (matSqrt_spec hA.posSemidef).1.isHermitian
  have hsq : ‖matSqrt A‖ ^ 2 = specBound A := by
    rw [pow_two, ← CStarRing.norm_self_mul_star,
      Matrix.star_eq_conjTranspose, hherm,
      (matSqrt_spec hA.posSemidef).2,
      specBound_eq_norm hA.posSemidef]
  symm
  exact (Real.sqrt_eq_iff_eq_sq (specBound_nonneg A) (norm_nonneg _)).mpr
    hsq.symm

/-- **The gauge condition number is the witness eccentricity.** -/
theorem norm_matSqrt_mul_norm_inv_eq_witnessEccentricity
    {A : Mat d} (hA : A.PosDef) :
    ‖matSqrt A‖ * ‖(matSqrt A)⁻¹‖ = witnessEccentricity A := by
  rw [← matSqrt_inv hA, norm_matSqrt_eq_sqrt_specBound hA,
    norm_matSqrt_eq_sqrt_specBound hA.inv, witnessEccentricity,
    ← Real.sqrt_mul (specBound_nonneg A)]

/-! ## The frame factor -/

/-- The dimension-only prefactor of the gauge frame change. -/
@[expose]
def gaugeFrameConstant (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (2 * s)

theorem gaugeFrameConstant_nonneg (d : ℕ) (s : ℝ) :
    0 ≤ gaugeFrameConstant d s := by
  unfold gaugeFrameConstant
  have h1 : 0 ≤ ((d : ℝ)) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (2 : ℝ) ^ (2 * s) :=
    Real.rpow_nonneg (by norm_num) _
  positivity

/-- The determinant branch of the affine distortion, against the operator
norm. -/
private theorem abs_det_rpow_le_norm_rpow [NeZero d] (L : Mat d) {t : ℝ}
    (ht : 0 ≤ t) :
    |L.det| ^ (t / (d : ℝ)) ≤
      (Real.sqrt (d : ℝ) * ‖L‖) ^ t := by
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hbase : 0 ≤ Real.sqrt (d : ℝ) * ‖L‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hstep :
      |L.det| ^ (t / (d : ℝ)) ≤
        ((Real.sqrt (d : ℝ) * ‖L‖) ^ d) ^ (t / (d : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg _) (Transport.abs_det_le_pow_norm L)
      (div_nonneg ht hd.le)
  refine hstep.trans_eq ?_
  rw [← Real.rpow_natCast (Real.sqrt (d : ℝ) * ‖L‖) d, ← Real.rpow_mul hbase]
  congr 1
  field_simp

/-- **The gauge frame factor, times the gauge cube side, is a power of the
witness eccentricity.**  The exponent is exactly `d + 2s`. -/
theorem hsAffineFactor_mul_cubeSide_le_witnessEccentricity_rpow
    [NeZero d] {M : Mat d} (hM : M.PosDef) {s ell : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2) (hell : 0 ≤ ell)
    (hellBound : ell ≤ 2 * ‖(matSqrt M)⁻¹‖) :
    hsAffineFactor (matSqrt M)⁻¹ s ‖matSqrt M‖ * ell ^ (2 * s) ≤
      gaugeFrameConstant d s *
        witnessEccentricity M ^ ((d : ℝ) + 2 * s) := by
  classical
  have hdPos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hone_le_d : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  set L : Mat d := matSqrt M with hLdef
  have hLunit : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_matSqrt hM)
  set nL : ℝ := ‖L‖ with hnLdef
  set nLi : ℝ := ‖L⁻¹‖ with hnLidef
  have hnL : 0 ≤ nL := norm_nonneg _
  have hnLi : 0 ≤ nLi := norm_nonneg _
  set ecc : ℝ := witnessEccentricity M with heccDef
  have hecc_eq : nL * nLi = ecc := by
    rw [hnLdef, hnLidef, hLdef, heccDef]
    exact norm_matSqrt_mul_norm_inv_eq_witnessEccentricity hM
  have hone_le_ecc : (1 : ℝ) ≤ ecc := by
    have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
    rw [heccDef]
    exact Initialization.one_le_witnessEccentricity hM
  have hecc_nonneg : (0 : ℝ) ≤ ecc := le_trans zero_le_one hone_le_ecc
  have hs2 : (0 : ℝ) ≤ 2 * s := by linarith only [hs]
  -- the cube-side factor
  have hellPow : ell ^ (2 * s) ≤ (2 * nLi) ^ (2 * s) :=
    Real.rpow_le_rpow hell hellBound hs2
  have hellPowNonneg : (0 : ℝ) ≤ ell ^ (2 * s) := Real.rpow_nonneg hell _
  have htwoNLi : (2 : ℝ) * nLi ≥ 0 := by positivity
  have hsplit : (2 * nLi) ^ (2 * s) = (2 : ℝ) ^ (2 * s) * nLi ^ (2 * s) :=
    Real.mul_rpow (by norm_num) hnLi
  -- branch one
  have hdetinv : |(L⁻¹).det| = |L.det|⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv]
  have hdetpos : 0 < |L.det| := abs_pos.mpr hLunit.ne_zero
  have hbranch1 :
      |(L⁻¹).det| ^ (-(2 * s) / (d : ℝ)) ≤
        (d : ℝ) ^ s * nL ^ (2 * s) := by
    have hrewrite :
        |(L⁻¹).det| ^ (-(2 * s) / (d : ℝ)) = |L.det| ^ ((2 * s) / (d : ℝ)) := by
      rw [hdetinv, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
      congr 1
      field_simp
    rw [hrewrite]
    refine (abs_det_rpow_le_norm_rpow L hs2).trans_eq ?_
    rw [Real.mul_rpow (Real.sqrt_nonneg _) hnL, hnLdef]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdPos.le]
    congr 1
    ring
  -- branch two
  have hbranch2 :
      |(L⁻¹).det| * nL ^ ((d : ℝ) + 2 * s) ≤
        (d : ℝ) ^ ((d : ℝ) / 2) * (ecc ^ (d : ℝ) * nL ^ (2 * s)) := by
    have hdetle : |(L⁻¹).det| ≤ (Real.sqrt (d : ℝ) * nLi) ^ d := by
      rw [hnLidef]
      exact Transport.abs_det_le_pow_norm L⁻¹
    have hpowSplit : nL ^ ((d : ℝ) + 2 * s) = nL ^ (d : ℝ) * nL ^ (2 * s) :=
      Real.rpow_add' hnL (by positivity)
    have hcast : ((Real.sqrt (d : ℝ) * nLi) ^ d : ℝ) =
        (d : ℝ) ^ ((d : ℝ) / 2) * nLi ^ (d : ℝ) := by
      rw [← Real.rpow_natCast (Real.sqrt (d : ℝ) * nLi) d,
        Real.mul_rpow (Real.sqrt_nonneg _) hnLi, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hdPos.le]
      congr 2
      ring
    have hnLpow : (0 : ℝ) ≤ nL ^ ((d : ℝ) + 2 * s) := Real.rpow_nonneg hnL _
    calc
      |(L⁻¹).det| * nL ^ ((d : ℝ) + 2 * s) ≤
          ((Real.sqrt (d : ℝ) * nLi) ^ d) * nL ^ ((d : ℝ) + 2 * s) :=
        mul_le_mul_of_nonneg_right hdetle hnLpow
      _ = ((d : ℝ) ^ ((d : ℝ) / 2) * nLi ^ (d : ℝ)) *
            (nL ^ (d : ℝ) * nL ^ (2 * s)) := by rw [hcast, hpowSplit]
      _ = (d : ℝ) ^ ((d : ℝ) / 2) *
            ((nL ^ (d : ℝ) * nLi ^ (d : ℝ)) * nL ^ (2 * s)) := by ring
      _ = (d : ℝ) ^ ((d : ℝ) / 2) * (ecc ^ (d : ℝ) * nL ^ (2 * s)) := by
        rw [← Real.mul_rpow hnL hnLi, hecc_eq]
  -- combine
  have hnLpow2 : (0 : ℝ) ≤ nL ^ (2 * s) := Real.rpow_nonneg hnL _
  have hkey :
      hsAffineFactor L⁻¹ s nL ≤
        (d : ℝ) ^ ((d : ℝ) / 2) * (ecc ^ (d : ℝ) * nL ^ (2 * s)) := by
    unfold hsAffineFactor
    refine max_le ?_ hbranch2
    refine hbranch1.trans ?_
    have hds : (d : ℝ) ^ s ≤ (d : ℝ) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hone_le_d (by
        have : (1 : ℝ) / 2 ≤ (d : ℝ) / 2 := by linarith only [hone_le_d]
        linarith only [hsHalf, this])
    have hecc1 : (1 : ℝ) ≤ ecc ^ (d : ℝ) :=
      Real.one_le_rpow hone_le_ecc (by positivity)
    calc
      (d : ℝ) ^ s * nL ^ (2 * s) ≤
          (d : ℝ) ^ ((d : ℝ) / 2) * nL ^ (2 * s) :=
        mul_le_mul_of_nonneg_right hds hnLpow2
      _ ≤ (d : ℝ) ^ ((d : ℝ) / 2) * (ecc ^ (d : ℝ) * nL ^ (2 * s)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hdPos.le _)
        calc
          nL ^ (2 * s) = 1 * nL ^ (2 * s) := (one_mul _).symm
          _ ≤ ecc ^ (d : ℝ) * nL ^ (2 * s) :=
            mul_le_mul_of_nonneg_right hecc1 hnLpow2
  have hfactorNonneg : (0 : ℝ) ≤ hsAffineFactor L⁻¹ s nL :=
    (hsAffineFactor_pos (Matrix.isUnit_nonsing_inv_det L hLunit) s nL).le
  calc
    hsAffineFactor L⁻¹ s nL * ell ^ (2 * s) ≤
        ((d : ℝ) ^ ((d : ℝ) / 2) * (ecc ^ (d : ℝ) * nL ^ (2 * s))) *
          ((2 : ℝ) ^ (2 * s) * nLi ^ (2 * s)) := by
      refine mul_le_mul hkey (hellPow.trans_eq hsplit) hellPowNonneg ?_
      exact mul_nonneg (Real.rpow_nonneg hdPos.le _)
        (mul_nonneg (Real.rpow_nonneg hecc_nonneg _) hnLpow2)
    _ = ((d : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (2 * s)) *
          (ecc ^ (d : ℝ) * (nL ^ (2 * s) * nLi ^ (2 * s))) := by ring
    _ = gaugeFrameConstant d s * (ecc ^ (d : ℝ) * ecc ^ (2 * s)) := by
      rw [gaugeFrameConstant, ← Real.mul_rpow hnL hnLi, hecc_eq]
    _ = gaugeFrameConstant d s * ecc ^ ((d : ℝ) + 2 * s) := by
      rw [Real.rpow_add' hecc_nonneg (by positivity)]

end

end EnergyPrice
end HighContrast
end HCPolySupport
