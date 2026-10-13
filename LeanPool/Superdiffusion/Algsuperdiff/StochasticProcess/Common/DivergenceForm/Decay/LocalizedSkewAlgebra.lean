/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.CaccioppoliAbsorbed

/-!
# LocalizedSkewAlgebra

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pointwise algebra of an antisymmetric coefficient

The localized decay estimates split a coefficient whose symmetric part is the
fixed scalar `nu • I` into that scalar part and an antisymmetric remainder.
Three pointwise facts are used repeatedly and are collected here.

* An antisymmetric matrix contributes nothing to the quadratic form, so the
  elliptic energy is exactly `nu` times the squared gradient, with no
  inequality and no upper constant.
* An antisymmetric matrix flips the sign of the flux pairing.
* Since the two parts are orthogonal in the pairing, the size of the whole
  matrix is `sqrt (nu ^ 2 + Ks ^ 2)` when the antisymmetric part has size
  `Ks`, in particular at most `nu + Ks`.

The Young inequality for the flux cross term is then stated with the size
constant of the matrix in place of the upper ellipticity constant, so that a
caller may supply it at a single point rather than on the whole domain.

## Main results

- `DivergenceFormProcess.Decay.vecDot_matVecMul_self_eq_zero_of_skew`
- `DivergenceFormProcess.Decay.vecNormSq_matVecMul_le_of_symmPart_eq`
- `DivergenceFormProcess.Decay.localizedFlux_young`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport

variable {d : ℕ} {p : Vec d}

/-! ### Antisymmetry -/

/-- Entrywise antisymmetry, read off the matrix identity. -/
theorem skew_entry_of_matTranspose {A : Mat d} (h : matTranspose A = -A)
    (i j : Fin d) : A j i = -A i j := by
  simpa only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply]
    using congrFun (congrFun h i) j

/-- Expansion of the flux pairing as a double sum. -/
theorem vecDot_matVecMul_eq_sum (A : Mat d) (p q : Vec d) :
    vecDot (matVecMul A p) q = ∑ i : Fin d, ∑ j : Fin d, A i j * p j * q i := by
  simp only [vecDot, matVecMul, Finset.sum_mul]

/-- An antisymmetric matrix flips the sign of the flux pairing. -/
theorem vecDot_matVecMul_eq_neg_of_skew {A : Mat d}
    (h : matTranspose A = -A) (p q : Vec d) :
    vecDot (matVecMul A p) q = -vecDot (matVecMul A q) p := by
  rw [vecDot_matVecMul_eq_sum, vecDot_matVecMul_eq_sum]
  have hswap : ∑ i : Fin d, ∑ j : Fin d, A i j * q j * p i =
      ∑ i : Fin d, ∑ j : Fin d, A j i * q i * p j := Finset.sum_comm
  have hpt : ∑ i : Fin d, ∑ j : Fin d, A j i * q i * p j =
      -∑ i : Fin d, ∑ j : Fin d, A i j * p j * q i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [skew_entry_of_matTranspose h i j]
    ring
  rw [hswap, hpt]
  ring

/-- An antisymmetric matrix has vanishing quadratic form. -/
theorem vecDot_matVecMul_self_eq_zero_of_skew {A : Mat d}
    (h : matTranspose A = -A) (p : Vec d) :
    vecDot (matVecMul A p) p = 0 := by
  have := vecDot_matVecMul_eq_neg_of_skew h p p
  linarith only [this]

/-- An antisymmetric array pairs to zero against a symmetric one. -/
theorem sum_sum_mul_eq_zero_of_skew_of_symm {K : Mat d}
    (hK : ∀ i j : Fin d, K j i = -K i j) {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = T j i) :
    ∑ i : Fin d, ∑ j : Fin d, K i j * T i j = 0 := by
  have hpoint : ∀ i j : Fin d, K j i * T j i = -(K i j * T i j) := by
    intro i j
    rw [hK i j, ← hT i j]
    ring
  have hswap : ∑ i : Fin d, ∑ j : Fin d, K i j * T i j =
      ∑ i : Fin d, ∑ j : Fin d, K j i * T j i := Finset.sum_comm
  have hneg : ∑ i : Fin d, ∑ j : Fin d, K j i * T j i =
      -∑ i : Fin d, ∑ j : Fin d, K i j * T i j := by
    rw [show (∑ i : Fin d, ∑ j : Fin d, K j i * T j i) =
        ∑ i : Fin d, ∑ j : Fin d, -(K i j * T i j) from
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpoint i j]
    simp only [Finset.sum_neg_distrib]
  have h2 := hswap.trans hneg
  linarith only [h2]

/-! ### The size of a coefficient with scalar symmetric part -/

/-- The scalar matrix acts by scalar multiplication. -/
theorem matVecMul_smul_one (nu : ℝ) (p : Vec d) (i : Fin d) :
    matVecMul (nu • (1 : Mat d)) p i = nu * p i := by
  simp only [matVecMul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul]
  simp

/-- Splitting the flux of a coefficient with scalar symmetric part. -/
theorem matVecMul_scalar_add_apply {nu : ℝ} {A K : Mat d}
    (hA : A = nu • (1 : Mat d) + K) (p : Vec d) (i : Fin d) :
    matVecMul A p i = nu * p i + matVecMul K p i := by
  rw [hA]
  simp only [matVecMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  rw [show (∑ j : Fin d, (nu • (1 : Mat d)) i j * p j) =
      matVecMul (nu • (1 : Mat d)) p i from rfl, matVecMul_smul_one]

/-- The symmetric part of `nu • I` plus an antisymmetric matrix. -/
theorem symmPart_scalar_add_skew {nu : ℝ} {A K : Mat d}
    (hA : A = nu • (1 : Mat d) + K) (hK : matTranspose K = -K) :
    symmPart A = nu • (1 : Mat d) := by
  ext i j
  have hentry := skew_entry_of_matTranspose hK i j
  rw [hA]
  simp only [symmPart, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rcases eq_or_ne i j with h | h
  · subst h
    linarith only [hentry]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [show K j i = -K i j from hentry]
    ring

/-- **The exact quadratic form.**  When the symmetric part of the coefficient
is the scalar `nu • I`, the elliptic energy is exactly `nu` times the squared
gradient: the antisymmetric remainder contributes nothing and no upper size
constant appears. -/
theorem vecDot_matVecMul_eq_of_scalar_add_skew {nu : ℝ} {A K : Mat d}
    (hA : A = nu • (1 : Mat d) + K) (hK : matTranspose K = -K) (p : Vec d) :
    vecDot (matVecMul A p) p = nu * vecNormSq p := by
  have hzero := vecDot_matVecMul_self_eq_zero_of_skew hK p
  simp only [vecDot, vecNormSq] at hzero ⊢
  rw [show (∑ i : Fin d, matVecMul A p i * p i) =
      (∑ i : Fin d, nu * (p i * p i)) + ∑ i : Fin d, matVecMul K p i * p i by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [matVecMul_scalar_add_apply hA p i]; ring]
  rw [hzero, add_zero, ← Finset.mul_sum]

/-- **The size on the layer.**  The scalar and antisymmetric parts are
orthogonal in the flux pairing, so the size of the whole coefficient is the
Pythagorean combination of `nu` and the size of the antisymmetric part. -/
theorem vecNormSq_matVecMul_le_of_scalar_add_skew {nu Ks : ℝ} {A K : Mat d}
    (hA : A = nu • (1 : Mat d) + K) (hK : matTranspose K = -K)
    (hKsize : vecNormSq (matVecMul K p) ≤ Ks ^ 2 * vecNormSq p) :
    vecNormSq (matVecMul A p) ≤ (nu ^ 2 + Ks ^ 2) * vecNormSq p := by
  have hcross : ∑ i : Fin d, p i * matVecMul K p i = 0 := by
    have hzero := vecDot_matVecMul_self_eq_zero_of_skew hK p
    simp only [vecDot] at hzero
    rw [show (∑ i : Fin d, p i * matVecMul K p i) =
        ∑ i : Fin d, matVecMul K p i * p i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact hzero
  have hexpand : vecNormSq (matVecMul A p) =
      nu ^ 2 * vecNormSq p + 2 * nu * (∑ i : Fin d, p i * matVecMul K p i) +
        vecNormSq (matVecMul K p) := by
    simp only [vecNormSq, vecDot, Finset.mul_sum]
    rw [show (∑ i : Fin d, matVecMul A p i * matVecMul A p i) =
        ∑ i : Fin d, (nu ^ 2 * (p i * p i) + 2 * nu * (p i * matVecMul K p i) +
          matVecMul K p i * matVecMul K p i) from
      Finset.sum_congr rfl fun i _ => by
        rw [matVecMul_scalar_add_apply hA p i]; ring]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hexpand, hcross, mul_zero, add_zero]
  linarith only [hKsize]

/-- The size bound in the additive form used by the layer hypotheses. -/
theorem vecNormSq_matVecMul_le_add_of_scalar_add_skew {nu Ks : ℝ} {A K : Mat d}
    (hnu : 0 ≤ nu) (hKs : 0 ≤ Ks) (hA : A = nu • (1 : Mat d) + K)
    (hK : matTranspose K = -K)
    (hKsize : vecNormSq (matVecMul K p) ≤ Ks ^ 2 * vecNormSq p) :
    vecNormSq (matVecMul A p) ≤ (nu + Ks) ^ 2 * vecNormSq p := by
  refine (vecNormSq_matVecMul_le_of_scalar_add_skew hA hK hKsize).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg p)
  nlinarith only [hnu, hKs]

/-! ### The Young inequality with a layer size constant -/

/-- Young inequality for the flux cross term with the size of the coefficient
in place of an upper ellipticity constant.  Half of the elliptic energy at
rate `nu` is kept and the remainder is charged to the weight gradient. -/
theorem localizedFlux_young {nu C e p : ℝ} {A : Mat d} (hnu : 0 < nu)
    (hC : 0 < C)
    (hA : ∀ v : Vec d, vecNormSq (matVecMul A v) ≤ C ^ 2 * vecNormSq v)
    (z de : Vec d) :
    |2 * e * p * vecDot (matVecMul A z) de| ≤
      nu / 2 * (e ^ 2 * vecNormSq z) +
        2 * C ^ 2 / nu * (p ^ 2 * vecNormSq de) := by
  set c : ℝ := Real.sqrt nu / C * e with hc_def
  set b : ℝ := 2 * C / Real.sqrt nu * p with hb_def
  have hsqrt : Real.sqrt nu ≠ 0 := (Real.sqrt_pos.2 hnu).ne'
  have hC0 : C ≠ 0 := hC.ne'
  have hcb : c * b = 2 * e * p := by
    rw [hc_def, hb_def]
    field_simp
  have hy := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    c b (matVecMul A z) de
  rw [hcb] at hy
  refine hy.trans (add_le_add ?_ ?_)
  · have hAz := hA z
    have hc2 : c ^ 2 = nu / C ^ 2 * e ^ 2 := by
      rw [hc_def, mul_pow, div_pow, Real.sq_sqrt hnu.le]
    rw [hc2]
    calc
      nu / C ^ 2 * e ^ 2 * vecNormSq (matVecMul A z) / 2 ≤
          nu / C ^ 2 * e ^ 2 * (C ^ 2 * vecNormSq z) / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAz
            (mul_nonneg (div_nonneg hnu.le (sq_nonneg C)) (sq_nonneg e)))
          zero_le_two
      _ = nu / 2 * (e ^ 2 * vecNormSq z) := by field_simp
  · have hb2 : b ^ 2 / 2 = 2 * C ^ 2 / nu * p ^ 2 := by
      rw [hb_def, mul_pow, div_pow, mul_pow, Real.sq_sqrt hnu.le]
      field_simp
    refine le_of_eq ?_
    rw [show b ^ 2 * vecNormSq de / 2 = b ^ 2 / 2 * vecNormSq de by ring, hb2]
    ring

end DivergenceFormProcess.Decay
