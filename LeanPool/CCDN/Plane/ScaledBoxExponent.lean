/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.ScaledPlaneCount
import LeanPool.CCDN.ForMathlib.Log

/-! The scaling-prime interval yields the affine box exponent 1/d. These
numerical bounds are independent of the coefficient height. -/

@[expose] public section
namespace CCDN
open Real

private lemma scaled_box_power_ratio_le {d : ℕ} (hd : 0 < d) {A B p : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hp : 0 < p) (hBp : B ≤ A * p) :
    (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) ≤
      Real.exp 2 * A * B ^ (1 / (d : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hdplus : (0 : ℝ) < d + 1 := by linarith
  have hlog : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self hd0.le
  have hdeg : ((d : ℝ) + 1) ^ (2 / (d : ℝ)) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos hdplus]
    apply Real.exp_le_exp.mpr
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    linarith
  have hquot : (B / p) ^ (1 / (d : ℝ)) ≤ A := by
    have hbase : B / p ≤ A := (div_le_iff₀ hp).mpr hBp
    have h := Real.rpow_le_rpow (div_nonneg hB0.le hp.le) hbase
      (show (0 : ℝ) ≤ 1 / d by positivity)
    apply h.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA
      (show (1 : ℝ) / d ≤ 1 by apply (div_le_iff₀ hd0).mpr; linarith)
  have he : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) =
      ((d : ℝ) + 1) ^ (2 / (d : ℝ)) * (B / p) ^ (1 / (d : ℝ)) * B ^ (1 / (d : ℝ)) := by
    rw [Real.mul_rpow hdplus.le hB0.le, Real.div_rpow hB0.le hp.le]
    rw [show (2 : ℝ) / d = 1 / d + 1 / d by ring, Real.rpow_add hB0]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hdeg hquot (Real.rpow_nonneg (div_nonneg hB0.le hp.le) _) (Real.exp_pos _).le)
    (Real.rpow_nonneg hB0.le _)

private lemma scaled_auxiliary_degree_bound_le {d : ℕ} (hd : 0 < d) {A B p C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hp : 1 ≤ p) (hpB : p ≤ B) (hBp : B ≤ A * p) :
    (d : ℝ) * scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
      (4 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * A) *
        (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hB0 : 0 < B := by linarith
  have hp0 : 0 < p := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogp := Real.log_nonneg hp
  have hlogpB := Real.log_le_log hp0 hpB
  have hlogR : Real.log (((d : ℝ) + 1) * B) ≤ d + Real.log B := by
    rw [Real.log_mul (by positivity) hB0.ne']
    linarith [Real.log_add_one_le_self hd0.le]
  let Q := B ^ (1 / (d : ℝ))
  let E := 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hratio := scaled_box_power_ratio_le hd hA hB hp0 hBp
  have hnum : 0 ≤ 1 + Real.log p / d := by positivity
  have hnumB : 1 + Real.log p / d ≤ 1 + Real.log B / d := by gcongr
  have hterm : E * (d : ℝ) ^ 3 * (1 + Real.log p / d) *
        ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ))) ≤
      E * Real.exp 2 * A * (d : ℝ) ^ 2 * Q * (Real.log B + d) := by
    have hh := mul_le_mul hnumB hratio
      (Real.rpow_nonneg (show 0 ≤ ((d : ℝ) + 1) * B by positivity) _ |> fun h =>
        div_nonneg h (Real.rpow_nonneg hp0.le _)) (by positivity : 0 ≤ 1 + Real.log B / d)
    have ht := mul_le_mul_of_nonneg_left hh (mul_nonneg hE (pow_nonneg hd0.le 3))
    convert ht using 1
    · ring
    · dsimp only [Q]
      field_simp
      ring
  have hrest : (d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2 ≤
      4 * (d : ℝ) ^ 2 * Q * (Real.log B + d) := by
    have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hprod : 1 ≤ (d : ℝ) ^ 2 * Q := one_le_mul_of_one_le_of_one_le hd2 hQ
    nlinarith [mul_le_mul_of_nonneg_right hprod
      (show 0 ≤ Real.log B + d by positivity)]
  have hb : scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
      (4 + E * Real.exp 2 * A) * (d : ℝ) ^ 2 * Q * (Real.log B + d) := by
    unfold scaledPlaneAuxiliaryDegreeBound
    calc
      _ = ((d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2) + E * (d : ℝ) ^ 3 *
          (1 + Real.log p / d) *
          ((((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ))) := by dsimp [E]; ring
      _ ≤ 4 * (d : ℝ) ^ 2 * Q * (Real.log B + d) +
          E * Real.exp 2 * A * (d : ℝ) ^ 2 * Q * (Real.log B + d) := add_le_add hrest hterm
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left hb hd0.le
  convert ht using 1
  dsimp [E, Q]
  ring

/-- A coefficient-uniform affine count with exponent 1/d, conditional on the
sharp finite-field estimate and a prime p in [B/A,B] not dividing f(0). -/
theorem scaled_plane_finite_count_one_over_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    {A B C : ℝ} (hzB : IsBoxZeroFamily f B z) (hA : 1 ≤ A) (hpB : (p : ℝ) ≤ B) (hBp : B ≤ A * p)
    (hC : 0 ≤ C)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤
      (38 + 8 * Real.exp (heightDeterminantError C + 20) +
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * A) *
      (f.totalDegree : ℝ) ^ 3 * B ^ (1 / (f.totalDegree : ℝ)) *
        (Real.log B + f.totalDegree) := by
  have hB := hzB.one_le_radius
  let d := f.totalDegree
  let Q := B ^ (1 / (d : ℝ))
  let U := Real.log B + d
  let K₁ := 4 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * A
  let K₂ := 34 + 8 * Real.exp (heightDeterminantError C + 20)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hB
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hU : (d : ℝ) ≤ U := by dsimp [U]; linarith
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hrest : (0 : ℝ) ≤ (d : ℝ) ^ 3 * Q * U := by dsimp [U]; positivity
  have hlarge : K₂ * (d : ℝ) ^ 4 ≤ K₂ * ((d : ℝ) ^ 3 * Q * U) := by
    apply mul_le_mul_of_nonneg_left _ hK₂
    have hh : (d : ℝ) ≤ Q * U := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg hdR.le 3)
    nlinarith only [ht]
  have hsmall := scaled_auxiliary_degree_bound_le hd hA hB
    (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le) hpB hBp (C := C)
  have hcount' := scaled_plane_finite_count f hprim hir hd hp hp0 z hinj hzB hpB hC hcount
  have hb : (t : ℝ) ≤ (K₁ + K₂) * ((d : ℝ) ^ 3 * Q * U) := by
    apply hcount'.trans
    apply max_le
    · have ht : (d : ℝ) * scaledPlaneAuxiliaryDegreeBound d C (((d : ℝ) + 1) * B) p ≤
          K₁ * ((d : ℝ) ^ 3 * Q * U) := by
        convert hsmall using 1
        simp only [K₁, Q, U]
        ring
      exact ht.trans (mul_le_mul_of_nonneg_right (by linarith) hrest)
    · exact hlarge.trans (mul_le_mul_of_nonneg_right (by linarith) hrest)
  convert hb using 1
  simp only [K₁, K₂, Q, U, d]
  ring

end CCDN
