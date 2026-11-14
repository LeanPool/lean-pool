/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Coordinates
public import LeanPool.PlanarMidpoint.ExceptionalGeometry
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-! Fixed conformal changes of coordinates and the complete pointwise kernel classification.
No position-dependent frame is differentiated. -/

@[expose] public section
noncomputable section

namespace PlanarMidpoint


/-- Pullback of a cubic tensor by a fixed conformal change of coordinates. -/
def pullCoeff (s t : ℝ) (c : Coeff) : Coeff :=
  ![c 0 * s ^ 3 + 3 * c 1 * s ^ 2 * t + 3 * c 2 * s * t ^ 2 + c 3 * t ^ 3,
    -c 0 * s ^ 2 * t + c 1 * (s ^ 3 - 2 * s * t ^ 2) + c 2 * (2 * s ^ 2 * t - t ^ 3) + c 3 * s * t
        ^ 2,
    c 0 * s * t ^ 2 + c 1 * (t ^ 3 - 2 * s ^ 2 * t) + c 2 * (s ^ 3 - 2 * s * t ^ 2) + c 3 * s ^ 2
        * t,
    -c 0 * t ^ 3 + 3 * c 1 * s * t ^ 2 - 3 * c 2 * s ^ 2 * t + c 3 * s ^ 3]

/-- Pullback of all four tensor indices of a cubic derivative. -/
def pullDerivative (s t : ℝ) (z : DerivativeArray) : DerivativeArray :=
  let x := pullCoeff s t ![s * z 0 + t * z 4, s * z 1 + t * z 5, s * z 2 + t * z 6, s * z 3 + t *
      z 7]
  let y := pullCoeff s t ![-t * z 0 + s * z 4, -t * z 1 + s * z 5, -t * z 2 + s * z 6, -t * z 3 +
      s * z 7]
  ![x 0, x 1, x 2, x 3, y 0, y 1, y 2, y 3]

theorem pullCoeff_inverse (s t : ℝ) (c : Coeff) :
    pullCoeff s (-t) (pullCoeff s t c) = (s ^ 2 + t ^ 2) ^ 3 • c := by
  ext i
  fin_cases i <;> simp [pullCoeff] <;> ring

theorem pullDerivative_inverse (s t : ℝ) (z : DerivativeArray) :
    pullDerivative s (-t) (pullDerivative s t z) = (s ^ 2 + t ^ 2) ^ 4 • z := by
  ext i
  fin_cases i <;> simp [pullDerivative, pullCoeff] <;> ring

theorem pullDerivative_ne_zero (s t : ℝ) (z : DerivativeArray)
    (hr : s ^ 2 + t ^ 2 ≠ 0) (hz : z ≠ 0) : pullDerivative s t z ≠ 0 := by
  intro he
  have hi := pullDerivative_inverse s t z
  rw [he] at hi
  have hh : pullDerivative s (-t) 0 = 0 := by simp [pullDerivative, pullCoeff]
  rw [hh] at hi
  exact hz ((smul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 4 hr))

theorem kernel_pull (s t : ℝ) (c : Coeff) (z : DerivativeArray)
    (h : Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z) :
    Algebra.Kernel (pullCoeff s t c 0) (pullCoeff s t c 1)
      (pullCoeff s t c 2) (pullCoeff s t c 3) (pullDerivative s t z) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  unfold Algebra.Kernel
  simp only [pullCoeff, pullDerivative, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (s ^ 7 + s ^ 5 * t ^ 2) * h0 + (s ^ 6 * t + s ^ 4 * t ^ 3) * h1 + (s ^ 5 *
      t ^ 2 + s ^ 3 * t ^ 4) * h2 + (s ^ 4 * t ^ 3 + s ^ 2 * t ^ 5) * h3 + (s ^ 3 * t ^ 4 + s * t
      ^ 6) * h4 + (s ^ 6 * t + s ^ 4 * t ^ 3) * h5 + (s ^ 5 * t ^ 2 + s ^ 3 * t ^ 4) * h6 + (s ^ 4
      * t ^ 3 + s ^ 2 * t ^ 5) * h7 + (s ^ 3 * t ^ 4 + s * t ^ 6) * h8 + (s ^ 2 * t ^ 5 + t ^ 7) *
      h9
  · linear_combination (-4 * s ^ 6 * t - 4 * s ^ 4 * t ^ 3) * h0 + (s ^ 7 - 2 * s ^ 5 * t ^ 2 - 3
      * s ^ 3 * t ^ 4) * h1 + (2 * s ^ 6 * t - 2 * s ^ 2 * t ^ 5) * h2 + (3 * s ^ 5 * t ^ 2 + 2 *
      s ^ 3 * t ^ 4 - s * t ^ 6) * h3 + (4 * s ^ 4 * t ^ 3 + 4 * s ^ 2 * t ^ 5) * h4 + (-4 * s ^ 5
      * t ^ 2 - 4 * s ^ 3 * t ^ 4) * h5 + (s ^ 6 * t - 2 * s ^ 4 * t ^ 3 - 3 * s ^ 2 * t ^ 5) * h6
      + (2 * s ^ 5 * t ^ 2 - 2 * s * t ^ 6) * h7 + (3 * s ^ 4 * t ^ 3 + 2 * s ^ 2 * t ^ 5 - t ^ 7)
      * h8 + (4 * s ^ 3 * t ^ 4 + 4 * s * t ^ 6) * h9
  · linear_combination (6 * s ^ 5 * t ^ 2 + 6 * s ^ 3 * t ^ 4) * h0 + (-3 * s ^ 6 * t + 3 * s ^ 2
      * t ^ 5) * h1 + (s ^ 7 - 3 * s ^ 5 * t ^ 2 - 3 * s ^ 3 * t ^ 4 + s * t ^ 6) * h2 + (3 * s ^
      6 * t - 3 * s ^ 2 * t ^ 5) * h3 + (6 * s ^ 5 * t ^ 2 + 6 * s ^ 3 * t ^ 4) * h4 + (6 * s ^ 4
      * t ^ 3 + 6 * s ^ 2 * t ^ 5) * h5 + (-3 * s ^ 5 * t ^ 2 + 3 * s * t ^ 6) * h6 + (s ^ 6 * t -
      3 * s ^ 4 * t ^ 3 - 3 * s ^ 2 * t ^ 5 + t ^ 7) * h7 + (3 * s ^ 5 * t ^ 2 - 3 * s * t ^ 6) *
      h8 + (6 * s ^ 4 * t ^ 3 + 6 * s ^ 2 * t ^ 5) * h9
  · linear_combination (-4 * s ^ 4 * t ^ 3 - 4 * s ^ 2 * t ^ 5) * h0 + (3 * s ^ 5 * t ^ 2 + 2 * s
      ^ 3 * t ^ 4 - s * t ^ 6) * h1 + (-2 * s ^ 6 * t + 2 * s ^ 2 * t ^ 5) * h2 + (s ^ 7 - 2 * s ^
      5 * t ^ 2 - 3 * s ^ 3 * t ^ 4) * h3 + (4 * s ^ 6 * t + 4 * s ^ 4 * t ^ 3) * h4 + (-4 * s ^ 3
      * t ^ 4 - 4 * s * t ^ 6) * h5 + (3 * s ^ 4 * t ^ 3 + 2 * s ^ 2 * t ^ 5 - t ^ 7) * h6 + (-2 *
      s ^ 5 * t ^ 2 + 2 * s * t ^ 6) * h7 + (s ^ 6 * t - 2 * s ^ 4 * t ^ 3 - 3 * s ^ 2 * t ^ 5) *
      h8 + (4 * s ^ 5 * t ^ 2 + 4 * s ^ 3 * t ^ 4) * h9
  · linear_combination (s ^ 3 * t ^ 4 + s * t ^ 6) * h0 + (-s ^ 4 * t ^ 3 - s ^ 2 * t ^ 5) * h1 +
      (s ^ 5 * t ^ 2 + s ^ 3 * t ^ 4) * h2 + (-s ^ 6 * t - s ^ 4 * t ^ 3) * h3 + (s ^ 7 + s ^ 5 *
      t ^ 2) * h4 + (s ^ 2 * t ^ 5 + t ^ 7) * h5 + (-s ^ 3 * t ^ 4 - s * t ^ 6) * h6 + (s ^ 4 * t
      ^ 3 + s ^ 2 * t ^ 5) * h7 + (-s ^ 5 * t ^ 2 - s ^ 3 * t ^ 4) * h8 + (s ^ 6 * t + s ^ 4 * t ^
      3) * h9
  · linear_combination (-s ^ 6 * t - s ^ 4 * t ^ 3) * h0 + (-s ^ 5 * t ^ 2 - s ^ 3 * t ^ 4) * h1 +
      (-s ^ 4 * t ^ 3 - s ^ 2 * t ^ 5) * h2 + (-s ^ 3 * t ^ 4 - s * t ^ 6) * h3 + (-s ^ 2 * t ^ 5
      - t ^ 7) * h4 + (s ^ 7 + s ^ 5 * t ^ 2) * h5 + (s ^ 6 * t + s ^ 4 * t ^ 3) * h6 + (s ^ 5 * t
      ^ 2 + s ^ 3 * t ^ 4) * h7 + (s ^ 4 * t ^ 3 + s ^ 2 * t ^ 5) * h8 + (s ^ 3 * t ^ 4 + s * t ^
      6) * h9
  · linear_combination (4 * s ^ 5 * t ^ 2 + 4 * s ^ 3 * t ^ 4) * h0 + (-s ^ 6 * t + 2 * s ^ 4 * t
      ^ 3 + 3 * s ^ 2 * t ^ 5) * h1 + (-2 * s ^ 5 * t ^ 2 + 2 * s * t ^ 6) * h2 + (-3 * s ^ 4 * t
      ^ 3 - 2 * s ^ 2 * t ^ 5 + t ^ 7) * h3 + (-4 * s ^ 3 * t ^ 4 - 4 * s * t ^ 6) * h4 + (-4 * s
      ^ 6 * t - 4 * s ^ 4 * t ^ 3) * h5 + (s ^ 7 - 2 * s ^ 5 * t ^ 2 - 3 * s ^ 3 * t ^ 4) * h6 +
      (2 * s ^ 6 * t - 2 * s ^ 2 * t ^ 5) * h7 + (3 * s ^ 5 * t ^ 2 + 2 * s ^ 3 * t ^ 4 - s * t ^
      6) * h8 + (4 * s ^ 4 * t ^ 3 + 4 * s ^ 2 * t ^ 5) * h9
  · linear_combination (-6 * s ^ 4 * t ^ 3 - 6 * s ^ 2 * t ^ 5) * h0 + (3 * s ^ 5 * t ^ 2 - 3 * s
      * t ^ 6) * h1 + (-s ^ 6 * t + 3 * s ^ 4 * t ^ 3 + 3 * s ^ 2 * t ^ 5 - t ^ 7) * h2 + (-3 * s
      ^ 5 * t ^ 2 + 3 * s * t ^ 6) * h3 + (-6 * s ^ 4 * t ^ 3 - 6 * s ^ 2 * t ^ 5) * h4 + (6 * s ^
      5 * t ^ 2 + 6 * s ^ 3 * t ^ 4) * h5 + (-3 * s ^ 6 * t + 3 * s ^ 2 * t ^ 5) * h6 + (s ^ 7 - 3
      * s ^ 5 * t ^ 2 - 3 * s ^ 3 * t ^ 4 + s * t ^ 6) * h7 + (3 * s ^ 6 * t - 3 * s ^ 2 * t ^ 5)
      * h8 + (6 * s ^ 5 * t ^ 2 + 6 * s ^ 3 * t ^ 4) * h9
  · linear_combination (4 * s ^ 3 * t ^ 4 + 4 * s * t ^ 6) * h0 + (-3 * s ^ 4 * t ^ 3 - 2 * s ^ 2
      * t ^ 5 + t ^ 7) * h1 + (2 * s ^ 5 * t ^ 2 - 2 * s * t ^ 6) * h2 + (-s ^ 6 * t + 2 * s ^ 4 *
      t ^ 3 + 3 * s ^ 2 * t ^ 5) * h3 + (-4 * s ^ 5 * t ^ 2 - 4 * s ^ 3 * t ^ 4) * h4 + (-4 * s ^
      4 * t ^ 3 - 4 * s ^ 2 * t ^ 5) * h5 + (3 * s ^ 5 * t ^ 2 + 2 * s ^ 3 * t ^ 4 - s * t ^ 6) *
      h6 + (-2 * s ^ 6 * t + 2 * s ^ 2 * t ^ 5) * h7 + (s ^ 7 - 2 * s ^ 5 * t ^ 2 - 3 * s ^ 3 * t
      ^ 4) * h8 + (4 * s ^ 6 * t + 4 * s ^ 4 * t ^ 3) * h9
  · linear_combination (-s ^ 2 * t ^ 5 - t ^ 7) * h0 + (s ^ 3 * t ^ 4 + s * t ^ 6) * h1 + (-s ^ 4
      * t ^ 3 - s ^ 2 * t ^ 5) * h2 + (s ^ 5 * t ^ 2 + s ^ 3 * t ^ 4) * h3 + (-s ^ 6 * t - s ^ 4 *
      t ^ 3) * h4 + (s ^ 3 * t ^ 4 + s * t ^ 6) * h5 + (-s ^ 4 * t ^ 3 - s ^ 2 * t ^ 5) * h6 + (s
      ^ 5 * t ^ 2 + s ^ 3 * t ^ 4) * h7 + (-s ^ 6 * t - s ^ 4 * t ^ 3) * h8 + (s ^ 7 + s ^ 5 * t ^
      2) * h9

theorem kernel_smul_coeff (r : ℝ) (c : Coeff) (z : DerivativeArray)
    (h : Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z) :
    Algebra.Kernel ((r • c) 0) ((r • c) 1) ((r • c) 2) ((r • c) 3) z := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold Algebra.Kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination r * h0
  · linear_combination r * h1
  · linear_combination r * h2
  · linear_combination r * h3
  · linear_combination r * h4
  · linear_combination r * h5
  · linear_combination r * h6
  · linear_combination r * h7
  · linear_combination r * h8
  · linear_combination r * h9

/-- Normalize a nonzero trace by a fixed conformal pullback. -/
def normalizedCoeff (c : Coeff) : Coeff :=
  (radiusSq (trace c) ^ 2)⁻¹ • pullCoeff (trace c 0) (trace c 1) c

theorem normalizedCoeff_trace (c : Coeff) (ht : trace c ≠ 0) :
    normalizedCoeff c 0 + normalizedCoeff c 2 = 1 ∧
    normalizedCoeff c 1 + normalizedCoeff c 3 = 0 := by
  have hr := radiusSq_ne_zero ht
  constructor <;> simp [normalizedCoeff, pullCoeff, trace, radiusSq] <;>
    field_simp [show (c 0 + c 2) ^ 2 + (c 1 + c 3) ^ 2 ≠ 0 from hr] <;> ring

theorem pullCoeff_smul (s t r : ℝ) (c : Coeff) :
    pullCoeff s t (r • c) = r • pullCoeff s t c := by
  ext i
  fin_cases i <;> simp [pullCoeff] <;> ring

theorem inverse_normalizedCoeff (c : Coeff) (ht : trace c ≠ 0) :
    pullCoeff (trace c 0) (-(trace c 1)) (normalizedCoeff c) =
      radiusSq (trace c) • c := by
  have hr := radiusSq_ne_zero ht
  rw [normalizedCoeff, pullCoeff_smul, pullCoeff_inverse, smul_smul]
  congr 1
  change (radiusSq (trace c) ^ 2)⁻¹ * radiusSq (trace c) ^ 3 = radiusSq (trace c)
  field_simp

theorem eq_Q_of_normalizedCoeff (c : Coeff) (ht : trace c ≠ 0)
    (hn : normalizedCoeff c = ![1, 0, 0, 0]) : c = Q (trace c) := by
  have hi := inverse_normalizedCoeff c ht
  rw [hn] at hi
  have hr := radiusSq_ne_zero ht
  ext i
  have he := congrFun hi i
  fin_cases i <;> simp only [pullCoeff, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, mul_zero, zero_mul, mul_neg,
    neg_zero, add_zero, Matrix.cons_val, even_two, Even.neg_pow, neg_mul, neg_neg,
    sub_neg_eq_add, sub_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.smul_apply,
    smul_eq_mul, Q] at he ⊢ <;>
    apply (eq_div_iff hr).mpr <;> nlinarith only [he]

theorem eq_R_of_normalizedCoeff (c : Coeff) (ht : trace c ≠ 0)
    (hn : normalizedCoeff c = ![0, 0, 1, 0]) : c = R (trace c) := by
  have hi := inverse_normalizedCoeff c ht
  rw [hn] at hi
  have hr := radiusSq_ne_zero ht
  ext i
  have he := congrFun hi i
  fin_cases i <;> simp [pullCoeff, R, Q] at he ⊢ <;>
    field_simp [hr] <;> simp only [radiusSq] at he ⊢ <;> nlinarith only [he]

/-- Complete pointwise classification: a nonzero kernel at a nonzero cubic
forces one of the two exceptional graphs. -/
theorem exceptional_of_kernel (c : Coeff) (z : DerivativeArray)
    (hc : c ≠ 0) (hz : z ≠ 0)
    (h : Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z) :
    trace c ≠ 0 ∧ (c = Q (trace c) ∨ c = R (trace c)) := by
  have ht : trace c ≠ 0 := by
    intro ht
    have hs := congrArg (fun v : E => v 0) ht
    have ht' := congrArg (fun v : E => v 1) ht
    simp only [Fin.isValue, trace, vec_zero, PiLp.zero_apply, vec_one] at hs ht'
    have h2 : c 2 = -c 0 := by linarith only [hs]
    have h3 : c 3 = -c 1 := by linarith only [ht']
    have hab : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
      by_contra hh
      push Not at hh
      apply hc
      ext i
      fin_cases i <;> simp [hh.1, hh.2, h2, h3]
    rw [h2, h3] at h
    exact hz (Algebra.tracefree_injective (c 0) (c 1) z h hab)
  refine ⟨ht, ?_⟩
  let z' := pullDerivative (trace c 0) (trace c 1) z
  have hz' : z' ≠ 0 := pullDerivative_ne_zero _ _ z (radiusSq_ne_zero ht) hz
  have hn := kernel_smul_coeff ((radiusSq (trace c) ^ 2)⁻¹) _ _
    (kernel_pull (trace c 0) (trace c 1) c z h)
  change Algebra.Kernel (normalizedCoeff c 0) (normalizedCoeff c 1)
    (normalizedCoeff c 2) (normalizedCoeff c 3) z' at hn
  obtain ⟨ht0, ht1⟩ := normalizedCoeff_trace c ht
  have h2 : normalizedCoeff c 2 = 1 - normalizedCoeff c 0 := by linarith only [ht0]
  have h3 : normalizedCoeff c 3 = -normalizedCoeff c 1 := by linarith only [ht1]
  rw [h2, h3] at hn
  obtain ⟨hb, ha|ha⟩ := Algebra.normalized_classification _ _ z' hn hz'
  · right
    apply eq_R_of_normalizedCoeff c ht
    ext i
    fin_cases i <;> simp [ha, hb, h2, h3]
  · left
    apply eq_Q_of_normalizedCoeff c ht
    ext i
    fin_cases i <;> simp [ha, hb, h2, h3]

end PlanarMidpoint
