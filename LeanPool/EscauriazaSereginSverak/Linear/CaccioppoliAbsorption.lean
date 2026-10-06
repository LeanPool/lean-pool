/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliIdentity
public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliProductCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.Real.Sqrt

/-!
# Absorption estimate for a localized energy identity

This module estimates the terms in the local identity from `lem:caccioppoli`.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace ESS

private theorem abs_sum_mul_le_sqrt_sumsq
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hupper := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have hlowerRaw := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  have hneg : (∑ i ∈ s, (-f i) * g i) = -(∑ i ∈ s, f i * g i) := by
    simp [Finset.sum_neg_distrib]
  have hsquare : (∑ i ∈ s, (-f i) ^ 2) = ∑ i ∈ s, f i ^ 2 := by
    simp
  rw [hneg, hsquare] at hlowerRaw
  rw [abs_le]
  exact ⟨by linarith only [hlowerRaw], hupper⟩

private theorem sqrt_mul_le_quarter_add {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X * Y) ≤ X / 4 + Y := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [sq_nonneg (X / 4 - Y)]

private theorem abs_vec3_dot_le (u v : Vec3) :
    |∑ i : Fin 3, u i * v i| ≤ vec3EuclideanNorm u * vec3EuclideanNorm v := by
  have hinner :
      inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = ∑ i : Fin 3, u i * v i := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  rw [← hinner, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  exact abs_real_inner_le_norm _ _

private theorem caccioppoli_source_vector_bound
    (c₁ φ : ℝ) (w L : Vec3) (g : ℝ)
    (hφ : 0 ≤ φ) (hg : 0 ≤ g)
    (hL : vec3EuclideanNorm L ≤ c₁ *
      (vec3EuclideanNorm w + Real.sqrt g)) :
    -φ * (∑ i : Fin 3, w i * L i) ≤
      (c₁ + c₁ ^ 2) * φ * (vec3EuclideanNorm w) ^ 2 +
        (1 / 4 : ℝ) * φ * g := by
  have hdot := abs_vec3_dot_le w L
  have hw : 0 ≤ vec3EuclideanNorm w := vec3EuclideanNorm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
  have hdotLower : -(∑ i : Fin 3, w i * L i) ≤
      vec3EuclideanNorm w * vec3EuclideanNorm L :=
    (neg_le_abs _).trans hdot
  have hdotWeighted := mul_le_mul_of_nonneg_left hdotLower hφ
  have hLweighted := mul_le_mul_of_nonneg_left hL hw
  have hYoung : c₁ * vec3EuclideanNorm w * Real.sqrt g ≤
      (1 / 4 : ℝ) * (Real.sqrt g) ^ 2 +
        c₁ ^ 2 * (vec3EuclideanNorm w) ^ 2 := by
    nlinarith only [sq_nonneg
      (Real.sqrt g / 2 - c₁ * vec3EuclideanNorm w)]
  have hYoungφ := mul_le_mul_of_nonneg_left hYoung hφ
  have hsqrtSq : (Real.sqrt g) ^ 2 = g := Real.sq_sqrt hg
  calc
    -φ * (∑ i : Fin 3, w i * L i) ≤
        φ * (vec3EuclideanNorm w * vec3EuclideanNorm L) := by
      calc
        _ = φ * (-(∑ i : Fin 3, w i * L i)) := by ring
        _ ≤ _ := hdotWeighted
    _ ≤ φ * (vec3EuclideanNorm w *
        (c₁ * (vec3EuclideanNorm w + Real.sqrt g))) := by
      exact mul_le_mul_of_nonneg_left hLweighted hφ
    _ ≤ (c₁ + c₁ ^ 2) * φ * (vec3EuclideanNorm w) ^ 2 +
        (1 / 4 : ℝ) * φ * g := by
      rw [hsqrtSq] at hYoungφ
      nlinarith only [hYoungφ, hφ, hw, hsqrt]

private theorem caccioppoli_gradient_cross_bound
    (φ Csp r : ℝ) (w : Vec3) (D : Fin 3 → Fin 3 → ℝ)
    (d : Fin 3 → ℝ) (hφ : 0 ≤ φ) (hCsp : 0 ≤ Csp)
    (hr : 0 < r)
    (hsp : ∑ j : Fin 3, d j ^ 2 ≤ Csp / r ^ 2 * φ) :
    -∑ i : Fin 3, ∑ j : Fin 3, d j * w i * D i j ≤
      (1 / 4 : ℝ) * φ * (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2) +
        Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2 := by
  let col : Fin 3 → ℝ := fun j => ∑ i : Fin 3, w i * D i j
  have hcol (j : Fin 3) : (col j) ^ 2 ≤
      (∑ i : Fin 3, (w i) ^ 2) * (∑ i : Fin 3, (D i j) ^ 2) := by
    simpa [col] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun i => w i) (fun i => D i j))
  have hcolSq : (∑ j : Fin 3, (col j) ^ 2) ≤
      (vec3EuclideanNorm w) ^ 2 *
        (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2) := by
    have hnorm : (vec3EuclideanNorm w) ^ 2 = ∑ i : Fin 3, (w i) ^ 2 := by
      change Real.sqrt (∑ i : Fin 3, (w i) ^ 2) ^ 2 = _
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (w i))]
    calc
      _ ≤ ∑ j : Fin 3, (∑ i : Fin 3, (w i) ^ 2) *
          (∑ i : Fin 3, (D i j) ^ 2) := Finset.sum_le_sum fun j hj => hcol j
      _ = _ := by
        rw [Finset.mul_sum, ← hnorm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
  have hsum := abs_sum_mul_le_sqrt_sumsq (Finset.univ : Finset (Fin 3)) d col
  have hG : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2 := by positivity
  have hd : 0 ≤ ∑ j : Fin 3, d j ^ 2 := by positivity
  have hcross : |∑ i : Fin 3, ∑ j : Fin 3, d j * w i * D i j| ≤
      Real.sqrt (∑ j : Fin 3, d j ^ 2) *
        Real.sqrt ((vec3EuclideanNorm w) ^ 2 *
          (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) := by
    have hsumEq : (∑ i : Fin 3, ∑ j : Fin 3, d j * w i * D i j) =
        ∑ j : Fin 3, d j * col j := by
      simp only [col]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsumEq]
    exact hsum.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hcolSq) (Real.sqrt_nonneg _))
  have hnormSq : (vec3EuclideanNorm w) ^ 2 =
      ∑ i : Fin 3, (w i) ^ 2 := by
    change Real.sqrt (∑ i : Fin 3, (w i) ^ 2) ^ 2 = _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (w i))]
  have hYoung : Real.sqrt ((φ *
      (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) *
      (Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2)) ≤
      (1 / 4 : ℝ) * φ * (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2) +
        Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2 := by
    convert sqrt_mul_le_quarter_add
      (by positivity : 0 ≤ φ * (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2))
      (by positivity : 0 ≤ Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2) using 1
    ring
  have hproduct :
      (∑ j : Fin 3, d j ^ 2) *
        ((vec3EuclideanNorm w) ^ 2 *
          (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) ≤
      (φ * (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) *
        (Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2) := by
    have hsp' := mul_le_mul_of_nonneg_right hsp
      (mul_nonneg (sq_nonneg (vec3EuclideanNorm w)) hG)
    calc
      _ ≤ (Csp / r ^ 2 * φ) *
          ((vec3EuclideanNorm w) ^ 2 *
            (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) := hsp'
      _ = _ := by ring
  have hrad :
      Real.sqrt (∑ j : Fin 3, d j ^ 2) *
        Real.sqrt ((vec3EuclideanNorm w) ^ 2 *
          (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) ≤
      Real.sqrt ((φ * (∑ i : Fin 3, ∑ j : Fin 3, (D i j) ^ 2)) *
        (Csp / r ^ 2 * (vec3EuclideanNorm w) ^ 2)) := by
    rw [← Real.sqrt_mul hd]
    exact Real.sqrt_le_sqrt hproduct
  have hfinal := hcross.trans (hrad.trans hYoung)
  have hlower := (abs_le.mp hfinal).1
  linarith only [hlower]

private theorem caccioppoli_source_pointwise_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (c₁ : ℝ)
    (φ : α → ℝ) (W T : α → Vec3)
    (H : α → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (L : α → Vec3) (G : α → ℝ)
    (hφrange : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1)
    (hGnonneg : ∀ q, 0 ≤ G q)
    (hL : ∀ q i, L q i = T q i + ∑ j : Fin 3, H q i j j)
    (hineq : ∀ᵐ q ∂μ, vec3EuclideanNorm (L q) ≤
      c₁ * (vec3EuclideanNorm (W q) + Real.sqrt (G q))) :
    ∀ᵐ q ∂μ,
      -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j) ≤
        (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
          (1 / 4 : ℝ) * φ q * G q := by
  filter_upwards [hineq] with q hineq
  have hlocal := caccioppoli_source_vector_bound c₁ (φ q) (W q) (L q)
    (G q) (hφrange q).1 (hGnonneg q) hineq
  have hsourceEq :
      (∑ i : Fin 3, W q i * T q i * φ q) +
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j) =
      φ q * (∑ i : Fin 3, W q i * L q i) := by
    calc
      _ = ∑ i : Fin 3,
          (W q i * T q i * φ q + ∑ j : Fin 3, φ q * W q i * H q i j j) := by
        rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin 3,
          φ q * W q i * (T q i + ∑ j : Fin 3, H q i j j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
        ring
      _ = φ q * (∑ i : Fin 3,
          W q i * (T q i + ∑ j : Fin 3, H q i j j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = φ q * (∑ i : Fin 3, W q i * L q i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [hL]
  calc
    _ = -((∑ i : Fin 3, W q i * T q i * φ q) +
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)) := by ring
    _ = -(φ q * (∑ i : Fin 3, W q i * L q i)) := by rw [hsourceEq]
    _ = -φ q * (∑ i : Fin 3, W q i * L q i) := by ring
    _ ≤ _ := hlocal

private theorem caccioppoli_integrated_source_bound
    (c₁ : ℝ) (φ : Vec3 × ℝ → ℝ) (W T : Vec3 × ℝ → Vec3)
    (H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (G : Vec3 × ℝ → ℝ)
    (hsourceInt : ∀ i : Fin 3, Integrable
      (fun q => W q i * T q i * φ q) (volume : Measure (Vec3 × ℝ)))
    (hlapInt : ∀ i j : Fin 3, Integrable
      (fun q => φ q * W q i * H q i j j) (volume : Measure (Vec3 × ℝ)))
    (hφWsqInt : Integrable
      (fun q => φ q * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)))
    (hφGint : Integrable (fun q => φ q * G q)
      (volume : Measure (Vec3 × ℝ)))
    (hpoint : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j) ≤
        (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
          (1 / 4 : ℝ) * φ q * G q) :
    -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
        ∂(volume : Measure (Vec3 × ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
          ∂(volume : Measure (Vec3 × ℝ))) ≤
      (c₁ + c₁ ^ 2) *
        (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) +
      (1 / 4 : ℝ) *
        (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) := by
  have hsourceSumInt : Integrable
      (fun q => ∑ i : Fin 3, W q i * T q i * φ q)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hsourceInt i
  have hlapRowInt (i : Fin 3) : Integrable
      (fun q => ∑ j : Fin 3, φ q * W q i * H q i j j)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hlapInt i j
  have hlapTotalInt : Integrable
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
      (volume : Measure (Vec3 × ℝ)) :=
    integrable_finsetSum Finset.univ fun i hi => hlapRowInt i
  have hsourceNegativeInt : Integrable
      (fun q => -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j))
      (volume : Measure (Vec3 × ℝ)) := hsourceSumInt.neg.sub hlapTotalInt
  have hsourceRightInt : Integrable
      (fun q => (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
        (1 / 4 : ℝ) * φ q * G q) (volume : Measure (Vec3 × ℝ)) := by
    have hleft := hφWsqInt.const_mul (c₁ + c₁ ^ 2)
    have hright := hφGint.const_mul (1 / 4 : ℝ)
    apply (hleft.add hright).congr
    filter_upwards [] with q
    simp only [Pi.add_apply]
    ring
  have hmono := integral_mono_ae hsourceNegativeInt hsourceRightInt hpoint
  have hleft :
      (∫ q : Vec3 × ℝ, -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
        ∂(volume : Measure (Vec3 × ℝ))) =
      -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
        ∂(volume : Measure (Vec3 × ℝ))) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
            ∂(volume : Measure (Vec3 × ℝ))) := by
    have hsub := integral_sub hsourceSumInt.neg hlapTotalInt
    simp only [Pi.neg_apply] at hsub
    rw [hsub, integral_neg,
      integral_finsetSum Finset.univ (fun i hi => hsourceInt i),
      integral_finsetSum Finset.univ (fun i hi => hlapRowInt i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j hj => hlapInt i j)
  have hright :
      (∫ q : Vec3 × ℝ, (c₁ + c₁ ^ 2) * φ q *
        (vec3EuclideanNorm (W q)) ^ 2 + (1 / 4 : ℝ) * φ q * G q
        ∂(volume : Measure (Vec3 × ℝ))) =
      (c₁ + c₁ ^ 2) *
        (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) +
      (1 / 4 : ℝ) *
        (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) := by
    rw [show (fun q => (c₁ + c₁ ^ 2) * φ q *
          (vec3EuclideanNorm (W q)) ^ 2 + (1 / 4 : ℝ) * φ q * G q) =
        (fun q => (c₁ + c₁ ^ 2) *
          (φ q * (vec3EuclideanNorm (W q)) ^ 2) +
            (1 / 4 : ℝ) * (φ q * G q)) by funext q; ring,
      integral_add (hφWsqInt.const_mul (c₁ + c₁ ^ 2))
        (hφGint.const_mul (1 / 4 : ℝ)),
      integral_const_mul, integral_const_mul]
  calc
    _ = ∫ q : Vec3 × ℝ, -(∑ i : Fin 3, W q i * T q i * φ q) -
          (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
          ∂(volume : Measure (Vec3 × ℝ)) := hleft.symm
    _ ≤ _ := hmono
    _ = _ := hright

private theorem caccioppoli_integrated_gradient_cross_bound
    (φ : Vec3 × ℝ → ℝ) (Csp r : ℝ) (W : Vec3 × ℝ → Vec3)
    (D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (hd : Fin 3 → Vec3 × ℝ → ℝ)
    (G : Vec3 × ℝ → ℝ)
    (hcrossInt : ∀ i j : Fin 3, Integrable
      (fun q => hd j q * W q i * D q i j)
      (volume : Measure (Vec3 × ℝ)))
    (hWsqInt : Integrable
      (fun q => (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)))
    (hφGint : Integrable (fun q => φ q * G q)
      (volume : Measure (Vec3 × ℝ)))
    (hpoint : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -∑ i : Fin 3, ∑ j : Fin 3, hd j q * W q i * D q i j ≤
        (1 / 4 : ℝ) * φ q * G q +
          Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2) :
    -(∑ i : Fin 3, ∑ j : Fin 3,
      ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
        ∂(volume : Measure (Vec3 × ℝ))) ≤
      (1 / 4 : ℝ) * (∫ q : Vec3 × ℝ, φ q * G q
        ∂(volume : Measure (Vec3 × ℝ))) +
      Csp / r ^ 2 * (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) := by
  have hcrossTotalInt : Integrable
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3,
        hd j q * W q i * D q i j) (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hcrossInt i j
  have hcrossRightInt : Integrable
      (fun q => (1 / 4 : ℝ) * φ q * G q +
        Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) := by
    have hleft := hφGint.const_mul (1 / 4 : ℝ)
    have hright := hWsqInt.const_mul (Csp / r ^ 2)
    apply (hleft.add hright).congr
    filter_upwards [] with q
    simp only [Pi.add_apply]
    ring
  have hmono := integral_mono_ae hcrossTotalInt.neg hcrossRightInt hpoint
  have hleft :
      (∫ q : Vec3 × ℝ, -∑ i : Fin 3, ∑ j : Fin 3,
        hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ))) =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
          ∂(volume : Measure (Vec3 × ℝ))) := by
    calc
      _ = -(∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
          hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ))) :=
        integral_neg _
      _ = -(∑ i : Fin 3, ∫ q : Vec3 × ℝ,
          ∑ j : Fin 3, hd j q * W q i * D q i j
            ∂(volume : Measure (Vec3 × ℝ))) := by
        congr 1
        exact integral_finsetSum Finset.univ fun i hi =>
          integrable_finsetSum Finset.univ fun j hj => hcrossInt i j
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum Finset.univ fun j hj => hcrossInt i j
  have hright :
      (∫ q : Vec3 × ℝ, (1 / 4 : ℝ) * φ q * G q +
        Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      (1 / 4 : ℝ) * (∫ q : Vec3 × ℝ, φ q * G q
        ∂(volume : Measure (Vec3 × ℝ))) +
      Csp / r ^ 2 * (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) := by
    rw [show (fun q => (1 / 4 : ℝ) * φ q * G q +
          Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2) =
        (fun q => (1 / 4 : ℝ) * (φ q * G q) +
          (Csp / r ^ 2) * (vec3EuclideanNorm (W q)) ^ 2) by funext q; ring,
      integral_add (hφGint.const_mul (1 / 4 : ℝ))
        (hWsqInt.const_mul (Csp / r ^ 2)),
      integral_const_mul, integral_const_mul]
  calc
    _ = ∫ q : Vec3 × ℝ, -∑ i : Fin 3, ∑ j : Fin 3,
          hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ)) := hleft.symm
    _ ≤ _ := hmono
    _ = _ := hright

private theorem caccioppoli_energy_absorption_algebra
    (c₁ Csp Ctime r E N P J S X Y : ℝ)
    (hc₁ : 0 ≤ c₁) (hr : 0 < r)
    (hsource : S ≤ (c₁ + c₁ ^ 2) * P + (1 / 4 : ℝ) * J)
    (hcross : X ≤ (1 / 4 : ℝ) * J + Csp / r ^ 2 * N)
    (htime : Y ≤ Ctime / (2 * r ^ 2) * N)
    (hidentity : E = S + X + Y) (hEJ : E = J) (hphi : P ≤ N) :
    E ≤ 2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) * N := by
  have hweighted : (c₁ + c₁ ^ 2) * P ≤ (c₁ + c₁ ^ 2) * N :=
    mul_le_mul_of_nonneg_left hphi (by positivity)
  have hpre : E ≤
      (c₁ + c₁ ^ 2) * N + Csp / r ^ 2 * N +
        Ctime / (2 * r ^ 2) * N + (1 / 2 : ℝ) * E := by
    linarith only [hsource, hcross, htime, hweighted, hidentity, hEJ]
  calc
    E ≤ 2 * ((c₁ + c₁ ^ 2) * N + Csp / r ^ 2 * N +
        Ctime / (2 * r ^ 2) * N) := by linarith only [hpre]
    _ = 2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) * N := by
      field_simp [ne_of_gt hr]
      ring

private theorem caccioppoli_time_component_integral_bound
    (Ctime r : ℝ) (Q hdt : Vec3 × ℝ → ℝ)
    (components : Fin 3 → Vec3 × ℝ → ℝ)
    (hQint : Integrable Q (volume : Measure (Vec3 × ℝ)))
    (hdtQint : Integrable (fun q => hdt q * Q q)
      (volume : Measure (Vec3 × ℝ)))
    (hQnonneg : ∀ q, 0 ≤ Q q)
    (htime : ∀ q, -Ctime / r ^ 2 ≤ hdt q)
    (hsumEq : (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
        (components i q) ^ 2 * hdt q ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, hdt q * Q q ∂(volume : Measure (Vec3 × ℝ))) :
    -(1 / 2 : ℝ) *
      (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
        (components i q) ^ 2 * hdt q ∂(volume : Measure (Vec3 × ℝ))) ≤
      Ctime / (2 * r ^ 2) *
        (∫ q : Vec3 × ℝ, Q q ∂(volume : Measure (Vec3 × ℝ))) := by
  have htimePoint (q : Vec3 × ℝ) :
      -(1 / 2 : ℝ) * (hdt q * Q q) ≤ Ctime / (2 * r ^ 2) * Q q := by
    have hmul := mul_le_mul_of_nonneg_right (htime q) (hQnonneg q)
    calc
      _ = -(1 / 2 : ℝ) * (hdt q * Q q) := by ring
      _ ≤ -(1 / 2 : ℝ) * ((-Ctime / r ^ 2) * Q q) :=
        mul_le_mul_of_nonpos_left hmul (by norm_num)
      _ = Ctime / (2 * r ^ 2) * Q q := by ring
  have htimeUpperInt : Integrable
      (fun q => Ctime / (2 * r ^ 2) * Q q)
      (volume : Measure (Vec3 × ℝ)) :=
    hQint.const_mul (Ctime / (2 * r ^ 2)) |>.congr
      (Filter.Eventually.of_forall fun q => by ring)
  have hbound := integral_mono_ae
    (hdtQint.const_mul (-(1 / 2 : ℝ))) htimeUpperInt
    (Filter.Eventually.of_forall htimePoint)
  calc
    _ = ∫ q : Vec3 × ℝ, -(1 / 2 : ℝ) * (hdt q * Q q)
        ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [integral_const_mul, hsumEq]
    _ ≤ _ := hbound
    _ = _ := by rw [integral_const_mul]

private theorem caccioppoli_time_sum_identity
    (Q hdt : Vec3 × ℝ → ℝ)
    (components : Fin 3 → Vec3 × ℝ → ℝ)
    (hQ : ∀ q, Q q = ∑ i : Fin 3, (components i q) ^ 2)
    (htermInt : ∀ i : Fin 3, Integrable
      (fun q => (components i q) ^ 2 * hdt q)
      (volume : Measure (Vec3 × ℝ))) :
    (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
      (components i q) ^ 2 * hdt q ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, hdt q * Q q ∂(volume : Measure (Vec3 × ℝ)) := by
  calc
    _ = ∫ q : Vec3 × ℝ, ∑ i : Fin 3,
        (components i q) ^ 2 * hdt q
          ∂(volume : Measure (Vec3 × ℝ)) := by
      symm
      exact integral_finsetSum Finset.univ fun i hi => htermInt i
    _ = ∫ q : Vec3 × ℝ, hdt q * Q q
        ∂(volume : Measure (Vec3 × ℝ)) := by
      congr 1
      funext q
      rw [hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem caccioppoli_zero_extend_memLp
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let U : Set (Vec3 × ℝ) := Ω ×ˢ I
    let W : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
    let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
    let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
    let T : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
    MemLp W 2 (volume : Measure (Vec3 × ℝ)) ∧
      MemLp D 2 (volume : Measure (Vec3 × ℝ)) ∧
      MemLp H 2 (volume : Measure (Vec3 × ℝ)) ∧
      MemLp T 2 (volume : Measure (Vec3 × ℝ)) ∧
      MemLp (fun q => vec3EuclideanNorm (W q)) 2
        (volume : Measure (Vec3 × ℝ)) := by
  classical
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let W : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
  let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
  let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
  let T : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
  have hdata := zeroExtend_spaceTimeData_memLp hΩ hI hderiv hL2
  have hWfun : W = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [W, U, zeroExtendField, hq]
  have hDfun : D = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [D, U, zeroExtendField, hq]
  have hHfun : H = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [H, U, zeroExtendField, hq]
  have hTfun : T = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [T, U, zeroExtendField, hq]
  have hWdata : MemLp W 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hWfun]
    exact hdata.1
  have hDdata : MemLp D 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hDfun]
    exact hdata.2.1
  have hHdata : MemLp H 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hHfun]
    exact hdata.2.2.1
  have hTdata : MemLp T 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hTfun]
    exact hdata.2.2.2
  have hWnorm : MemLp (fun q => vec3EuclideanNorm (W q)) 2
      (volume : Measure (Vec3 × ℝ)) := by
    apply hWdata.norm.of_nnnorm_le_mul (c := 2)
      ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hWdata.aestronglyMeasurable))
    filter_upwards [] with q
    have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have hreal : vec3EuclideanNorm (W q) ≤ 2 * ‖W q‖ := by
      calc
        vec3EuclideanNorm (W q) ≤ Real.sqrt 3 * ‖W q‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
        _ ≤ 2 * ‖W q‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    have hreal' : (‖vec3EuclideanNorm (W q)‖₊ : ℝ) ≤
        2 * (‖‖W q‖‖₊ : ℝ) := by
      simpa only [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (vec3EuclideanNorm_nonneg _),
        abs_of_nonneg (norm_nonneg _)] using hreal
    exact_mod_cast hreal'
  exact ⟨hWdata, hDdata, hHdata, hTdata, hWnorm⟩

private theorem caccioppoli_weighted_gradient_sum
    (φ : Vec3 × ℝ → ℝ) (D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (G : Vec3 × ℝ → ℝ)
    (hG : ∀ q, G q = ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2)
    (htermInt : ∀ i j : Fin 3, Integrable
      (fun q => φ q * (D q i j) ^ 2) (volume : Measure (Vec3 × ℝ))) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
      φ q * (D q i j) ^ 2 ∂(volume : Measure (Vec3 × ℝ))) =
    ∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ)) := by
  calc
    _ = ∑ i : Fin 3, ∫ q : Vec3 × ℝ,
        ∑ j : Fin 3, φ q * (D q i j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      exact integral_finsetSum Finset.univ fun j hj => htermInt i j
    _ = ∫ q : Vec3 × ℝ,
        ∑ i : Fin 3, ∑ j : Fin 3, φ q * (D q i j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
      symm
      apply integral_finsetSum Finset.univ
      intro i hi
      exact integrable_finsetSum Finset.univ fun j hj => htermInt i j
    _ = ∫ q : Vec3 × ℝ, φ q * G q
        ∂(volume : Measure (Vec3 × ℝ)) := by
      congr 1
      funext q
      rw [hG, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

private theorem caccioppoli_product_ae_transfer
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {P : ParabolicPoint → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)), P z) :
    ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)), q ∈ Ω ×ˢ I →
      P (parabolicHomeomorph.symm q) := by
  have hSmeas : MeasurableSet (spaceTimeSet Ω I) :=
    (isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  have hPfull : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ spaceTimeSet Ω I → P z := (ae_restrict_iff' hSmeas).1 hP
  have hmapped : ∀ᵐ q ∂(Measure.map parabolicHomeomorph
      (volume : Measure ParabolicPoint)), q ∈ Ω ×ˢ I →
        P (parabolicHomeomorph.symm q) := by
    apply parabolicHomeomorph.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hPfull] with z hz
    intro hzU
    have hzS : z ∈ spaceTimeSet Ω I := by
      change parabolicHomeomorph z ∈ Ω ×ˢ I at hzU
      change z ∈ Ω ×ˢ I
      exact hzU
    have hmain := hz hzS
    have hinv : parabolicHomeomorph.symm (parabolicHomeomorph z) = z :=
      parabolicHomeomorph.left_inv z
    rw [hinv]
    exact hmain
  rw [parabolicHomeomorph_measurePreserving.map_eq] at hmapped
  exact hmapped

private theorem caccioppoli_cutoff_integral_bounds
    (φ : Vec3 × ℝ → ℝ) (W : Vec3 × ℝ → Vec3)
    (Q : Vec3 × ℝ → ℝ)
    (hφrange : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1)
    (hφWsqInt : Integrable
      (fun q => φ q * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)))
    (hWsqInt : Integrable
      (fun q => (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)))
    (hnormSq : ∀ q, (vec3EuclideanNorm (W q)) ^ 2 = Q q) :
    (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
      ∂(volume : Measure (Vec3 × ℝ))) ≤
        ∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) ∧
      (∫ q : Vec3 × ℝ, Q q ∂(volume : Measure (Vec3 × ℝ))) =
        ∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
  refine ⟨?_, ?_⟩
  · apply integral_mono_ae hφWsqInt hWsqInt
    filter_upwards [] with q
    calc
      φ q * (vec3EuclideanNorm (W q)) ^ 2 ≤
          1 * (vec3EuclideanNorm (W q)) ^ 2 :=
        mul_le_mul_of_nonneg_right (hφrange q).2 (sq_nonneg _)
      _ = _ := by ring
  · apply integral_congr_ae
    filter_upwards [] with q
    exact (hnormSq q).symm

private theorem caccioppoli_localized_energy_identity
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I)
    (G : Vec3 × ℝ → ℝ)
    (hgradSumEq : (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q *
          ((Ω ×ˢ I).indicator
            (fun y => Dw (parabolicHomeomorph.symm y)) q i j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) :
    let U : Set (Vec3 × ℝ) := Ω ×ˢ I
    let W : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
    let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
    let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
    let T : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
    let hd (j : Fin 3) : Vec3 × ℝ → ℝ :=
      fun q => (fderiv ℝ φ q) (basisVec j, 0)
    let hdt : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (0, 1)
    (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
        W q i * T q i * φ q ∂(volume : Measure (Vec3 × ℝ))) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
          ∂(volume : Measure (Vec3 × ℝ))) =
      -(1 / 2 : ℝ) *
        (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
          (W q i) ^ 2 * hdt q ∂(volume : Measure (Vec3 × ℝ))) -
      (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
          ∂(volume : Measure (Vec3 × ℝ))) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let W : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
  let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
  let T : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
  let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
  let hd (j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun q => (fderiv ℝ φ q) (basisVec j, 0)
  let hdt : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (0, 1)
  have hidentity := localizedEnergyIdentity hΩ hI hderiv hL2 hφ hφc hδ₀ hbuffer
  simpa only [W, T, H, D, hd, hdt, U, hgradSumEq] using hidentity

/-- A compactly supported cutoff turns the differential inequality into a weighted
spatial energy estimate (`lem:caccioppoli`). -/
theorem caccioppoliWeightedEnergyBound
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (r c₁ Csp Ctime : ℝ)
    (hr : 0 < r) (hc₁ : 0 ≤ c₁) (hCsp : 0 ≤ Csp)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)))
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I)
    (hφrange : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1)
    (hspatial : ∀ q, ∑ j : Fin 3,
      ((fderiv ℝ φ q) (basisVec j, 0)) ^ 2 ≤ Csp / r ^ 2 * φ q)
    (htime : ∀ q, -Ctime / r ^ 2 ≤ (fderiv ℝ φ q) (0, 1)) :
    let U : Set (Vec3 × ℝ) := Ω ×ˢ I
    let W : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
    let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
    (∫ q : Vec3 × ℝ, φ q *
      (∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2)
      ∂(volume : Measure (Vec3 × ℝ))) ≤
      2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) *
        (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  classical
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let W : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
  let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
  let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
  let T : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
  let G : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2
  let Q : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, (W q i) ^ 2
  let L : Vec3 × ℝ → Vec3 := fun q => fun i => T q i + ∑ j : Fin 3, H q i j j
  have hSmeas : MeasurableSet (spaceTimeSet Ω I) :=
    (isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  obtain ⟨hWdata, hDdata, hHdata, hTdata, hWnorm⟩ :=
    caccioppoli_zero_extend_memLp hΩ hI hderiv hL2
  have hWcomp (i : Fin 3) : MemLp (fun q => W q i) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component hWdata i
  have hDcomp (i j : Fin 3) : MemLp (fun q => D q i j) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component
        (memLp_pi_component hDdata i) j
  have hHcomp (i j k : Fin 3) : MemLp (fun q => H q i j k) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component
        (memLp_pi_component (memLp_pi_component hHdata i) j) k
  have hTcomp (i : Fin 3) : MemLp (fun q => T q i) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component hTdata i
  have hineqProduct := caccioppoli_product_ae_transfer hΩ hI hineq
  have hφbound : ∃ C : NNReal, ∀ q, ‖φ q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound hφ.continuous hφc
  obtain ⟨Cφ, hCφ⟩ := hφbound
  have hφboundReal (q : Vec3 × ℝ) : ‖φ q‖ ≤ Cφ := by
    have hreal : (‖φ q‖₊ : ℝ) ≤ Cφ := by exact_mod_cast hCφ q
    simpa only [coe_nnnorm] using hreal
  have hφmeas : AEStronglyMeasurable φ (volume : Measure (Vec3 × ℝ)) :=
    hφ.continuous.aestronglyMeasurable
  let hd (j : Fin 3) : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (basisVec j, 0)
  let hdt : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (0, 1)
  have hdcont (j : Fin 3) : Continuous (hd j) := by
    dsimp only [hd]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdtcont : Continuous hdt := by
    dsimp only [hdt]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (j : Fin 3) : HasCompactSupport (hd j) := by
    dsimp only [hd]
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j, 0)
  have hdtc : HasCompactSupport hdt := by
    dsimp only [hdt]
    exact hφc.fderiv_apply (𝕜 := ℝ) (0, 1)
  have hdbound (j : Fin 3) : ∃ C : NNReal, ∀ q, ‖hd j q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound (hdcont j) (hdc j)
  have hdtbound : ∃ C : NNReal, ∀ q, ‖hdt q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound hdtcont hdtc
  obtain ⟨Ct, hCt⟩ := hdtbound
  have hdtboundReal (q : Vec3 × ℝ) : ‖hdt q‖ ≤ Ct := by
    have hreal : (‖hdt q‖₊ : ℝ) ≤ Ct := by exact_mod_cast hCt q
    simpa only [coe_nnnorm] using hreal
  have hφGint : Integrable (fun q => φ q * G q) (volume : Measure (Vec3 × ℝ)) := by
    have hGint : Integrable G (volume : Measure (Vec3 × ℝ)) := by
      change Integrable (fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2) _
      exact integrable_finsetSum Finset.univ fun i hi =>
        integrable_finsetSum Finset.univ fun j hj => (hDcomp i j).integrable_sq
    exact hGint.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hWsqInt : Integrable (fun q => (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) := hWnorm.integrable_sq
  have hφWsqInt : Integrable (fun q => φ q * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) :=
    hWsqInt.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hsourceInt (i : Fin 3) : Integrable
      (fun q => φ q * (W q i * T q i)) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hTcomp i)
    exact hbase.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hlapInt (i j : Fin 3) : Integrable
      (fun q => φ q * (W q i * H q i j j)) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hHcomp i j j)
    exact hbase.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have htimeInt (i : Fin 3) : Integrable
      (fun q => hdt q * (W q i) ^ 2) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_sq
    simpa only [mul_comm] using hbase.bdd_mul hdtcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdtboundReal)
  have hcrossInt (i j : Fin 3) : Integrable
      (fun q => hd j q * W q i * D q i j) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hDcomp i j)
    obtain ⟨Cj, hCj⟩ := hdbound j
    have hboundReal (q : Vec3 × ℝ) : ‖hd j q‖ ≤ Cj := by
      have hreal : (‖hd j q‖₊ : ℝ) ≤ Cj := by exact_mod_cast hCj q
      simpa only [coe_nnnorm] using hreal
    have hweighted := hbase.bdd_mul (hdcont j).aestronglyMeasurable
      (Filter.Eventually.of_forall hboundReal)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hLdecomp (q : Vec3 × ℝ) (i : Fin 3) :
      L q i = T q i + ∑ j : Fin 3, H q i j j := by
    rfl
  have hineqGlobal : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      vec3EuclideanNorm (L q) ≤
        c₁ * (vec3EuclideanNorm (W q) + Real.sqrt (G q)) := by
    filter_upwards [hineqProduct] with q hq
    by_cases hqU : q ∈ U
    · simpa only [L, T, H, W, G, D, U, Set.indicator_of_mem hqU,
        spatialGradientSq] using hq hqU
    · have hWzero : W q = 0 := by simp [W, U, hqU]
      have hLzero : L q = 0 := by ext i; simp [L, T, H, U, hqU]
      have hGzero : G q = 0 := by simp [G, D, U, hqU]
      simp only [hWzero, hLzero, hGzero, vec3EuclideanNorm_zero,
        Real.sqrt_zero, add_zero, mul_zero, le_refl]
  have hGnonneg (q : Vec3 × ℝ) : 0 ≤ G q := by
    dsimp [G]
    positivity
  have hsourcePoint := caccioppoli_source_pointwise_bound
    (volume : Measure (Vec3 × ℝ)) c₁ φ W T H L G
    hφrange hGnonneg hLdecomp hineqGlobal
  have hcrossPoint : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -∑ i : Fin 3, ∑ j : Fin 3, hd j q * W q i * D q i j ≤
        (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2 := by
    filter_upwards [] with q
    let d : Fin 3 → ℝ := fun j => hd j q
    have hDsum : ∑ j : Fin 3, d j ^ 2 ≤ Csp / r ^ 2 * φ q := by
      simpa only [d, hd] using hspatial q
    simpa only [d] using caccioppoli_gradient_cross_bound (φ q) Csp r
      (W q) (fun i j => D q i j) d (hφrange q).1 hCsp hr hDsum
  have hQint : Integrable Q (volume : Measure (Vec3 × ℝ)) := by
    change Integrable (fun q => ∑ i : Fin 3, (W q i) ^ 2) _
    exact integrable_finsetSum Finset.univ fun i hi => (hWcomp i).integrable_sq
  have hQnonneg (q : Vec3 × ℝ) : 0 ≤ Q q := by
    dsimp [Q]
    positivity
  have hnormSq (q : Vec3 × ℝ) : (vec3EuclideanNorm (W q)) ^ 2 = Q q := by
    change Real.sqrt (∑ i : Fin 3, (W q i) ^ 2) ^ 2 = _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (W q i))]
  have hdtQint : Integrable (fun q => hdt q * Q q)
      (volume : Measure (Vec3 × ℝ)) := by
    have h := hQint.bdd_mul hdtcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdtboundReal)
    simpa only [mul_comm] using h
  have htimeSumEq := caccioppoli_time_sum_identity Q hdt
    (fun i q => W q i) (by intro q; rfl) (by
      intro i
      simpa only [mul_comm] using htimeInt i)
  have htimeIntegralBound := caccioppoli_time_component_integral_bound
    Ctime r Q hdt (fun i q => W q i) hQint hdtQint hQnonneg htime htimeSumEq
  have hsourceBound := caccioppoli_integrated_source_bound c₁ φ W T H G
    (fun i => by simpa only [mul_comm, mul_left_comm, mul_assoc] using hsourceInt i)
    (fun i j => by simpa only [mul_assoc] using hlapInt i j)
    hφWsqInt hφGint hsourcePoint
  have hcrossBound := caccioppoli_integrated_gradient_cross_bound
    φ Csp r W D hd G hcrossInt hWsqInt hφGint hcrossPoint
  have hgradTermInt (i j : Fin 3) : Integrable
      (fun q => φ q * (D q i j) ^ 2) (volume : Measure (Vec3 × ℝ)) := by
    have h := (hDcomp i j).integrable_sq
    simpa only [mul_comm] using
      h.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hgradSumEq := caccioppoli_weighted_gradient_sum φ D G
    (by intro q; rfl) hgradTermInt
  have henergyIdentity := caccioppoli_localized_energy_identity
    hΩ hI hderiv hL2 hφ hφc hδ₀ hbuffer G hgradSumEq
  have ⟨hphiEnergyBound, hQintegralEq⟩ := caccioppoli_cutoff_integral_bounds
    φ W Q hφrange hφWsqInt hWsqInt hnormSq
  let E : ℝ := ∫ q : Vec3 × ℝ, φ q * G q
    ∂(volume : Measure (Vec3 × ℝ))
  let N : ℝ := ∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
    ∂(volume : Measure (Vec3 × ℝ))
  let P : ℝ := ∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
    ∂(volume : Measure (Vec3 × ℝ))
  let S : ℝ := -(∑ i : Fin 3, ∫ q : Vec3 × ℝ,
      W q i * T q i * φ q ∂(volume : Measure (Vec3 × ℝ))) -
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
      φ q * W q i * H q i j j ∂(volume : Measure (Vec3 × ℝ)))
  let X : ℝ := -(∑ i : Fin 3, ∑ j : Fin 3, ∫ q : Vec3 × ℝ,
    hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ)))
  let Y : ℝ := -(1 / 2 : ℝ) * (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
    (W q i) ^ 2 * hdt q ∂(volume : Measure (Vec3 × ℝ)))
  have hsource : S ≤ (c₁ + c₁ ^ 2) * P + (1 / 4 : ℝ) * E := by
    simpa [S, P, E] using hsourceBound
  have hcross : X ≤ (1 / 4 : ℝ) * E + Csp / r ^ 2 * N := by
    simpa [X, E, N] using hcrossBound
  have htime : Y ≤ Ctime / (2 * r ^ 2) * N := by
    dsimp [Y, N] at htimeIntegralBound ⊢
    rw [hQintegralEq] at htimeIntegralBound
    exact htimeIntegralBound
  have hidentity' : E = S + X + Y := by
    dsimp [E, S, X, Y]
    linarith only [henergyIdentity]
  have henergyBound := caccioppoli_energy_absorption_algebra
    c₁ Csp Ctime r E N P E S X Y hc₁ hr hsource hcross htime
    hidentity' rfl hphiEnergyBound
  exact henergyBound

end ESS
