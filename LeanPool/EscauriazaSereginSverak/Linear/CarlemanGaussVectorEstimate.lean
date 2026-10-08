/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussVector
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreConjugation

/-!
# Componentwise Gaussian conjugation

The scalar gradient comparison from `eq:carleman-gradient-pointwise` is summed
over the three components in `prop:carleman-gauss`.
-/

public section


open CKN CKN.Foundation.Parabolic Set

noncomputable section

namespace ESS

/-- The product norm on parabolic space-time used in this identity. -/
local instance gaussVectorNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance gaussVectorNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The scalar gradient estimate summed over a vector field's components. -/
theorem gauss_vector_gradient_comparison (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (z : ParabolicPoint) (hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Real.exp (gaussCarlemanPhase q z) ^ 2 *
        spatialGradientSq w (spatialGradient w) z ≤
      2 * ((∑ i : Fin 3,
          scalarGradSq (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z) +
        vec3EuclideanNorm
          (fun i => Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
          scalarGradSq (gaussCarlemanPhase q) z) := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  have hcomponent (i : Fin 3) :
      Real.exp (gaussCarlemanPhase q z) ^ 2 *
          scalarGradSq (fun y => w y i) z ≤
        2 * (scalarGradSq
            (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z +
          (Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
            scalarGradSq (gaussCarlemanPhase q) z) := by
    have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun y : ParabolicPoint => w y i) := by
      fun_prop
    exact exp_sq_scalarGradSq_le hU hφ hwi hz
  calc
    Real.exp (gaussCarlemanPhase q z) ^ 2 *
        spatialGradientSq w (spatialGradient w) z =
        ∑ i : Fin 3, Real.exp (gaussCarlemanPhase q z) ^ 2 *
          scalarGradSq (fun y => w y i) z := by
          rw [gauss_spatialGradientSq_eq_sum_scalarGradSq, Finset.mul_sum]
    _ ≤ ∑ i : Fin 3, 2 *
        (scalarGradSq (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z +
          (Real.exp (gaussCarlemanPhase q z) * w z i) ^ 2 *
            scalarGradSq (gaussCarlemanPhase q) z) := by
          apply Finset.sum_le_sum
          intro i _
          exact hcomponent i
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [gauss_vec3EuclideanNorm_sq]

/-- The sum of scalar conjugated heat energies is the weighted vector heat
energy on the positive-time cylinder. -/
theorem gauss_vector_conjugated_heat_sq (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (z : ParabolicPoint) (hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∑ i : Fin 3, carlemanConj (gaussCarlemanPhase q)
      (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) =
      Real.exp (gaussCarlemanPhase q z) ^ 2 *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  have hcomponent (i : Fin 3) :
      carlemanConj (gaussCarlemanPhase q)
          (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z =
        Real.exp (gaussCarlemanPhase q z) *
          (timePartial (fun y => w y i) z +
            scalarLaplacian (fun y => w y i) z) := by
    have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun y : ParabolicPoint => w y i) := by
      fun_prop
    exact carlemanConj_exp_mul hU hφ hwi hz
  rw [gauss_heatVec_norm_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcomponent i]
  ring

/-- The original weighted field and gradient are bounded pointwise by the
conjugated field energy. -/
theorem gauss_vector_weighted_energy_le (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (ha : 0 < a)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (z : ParabolicPoint) (hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
          spatialGradientSq w (spatialGradient w) z) ≤
      Real.exp (2 / 3 : ℝ) *
        ((a + 1) * z.2 *
            vec3EuclideanNorm (fun i =>
              Real.exp (gaussCarlemanPhase (a + 1) z) * w z i) ^ 2 +
          2 * z.2 ^ 2 *
            ((∑ i : Fin 3, scalarGradSq
                (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z) +
              vec3EuclideanNorm (fun i =>
                Real.exp (gaussCarlemanPhase (a + 1) z) * w z i) ^ 2 *
                scalarGradSq (gaussCarlemanPhase (a + 1)) z)) := by
  have ht0 : 0 < z.2 := hz.2.1
  have ht2 : z.2 < 2 := hz.2.2
  let φ := gaussCarlemanPhase (a + 1)
  let B : ℝ := a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
    spatialGradientSq w (spatialGradient w) z
  let N : ℝ := vec3EuclideanNorm (fun i => Real.exp (φ z) * w z i) ^ 2
  let G : ℝ := ∑ i : Fin 3,
    scalarGradSq (fun y => Real.exp (φ y) * w y i) z
  let H : ℝ := scalarGradSq φ z
  have hgradnonneg : 0 ≤ spatialGradientSq w (spatialGradient w) z := by
    unfold spatialGradientSq
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg (div_nonneg (le_of_lt ha) (le_of_lt ht0))
      (sq_nonneg _)) hgradnonneg
  have hW := gauss_weight_le_phase a z ht0 ht2
  have hfirst := mul_le_mul_of_nonneg_right hW hB
  have hgrad := gauss_vector_gradient_comparison (a + 1) w hw z hz
  have hnorm : Real.exp (φ z) ^ 2 * vec3EuclideanNorm (w z) ^ 2 = N := by
    exact (gauss_conjugated_norm_sq φ w z).symm
  have hN : 0 ≤ N := sq_nonneg _
  have haN : a / z.2 * N ≤ (a + 1) / z.2 * N := by
    have hNt : 0 ≤ N / z.2 := div_nonneg hN (le_of_lt ht0)
    have heq : (a + 1) / z.2 * N = a / z.2 * N + N / z.2 := by ring
    rw [heq]
    exact le_add_of_nonneg_right hNt
  have htotal : Real.exp (φ z) ^ 2 * B ≤
      (a + 1) / z.2 * N + 2 * (G + N * H) := by
    calc
      Real.exp (φ z) ^ 2 * B =
          a / z.2 * N + Real.exp (φ z) ^ 2 *
            spatialGradientSq w (spatialGradient w) z := by
              dsimp [B]
              rw [mul_add, ← hnorm]
              ring
      _ ≤ (a + 1) / z.2 * N + 2 * (G + N * H) :=
        add_le_add haN hgrad
  have hexp : Real.exp (2 * φ z) = Real.exp (φ z) ^ 2 := by
    rw [show 2 * φ z = φ z + φ z by ring, Real.exp_add, pow_two]
  have hscale : 0 ≤ Real.exp (2 / 3 : ℝ) * z.2 ^ 2 :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (sq_nonneg _)
  have hsecond := mul_le_mul_of_nonneg_left htotal hscale
  change (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) * B ≤
    Real.exp (2 / 3 : ℝ) * ((a + 1) * z.2 * N + 2 * z.2 ^ 2 * (G + N * H))
  calc
    _ ≤ (Real.exp (2 / 3 : ℝ) *
          (z.2 ^ 2 * Real.exp (2 * φ z))) * B := hfirst
    _ = (Real.exp (2 / 3 : ℝ) * z.2 ^ 2) *
          (Real.exp (φ z) ^ 2 * B) := by rw [hexp]; ring
    _ ≤ (Real.exp (2 / 3 : ℝ) * z.2 ^ 2) *
          ((a + 1) / z.2 * N + 2 * (G + N * H)) := hsecond
    _ = _ := by field_simp [ne_of_gt ht0]

/-- The conjugated heat energy is bounded by the weighted vector heat energy. -/
theorem gauss_vector_operator_energy_le (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (z : ParabolicPoint) (hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    z.2 ^ 2 * (∑ i : Fin 3,
      carlemanConj (gaussCarlemanPhase (a + 1))
        (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z ^ 2) ≤
      Real.exp (2 / 3 : ℝ) *
        ((gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) := by
  rw [gauss_vector_conjugated_heat_sq (a + 1) w hw z hz]
  have hW := gauss_phase_le_weight a z hz.2.1 hz.2.2
  have hexp : Real.exp (2 * gaussCarlemanPhase (a + 1) z) =
      Real.exp (gaussCarlemanPhase (a + 1) z) ^ 2 := by
    rw [show 2 * gaussCarlemanPhase (a + 1) z =
      gaussCarlemanPhase (a + 1) z + gaussCarlemanPhase (a + 1) z by ring,
      Real.exp_add, pow_two]
  rw [hexp] at hW
  have h := mul_le_mul_of_nonneg_right hW (sq_nonneg (vec3EuclideanNorm
    (fun i => timePartial (fun y => w y i) z +
      ∑ j, spatialSecondPartial (fun y => w y i) j j z)))
  convert h using 1 <;> ring

end ESS
