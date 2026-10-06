/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessFiniteRankCore

/-!
# Compactness Finite Rank

Supporting estimates for the Navier–Stokes development.
-/

public section
open MeasureTheory
open Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

private theorem ofReal_vec3EuclideanNorm_sq_eq_sum (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v ^ 2) =
      ∑ i, ENNReal.ofReal ((v i) ^ 2) := by
  rw [CKN.vec3EuclideanNorm_sq]
  exact ENNReal.ofReal_sum_of_nonneg (fun i hi => sq_nonneg (v i))

/-- The field-level scalar Poincaré estimates control the vector error from a
ball average by the space-time gradient energy on that ball. -/
theorem lintegral_vec3_ball_average_error_le_of_field_energy
    {U : Set Vec3} {J : Set ℝ} {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u) (hDuMeas : Measurable Du)
    (huenergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (2 : ℝ) ∂volume) < ∞)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (henergy :
      (∫⁻ t in J, ∫⁻ x in U,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞)
    (hball : CKN.euclideanBall x₀ r ⊆ U)
    [IsFiniteMeasure (volume.restrict (CKN.euclideanBall x₀ r))] :
    (∫⁻ t in J, ∫⁻ x in CKN.euclideanBall x₀ r,
      ENNReal.ofReal (vec3EuclideanNorm
        (u (x, t) - (fun i => average
          (volume.restrict (CKN.euclideanBall x₀ r))
            (fun y => u (y, t) i))) ^ 2) ∂volume) ≤
      3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall x₀ r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
    (∫⁻ t in J, ∫⁻ x in CKN.euclideanBall x₀ r,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
  let B : Set Vec3 := CKN.euclideanBall x₀ r
  let avg : ℝ → Vec3 := fun t i =>
    average (volume.restrict B) (fun y => u (y, t) i)
  let e : ParabolicPoint → ℝ≥0∞ := fun z => ENNReal.ofReal
    (vec3EuclideanNorm (u z - avg z.2) ^ 2)
  let f : Fin 3 → ParabolicPoint → ℝ≥0∞ := fun i z =>
    ENNReal.ofReal |u z i - avg z.2 i| ^ (2 : ℝ)
  have hopenB : IsOpen B := by
    simpa [B, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr] using
      CKN.Foundation.Parabolic.isOpen_vec3Ball x₀ r
  have hweakB : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn B (fun x => u (x, t) i)
        (fun x => Du (x, t) i) := by
    filter_upwards [hweak] with t ht i
    exact CKN.HasWeakGradientOn.restrict hopenB hball (ht i)
  have huenergyB :
      (∫⁻ t in J, ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (2 : ℝ) ∂volume) < ∞ := by
    apply lt_of_le_of_lt ?_ huenergy
    apply lintegral_mono
    intro t
    exact lintegral_mono_set hball
  have henergyB :
      (∫⁻ t in J, ∫⁻ x in B,
        ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) < ∞ := by
    apply lt_of_le_of_lt ?_ henergy
    apply lintegral_mono
    intro t
    exact lintegral_mono_set hball
  have hpow (x : ℝ) : ENNReal.ofReal |x| ^ (2 : ℝ) =
      ENNReal.ofReal (x ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num)]
    simp [sq_abs]
  have hpoint (z : ParabolicPoint) : e z = ∑ i, f i z := by
    calc
      e z = ∑ i, ENNReal.ofReal ((u z i - avg z.2 i) ^ 2) := by
        dsimp [e, avg]
        rw [ofReal_vec3EuclideanNorm_sq_eq_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply]
      _ = ∑ i, f i z := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hpow (u z i - avg z.2 i)).symm
  have hfmeas (i : Fin 3) : Measurable (f i) := by
    dsimp [f, avg]
    have hu_i : Measurable (fun z : ParabolicPoint => u z i) :=
      (measurable_pi_apply i).comp huMeas
    have havg_i : Measurable (fun z : ParabolicPoint =>
        average (volume.restrict B) (fun y => u (y, z.2) i)) :=
      (CKN.Foundation.measurable_average_scalar_slice (B := B)
        (fun z : ParabolicPoint => u z i) hu_i).comp measurable_snd
    exact (ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp (hu_i.sub havg_i))).pow_const (2 : ℝ)
  let A : Fin 3 → ℝ → ℝ≥0∞ := fun i t => ∫⁻ x in B, f i (x, t) ∂volume
  have hAmeas (i : Fin 3) : Measurable (A i) := by
    dsimp [A]
    exact (hfmeas i).lintegral_prod_left'
  have hinner (t : ℝ) :
      (∫⁻ x in B, e (x, t) ∂volume) = ∑ i, A i t := by
    calc
      (∫⁻ x in B, e (x, t) ∂volume) =
          ∫⁻ x in B, ∑ i, f i (x, t) ∂volume := by
        apply lintegral_congr
        intro x
        exact hpoint (x, t)
      _ = ∑ i, A i t := by
        simpa [A] using (lintegral_finsetSum' (μ := volume.restrict B)
          Finset.univ (f := fun i x => f i (x, t))
          (fun i hi =>
            ((hfmeas i).comp measurable_prodMk_right).aemeasurable.restrict))
  have htotal :
      (∫⁻ t in J, ∫⁻ x in B, e (x, t) ∂volume) =
        ∑ i, ∫⁻ t in J, A i t ∂volume := by
    calc
      (∫⁻ t in J, ∫⁻ x in B, e (x, t) ∂volume) =
          ∫⁻ t in J, ∑ i, A i t ∂volume := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = ∑ i, ∫⁻ t in J, A i t ∂volume := by
        simpa using (lintegral_finsetSum' (μ := volume.restrict J)
          Finset.univ (f := fun i t => A i t)
          (fun i hi => (hAmeas i).aemeasurable.restrict))
  let C : ℝ≥0∞ := CKN.sobolevPoincareL6Constant *
    (volume B) ^ (1 / 3 : ℝ)
  have hcomponent (i : Fin 3) :
      (∫⁻ t in J, A i t ∂volume) ≤ C ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ x in B, ‖Du (x, t) i‖ₑ ^ (2 : ℝ) ∂volume) := by
    have h := CKN.Foundation.lintegral_component_ball_average_error_le_of_field_energy
      hr u Du huMeas hDuMeas huenergyB hweakB henergyB (subset_rfl) i
    simpa [A, f, avg, C, B] using h
  have hgradPoint (z : ParabolicPoint) (i : Fin 3) :
      ‖Du z i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (CKN.spatialGradientSq u Du z) := by
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hnorm := norm_le_vec3EuclideanNorm (Du z i)
    have hnormSq : ‖Du z i‖ ^ (2 : ℝ) ≤
        vec3EuclideanNorm (Du z i) ^ (2 : ℝ) := by
      rw [Real.rpow_two, Real.rpow_two]
      nlinarith only [norm_nonneg (Du z i), hnorm]
    have hrow : ∑ j, (Du z i j) ^ 2 ≤
        ∑ k, ∑ j, (Du z k j) ^ 2 :=
      Finset.single_le_sum (fun k hk => Finset.sum_nonneg
        fun j hj => sq_nonneg (Du z k j)) (Finset.mem_univ i)
    calc
      ‖Du z i‖ ^ (2 : ℝ) ≤ vec3EuclideanNorm (Du z i) ^ (2 : ℝ) := hnormSq
      _ = ∑ j, (Du z i j) ^ 2 := by
        rw [Real.rpow_two, CKN.vec3EuclideanNorm_sq]
      _ ≤ ∑ k, ∑ j, (Du z k j) ^ 2 := hrow
      _ = CKN.spatialGradientSq u Du z := rfl
  have hgradIntegral (i : Fin 3) :
      (∫⁻ t in J, ∫⁻ x in B, ‖Du (x, t) i‖ₑ ^ (2 : ℝ) ∂volume) ≤
        (∫⁻ t in J, ∫⁻ x in B,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
    apply lintegral_mono
    intro t
    calc
      (∫⁻ x in B, ‖Du (x, t) i‖ₑ ^ (2 : ℝ) ∂volume) ≤
          ∫⁻ x in B, ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume := by
        apply lintegral_mono
        intro x
        exact hgradPoint (x, t) i
      _ ≤ ∫⁻ x in B,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume := le_rfl
  calc
    (∫⁻ t in J, ∫⁻ x in B, e (x, t) ∂volume) =
        ∑ i, ∫⁻ t in J, A i t ∂volume := htotal
    _ ≤ ∑ i, C ^ (2 : ℕ) *
          (∫⁻ t in J, ∫⁻ x in B, ‖Du (x, t) i‖ₑ ^ (2 : ℝ) ∂volume) :=
        Finset.sum_le_sum fun i hi => hcomponent i
    _ ≤ ∑ i, C ^ (2 : ℕ) *
          (∫⁻ t in J, ∫⁻ x in B,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hgradIntegral i) (by positivity)
    _ = 3 * C ^ (2 : ℕ) *
          (∫⁻ t in J, ∫⁻ x in B,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (x, t)) ∂volume) := by
        simp [C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_assoc]

/-- The finite-rank approximation error is bounded by the sum of the
space-time gradient energies on the balls of the cover. -/
theorem lintegral_vec3_finite_rank_average_error_le_of_field_energy
    {ι : Type*} [Fintype ι] {U : Set Vec3} {J : Set ℝ} {K : Set Vec3}
    {x : ι → Vec3} {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u) (hDuMeas : Measurable Du)
    (huenergy : (∫⁻ t in J, ∫⁻ y in U,
      ENNReal.ofReal (vec3EuclideanNorm (u (y,t))) ^ (2 : ℝ) ∂volume) < ∞)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun y => u (y,t) i) (fun y => Du (y,t) i))
    (henergy : (∫⁻ t in J, ∫⁻ y in U,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) < ∞)
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hweight : ∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1)
    (hsum : ∀ y ∈ K, ∑ i, φ i y = 1)
    (hcover : ∀ i, CKN.euclideanBall (x i) r ⊆ U)
    (hsupport : ∀ i y, φ i y ≠ 0 → y ∈ CKN.euclideanBall (x i) r) :
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u z - ∑ i, φ i z.1 • (fun j => average
        (volume.restrict (CKN.euclideanBall (x i) r))
          (fun y => u (y,z.2) j))) ^ 2)
      ∂(volume : Measure ParabolicPoint)) ≤
      ∑ i, 3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (x i) r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ y in CKN.euclideanBall (x i) r,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) := by
  let B : ι → Set Vec3 := fun i => CKN.euclideanBall (x i) r
  let a : ι → ℝ → Vec3 := fun i t j => average (volume.restrict (B i))
    (fun y => u (y,t) j)
  have ha : ∀ i, Measurable (a i) := by
    intro i
    apply measurable_pi_iff.mpr
    intro j
    have hu_j : Measurable (fun z : ParabolicPoint => u z j) :=
      (measurable_pi_apply j).comp huMeas
    exact CKN.Foundation.measurable_average_scalar_slice
      (B := B i) (fun z : ParabolicPoint => u z j) hu_j
  have hballMeas : ∀ i, MeasurableSet (B i) := by
    intro i
    have hopen : IsOpen (B i) := by
      simpa [B, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr] using
        CKN.Foundation.Parabolic.isOpen_vec3Ball (x i) r
    exact hopen.measurableSet
  have happrox := lintegral_vec3_finite_rank_average_error_le_unweighted
    (μ := (volume : Measure ParabolicPoint)) J K B φ u a hJ hK hballMeas
    hφ huMeas ha hweight hsum hsupport
  have hlocal (i : ι) :
      (∫⁻ z in B i ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
        (u z - a i z.2) ^ 2) ∂(volume : Measure ParabolicPoint)) ≤
        3 * (CKN.sobolevPoincareL6Constant *
          (volume (B i)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
          (∫⁻ t in J, ∫⁻ y in B i,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) := by
    have hvol : volume (B i) < ∞ := by
      change volume (CKN.euclideanBall (x i) r) < ∞
      rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr]
      exact (measure_mono subset_closure).trans_lt
        (CKN.Foundation.Parabolic.measure_closure_vec3Ball_lt_top hr)
    have hfinite : IsFiniteMeasure (volume.restrict (B i)) :=
      isFiniteMeasure_restrict.mpr (ne_of_lt hvol)
    have herrMeas : Measurable (fun z : ParabolicPoint =>
        ENNReal.ofReal (vec3EuclideanNorm (u z - a i z.2) ^ 2)) := by
      exact ENNReal.measurable_ofReal.comp <|
        ((continuous_vec3EuclideanNorm.measurable.comp
          (huMeas.sub ((ha i).comp measurable_snd))).pow_const 2)
    rw [lintegral_parabolic_rectangle_eq_iterated (K := B i) (J := J) _ herrMeas]
    simpa [a, B] using lintegral_vec3_ball_average_error_le_of_field_energy
      (U := U) hr u Du huMeas hDuMeas huenergy hweak henergy (hcover i)
  calc
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u z - ∑ i, φ i z.1 • a i z.2) ^ 2)
        ∂(volume : Measure ParabolicPoint)) ≤
        ∑ i, ∫⁻ z in B i ×ˢ J,
          ENNReal.ofReal (vec3EuclideanNorm (u z - a i z.2) ^ 2)
            ∂(volume : Measure ParabolicPoint) := by
      simpa [B, a] using happrox
    _ ≤ ∑ i, 3 * (CKN.sobolevPoincareL6Constant *
          (volume (B i)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
          (∫⁻ t in J, ∫⁻ y in B i,
            ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) :=
      Finset.sum_le_sum fun i hi => hlocal i

/-- Combining the ball Poincaré estimate with a bounded-overlap coloring gives
a uniform error bound for the finite-rank average on the compact region. -/
theorem lintegral_vec3_finite_rank_average_error_le_of_colored_cover
    {ι : Type*} [Fintype ι] {N : ℕ} {U : Set Vec3} {J : Set ℝ}
    {K : Set Vec3} {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u) (hDuMeas : Measurable Du)
    (huenergy : (∫⁻ t in J, ∫⁻ y in U,
      ENNReal.ofReal (vec3EuclideanNorm (u (y,t))) ^ (2 : ℝ) ∂volume) < ∞)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun y => u (y,t) i) (fun y => Du (y,t) i))
    (henergy : (∫⁻ t in J, ∫⁻ y in U,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) < ∞)
    (hK : MeasurableSet K) (hJ : MeasurableSet J)
    (x : ι → Vec3) (color : ι → Fin N)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hweight : ∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1)
    (hsum : ∀ y ∈ K, ∑ i, φ i y = 1)
    (hball : ∀ i, CKN.euclideanBall (x i) r ⊆ U)
    (hsupport : ∀ i y, φ i y ≠ 0 → y ∈ CKN.euclideanBall (x i) r)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (CKN.euclideanBall (x i) r) (CKN.euclideanBall (x j) r)) :
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u z - ∑ i, φ i z.1 • (fun j => average
        (volume.restrict (CKN.euclideanBall (x i) r))
          (fun y => u (y,z.2) j))) ^ 2)
      ∂(volume : Measure ParabolicPoint)) ≤
      3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∑ _j : Fin N, ∫⁻ t in J, ∫⁻ y in U,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) := by
  let B : ι → Set Vec3 := fun i => CKN.euclideanBall (x i) r
  let q : ParabolicPoint → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (CKN.spatialGradientSq u Du z)
  have hBmeas : ∀ i, MeasurableSet (B i) := by
    intro i
    have hopen : IsOpen (B i) := by
      simpa [B, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr] using
        CKN.Foundation.Parabolic.isOpen_vec3Ball (x i) r
    exact hopen.measurableSet
  have hqmeas : Measurable q := by
    dsimp [q]
    exact ENNReal.measurable_ofReal.comp <| by
      unfold CKN.spatialGradientSq
      fun_prop
  have hcolors := sum_lintegral_ball_gradient_energy_le_of_coloring
    (J := J) B color q hBmeas hball hdisjoint hqmeas
  have hsumErr := lintegral_vec3_finite_rank_average_error_le_of_field_energy
    (U := U) (J := J) (K := K) (x := x) hr u Du huMeas hDuMeas huenergy
    hweak henergy hK hJ φ hφ hweight hsum hball hsupport
  have hvolume (i : ι) : volume (B i) = volume (CKN.euclideanBall (0 : Vec3) r) := by
    change volume (CKN.euclideanBall (x i) r) = volume (CKN.euclideanBall (0 : Vec3) r)
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr,
      CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hr,
      CKN.Foundation.Parabolic.volume_vec3Ball]
  let C : ℝ≥0∞ := CKN.sobolevPoincareL6Constant *
    (volume (CKN.euclideanBall (0 : Vec3) r)) ^ (1 / 3 : ℝ)
  have hsumFactor :
      (∑ i, 3 * (CKN.sobolevPoincareL6Constant *
        (volume (B i)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ y in B i,
          q (y,t) ∂volume ∂volume)) =
        3 * C ^ (2 : ℕ) *
          (∑ i, ∫⁻ t in J, ∫⁻ y in B i, q (y,t) ∂volume ∂volume) := by
    simp_rw [hvolume, C]
    rw [← Finset.mul_sum]
  calc
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u z - ∑ i, φ i z.1 • (fun j => average
        (volume.restrict (CKN.euclideanBall (x i) r))
          (fun y => u (y,z.2) j))) ^ 2)
      ∂(volume : Measure ParabolicPoint)) ≤
      ∑ i, 3 * (CKN.sobolevPoincareL6Constant *
        (volume (B i)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∫⁻ t in J, ∫⁻ y in B i,
          q (y,t) ∂volume ∂volume) := by
      simpa [B, q] using hsumErr
    _ = 3 * C ^ (2 : ℕ) *
        (∑ i, ∫⁻ t in J, ∫⁻ y in B i, q (y,t) ∂volume ∂volume) := hsumFactor
    _ ≤ 3 * C ^ (2 : ℕ) *
        (∑ _j : Fin N, ∫⁻ t in J, ∫⁻ y in U,
          q (y,t) ∂volume ∂volume) := by
      gcongr
    _ = 3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∑ _j : Fin N, ∫⁻ t in J, ∫⁻ y in U,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume ∂volume) := by
      simp only [C, q]

/-- The finite-rank estimate uses a uniform velocity slice bound and an
integrated gradient bound, as in the local compactness hypothesis. -/
theorem lintegral_vec3_finite_rank_average_error_le_of_mixed_bounds
    {ι : Type*} [Fintype ι] {N : ℕ} {W Kc K : Set Vec3} {J : Set ℝ} {r : ℝ}
    (hr : 0 < r) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (huMeas : Measurable u) (hDuMeas : Measurable Du)
    (hweak : ∀ᵐ t ∂(volume.restrict J), ∀ i : Fin 3,
      CKN.HasWeakGradientOn W (fun y => u (y,t) i) (fun y => Du (y,t) i))
    (hJ : MeasurableSet J) [IsFiniteMeasure (volume.restrict J)]
    (M G : ℝ≥0∞) (hM : M < ⊤) (hG : G < ⊤)
    (hWKc : W ⊆ Kc)
    (huBound : ∀ t ∈ J, ∫⁻ x in Kc,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (2 : ℝ) ∂volume ≤ M)
    (hDuBound : (∫⁻ t in J, ∫⁻ x in Kc,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (x,t)) ∂volume) ≤ G)
    (hK : MeasurableSet K)
    (x : ι → Vec3) (color : ι → Fin N)
    (φ : ι → Vec3 → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hweight : ∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1)
    (hsum : ∀ y ∈ K, ∑ i, φ i y = 1)
    (hball : ∀ i, CKN.euclideanBall (x i) r ⊆ W)
    (hsupport : ∀ i y, φ i y ≠ 0 → y ∈ CKN.euclideanBall (x i) r)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (CKN.euclideanBall (x i) r) (CKN.euclideanBall (x j) r)) :
    (∫⁻ z in K ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm
      (u z - ∑ i, φ i z.1 • (fun j => average
        (volume.restrict (CKN.euclideanBall (x i) r))
          (fun y => u (y,z.2) j))) ^ 2)
      ∂(volume : Measure ParabolicPoint)) ≤
      3 * (CKN.sobolevPoincareL6Constant *
        (volume (CKN.euclideanBall (0 : Vec3) r)) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) *
        (∑ _j : Fin N, ∫⁻ t in J, ∫⁻ y in W,
          ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) := by
  have humeas : Measurable (fun z : ParabolicPoint =>
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ)) := by
    have hnorm : Measurable (fun z : ParabolicPoint =>
        vec3EuclideanNorm (u z)) := by
      unfold vec3EuclideanNorm
      fun_prop
    fun_prop
  have huenergy : (∫⁻ t in J, ∫⁻ y in W,
      ENNReal.ofReal (vec3EuclideanNorm (u (y,t))) ^ (2 : ℝ) ∂volume) < ⊤ := by
    apply lt_of_le_of_lt ?_
      (finite_lintegral_prod_of_uniform_slice_bound
        (K := Kc) (J := J) _ humeas hJ M hM huBound)
    apply lintegral_mono
    intro t
    exact lintegral_mono_set hWKc
  have hgradenergy : (∫⁻ t in J, ∫⁻ y in W,
      ENNReal.ofReal (CKN.spatialGradientSq u Du (y,t)) ∂volume) < ⊤ := by
    apply lt_of_le_of_lt ?_ (lt_of_le_of_lt hDuBound hG)
    apply lintegral_mono
    intro t
    exact lintegral_mono_set hWKc
  exact lintegral_vec3_finite_rank_average_error_le_of_colored_cover
    hr u Du huMeas hDuMeas huenergy hweak hgradenergy hK hJ x color φ hφ
    hweight hsum hball hsupport hdisjoint



end CKN.Leray
