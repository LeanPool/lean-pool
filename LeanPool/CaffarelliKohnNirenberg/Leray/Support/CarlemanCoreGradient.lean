/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreIBP
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# The weighted gradient identity

The space-time integration identity used in `eq:carleman-gradient-integrated` of the
Escauriaza–Seregin–Šverák manuscript
and `eq:carleman-half-gradient-id` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

local instance carlemanCoreGradientMeasureSpace : MeasureSpace ParabolicPoint :=
  Measure.prod.measureSpace

local instance carlemanCoreGradientNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreGradientNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

/-- The time derivative of an integral power of the time coordinate. -/
theorem timePartial_time_pow (m : ℕ) (z : ParabolicPoint) :
    timePartial (fun y : ParabolicPoint => y.2 ^ m) z =
      (m : ℝ) * z.2 ^ (m - 1) := by
  change (fderiv ℝ (fun t : ℝ => t ^ m) z.2) 1 = _
  rw [fderiv_pow_ring]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one, nsmul_eq_mul]

/-- A function of time alone has zero spatial derivative. -/
theorem spatialPartial_time_pow (m : ℕ) (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (fun y : ParabolicPoint => y.2 ^ m) i z = 0 := by
  simp [spatialPartial]

/-- The time derivative of the square of a smooth scalar field. -/
theorem timePartial_sq_at {v : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hv : DifferentiableAt ℝ v z) :
    timePartial (fun y => v y ^ 2) z = 2 * v z * timePartial v z := by
  simp only [pow_two]
  rw [timePartial_mul_at hv hv]
  ring

/-- A spatial derivative of the square of a smooth scalar field. -/
theorem spatialPartial_sq_at {v : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hv : DifferentiableAt ℝ v z) (i : Fin 3) :
    spatialPartial (fun y => v y ^ 2) i z =
      2 * v z * spatialPartial v i z := by
  simp only [pow_two]
  rw [spatialPartial_mul_at hv hv i]
  ring

/-- Time derivative of the weighted square flux. -/
theorem timePartial_time_pow_mul_sq_at
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (z : ParabolicPoint) :
    timePartial (fun y => y.2 ^ m * v y ^ 2) z =
      (m : ℝ) * z.2 ^ (m - 1) * v z ^ 2 +
        2 * z.2 ^ m * v z * timePartial v z := by
  have ht : DifferentiableAt ℝ (fun y : ParabolicPoint => y.2 ^ m) z :=
    by fun_prop
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hmul : timePartial (fun y => y.2 ^ m * v y ^ 2) z =
      timePartial (fun y : ParabolicPoint => y.2 ^ m) z * v z ^ 2 +
        z.2 ^ m * timePartial (fun y => v y ^ 2) z :=
    timePartial_mul_at ht (hvd.pow 2)
  calc
    _ = timePartial (fun y : ParabolicPoint => y.2 ^ m) z * v z ^ 2 +
          z.2 ^ m * timePartial (fun y => v y ^ 2) z := hmul
    _ = _ := by rw [timePartial_time_pow, timePartial_sq_at hvd]; ring

/-- Spatial derivative of the weighted gradient flux. -/
theorem spatialPartial_time_pow_mul_gradient_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z =
      z.2 ^ m * (spatialPartial v i z ^ 2 +
        v z * spatialSecondPartial v i i z) := by
  have ht : DifferentiableAt ℝ (fun y : ParabolicPoint => y.2 ^ m) z :=
    by fun_prop
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hprod : DifferentiableAt ℝ (fun y => y.2 ^ m * v y) z := ht.mul hvd
  have hgrad : DifferentiableAt ℝ (fun y => spatialPartial v i y) z :=
    ((contDiffOn_spatialPartial hU hv.contDiffOn i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  rw [spatialPartial_mul_at hprod hgrad i,
    spatialPartial_mul_at ht hvd i, spatialPartial_time_pow]
  simp only [zero_mul, zero_add]
  unfold spatialSecondPartial
  ring

/-- Spatial derivative of the weighted phase flux. -/
theorem spatialPartial_time_pow_mul_phase_at
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) (i : Fin 3) :
    spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z =
      z.2 ^ m *
        (2 * v z * spatialPartial v i z * spatialPartial φ i z +
          v z ^ 2 * spatialSecondPartial φ i i z) := by
  have ht : DifferentiableAt ℝ (fun y : ParabolicPoint => y.2 ^ m) z :=
    by fun_prop
  have hvd : DifferentiableAt ℝ v z := hv.differentiable (by simp) z
  have hprod : DifferentiableAt ℝ (fun y => y.2 ^ m * v y ^ 2) z :=
    ht.mul (hvd.pow 2)
  have hgrad : DifferentiableAt ℝ (fun y => spatialPartial φ i y) z :=
    ((contDiffOn_spatialPartial hU hφ i).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hinner : spatialPartial (fun y => y.2 ^ m * v y ^ 2) i z =
      spatialPartial (fun y : ParabolicPoint => y.2 ^ m) i z * v z ^ 2 +
        z.2 ^ m * spatialPartial (fun y => v y ^ 2) i z :=
    spatialPartial_mul_at ht (hvd.pow 2) i
  rw [spatialPartial_mul_at hprod hgrad i, hinner,
    spatialPartial_time_pow, spatialPartial_sq_at hvd]
  simp only [zero_mul, zero_add]
  unfold spatialSecondPartial
  ring

private theorem gradient_density_algebra
    (m T R v vt ft : ℝ) (p q r s : Fin 3 → ℝ) :
    T * (∑ i, q i ^ 2) =
      -(m / 2) * R * v ^ 2 -
        T * v * (vt + (∑ i, s i) - 2 * (∑ i, p i * q i) +
          ((∑ i, p i ^ 2) - ft - (∑ i, r i)) * v) +
        T * v ^ 2 * ((∑ i, p i ^ 2) - ft) +
        (1 / 2) * (m * R * v ^ 2 + 2 * T * v * vt) +
        (∑ i, T * (q i ^ 2 + v * s i)) -
        (∑ i, T * (2 * v * q i * p i + v ^ 2 * r i)) := by
  have hspace :
      (∑ i, T * (q i ^ 2 + v * s i)) =
        T * (∑ i, q i ^ 2) + T * v * (∑ i, s i) := by
    calc
      _ = ∑ i, (T * q i ^ 2 + T * v * s i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.mul_sum]
  have hphase :
      (∑ i, T * (2 * v * q i * p i + v ^ 2 * r i)) =
        2 * T * v * (∑ i, p i * q i) + T * v ^ 2 * (∑ i, r i) := by
    calc
      _ = ∑ i, (2 * T * v * (p i * q i) + T * v ^ 2 * r i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.mul_sum]
  rw [hspace, hphase]
  ring

/-- The weighted gradient density differs from the conjugated heat pairing
by space-time derivatives of compactly supported fluxes. -/
theorem carleman_gradient_density
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) :
    z.2 ^ m * scalarGradSq v z =
      -((m : ℝ) / 2) * z.2 ^ (m - 1) * v z ^ 2 -
        z.2 ^ m * v z * carlemanConj φ v z +
        z.2 ^ m * v z ^ 2 * (scalarGradSq φ z - timePartial φ z) +
        (1 / 2) * timePartial (fun y => y.2 ^ m * v y ^ 2) z +
        (∑ i, spatialPartial
          (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) -
        (∑ i, spatialPartial
          (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) := by
  have ht := timePartial_time_pow_mul_sq_at m hv z
  have hs (i : Fin 3) := spatialPartial_time_pow_mul_gradient_at hU m hv hz i
  have hp (i : Fin 3) := spatialPartial_time_pow_mul_phase_at hU m hφ hv hz i
  unfold carlemanConj scalarGradSq scalarLaplacian
  rw [ht]
  simp_rw [hs, hp]
  exact gradient_density_algebra (m : ℝ) (z.2 ^ m) (z.2 ^ (m - 1))
    (v z) (timePartial v z) (timePartial φ z)
    (fun i => spatialPartial φ i z) (fun i => spatialPartial v i z)
    (fun i => spatialSecondPartial φ i i z)
    (fun i => spatialSecondPartial v i i z)

private theorem tsupport_time_pow_mul_sq_subset
    (m : ℕ) (v : ParabolicPoint → ℝ) :
    tsupport (fun y => y.2 ^ m * v y ^ 2) ⊆ tsupport v := by
  have h1 : tsupport (fun y => y.2 ^ m * v y ^ 2) ⊆
      tsupport (fun y => v y ^ 2) := tsupport_mul_subset_right
  have h2 : tsupport (fun y => v y ^ 2) ⊆ tsupport v := by
    simpa only [pow_two] using
      (tsupport_mul_subset_right (f := v) (g := v))
  exact h1.trans h2

private theorem tsupport_time_pow_mul_gradient_subset
    (m : ℕ) (v : ParabolicPoint → ℝ) (i : Fin 3) :
    tsupport (fun y => (y.2 ^ m * v y) * spatialPartial v i y) ⊆
      tsupport v := by
  exact tsupport_mul_subset_left.trans tsupport_mul_subset_right

private theorem tsupport_time_pow_mul_phase_subset
    (m : ℕ) (φ v : ParabolicPoint → ℝ) (i : Fin 3) :
    tsupport (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) ⊆
      tsupport v := by
  exact tsupport_mul_subset_left.trans (tsupport_time_pow_mul_sq_subset m v)

/-- The weighted gradient density identity holds on all space-time when the
field is supported in the phase domain. -/
theorem carleman_gradient_density_global
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvU : tsupport v ⊆ U) (z : ParabolicPoint) :
    z.2 ^ m * scalarGradSq v z =
      -((m : ℝ) / 2) * z.2 ^ (m - 1) * v z ^ 2 -
        z.2 ^ m * v z * carlemanConj φ v z +
        z.2 ^ m * v z ^ 2 * (scalarGradSq φ z - timePartial φ z) +
        (1 / 2) * timePartial (fun y => y.2 ^ m * v y ^ 2) z +
        (∑ i, spatialPartial
          (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) -
        (∑ i, spatialPartial
          (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) := by
  by_cases hz : z ∈ U
  · exact carleman_gradient_density hU m hφ hv hz
  · have hnot : z ∉ tsupport v := fun h => hz (hvU h)
    have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hgrad0 (i : Fin 3) : spatialPartial v i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport hnot i
    have ht0 : timePartial (fun y => y.2 ^ m * v y ^ 2) z = 0 :=
      CKN.timePartial_eq_zero_off_tsupport
        (fun h => hnot (tsupport_time_pow_mul_sq_subset m v h))
    have hs0 (i : Fin 3) :
        spatialPartial
          (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport
        (fun h => hnot (tsupport_time_pow_mul_gradient_subset m v i h)) i
    have hp0 (i : Fin 3) :
        spatialPartial
          (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport
        (fun h => hnot (tsupport_time_pow_mul_phase_subset m φ v i h)) i
    simp [scalarGradSq, hv0, hgrad0, ht0, hs0, hp0]

private theorem contDiff_spatialPartial_of_contDiff
    {v : ParabolicPoint → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => spatialPartial v i z) :=
  contDiffOn_univ.mp (contDiffOn_spatialPartial isOpen_univ hv.contDiffOn i)

private theorem contDiff_timePartial_of_contDiff
    {v : ParabolicPoint → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => timePartial v z) :=
  contDiffOn_univ.mp (contDiffOn_timePartial isOpen_univ hv.contDiffOn)

private theorem contDiff_time_pow_mul_sq
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => z.2 ^ m * v z ^ 2) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 ^ m) := by fun_prop
  exact ht.mul (hv.pow 2)

private theorem hasCompactSupport_time_pow_mul_sq
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hvc : HasCompactSupport v) :
    HasCompactSupport (fun z => z.2 ^ m * v z ^ 2) :=
  hvc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_time_pow_mul_sq_subset m v)

private theorem contDiff_time_pow_mul_gradient
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => (z.2 ^ m * v z) * spatialPartial v i z) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 ^ m) := by fun_prop
  exact (ht.mul hv).mul (contDiff_spatialPartial_of_contDiff hv i)

private theorem hasCompactSupport_time_pow_mul_gradient
    (m : ℕ) {v : ParabolicPoint → ℝ}
    (hvc : HasCompactSupport v) (i : Fin 3) :
    HasCompactSupport
      (fun z => (z.2 ^ m * v z) * spatialPartial v i z) :=
  hvc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_time_pow_mul_gradient_subset m v i)

private theorem contDiff_time_pow_mul_phase
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvU : tsupport v ⊆ U) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => (z.2 ^ m * v z ^ 2) * spatialPartial φ i z) := by
  have hbase := contDiff_time_pow_mul_sq m hv
  have hbaseU : tsupport (fun z => z.2 ^ m * v z ^ 2) ⊆ U :=
    (tsupport_time_pow_mul_sq_subset m v).trans hvU
  have h := contDiff_mul_of_tsupport hU
    (contDiffOn_spatialPartial hU hφ i) hbase hbaseU
  have heq : (fun z => (z.2 ^ m * v z ^ 2) * spatialPartial φ i z) =
      (fun z => spatialPartial φ i z * (z.2 ^ m * v z ^ 2)) := by
    funext z
    ring
  rw [heq]
  exact h

private theorem hasCompactSupport_time_pow_mul_phase
    (m : ℕ) (φ : ParabolicPoint → ℝ) {v : ParabolicPoint → ℝ}
    (hvc : HasCompactSupport v) (i : Fin 3) :
    HasCompactSupport
      (fun z => (z.2 ^ m * v z ^ 2) * spatialPartial φ i z) :=
  hvc.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_time_pow_mul_phase_subset m φ v i)

/-- All three boundary fluxes in the weighted gradient identity integrate to
zero for a field compactly supported in the phase domain. -/
theorem carleman_gradient_flux_integrals_zero
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (m : ℕ) {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z : Vec3 × ℝ,
      timePartial (fun y => y.2 ^ m * v y ^ 2) z ∂volume) = 0 ∧
    (∫ z : Vec3 × ℝ, ∑ i : Fin 3,
      spatialPartial
        (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z ∂volume) = 0 ∧
    (∫ z : Vec3 × ℝ, ∑ i : Fin 3,
      spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z ∂volume) = 0 := by
  have h0 := integral_timePartial_eq_zero
    (contDiff_time_pow_mul_sq m hv)
    (hasCompactSupport_time_pow_mul_sq m hvc)
  have h1 (i : Fin 3) := integral_spatialPartial_eq_zero
    (contDiff_time_pow_mul_gradient m hv i)
    (hasCompactSupport_time_pow_mul_gradient m hvc i) i
  have h2 (i : Fin 3) := integral_spatialPartial_eq_zero
    (contDiff_time_pow_mul_phase hU m hφ hv hvU i)
    (hasCompactSupport_time_pow_mul_phase m φ hvc i) i
  have h1int (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) volume := by
    have hcont : Continuous (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) :=
      (contDiff_spatialPartial_of_contDiff
        (contDiff_time_pow_mul_gradient m hv i) i).continuous
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) :=
      CKN.hasCompactSupport_spatialPartial
        (hasCompactSupport_time_pow_mul_gradient m hvc i) i
    exact hcont.integrable_of_hasCompactSupport hcompact
  have h2int (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) volume := by
    have hcont : Continuous (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) :=
      (contDiff_spatialPartial_of_contDiff
        (contDiff_time_pow_mul_phase hU m hφ hv hvU i) i).continuous
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) :=
      CKN.hasCompactSupport_spatialPartial
        (hasCompactSupport_time_pow_mul_phase m φ hvc i) i
    exact hcont.integrable_of_hasCompactSupport hcompact
  refine ⟨h0, ?_, ?_⟩
  · rw [integral_finsetSum Finset.univ (fun i _ => h1int i)]
    simp only [h1, Finset.sum_const_zero]
  · rw [integral_finsetSum Finset.univ (fun i _ => h2int i)]
    simp only [h2, Finset.sum_const_zero]

private theorem gradient_integral_linear
    {A B C D F₀ F₁ F₂ : ParabolicPoint → ℝ} (c : ℝ)
    (hB : Integrable B volume) (hC : Integrable C volume)
    (hD : Integrable D volume)
    (hF₀ : Integrable F₀ volume) (hF₁ : Integrable F₁ volume)
    (hF₂ : Integrable F₂ volume)
    (hpoint : ∀ z, A z =
      -c * B z - C z + D z + (1 / 2) * F₀ z + F₁ z - F₂ z)
    (hz₀ : (∫ z, F₀ z ∂volume) = 0)
    (hz₁ : (∫ z, F₁ z ∂volume) = 0)
    (hz₂ : (∫ z, F₂ z ∂volume) = 0) :
    (∫ z, A z ∂volume) =
      -c * (∫ z, B z ∂volume) - (∫ z, C z ∂volume) +
        (∫ z, D z ∂volume) := by
  have hbase : Integrable (fun z => -c * B z - C z + D z) volume :=
    ((hB.const_mul (-c)).sub hC).add hD
  have hflux : Integrable (fun z => (1 / 2) * F₀ z + F₁ z - F₂ z) volume :=
    ((hF₀.const_mul (1 / 2)).add hF₁).sub hF₂
  calc
    (∫ z, A z ∂volume) =
        ∫ z, (-c * B z - C z + D z) +
          ((1 / 2) * F₀ z + F₁ z - F₂ z) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [hpoint z]
            ring
    _ = (∫ z, -c * B z - C z + D z ∂volume) +
          (∫ z, (1 / 2) * F₀ z + F₁ z - F₂ z ∂volume) :=
            integral_add hbase hflux
    _ = _ := by
          have he1 : (∫ z, -c * B z - C z + D z ∂volume) =
              (∫ z, -c * B z - C z ∂volume) + (∫ z, D z ∂volume) :=
            integral_add ((hB.const_mul (-c)).sub hC) hD
          have he2 : (∫ z, -c * B z - C z ∂volume) =
              (∫ z, -c * B z ∂volume) - (∫ z, C z ∂volume) :=
            integral_sub (hB.const_mul (-c)) hC
          have he3 : (∫ z, (1 / 2) * F₀ z + F₁ z - F₂ z ∂volume) =
              (∫ z, (1 / 2) * F₀ z + F₁ z ∂volume) - (∫ z, F₂ z ∂volume) :=
            integral_sub ((hF₀.const_mul (1 / 2)).add hF₁) hF₂
          have he4 : (∫ z, (1 / 2) * F₀ z + F₁ z ∂volume) =
              (∫ z, (1 / 2) * F₀ z ∂volume) + (∫ z, F₁ z ∂volume) :=
            integral_add (hF₀.const_mul (1 / 2)) hF₁
          rw [he1, he2, he3, he4, integral_const_mul, integral_const_mul,
            hz₀, hz₁, hz₂]
          ring

/-- A smooth compactly supported scalar field on space-time is integrable. -/
theorem integrable_contDiff_compact
    {f : ParabolicPoint → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) : Integrable f volume := by
  change Integrable (fun z : Vec3 × ℝ => f z) volume
  have h := integrable_mul_of_tsupport isOpen_univ
    (contDiff_const.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : ParabolicPoint => (1 : ℝ)) Set.univ)
    hf hfc (Set.subset_univ _)
  simpa only [one_mul] using h

/-- The integrated weighted gradient identity from
`eq:carleman-gradient-integrated` (ESS). -/
theorem carleman_gradient_identity
    (m : ℕ)
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z, z.2 ^ m * scalarGradSq v z ∂volume) =
      -((m : ℝ) / 2) *
        (∫ z, z.2 ^ (m - 1) * v z ^ 2 ∂volume) -
      (∫ z, z.2 ^ m * v z * carlemanConj φ v z ∂volume) +
      (∫ z, z.2 ^ m * v z ^ 2 *
        (scalarGradSq φ z - timePartial φ z) ∂volume) := by
  let B : ParabolicPoint → ℝ := fun z => z.2 ^ (m - 1) * v z ^ 2
  let C : ParabolicPoint → ℝ := fun z => z.2 ^ m * v z * carlemanConj φ v z
  let D : ParabolicPoint → ℝ := fun z =>
    z.2 ^ m * v z ^ 2 * (scalarGradSq φ z - timePartial φ z)
  let F₀ : ParabolicPoint → ℝ := fun z =>
    timePartial (fun y => y.2 ^ m * v y ^ 2) z
  let F₁ : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, spatialPartial
      (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z
  let F₂ : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, spatialPartial
      (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z
  have hB : Integrable B volume := by
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ =>
        z.2 ^ (m - 1) * v z ^ 2) :=
      hasCompactSupport_time_pow_mul_sq (m - 1) hvc
    exact integrable_contDiff_compact (contDiff_time_pow_mul_sq (m - 1) hv) hcompact
  have hC : Integrable C volume := by
    have ht : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => z.2 ^ m) := by fun_prop
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => z.2 ^ m * v z) := ht.mul hv
    have hcompact : HasCompactSupport
        (fun z => z.2 ^ m * v z) :=
      hvc.isCompact.of_isClosed_subset (isClosed_tsupport _)
        tsupport_mul_subset_right
    have hsubset : tsupport (fun z => z.2 ^ m * v z) ⊆ U :=
      tsupport_mul_subset_right.trans hvU
    have h := integrable_mul_of_tsupport hU
      (contDiffOn_carlemanConj hU hφ hv) hbase hcompact hsubset
    have heq : C = (fun z => carlemanConj φ v z * (z.2 ^ m * v z)) := by
      funext z
      dsimp [C]
      ring
    rw [heq]
    exact h
  have hD : Integrable D volume := by
    have h := integrable_mul_of_tsupport hU
      ((contDiffOn_scalarGradSq hU hφ).sub
        (contDiffOn_timePartial hU hφ))
      (contDiff_time_pow_mul_sq m hv)
      (hasCompactSupport_time_pow_mul_sq m hvc)
      ((tsupport_time_pow_mul_sq_subset m v).trans hvU)
    have heq : D = (fun z =>
        (scalarGradSq φ z - timePartial φ z) * (z.2 ^ m * v z ^ 2)) := by
      funext z
      dsimp [D]
      ring
    rw [heq]
    exact h
  have hF₀ : Integrable F₀ volume := by
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => F₀ z) :=
      CKN.hasCompactSupport_timePartial
        (hasCompactSupport_time_pow_mul_sq m hvc)
    exact integrable_contDiff_compact
      (contDiff_timePartial_of_contDiff (contDiff_time_pow_mul_sq m hv)) hcompact
  have hF₁ : Integrable F₁ volume := by
    apply integrable_finsetSum Finset.univ
    intro i _
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y) * spatialPartial v i y) i z) :=
      CKN.hasCompactSupport_spatialPartial
        (hasCompactSupport_time_pow_mul_gradient m hvc i) i
    exact integrable_contDiff_compact
      (contDiff_spatialPartial_of_contDiff
        (contDiff_time_pow_mul_gradient m hv i) i) hcompact
  have hF₂ : Integrable F₂ volume := by
    apply integrable_finsetSum Finset.univ
    intro i _
    have hcompact : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial
        (fun y => (y.2 ^ m * v y ^ 2) * spatialPartial φ i y) i z) :=
      CKN.hasCompactSupport_spatialPartial
        (hasCompactSupport_time_pow_mul_phase m φ hvc i) i
    exact integrable_contDiff_compact
      (contDiff_spatialPartial_of_contDiff
        (contDiff_time_pow_mul_phase hU m hφ hv hvU i) i) hcompact
  have hz := carleman_gradient_flux_integrals_zero hU m hφ hv hvc hvU
  exact gradient_integral_linear ((m : ℝ) / 2) hB hC hD hF₀ hF₁ hF₂
    (fun z => by
      rw [carleman_gradient_density_global hU m hφ hv hvU z]
      dsimp [B, C, D, F₀, F₁, F₂]
      ring)
    hz.1 hz.2.1 hz.2.2

end CKN
