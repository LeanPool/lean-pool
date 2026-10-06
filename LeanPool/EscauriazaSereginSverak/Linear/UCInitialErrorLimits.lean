/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCInitialErrorMass
public import LeanPool.EscauriazaSereginSverak.Linear.UCDecay

/-!
# Vanishing initial-time Gaussian error

The fourth-root spatial split and all-orders integral flatness make the
weighted initial cutoff term vanish.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

private theorem uc_near_power_tendsto_zero
    (a : ℝ) (N : ℕ) (hN : 2 * a + 2 < (N : ℝ)) :
    Tendsto (fun ε : ℝ => ε ^ (-(2 : ℝ)) *
      (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) * ε ^ N)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let k : ℝ := Real.exp (-(1 / 3 : ℝ)) ^ (-2 * a)
  let p : ℝ := (N : ℝ) - 2 * a - 2
  have hp : 0 < p := by dsimp [p]; linarith only [hN]
  have hbase : 0 ≤ Real.exp (-(1 / 3 : ℝ)) := (Real.exp_pos _).le
  have heq (ε : ℝ) (hε : 0 < ε) :
      ε ^ (-(2 : ℝ)) *
        (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) * ε ^ N =
      k * ε ^ p := by
    rw [Real.mul_rpow hε.le hbase, ← Real.rpow_natCast]
    calc
      ε ^ (-(2 : ℝ)) *
          (ε ^ (-2 * a) * Real.exp (-(1 / 3 : ℝ)) ^ (-2 * a)) *
          ε ^ (N : ℝ) =
        k * (ε ^ (-(2 : ℝ)) * ε ^ (-2 * a) * ε ^ (N : ℝ)) := by
          dsimp [k]
          ring_nf
      _ = k * ε ^ p := by
        rw [← Real.rpow_add hε, ← Real.rpow_add hε]
        congr 1
        dsimp [p]
        ring_nf
  have ht : Tendsto (fun ε : ℝ => ε ^ p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact Filter.Tendsto.rpow_const_nhds_zero
      (tendsto_id.mono_left nhdsWithin_le_nhds) hp
  have ht' : Tendsto (fun ε : ℝ => k * ε ^ p)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (heq ε hε).symm

private theorem uc_far_exponential_tendsto_zero (a : ℝ) :
    Tendsto (fun ε : ℝ => ε ^ (-(2 : ℝ)) *
      (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) *
        Real.exp (-(Real.sqrt ε / (8 * ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let k : ℝ := Real.exp (-(1 / 3 : ℝ)) ^ (-2 * a)
  let p : ℝ := 4 * a + 4
  have hId : Tendsto (id : ℝ → ℝ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
      nhdsWithin_le_nhds
  have ht0 : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hId
  have htpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.sqrt ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Real.sqrt_pos.2 hε
  have ht : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0, htpos⟩
  have hexp := (uc_exp_dominates_inverse_power (1 / 8) p
    (by norm_num)).comp ht
  have heq (ε : ℝ) (hε : 0 < ε) :
      ε ^ (-(2 : ℝ)) *
        (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) *
          Real.exp (-(Real.sqrt ε / (8 * ε))) =
      k * ((Real.sqrt ε) ^ (-p) *
        Real.exp (-((1 / 8 : ℝ) / Real.sqrt ε))) := by
    have hroot : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hrootsq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    have hpower : ε ^ (-(2 : ℝ)) *
        (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) =
        k * (Real.sqrt ε) ^ (-p) := by
      rw [Real.mul_rpow hε.le (Real.exp_pos _).le]
      calc
        ε ^ (-(2 : ℝ)) *
            (ε ^ (-2 * a) * Real.exp (-(1 / 3 : ℝ)) ^ (-2 * a)) =
          k * (ε ^ (-(2 : ℝ)) * ε ^ (-2 * a)) := by
            dsimp [k]
            ring_nf
        _ = k * ε ^ (-(2 * a + 2)) := by
          rw [← Real.rpow_add hε]
          congr 1
          ring_nf
        _ = k * (Real.sqrt ε) ^ (-p) := by
          congr 1
          calc
            ε ^ (-(2 * a + 2)) =
                ((Real.sqrt ε) ^ 2) ^ (-(2 * a + 2)) := by
                  rw [hrootsq]
            _ = (Real.sqrt ε) ^ (2 * (-(2 * a + 2))) := by
                  rw [← Real.rpow_two (Real.sqrt ε), ← Real.rpow_mul hroot.le]
            _ = (Real.sqrt ε) ^ (-p) := by
                  congr 1
                  dsimp [p]
                  ring_nf
    have hexpEq : Real.sqrt ε / (8 * ε) =
        (1 / 8 : ℝ) / Real.sqrt ε := by
      calc
        Real.sqrt ε / (8 * ε) =
            Real.sqrt ε / (8 * (Real.sqrt ε) ^ 2) := by rw [hrootsq]
        _ = (1 / 8 : ℝ) / Real.sqrt ε := by
            field_simp [hroot.ne']
    rw [hpower, hexpEq]
    ring_nf
  have hlimit : Tendsto
      (fun ε : ℝ => k * ((Real.sqrt ε) ^ (-p) *
        Real.exp (-((1 / 8 : ℝ) / Real.sqrt ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    change Tendsto (fun ε : ℝ => (Real.sqrt ε) ^ (-p) *
      Real.exp (-((1 / 8 : ℝ) / Real.sqrt ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) at hexp
    simpa only [mul_zero] using tendsto_const_nhds.mul hexp
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (heq ε hε).symm


/-- Integral flatness makes the weighted initial-time cutoff error vanish
as the transition shrinks to time zero. -/
theorem uc_initial_time_error_tendsto_zero
    (ρ : ℝ) (hρ : 4 ≤ ρ) (a : ℝ) (ha : 0 ≤ a)
    (v : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (ucCylinder ρ) volume)
    (hflat : UCIntegralFlatness 0 ρ 2 v) :
    Tendsto (fun ε : ℝ => ε ^ (-(2 : ℝ)) *
      (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
        ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * a + 2)
  obtain ⟨C, δ, hC, hδ, hmass⟩ :=
    uc_initial_weighted_transition_bound ρ hρ a ha v hInt hflat N
  let V : ℝ := ∫ z in ucCylinder ρ, vec3EuclideanNorm (v z) ^ 2
  let B (ε : ℝ) : ℝ :=
    (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  let near (ε : ℝ) : ℝ :=
    ε ^ (-(2 : ℝ)) * B ε * ε ^ N
  let far (ε : ℝ) : ℝ :=
    ε ^ (-(2 : ℝ)) * B ε *
      Real.exp (-(Real.sqrt ε / (8 * ε)))
  have hNear : Tendsto near (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    uc_near_power_tendsto_zero a N hN
  have hFar : Tendsto far (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    uc_far_exponential_tendsto_zero a
  have hUpper : Tendsto (fun ε : ℝ => C * near ε + V * far ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hNear).add
        (tendsto_const_nhds.mul hFar)
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ ε ^ (-(2 : ℝ)) *
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hSmeas : MeasurableSet
        (spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε))) := by
      change MeasurableSet (vec3Ball 0 ρ ×ˢ Icc ε (2 * ε))
      exact (isOpen_vec3Ball 0 ρ).measurableSet.prod measurableSet_Icc
    have hweightInt : 0 ≤ (∫ z in spaceTimeSet (vec3Ball 0 ρ)
        (Icc ε (2 * ε)),
        ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact mul_nonneg
        (ucGaussianWeight_nonneg a (hε.trans_le hz.2.1))
        (sq_nonneg _)
    exact mul_nonneg (Real.rpow_pos_of_pos hε _).le hweightInt
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ε ^ (-(2 : ℝ)) *
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
        C * near ε + V * far ε := by
    have hδev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < δ :=
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin, hδev] with ε hε hεδ
    let r := Real.sqrt (Real.sqrt ε)
    have hrSq : r ^ 2 = Real.sqrt ε := Real.sq_sqrt (Real.sqrt_nonneg ε)
    have hm := hmass ε hε hεδ
    change (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
      ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
        B ε * (C * ε ^ N +
          Real.exp (-(r ^ 2 / (8 * ε))) * V) at hm
    have hmul : ε ^ (-(2 : ℝ)) *
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
        ε ^ (-(2 : ℝ)) * (B ε * (C * ε ^ N +
          Real.exp (-(r ^ 2 / (8 * ε))) * V)) :=
      mul_le_mul_of_nonneg_left hm
        (Real.rpow_pos_of_pos hε (-(2 : ℝ))).le
    change ε ^ (-(2 : ℝ)) *
      (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
        ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) ≤
      C * near ε + V * far ε
    calc
      _ ≤ ε ^ (-(2 : ℝ)) *
          (B ε * (C * ε ^ N +
            Real.exp (-(r ^ 2 / (8 * ε))) * V)) := hmul
      _ = C * near ε + V * far ε := by
        dsimp [near, far]
        rw [hrSq]
        ring_nf
  exact squeeze_zero' hpos hbound hUpper


end ESS
