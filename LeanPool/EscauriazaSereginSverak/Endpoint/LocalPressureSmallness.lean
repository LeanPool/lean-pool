/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthLocalBox
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationHarmonic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PressureDecompositionRiesz
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryFaithful
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsAE
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceProductMeasurability
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Local Pressure Smallness

Local pressure estimates used in the endpoint regularity argument.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic.Integration


private theorem closure_parabolicCylinder_subset_metricBall
    {z : ParabolicPoint} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hρδ : ρ < δ) :
    closure (parabolicCylinder z.1 z.2 ρ) ⊆ Metric.ball z δ := by
  intro q hq
  rw [closure_parabolicCylinder hρ] at hq
  rcases hq with ⟨hspace, ht⟩
  rcases ht with ⟨htlo, hthi⟩
  have htime : |q.2 - z.2| ≤ ρ ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [htlo, hthi]
  have htimeRoot : Real.sqrt |q.2 - z.2| ≤ ρ := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hρ.le
    · nlinarith only [htime]
  rw [Metric.mem_ball, dist_eq_parabolicDist, parabolicDist]
  apply max_lt_iff.mpr
  constructor
  · exact hspace.trans_lt hρδ
  · exact htimeRoot.trans_lt hρδ

private theorem lpNorm_threeHalves_le_lpNorm_two_on_ball
    {f : Vec3 → ℝ} {x : Vec3} {r : ℝ}
    (hf : MemLp f 2 volume)
    (hfmeas : AEStronglyMeasurable f (volume.restrict (vec3Ball x r))) :
    lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball x r)) ≤
      lpNorm f 2 volume * (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x r)
  have hballtop : volume (vec3Ball x r) < ∞ := volume_vec3Ball_lt_top
  have hμtop : μ Set.univ < ∞ := by
    change (volume.restrict (vec3Ball x r)) Set.univ < ∞
    rw [Measure.restrict_apply_univ (vec3Ball x r)]
    exact hballtop
  let : IsFiniteMeasure μ := ⟨hμtop⟩
  have hlow : eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      eLpNorm f 2 μ * μ Set.univ ^
        (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hfmeas
  have htwo : eLpNorm f 2 μ ≤ eLpNorm f 2 volume :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  have htop : (eLpNorm f 2 μ * μ Set.univ ^
      (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal - 1 / (2 : ℝ≥0∞).toReal)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact (hf.mono_measure Measure.restrict_le_self).eLpNorm_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · norm_num
      · exact hμtop.ne
  change (eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal ≤ _
  calc
    (eLpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ).toReal ≤
        (eLpNorm f 2 μ * μ Set.univ ^
          (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal :=
      ENNReal.toReal_mono htop hlow
    _ ≤ (eLpNorm f 2 volume).toReal *
        (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) := by
      rw [ENNReal.toReal_mul]
      rw [← ENNReal.toReal_rpow]
      have hfactor : (1 / (ENNReal.ofReal (3 / 2 : ℝ)).toReal -
            1 / (2 : ℝ≥0∞).toReal) = (1 / 6 : ℝ) := by norm_num
      have hmeasure : (μ Set.univ).toReal =
          (volume (vec3Ball x r)).toReal := by
        simp [μ]
      rw [hfactor, hmeasure]
      have htwoReal : (eLpNorm f 2 μ).toReal ≤ (eLpNorm f 2 volume).toReal :=
        ENNReal.toReal_mono (hf.eLpNorm_ne_top) htwo
      have hvolnonneg : 0 ≤ (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) := by positivity
      calc
        (eLpNorm f 2 μ).toReal * (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) ≤
            (eLpNorm f 2 volume).toReal * (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) :=
          mul_le_mul_of_nonneg_right htwoReal hvolnonneg
        _ = lpNorm f 2 volume * (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ) := rfl

private theorem pressure_average_component_abs_le
    {u : ParabolicPoint → Vec3} {x : Vec3} {ρ s H : ℝ}
    (hρ : 0 < ρ)
    (hUmeas : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x ρ)))
    (hUbound : ∀ᵐ y ∂volume.restrict (vec3Ball x ρ),
      vec3EuclideanNorm (u (y, s)) ≤ H) :
    ∀ j : Fin 3,
      |average (volume.restrict (vec3Ball x ρ))
        (fun y : Vec3 => u (y, s) j)| ≤ H := by
  let B : Set Vec3 := vec3Ball x ρ
  let μ : Measure Vec3 := volume.restrict B
  have hBpos : 0 < volume B := by
    dsimp [B]
    exact volume_vec3Ball_pos hρ
  have hBtop : volume B < ∞ := by
    dsimp [B]
    exact volume_vec3Ball_lt_top
  have hμtop : μ Set.univ < ∞ := by
    change (volume.restrict B) Set.univ < ∞
    rw [Measure.restrict_apply_univ B]
    exact hBtop
  let : IsFiniteMeasure μ := ⟨hμtop⟩
  intro j
  have hcompMeas : AEStronglyMeasurable (fun y : Vec3 => u (y, s) j) μ :=
    ((measurable_pi_apply j).comp_aemeasurable hUmeas.aemeasurable).aestronglyMeasurable
  have hcompBound : ∀ᵐ y ∂μ, ‖u (y, s) j‖ ≤ H := by
    filter_upwards [hUbound] with y hy
    simpa only [Real.norm_eq_abs] using
      (abs_apply_le_vec3EuclideanNorm (u (y, s)) j).trans hy
  have habsMeas : AEStronglyMeasurable
      (fun y : Vec3 => |u (y, s) j|) μ :=
    continuous_abs.comp_aestronglyMeasurable hcompMeas
  have hcompInt : Integrable (fun y : Vec3 => |u (y, s) j|) μ := by
    apply Integrable.of_bound habsMeas H
    filter_upwards [hcompBound] with y hy
    simpa only [Real.norm_eq_abs, abs_abs] using hy
  have hconstInt : Integrable (fun _ : Vec3 => H) μ := integrable_const H
  have hmono : (⨍ y in B, |u (y, s) j| ∂volume) ≤
      ⨍ y in B, H ∂volume := by
    exact setAverage_mono_of_ae hcompInt hconstInt (by
      filter_upwards [hUbound] with y hy
      exact (abs_apply_le_vec3EuclideanNorm (u (y, s)) j).trans hy)
  have hnormAvg : |average μ (fun y : Vec3 => u (y, s) j)| ≤
      ⨍ y in B, |u (y, s) j| ∂volume := by
    simpa [μ, B, Real.norm_eq_abs] using
      (setAverage_norm_le volume B (fun y : Vec3 => u (y, s) j))
  have hconst : (⨍ y in B, H ∂volume) = H :=
    setAverage_const_of_pos_of_lt_top hBpos hBtop H
  calc
    |average μ (fun y : Vec3 => u (y, s) j)| ≤
        ⨍ y in B, |u (y, s) j| ∂volume := hnormAvg
    _ ≤ ⨍ y in B, H ∂volume := hmono
    _ = H := hconst

private theorem memLp_threeHalves_restrict_ball_of_memLp_two
    {f : Vec3 → ℝ} {x : Vec3} {r : ℝ}
    (hf : MemLp f 2 volume) :
    MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x r)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x r)
  have hμtop : μ Set.univ < ∞ := by
    change (volume.restrict (vec3Ball x r)) Set.univ < ∞
    rw [Measure.restrict_apply_univ (vec3Ball x r)]
    exact volume_vec3Ball_lt_top
  let : IsFiniteMeasure μ := ⟨hμtop⟩
  exact (hf.mono_measure Measure.restrict_le_self).mono_exponent (by norm_num)

private theorem integral_abs_rpow_threeHalves_le_of_memLp_two
    {f : Vec3 → ℝ} {x : Vec3} {r : ℝ}
    (hf : MemLp f 2 volume) :
    ∫ y in vec3Ball x r, |f y| ^ (3 / 2 : ℝ) ≤
      (lpNorm f 2 volume) ^ (3 / 2 : ℝ) *
        (volume (vec3Ball x r)).toReal ^ (1 / 4 : ℝ) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x r)
  have hμtop : μ Set.univ < ∞ := by
    change (volume.restrict (vec3Ball x r)) Set.univ < ∞
    rw [Measure.restrict_apply_univ (vec3Ball x r)]
    exact volume_vec3Ball_lt_top
  let : IsFiniteMeasure μ := ⟨hμtop⟩
  have hf32 := memLp_threeHalves_restrict_ball_of_memLp_two
    (x := x) (r := r) hf
  have hnorm := lpNorm_threeHalves_le_lpNorm_two_on_ball hf hf32.aestronglyMeasurable
  have hIntegral := CKN.integral_rpow_norm_eq_lpNorm_rpow
    (by norm_num) (by norm_num) hf32
  have hIntegral' : (∫ y in vec3Ball x r, |f y| ^ (3 / 2 : ℝ)) =
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ^ (3 / 2 : ℝ) := by
    simpa [μ, Real.norm_eq_abs,
      ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 2 : ℝ))] using hIntegral
  have hpnonneg : 0 ≤ lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ := lpNorm_nonneg
  have hvolnonneg : 0 ≤ (volume (vec3Ball x r)).toReal := by positivity
  calc
    ∫ y in vec3Ball x r, |f y| ^ (3 / 2 : ℝ) =
        lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ^ (3 / 2 : ℝ) := hIntegral'
    _ ≤ (lpNorm f 2 volume * (volume (vec3Ball x r)).toReal ^ (1 / 6 : ℝ)) ^
        (3 / 2 : ℝ) := Real.rpow_le_rpow hpnonneg hnorm (by norm_num)
    _ = (lpNorm f 2 volume) ^ (3 / 2 : ℝ) *
        (volume (vec3Ball x r)).toReal ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (lpNorm_nonneg) (Real.rpow_nonneg hvolnonneg _),
        ← Real.rpow_mul hvolnonneg]
      norm_num

private theorem rpow_add_threeHalves_le
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (3 / 2 : ℝ) ≤ 2 * (a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ)) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a b
    (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have h2 : (2 : ℝ≥0) ^ ((3 / 2 : ℝ) - 1) ≤ 2 := by
    simpa only [show ((3 / 2 : ℝ) - 1) = (1 / 2 : ℝ) by norm_num,
      NNReal.rpow_one] using
      (NNReal.rpow_le_rpow_of_exponent_le
        (x := (2 : ℝ≥0)) (y := (1 / 2 : ℝ)) (z := (1 : ℝ))
        (by norm_num) (by norm_num))
  have hsum : 0 ≤ a ^ (3 / 2 : ℝ) + b ^ (3 / 2 : ℝ) := by positivity
  have h' := mul_le_mul_of_nonneg_right h2 hsum
  have h'' := le_trans h h'
  norm_cast at h''

/-- A nonnegative sequence satisfying a contracting half-scale recurrence
with a geometrically vanishing source converges to zero. -/
theorem ESS.tendsto_of_half_recurrence
    {d : ℕ → ℝ} {A : ℝ}
    (hd : ∀ n, 0 ≤ d n)
    (hrec : ∀ n, d (n + 1) ≤ (1 / 2 : ℝ) * d n +
      A * (1 / 2 : ℝ) ^ (n + 1)) :
    Tendsto d atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnPow : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 0) := tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hupper : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n *
      (d 0 + A * n)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ => d 0 * (1 / 2 : ℝ) ^ n +
        A * ((n : ℝ) * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using (hpow.const_mul (d 0)).add (hnPow.const_mul A)
    have hfun : (fun n : ℕ => (1 / 2 : ℝ) ^ n * (d 0 + A * n)) =
        (fun n : ℕ => d 0 * (1 / 2 : ℝ) ^ n +
          A * ((n : ℝ) * (1 / 2 : ℝ) ^ n)) := by
      funext n
      ring
    rw [hfun]
    exact hsum
  have hbound : ∀ n, d n ≤ (1 / 2 : ℝ) ^ n * (d 0 + A * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        d (n + 1) ≤ (1 / 2 : ℝ) * d n + A * (1 / 2 : ℝ) ^ (n + 1) := hrec n
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * (d 0 + A * n)) +
            A * (1 / 2 : ℝ) ^ (n + 1) := by
          gcongr
        _ = (1 / 2 : ℝ) ^ (n + 1) *
            (d 0 + A * ((n : ℝ) + 1)) := by
          rw [pow_succ]
          ring
        _ = (1 / 2 : ℝ) ^ (n + 1) *
            (d 0 + A * ((n + 1 : ℕ) : ℝ)) := by
          rw [Nat.cast_succ]
  exact squeeze_zero' (Filter.Eventually.of_forall hd)
    (Filter.Eventually.of_forall hbound) hupper

noncomputable section

namespace ESS

private theorem parabolicCylinder_subset_radius
    {z : ParabolicPoint} {r R : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ R) :
    parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 R := by
  exact parabolicCylinder_mono hr hrr

/-- A uniform cylinder bound for the velocity bounds its normalized cubic
quantity and its cubic cylinder integral. -/
theorem gamma_cube_le_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r B : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I 3 u Du p
      (fun _ => (0 : Vec3))) (hr : 0 < r) (hsub :
    closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hu : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 r),
      vec3EuclideanNorm (u w) ≤ B) :
    gamma u z r ^ (3 : ℕ) ≤ (4 * Real.pi / 3) * B ^ 3 * r ^ 3 ∧
      r⁻¹ ^ (2 : ℕ) *
        (∫ w in parabolicCylinder z.1 z.2 r,
          vec3EuclideanNorm (u w) ^ (3 : ℕ)) ≤
          (4 * Real.pi / 3) * B ^ 3 * r ^ 3 := by
  let Q := parabolicCylinder z.1 z.2 r
  have hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ)) Q volume :=
    CKN.tsai_integrable_velocity_cube_on_cylinder hsol hr hsub
  have hconst : IntegrableOn (fun _ : ParabolicPoint => B ^ 3) Q volume :=
    integrableOn_const (volume_parabolicCylinder_lt_top.ne)
  have hpoint : (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ)) ≤ᵐ[
      volume.restrict Q] (fun _ => B ^ 3) := by
    filter_upwards [hu] with w hw
    exact pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hw 3
  have hcube : ∫ w in Q, vec3EuclideanNorm (u w) ^ (3 : ℕ) ≤
      B ^ 3 * (volume Q).toReal := by
    calc
      _ ≤ ∫ w in Q, B ^ 3 := setIntegral_mono_ae_restrict hu3 hconst hpoint
      _ = B ^ 3 * (volume Q).toReal := by
        rw [setIntegral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]
  have hvol : (volume Q).toReal = (4 * Real.pi / 3) * r ^ 5 := by
    dsimp only [Q]
    rw [volume_parabolicCylinder, volume_vec3Ball_eq, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hgamma : gamma u z r ^ (3 : ℕ) =
      r ^ (-2 : ℝ) * (∫ w in Q,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) := by
    rw [gamma_cube_eq u z r hr]
    have h := setIntegral_eq_toReal_setLIntegral_of_nonneg hu3
      (Filter.Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
    have h' : (∫⁻ w in Q,
        ENNReal.ofReal (vec3EuclideanNorm (u w) ^ (3 : ℕ))).toReal =
        (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
      congr 1
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
      norm_num [ENNReal.rpow_natCast]
    rw [h.trans h']
  have hgammaBound : gamma u z r ^ (3 : ℕ) ≤
      (4 * Real.pi / 3) * B ^ 3 * r ^ 3 := by
    calc
      gamma u z r ^ (3 : ℕ) = r ^ (-2 : ℝ) *
          (∫ w in Q, vec3EuclideanNorm (u w) ^ (3 : ℕ)) := hgamma
      _ ≤ r ^ (-2 : ℝ) * (B ^ 3 * (volume Q).toReal) :=
        mul_le_mul_of_nonneg_left hcube (Real.rpow_nonneg hr.le _)
      _ = (4 * Real.pi / 3) * B ^ 3 * r ^ 3 := by
        rw [hvol]
        rw [Real.rpow_neg hr.le]
        field_simp
        have hpow : r ^ (2 : ℝ) = r ^ (2 : ℕ) := Real.rpow_natCast r 2
        calc
          B ^ 3 * r ^ (2 : ℕ) = r ^ (2 : ℕ) * B ^ 3 := mul_comm _ _
          _ = r ^ (2 : ℝ) * B ^ 3 := by rw [hpow.symm]
  refine ⟨hgammaBound, ?_⟩
  calc
    r⁻¹ ^ (2 : ℕ) * (∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) ≤
        r⁻¹ ^ (2 : ℕ) * (B ^ 3 * (volume Q).toReal) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (4 * Real.pi / 3) * B ^ 3 * r ^ 3 := by
      rw [hvol]
      field_simp [hr.ne']

/-- The velocity bound gives cubic decay of CKN's normalized velocity
oscillation on smaller cylinders. -/
theorem pressureChat_le_cubic_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r B : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I 3 u Du p
      (fun _ => (0 : Vec3))) (hr : 0 < r) (hsub :
      closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hu : ∀ᵐ w ∂volume.restrict (parabolicCylinder z.1 z.2 r),
      vec3EuclideanNorm (u w) ≤ B) :
    pressureChat u z r ≤ 8 * ((4 * Real.pi / 3) * B ^ 3) * r ^ 3 := by
  have hgamma := gamma_cube_le_of_ae_bound hsol hr hsub hu
  calc
    pressureChat u z r ≤ 8 * gamma u z r ^ (3 : ℕ) :=
      CKN.pressureChat_le_eight_gamma_cube hsol hr hsub
    _ ≤ 8 * ((4 * Real.pi / 3) * B ^ 3 * r ^ 3) :=
      mul_le_mul_of_nonneg_left hgamma.1 (by norm_num)
    _ = 8 * ((4 * Real.pi / 3) * B ^ 3) * r ^ 3 := by ring

private theorem pressureSecondExtension_memLp_two
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG32 : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hG2 : ∀ i j, MemLp (G i j) 2 volume) :
    MemLp (pressureSecondExtensionOperator rieszSecondL2Input
      rieszSecondL2_weak_type G) 2 volume ∧
      lpNorm (pressureSecondExtensionOperator rieszSecondL2Input
        rieszSecondL2_weak_type G) 2 volume ≤
        ∑ i : Fin 3, ∑ j : Fin 3, lpNorm (G i j) 2 volume := by
  have hcomponent : ∀ i j : Fin 3,
      MemLp (rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
        (rieszSecondL2_weak_type i j) (G i j)) 2 volume ∧
      lpNorm (rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
        (rieszSecondL2_weak_type i j) (G i j)) 2 volume ≤
        lpNorm (G i j) 2 volume := by
    intro i j
    have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
    have hrawAE := rieszSecondL2RawOperator_ae_eq
      (rieszSecondL2Input i j) (hG2 i j)
    have hmeasAE := rieszSecondL2MeasurableOperator_ae_eq_extension
      (rieszSecondL2Input i j) ((hG2 i j).toLp (G i j))
    have hrawEq : rieszSecondL2RawOperator (rieszSecondL2Input i j)
        (G i j) =ᵐ[volume]
        (rieszSecondL2Extension (rieszSecondL2Input i j)
          ((hG2 i j).toLp (G i j)) : Vec3 → ℝ) := hrawAE.trans hmeasAE
    have hraw : MemLp (rieszSecondL2RawOperator (rieszSecondL2Input i j)
        (G i j)) 2 volume := (memLp_congr_ae hrawEq).2
        (Lp.memLp (rieszSecondL2Extension (rieszSecondL2Input i j)
          ((hG2 i j).toLp (G i j))))
    have hrawEqLp : hraw.toLp (rieszSecondL2RawOperator
        (rieszSecondL2Input i j) (G i j)) = rieszSecondL2Extension
          (rieszSecondL2Input i j) ((hG2 i j).toLp (G i j)) := by
      apply Lp.ext
      exact hraw.coeFn_toLp.trans hrawEq
    have hnorm : lpNorm (rieszSecondL2RawOperator
        (rieszSecondL2Input i j) (G i j)) 2 volume ≤ lpNorm (G i j) 2 volume := by
      change (eLpNorm (rieszSecondL2RawOperator
        (rieszSecondL2Input i j) (G i j)) 2 volume).toReal ≤
        (eLpNorm (G i j) 2 volume).toReal
      rw [← Lp.norm_toLp _ hraw, ← Lp.norm_toLp _ (hG2 i j), hrawEqLp]
      exact rieszSecondL2Extension_norm_le (rieszSecondL2Input i j)
        ((hG2 i j).toLp (G i j))
    have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
    let hInput := rieszSecondP1ExtensionInput (rieszSecondL2Input i j)
      (rieszSecondL2_weak_type i j)
    have hrep := lpExtensionRepresentative_ae_eq_T
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num)
      hInput (hG32 i j) (hG2 i j)
    have hT : hInput.T = fun f => rieszSecondL2RawOperator
        (rieszSecondL2Input i j) f := by
      simp only [hInput, rieszSecondP1ExtensionInput]
      dsimp only [czP1Constant, id]
      rw [lpExtensionInput_mp_T (by norm_num [czP1Constant])]
      rfl
    have hrepRaw : rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
        (rieszSecondL2_weak_type i j) (G i j) =ᵐ[volume]
        fun x => rieszSecondL2RawOperator (rieszSecondL2Input i j)
          (G i j) x := by
      have hrepNeg : lpExtensionRepresentative (by norm_num)
          (rieszSecondP1ExtensionInput (rieszSecondL2Input i j)
            (rieszSecondL2_weak_type i j)) (G i j) =ᵐ[volume]
          fun x => rieszSecondL2RawOperator (rieszSecondL2Input i j)
            (G i j) x := by
        filter_upwards [hrep] with x hx
        exact hx.trans (congrFun (congrFun hT (G i j)) x)
      simpa [rieszSecondP1ExtensionOperator] using hrepNeg
    have hmem : MemLp (rieszSecondP1ExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (G i j))
        2 volume := (memLp_congr_ae hrepRaw).2 hraw
    have hnormComp : lpNorm (rieszSecondP1ExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (G i j))
        2 volume ≤ lpNorm (G i j) 2 volume := by
      change (eLpNorm (rieszSecondP1ExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (G i j))
          2 volume).toReal ≤ _
      rw [eLpNorm_congr_ae hrepRaw]
      exact hnorm
    exact ⟨hmem, hnormComp⟩
  have hrow (i : Fin 3) : MemLp (fun x : Vec3 =>
      ∑ j : Fin 3, rieszSecondP1ExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) (G i j) x)
      2 volume := by
    apply memLp_finsetSum Finset.univ
    intro j hj
    exact (hcomponent i j).1
  have hsum : MemLp (fun x : Vec3 =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
          (rieszSecondL2_weak_type i j) (G i j) x) 2 volume := by
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact hrow i
  have hnormsum : lpNorm (fun x : Vec3 =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
          (rieszSecondL2_weak_type i j) (G i j) x) 2 volume ≤
      ∑ i : Fin 3, ∑ j : Fin 3, lpNorm (G i j) 2 volume := by
    calc
      _ ≤ ∑ i : Fin 3, lpNorm (fun x : Vec3 =>
          ∑ j : Fin 3, rieszSecondP1ExtensionOperator
            (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
            (G i j) x) 2 volume :=
        lpNorm_sum_le (p := (2 : ℝ≥0∞)) (μ := volume)
          (s := Finset.univ) (fun i _ => hrow i) (by norm_num)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          lpNorm (rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
            (rieszSecondL2_weak_type i j) (G i j)) 2 volume := by
        apply Finset.sum_le_sum
        intro i hi
        exact lpNorm_sum_le (p := (2 : ℝ≥0∞)) (μ := volume)
          (s := Finset.univ) (fun j _ => (hcomponent i j).1) (by norm_num)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, lpNorm (G i j) 2 volume := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (hcomponent i j).2
  constructor
  · change MemLp (fun x : Vec3 =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
          (rieszSecondL2_weak_type i j) (G i j) x) 2 volume
    exact hsum
  · change lpNorm (fun x : Vec3 =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        rieszSecondP1ExtensionOperator (rieszSecondL2Input i j)
          (rieszSecondL2_weak_type i j) (G i j) x) 2 volume ≤ _
    exact hnormsum

private theorem boundedPressureSource_memLp_two
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ s B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hΩmeas : MeasurableSet Ω)
    (hball : vec3Ball x₀ ρ ⊆ Ω)
    (hUmeas : AEStronglyMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict Ω))
    (hUbound : ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ),
      vec3EuclideanNorm (u (x, s)) ≤ B)
    (hcBound : ∀ j : Fin 3, |c s j| ≤ B) :
    ∀ i j : Fin 3,
      MemLp (fun x => mollifiedBallCutoff x₀ hρ x *
        pressureUTensor u c (x, s) i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      MemLp (fun x => mollifiedBallCutoff x₀ hρ x *
        pressureUTensor u c (x, s) i j) 2 volume ∧
      lpNorm (fun x => mollifiedBallCutoff x₀ hρ x *
        pressureUTensor u c (x, s) i j) 2 volume ≤
        (2 * B ^ 2) * (volume (vec3Ball x₀ ρ)).toReal ^ (1 / 2 : ℝ) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff x₀ hρ
  let uExt : Vec3 → Vec3 := (Ω.indicator fun x => u (x, s))
  have hηmeas : Measurable η := (mollifiedBallCutoff_smooth x₀ hρ).continuous.measurable
  have hηcomp : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport x₀ hρ
  have hηsupport : tsupport η ⊆ vec3Ball x₀ ρ := by
    simpa [η] using pressure_cutoff_support_subset_ball x₀ hρ
  have hBmeas : MeasurableSet (vec3Ball x₀ ρ) := vec3Ball_measurable x₀ ρ
  have huExt : AEStronglyMeasurable uExt volume := by
    apply (aestronglyMeasurable_indicator_iff hΩmeas).2
    exact hUmeas
  have huExtBound : ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ),
      vec3EuclideanNorm (uExt x) ≤ B := by
    filter_upwards [hUbound, ae_restrict_mem hBmeas] with x hx hxB
    have hxΩ : x ∈ Ω := hball hxB
    simp [uExt, hxΩ, hx]
  have hGmeas (i j : Fin 3) : AEStronglyMeasurable
      (fun x => η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j) volume := by
    change AEStronglyMeasurable (fun x => η x *
      (-uExt x i * (uExt x j - c s j))) volume
    fun_prop
  have hGbound (i j : Fin 3) : ∀ᵐ x ∂volume,
      |η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j| ≤ 2 * B ^ 2 := by
    have hballbound : ∀ᵐ x ∂volume.restrict (vec3Ball x₀ ρ),
        |η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j| ≤ 2 * B ^ 2 := by
      filter_upwards [huExtBound] with x hx
      have hη0 : 0 ≤ η x := by simpa [η] using mollifiedBallCutoff_nonneg x₀ hρ x
      have hη1 : η x ≤ 1 := by simpa [η] using mollifiedBallCutoff_le_one x₀ hρ x
      have hui : |uExt x i| ≤ B := by
        exact (abs_apply_le_vec3EuclideanNorm (uExt x) i).trans hx
      have huj : |uExt x j| ≤ B := by
        exact (abs_apply_le_vec3EuclideanNorm (uExt x) j).trans hx
      have hdiff : |uExt x j - c s j| ≤ 2 * B := by
        calc
          |uExt x j - c s j| ≤ |uExt x j| + |c s j| := abs_sub _ _
          _ ≤ B + B := add_le_add huj (hcBound j)
          _ = 2 * B := by ring
      calc
        |η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j| =
            η x * (|uExt x i| * |uExt x j - c s j|) := by
          simp [pressureUTensor, abs_of_nonneg hη0, abs_mul, abs_neg]
        _ ≤ 1 * (B * (2 * B)) := by
          gcongr
        _ = 2 * B ^ 2 := by ring
    have hballbound' := ae_imp_of_ae_restrict hballbound
    filter_upwards [hballbound'] with x hx1
    by_cases hx : x ∈ vec3Ball x₀ ρ
    · exact hx1 hx
    · have hη0 : η x = 0 := by
        by_contra hne
        apply hx
        exact hηsupport (subset_closure (by simpa [Function.mem_support] using hne))
      simpa only [hη0, zero_mul, abs_zero] using
        (by positivity : (0 : ℝ) ≤ 2 * B ^ 2)
  have hGcompact (i j : Fin 3) : HasCompactSupport
      (fun x => η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j) :=
    hηcomp.mul_right
  have hGboundNorm (i j : Fin 3) : ∀ᵐ x ∂volume,
      ‖η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j‖ ≤ 2 * B ^ 2 := by
    filter_upwards [hGbound i j] with x hx
    simpa only [Real.norm_eq_abs] using hx
  have hGmem (i j : Fin 3) (p : ℝ≥0∞) :
      MemLp (fun x => η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j)
        p volume :=
    (hGcompact i j).memLp_of_bound (hGmeas i j) (2 * B ^ 2)
      (hGboundNorm i j)
  have hGlpNorm (i j : Fin 3) :
      lpNorm (fun x => η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j)
        2 volume ≤
        (2 * B ^ 2) * (volume (vec3Ball x₀ ρ)).toReal ^ (1 / 2 : ℝ) := by
    let V : Set Vec3 := vec3Ball x₀ ρ
    let μ : Measure Vec3 := volume.restrict V
    have hVmeas : MeasurableSet V := by
      dsimp [V]
      exact vec3Ball_measurable x₀ ρ
    have hVbound : ∀ᵐ x ∂μ,
        ‖(fun y => η y * pressureUTensor (fun z => uExt z.1) c
          (y, s) i j) x‖ ≤ ‖(2 * B ^ 2 : ℝ)‖ := by
      have hconst : 0 ≤ (2 * B ^ 2 : ℝ) := by positivity
      filter_upwards [ae_restrict_of_ae (hGbound i j)] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg hconst] using hx
    have hmono : eLpNorm (fun x => η x *
        pressureUTensor (fun z => uExt z.1) c (x, s) i j) 2 μ ≤
        eLpNorm (fun _ : Vec3 => (2 * B ^ 2 : ℝ)) 2 μ :=
      eLpNorm_mono_ae (hGmeas i j).restrict hVbound
    have hGindicator : (fun x => η x *
        pressureUTensor (fun z => uExt z.1) c (x, s) i j) =ᵐ[volume]
        V.indicator (fun x => η x *
          pressureUTensor (fun z => uExt z.1) c (x, s) i j) := by
      filter_upwards [] with x
      by_cases hx : x ∈ V
      · simp [hx]
      · have hη0 : η x = 0 := by
          by_contra hne
          apply hx
          exact hηsupport (subset_closure (by simpa [Function.mem_support] using hne))
        simp [hx, hη0]
    have hglobal : eLpNorm (fun x => η x *
        pressureUTensor (fun z => uExt z.1) c (x, s) i j) 2 volume =
        eLpNorm (fun x => η x * pressureUTensor (fun z => uExt z.1)
          c (x, s) i j) 2 μ := by
      rw [eLpNorm_congr_ae hGindicator,
        eLpNorm_indicator_eq_eLpNorm_restrict hVmeas]
    have hVbounded : Bornology.IsBounded V := by
      dsimp [V]
      exact Metric.isBounded_ball.subset (vec3Ball_subset_ball x₀ ρ)
    have hVvol : volume V < ∞ := hVbounded.measure_lt_top
    have hμfinite : μ Set.univ < ∞ := by
      change (volume.restrict V) Set.univ < ∞
      rw [Measure.restrict_apply_univ V]
      exact hVvol
    let : IsFiniteMeasure μ := ⟨hμfinite⟩
    have hconstMem : MemLp (fun _ : Vec3 => (2 * B ^ 2 : ℝ)) 2 μ :=
      memLp_const _
    have hconstNorm :
        (eLpNorm (fun _ : Vec3 => (2 * B ^ 2 : ℝ)) 2 μ).toReal =
          (2 * B ^ 2) * (volume V).toReal ^ (1 / 2 : ℝ) := by
      change lpNorm (fun _ : Vec3 => (2 * B ^ 2 : ℝ)) 2 μ = _
      rw [lpNorm_const' (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
      simp only [Measure.real, μ, Measure.restrict_apply_univ V,
        Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * B ^ 2)]
      norm_num
    change (eLpNorm (fun x => η x * pressureUTensor
      (fun z => uExt z.1) c (x, s) i j) 2 volume).toReal ≤ _
    rw [hglobal]
    calc
      (eLpNorm (fun x => η x * pressureUTensor
        (fun z => uExt z.1) c (x, s) i j) 2 μ).toReal ≤
          (eLpNorm (fun _ : Vec3 => (2 * B ^ 2 : ℝ)) 2 μ).toReal :=
            ENNReal.toReal_mono hconstMem.eLpNorm_ne_top hmono
      _ = (2 * B ^ 2) * (volume V).toReal ^ (1 / 2 : ℝ) := hconstNorm
  intro i j
  have hGae (x : Vec3) :
      η x * pressureUTensor (fun z => uExt z.1) c (x, s) i j =
      η x * pressureUTensor u c (x, s) i j := by
    by_cases hxΩ : x ∈ Ω
    · simp [pressureUTensor, uExt, hxΩ]
    · have hη0 : η x = 0 := by
        by_contra hne
        have hxη : x ∈ tsupport η :=
          subset_closure (by simpa [Function.mem_support] using hne)
        exact hxΩ (hball (hηsupport hxη))
      simp [hη0]
  constructor
  · exact (memLp_congr_ae (Eventually.of_forall hGae)).1
      (hGmem i j (ENNReal.ofReal (3 / 2 : ℝ)))
  constructor
  · exact (memLp_congr_ae (Eventually.of_forall hGae)).1
      (hGmem i j 2)
  · change (eLpNorm (fun x => η x * pressureUTensor u c (x, s) i j)
        2 volume).toReal ≤ _
    rw [eLpNorm_congr_ae (Eventually.of_forall (fun x => (hGae x).symm))]
    exact hGlpNorm i j

end ESS

end
