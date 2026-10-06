/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CIVAxisymmetric.Reduction.ClassicalSolutionLocalBoxMeasurability

/-!
# From `L⁴_t L⁶_x` smallness to `L³` smallness on backward cylinders

The hypothesis of the Gustafson–Kang–Tsai criterion as it is used at the end of the proof of
`lem:aniso:closure` controls `∫_{-r²}^0 ‖u(t)‖_{L⁶(B_r)}^4 dt`. Two Hölder inequalities, in
space (`L⁶(B_r) ⊂ L³(B_r)` with the factor `|B_r|^{1/2}`) and then in time (exponent `3/4`
against the interval of length `r²`), turn it into the scale-invariant bound
`∫_{B_r × (-r², 0)} |u|³ ≤ (4π/3)^{1/2} r² (∫ ‖u(t)‖_{L⁶}^4 dt)^{3/4}`. The last theorem packages
this as `L³` smallness `≤ η r²` on all small backward cylinders at the origin, which is the
velocity half of the smallness hypothesis of CKN's Theorem A on those cylinders.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The spatial Hölder inequality `∫ g³ ≤ (∫ g⁶)^{1/2} |s|^{1/2}` for an arbitrary `ℝ≥0∞`-valued
function; no measurability is needed because the lower Lebesgue integral of `g³` is attained by
a measurable minorant. -/
theorem gkt_lintegral_rpow_three_le {s : Set Vec3} (g : Vec3 → ℝ≥0∞) :
    (∫⁻ x in s, g x ^ (3 : ℝ)) ≤
      (∫⁻ x in s, g x ^ (6 : ℝ)) ^ (1 / 2 : ℝ) * volume s ^ (1 / 2 : ℝ) := by
  obtain ⟨h3, hm, hle, heq⟩ := exists_measurable_le_lintegral_eq (volume.restrict s)
    (fun x => g x ^ (3 : ℝ))
  set h : Vec3 → ℝ≥0∞ := fun x => h3 x ^ (1 / 3 : ℝ) with hdef
  have hh3 : ∀ x, h x ^ (3 : ℝ) = h3 x := fun x => by
    rw [hdef, ← ENNReal.rpow_mul]; norm_num
  have hhg : ∀ x, h x ≤ g x := fun x => by
    have := ENNReal.rpow_le_rpow (hle x) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [← ENNReal.rpow_mul, show (3 : ℝ) * (1 / 3) = 1 by norm_num, ENNReal.rpow_one] at this
  have hmeas : AEMeasurable h (volume.restrict s) := (hm.pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_norm_pow_le (μ := volume.restrict s)
    (f := fun x => h x ^ (6 : ℝ)) (g := fun _ => (1 : ℝ≥0∞)) (hmeas.pow_const _)
    aemeasurable_const (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [ENNReal.one_rpow, mul_one, lintegral_const, Measure.restrict_apply_univ,
    one_mul] at hH
  have hsix : (∫⁻ x in s, h x ^ (6 : ℝ)) ≤ ∫⁻ x in s, g x ^ (6 : ℝ) :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hhg x) (by norm_num)
  calc (∫⁻ x in s, g x ^ (3 : ℝ)) = ∫⁻ x in s, h3 x := heq
    _ = ∫⁻ x in s, (h x ^ (6 : ℝ)) ^ (1 / 2 : ℝ) := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.rpow_mul, show (6 : ℝ) * (1 / 2) = 3 by norm_num, hh3 x]
    _ ≤ (∫⁻ x in s, h x ^ (6 : ℝ)) ^ (1 / 2 : ℝ) * volume s ^ (1 / 2 : ℝ) := hH
    _ ≤ (∫⁻ x in s, g x ^ (6 : ℝ)) ^ (1 / 2 : ℝ) * volume s ^ (1 / 2 : ℝ) := by
        gcongr

/-- The temporal Hölder inequality `∫ G^{3/4} ≤ (∫ G)^{3/4} |s|^{1/4}` for an arbitrary
`ℝ≥0∞`-valued function, by the same measurable-minorant argument. -/
theorem gkt_lintegral_rpow_three_fourths_le {s : Set ℝ} (G : ℝ → ℝ≥0∞) :
    (∫⁻ t in s, G t ^ (3 / 4 : ℝ)) ≤
      (∫⁻ t in s, G t) ^ (3 / 4 : ℝ) * volume s ^ (1 / 4 : ℝ) := by
  obtain ⟨h3, hm, hle, heq⟩ := exists_measurable_le_lintegral_eq (volume.restrict s)
    (fun t => G t ^ (3 / 4 : ℝ))
  set h : ℝ → ℝ≥0∞ := fun t => h3 t ^ (4 / 3 : ℝ) with hdef
  have hh3 : ∀ t, h t ^ (3 / 4 : ℝ) = h3 t := fun t => by
    rw [hdef, ← ENNReal.rpow_mul]; norm_num
  have hhG : ∀ t, h t ≤ G t := fun t => by
    have := ENNReal.rpow_le_rpow (hle t) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    rwa [← ENNReal.rpow_mul, show (3 / 4 : ℝ) * (4 / 3) = 1 by norm_num,
      ENNReal.rpow_one] at this
  have hmeas : AEMeasurable h (volume.restrict s) := (hm.pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_norm_pow_le (μ := volume.restrict s)
    (f := h) (g := fun _ => (1 : ℝ≥0∞)) hmeas aemeasurable_const
    (p := 3 / 4) (q := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  simp only [ENNReal.one_rpow, mul_one, lintegral_const, Measure.restrict_apply_univ,
    one_mul] at hH
  calc (∫⁻ t in s, G t ^ (3 / 4 : ℝ)) = ∫⁻ t in s, h3 t := heq
    _ = ∫⁻ t in s, h t ^ (3 / 4 : ℝ) := lintegral_congr fun t => (hh3 t).symm
    _ ≤ (∫⁻ t in s, h t) ^ (3 / 4 : ℝ) * volume s ^ (1 / 4 : ℝ) := hH
    _ ≤ (∫⁻ t in s, G t) ^ (3 / 4 : ℝ) * volume s ^ (1 / 4 : ℝ) := by
        gcongr with t
        exact hhG t

/-- The volume factor `|(-r², 0)|^{1/4} |B_r|^{1/2} = (4π/3)^{1/2} r²` of the mixed-norm Hölder
inequality. -/
theorem gkt_volume_factor {r : ℝ} (hr : 0 < r) :
    volume (Ioo (-(r ^ 2)) (0 : ℝ)) ^ (1 / 4 : ℝ) * volume (vec3Ball (0 : Vec3) r) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (4 * Real.pi / 3) * r ^ 2) := by
  have hI : volume (Ioo (-(r ^ 2)) (0 : ℝ)) = ENNReal.ofReal (r ^ 2) := by
    rw [Real.volume_Ioo]; congr 1; ring
  have hB : volume (vec3Ball (0 : Vec3) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
    rw [volume_vec3Ball_zero, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr.le]
  rw [hI, hB, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le]
  have e1 : r ^ ((2 : ℕ) * (1 / 4) : ℝ) * r ^ ((3 : ℕ) * (1 / 2) : ℝ) = r ^ ((2 : ℕ) : ℝ) := by
    rw [← Real.rpow_add hr]; norm_num
  have e2 : Real.pi * 4 / 3 = 4 * Real.pi / 3 := by ring
  calc r ^ ((2 : ℕ) * (1 / 4) : ℝ) * (r ^ ((3 : ℕ) * (1 / 2) : ℝ) *
        (Real.pi * 4 / 3) ^ (1 / 2 : ℝ))
      = (Real.pi * 4 / 3) ^ (1 / 2 : ℝ) *
        (r ^ ((2 : ℕ) * (1 / 4) : ℝ) * r ^ ((3 : ℕ) * (1 / 2) : ℝ)) := by ring
    _ = (4 * Real.pi / 3) ^ (1 / 2 : ℝ) * r ^ ((2 : ℕ) : ℝ) := by rw [e1, e2]

/-- The mixed-norm Hölder inequality on the backward cylinder `B_r × (-r², 0)` at the origin:
the `L³` integral of `u` is at most `(4π/3)^{1/2} r²` times the `3/4` power of the `L⁴_t L⁶_x`
quantity, by Tonelli and the two one-variable Hölder inequalities above. -/
theorem gkt_lintegral_cube_topCylinder_le (u : ParabolicPoint → Vec3) {r : ℝ} (hr : 0 < r)
    (hum : AEStronglyMeasurable u (volume.restrict (vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0))) :
    (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt (4 * Real.pi / 3) * r ^ 2) *
        (∫⁻ t in Ioo (-(r ^ 2)) 0,
          (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
            ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  set B : Set Vec3 := vec3Ball (0 : Vec3) r with hB
  set I : Set ℝ := Ioo (-(r ^ 2)) 0 with hI
  have hmeq : ((volume : Measure Vec3).restrict B).prod ((volume : Measure ℝ).restrict I) =
      (volume : Measure ParabolicPoint).restrict (B ×ˢ I) := by
    rw [Measure.prod_restrict]; rfl
  have hF : AEMeasurable (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      (((volume : Measure Vec3).restrict B).prod ((volume : Measure ℝ).restrict I)) := by
    rw [hmeq]
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hum).aemeasurable).pow_const _
  have hvolB : volume B ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top).ne
  calc (∫⁻ z in (B ×ˢ I : Set ParabolicPoint), ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      = ∫⁻ z, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) ∂
          (((volume : Measure Vec3).restrict B).prod ((volume : Measure ℝ).restrict I)) := by
        rw [hmeq]; rfl
    _ = ∫⁻ t in I, ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) :=
        lintegral_prod_symm _ hF
    _ ≤ ∫⁻ t in I, (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (1 / 2 : ℝ) * volume B ^ (1 / 2 : ℝ) :=
        lintegral_mono fun t => gkt_lintegral_rpow_three_le _
    _ = (∫⁻ t in I, ((∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ)) * volume B ^ (1 / 2 : ℝ) := by
        rw [lintegral_mul_const' _ _ hvolB]
        congr 1
        refine lintegral_congr fun t => ?_
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ ((∫⁻ t in I, (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) * volume I ^ (1 / 4 : ℝ)) * volume B ^ (1 / 2 : ℝ) := by
        gcongr
        exact gkt_lintegral_rpow_three_fourths_le _
    _ = ENNReal.ofReal (Real.sqrt (4 * Real.pi / 3) * r ^ 2) *
        (∫⁻ t in I, (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
        rw [← gkt_volume_factor hr]; ring

/-- A backward cylinder of radius `r < 1` at the origin lies in the unit cylinder. -/
theorem gkt_topCylinder_subset_unitCylinder {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0 ⊆ unitCylinder := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  refine ⟨?_, ?_, ht.2⟩
  · have hx' : vec3EuclideanNorm (x - 0) < r := hx
    show vec3EuclideanNorm (x - 0) < 1
    linarith only [hx', hr1]
  · have hr2 : r ^ 2 < 1 := by nlinarith only [hr, hr1]
    linarith only [ht.1, hr2]

/-- If the `L⁴_t L⁶_x` quantity on backward cylinders at the origin tends to zero, then for
every `η > 0` the `L³` integral of `u` over every sufficiently small backward cylinder is at
most `η r²`. -/
theorem gkt_exists_topCylinder_cube_small {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r < r₁ →
      (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (η * r ^ 2) := by
  set c : ℝ := Real.sqrt (4 * Real.pi / 3) with hc
  have hcpos : 0 < c := Real.sqrt_pos.2 (by positivity)
  set ε : ℝ := (η / c) ^ (4 / 3 : ℝ) with hεdef
  have hε : 0 < ε := by positivity
  have hcε : c * ε ^ (3 / 4 : ℝ) = η := by
    rw [hεdef, ← Real.rpow_mul (by positivity)]
    norm_num
    field_simp
  obtain ⟨r₀, hr₀, hsm⟩ := hsmall ε hε
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, min_le_right _ _, ?_⟩
  intro r hr hrr
  have hr1 : r < 1 := lt_of_lt_of_le hrr (min_le_right _ _)
  have hsub := gkt_topCylinder_subset_unitCylinder hr hr1
  have hum : AEStronglyMeasurable u
      (volume.restrict (vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0)) :=
    (aestronglyMeasurable_of_contDiffOn_spaceTimeSet (isOpen_vec3Ball 0 1) isOpen_Ioo
      hu).mono_set hsub
  refine le_trans (gkt_lintegral_cube_topCylinder_le u hr hum) ?_
  have hle := ENNReal.rpow_le_rpow (hsm r hr (lt_of_lt_of_le hrr (min_le_left _ _)))
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  refine le_trans (by gcongr) (le_of_eq_of_le (congrArg (ENNReal.ofReal (c * r ^ 2) * ·) rfl) ?_)
  refine le_trans (mul_le_mul_of_nonneg_left hle (zero_le)) ?_
  rw [ENNReal.ofReal_rpow_of_nonneg hε.le (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [← hcε]; ring

end CIV
