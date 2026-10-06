/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Interpolation
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSourceObligations
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantityNonneg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# Energy Integrable

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN CKN.Foundation.Parabolic.Integration CKN.Core.Step4


noncomputable section

namespace CIV

/-- The Euclidean-norm-squared density of a `Vec3`-valued function is dominated by three
times its `enorm`-squared density, the two norms on `Vec3` being equivalent up to `√3`. -/
private lemma ofReal_vec3EuclideanNorm_sq_le (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤ 3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have h1 : vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := vec3EuclideanNorm_le_sqrt_three_mul_norm v
  have h2 : (vec3EuclideanNorm v) ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) h1 2
    rwa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hp
  have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hL : ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) =
      ENNReal.ofReal ((vec3EuclideanNorm v) ^ 2) := by
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg v), hcast, ENNReal.rpow_natCast]
  have hR : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg v), hcast, ENNReal.rpow_natCast]
  rw [hL, hR, ← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  exact ENNReal.ofReal_le_ofReal h2

/-- The squared spatial-gradient density is dominated by nine times the square of the
gradient's `enorm`, the entrywise sup norm of the `3 × 3` gradient tensor. -/
theorem ofReal_spatialGradientSq_le_nine (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hsq : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ 2 := by
    rw [spatialGradientSq]
    calc ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            ((norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)) 2
      _ = 9 * ‖Du z‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  calc ENNReal.ofReal (spatialGradientSq u Du z)
      ≤ ENNReal.ofReal (9 * ‖Du z‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num, ← ofReal_norm,
          ENNReal.ofReal_pow (norm_nonneg _), hcast, ENNReal.rpow_natCast]

/-- The pressure integrand of Theorem A is finite over `Q`, directly from the `L^{3/2}`
membership conjunct of the energy class. -/
theorem lintegral_pressure_lt_top (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (h : GlobalEnergyClass u Du p) :
    (∫⁻ z in unitCylinder, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) < ⊤ := by
  have hmem : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict unitCylinder) := h.2.2
  have hlt := hmem.eLpNorm_lt_top
  have hne0 : (ENNReal.ofReal (3 / 2 : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hnetop : (ENNReal.ofReal (3 / 2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hres := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hne0 hnetop hlt
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] at hres
  simpa only [Real.enorm_eq_ofReal_abs] using hres

/-- The force integrand of Theorem A is finite over `Q`: `ForceC2Bounded` gives a pointwise
bound on `Q`, which integrates over the finite-measure cylinder. -/
theorem lintegral_force_lt_top (f : ParabolicPoint → Vec3) (hf : ForceC2Bounded f) (q : ℝ)
    (hq : 0 ≤ q) :
    (∫⁻ z in unitCylinder, ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) < ⊤ := by
  obtain ⟨M, hM⟩ := hf
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hmeas : MeasurableSet unitCylinder := by
    unfold unitCylinder CKN.spaceTimeSet
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hbound : ∀ z ∈ unitCylinder,
      ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q ≤ ENNReal.ofReal (Real.sqrt 3 * M') ^ q := by
    intro z hz
    have hcomp : ∀ i : Fin 3, |f z i| ≤ M' := by
      intro i
      have hzero : (0 : Fin 3 → ℕ) 0 + (0 : Fin 3 → ℕ) 1 + (0 : Fin 3 → ℕ) 2 ≤ 2 := by
        norm_num
      have := hM z hz i (0 : Fin 3 → ℕ) hzero
      simp only [multiPartial] at this
      exact this.trans (le_max_left _ _)
    have hnorm : ‖f z‖ ≤ M' := (pi_norm_le_iff_of_nonneg hM'0).2 hcomp
    have hle : vec3EuclideanNorm (f z) ≤ Real.sqrt 3 * M' := by
      calc vec3EuclideanNorm (f z) ≤ Real.sqrt 3 * ‖f z‖ :=
            vec3EuclideanNorm_le_sqrt_three_mul_norm (f z)
        _ ≤ Real.sqrt 3 * M' := by gcongr
    gcongr
  calc (∫⁻ z in unitCylinder, ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)
      ≤ ∫⁻ _z in unitCylinder, ENNReal.ofReal (Real.sqrt 3 * M') ^ q :=
        setLIntegral_mono' hmeas hbound
    _ = ENNReal.ofReal (Real.sqrt 3 * M') ^ q * volume unitCylinder := setLIntegral_const _ _
    _ < ⊤ := by
        apply ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq ENNReal.ofReal_ne_top)
        unfold unitCylinder CKN.spaceTimeSet
        change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
            (vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0) < ⊤
        rw [Measure.prod_prod, volume_vec3Ball_eq, Real.volume_Ioo]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top

private theorem exists_unitCylinder_exhaustion :
    ∃ (r t : ℕ → ℝ), (∀ n, 0 < r n) ∧ (∀ n, r n < 1) ∧ (∀ n, t n < 0) ∧
      (∀ n, -1 < t n - (r n) ^ 2) ∧
      (∀ n, parabolicCylinder (0 : Vec3) (t n) (r n) ⊆
        parabolicCylinder (0 : Vec3) (t (n + 1)) (r (n + 1))) ∧
      (∀ n, closure (parabolicCylinder (0 : Vec3) (t n) (r n)) ⊆ unitCylinder) ∧
      (⋃ n, parabolicCylinder (0 : Vec3) (t n) (r n)) = unitCylinder ∧
      (∀ n, (r n)⁻¹ ≤ (Real.sqrt (1 / 2))⁻¹) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let r : ℕ → ℝ := fun n => Real.sqrt (1 - ε n)
  let t : ℕ → ℝ := fun n => -(ε n / 2)
  have hεdef : ∀ n, ε n = 1 / ((n : ℝ) + 2) := fun _ => rfl
  have hrdef : ∀ n, r n = Real.sqrt (1 - ε n) := fun _ => rfl
  have htdef : ∀ n, t n = -(ε n / 2) := fun _ => rfl
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    rw [hεdef]
    positivity
  have hεle : ∀ n, ε n ≤ 1 / 2 := by
    intro n
    rw [hεdef]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
  have hεanti : ∀ n, ε (n + 1) < ε n := by
    intro n
    rw [hεdef, hεdef]
    have hcast : ((n + 1 : ℕ) : ℝ) + 2 = ((n : ℝ) + 2) + 1 := by push_cast; ring
    rw [hcast]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith only [])
  have hεtendsto : Tendsto ε atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun n => (hεpos n).le) (Eventually.of_forall fun n => ?_)
    rw [hεdef]
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [])
  have hrpos : ∀ n, 0 < r n := by
    intro n
    rw [hrdef]
    exact Real.sqrt_pos.mpr (by linarith only [hεle n])
  have hrsq : ∀ n, (r n) ^ 2 = 1 - ε n := by
    intro n
    rw [hrdef, Real.sq_sqrt (by linarith only [hεle n])]
  have hrlt1 : ∀ n, r n < 1 := by
    intro n
    have h1 : (r n) ^ 2 < 1 ^ 2 := by rw [hrsq n]; nlinarith only [hεpos n]
    nlinarith only [h1, hrpos n]
  have htlt0 : ∀ n, t n < 0 := by
    intro n
    rw [htdef]
    linarith only [hεpos n]
  have htsub_eq : ∀ n, t n - (r n) ^ 2 = -1 + ε n / 2 := by
    intro n
    rw [htdef, hrsq n]
    ring
  have htsub : ∀ n, -1 < t n - (r n) ^ 2 := by
    intro n
    rw [htsub_eq n]
    linarith only [hεpos n]
  have hεC : ∀ C : ℝ, 0 < C → ∃ N, ∀ n ≥ N, ε n < C := by
    intro C hC
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hεtendsto C hC
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_pos (hεpos n)] at this
  have hCsub : ∀ n, parabolicCylinder (0 : Vec3) (t n) (r n) ⊆
      parabolicCylinder (0 : Vec3) (t (n + 1)) (r (n + 1)) := by
    intro n
    have hrmono : r n < r (n + 1) := by
      rw [hrdef n, hrdef (n + 1)]
      exact Real.sqrt_lt_sqrt (by linarith only [hεle n]) (by linarith only [hεanti n])
    apply Set.prod_mono (vec3Ball_mono hrmono.le)
    apply Set.Ioc_subset_Ioc
    · rw [htsub_eq (n + 1), htsub_eq n]
      linarith only [hεanti n]
    · rw [htdef n, htdef (n + 1)]
      linarith only [hεanti n]
  have hclosure : ∀ n, closure (parabolicCylinder (0 : Vec3) (t n) (r n)) ⊆ unitCylinder := by
    intro n
    rw [closure_parabolicCylinder (hrpos n)]
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    have hy' : vec3EuclideanNorm y ≤ r n := by simpa using hy
    have hs1 : t n - (r n) ^ 2 ≤ s := hs.1
    have hs2 : s ≤ t n := hs.2
    refine ⟨?_, ?_, ?_⟩
    · simpa using hy'.trans_lt (hrlt1 n)
    · exact (htsub n).trans_le hs1
    · exact hs2.trans_lt (htlt0 n)
  have hunion : (⋃ n, parabolicCylinder (0 : Vec3) (t n) (r n)) = unitCylinder := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset
        (fun n => (parabolicCylinder_subset_closure _ _ _).trans (hclosure n))
    · rintro ⟨x, s⟩ ⟨hx, hs1, hs2⟩
      have hx' : vec3EuclideanNorm x < 1 := by simpa using hx
      have hC1 : (0 : ℝ) < 1 - (vec3EuclideanNorm x) ^ 2 := by
        nlinarith only [hx', vec3EuclideanNorm_nonneg x]
      have hC2 : (0 : ℝ) < -2 * s := by linarith only [hs2]
      have hC3 : (0 : ℝ) < 2 * (s + 1) := by linarith only [hs1]
      obtain ⟨N, hN⟩ := hεC
        (min (1 - (vec3EuclideanNorm x) ^ 2) (min (-2 * s) (2 * (s + 1))))
        (lt_min hC1 (lt_min hC2 hC3))
      have hεN := hN N le_rfl
      have hεN1 : ε N < 1 - (vec3EuclideanNorm x) ^ 2 := hεN.trans_le (min_le_left _ _)
      have hεN2 : ε N < -2 * s :=
        hεN.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hεN3 : ε N < 2 * (s + 1) :=
        hεN.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      refine Set.mem_iUnion.2 ⟨N, ?_⟩
      have hxrN : vec3EuclideanNorm x < r N := by
        by_contra hcon
        rw [not_lt] at hcon
        have hsq : (r N) ^ 2 ≤ (vec3EuclideanNorm x) ^ 2 :=
          pow_le_pow_left₀ (hrpos N).le hcon 2
        rw [hrsq N] at hsq
        linarith only [hsq, hεN1]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hxrN
      · rw [htsub_eq N]; linarith only [hεN3]
      · rw [htdef N]; linarith only [hεN2]
  have hRmin : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
  have hrge : ∀ n, Real.sqrt (1 / 2) ≤ r n := by
    intro n
    rw [hrdef n]
    exact Real.sqrt_le_sqrt (by linarith only [hεle n])
  have hrinv_le : ∀ n, (r n)⁻¹ ≤ (Real.sqrt (1 / 2))⁻¹ := by
    intro n
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hRmin (hrge n)
  exact ⟨r, t, hrpos, hrlt1, htlt0, htsub, hCsub, hclosure, hunion, hrinv_le⟩

private theorem exists_alpha_bound_on_exhaustion
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : GlobalEnergyClass u Du p) {r t : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hrlt1 : ∀ n, r n < 1) (htlt0 : ∀ n, t n < 0)
    (htsub : ∀ n, -1 < t n - (r n) ^ 2)
    (hrinv_le : ∀ n, (r n)⁻¹ ≤ (Real.sqrt (1 / 2))⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n, alpha u ((0 : Vec3), t n) (r n) ≤ A := by
  set E0 : ℝ≥0∞ :=
      essSup (fun s => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1 : ℝ) 0)) with hE0def
  have hE0fin : E0 < ⊤ := h.1
  have halpha_bound : ∀ n, timeSliceEnergyEssSup (0 : Vec3) (t n) (r n)
      (fun w => vec3EuclideanNorm (u w)) ≤ 3 * E0 := by
    intro n
    have hpoint : ∀ s, timeSliceBallEnergy (0 : Vec3) (r n) s (fun w => vec3EuclideanNorm (u w)) ≤
        3 * ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, s)‖ₑ ^ (2 : ℝ) := by
      intro s
      calc timeSliceBallEnergy (0 : Vec3) (r n) s (fun w => vec3EuclideanNorm (u w))
          = ∫⁻ y in vec3Ball (0 : Vec3) (r n),
              ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) := by
            unfold timeSliceBallEnergy
            refine lintegral_congr (fun y => ?_)
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
        _ ≤ ∫⁻ y in vec3Ball (0 : Vec3) (r n), 3 * ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
            lintegral_mono (fun y => ofReal_vec3EuclideanNorm_sq_le (u (y, s)))
        _ = 3 * ∫⁻ y in vec3Ball (0 : Vec3) (r n), ‖u (y, s)‖ₑ ^ (2 : ℝ) :=
            lintegral_const_mul' 3 _ (by norm_num)
        _ ≤ 3 * ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_left (lintegral_mono_set (vec3Ball_mono (hrlt1 n).le)) (by
              positivity)
    have htimesub : Ioc (t n - (r n) ^ 2) (t n) ⊆ Ioo (-1 : ℝ) 0 :=
      fun s hs => ⟨(htsub n).trans hs.1, hs.2.trans_lt (htlt0 n)⟩
    have hmono := essSup_mono_measure_and_ae
      (μ := volume.restrict (Ioc (t n - (r n) ^ 2) (t n)))
      (ν := volume.restrict (Ioo (-1 : ℝ) 0))
      (Measure.restrict_mono htimesub le_rfl) (Filter.Eventually.of_forall hpoint)
    rw [ENNReal.essSup_const_mul] at hmono
    exact hmono
  have hE0ne : (3 : ℝ≥0∞) * E0 ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hE0fin.ne
  set A : ℝ := ((Real.sqrt (1 / 2))⁻¹ * (3 * E0).toReal) ^ (1 / 2 : ℝ) with hAdef
  have hA : ∀ n, alpha u ((0 : Vec3), t n) (r n) ≤ A := by
    intro n
    have halpha_eq : alpha u ((0 : Vec3), t n) (r n) =
        ((r n)⁻¹ * (timeSliceEnergyEssSup (0 : Vec3) (t n) (r n)
          (fun w => vec3EuclideanNorm (u w))).toReal) ^ (1 / 2 : ℝ) := rfl
    have hfin_n : timeSliceEnergyEssSup (0 : Vec3) (t n) (r n)
        (fun w => vec3EuclideanNorm (u w)) ≠ ⊤ :=
      ne_top_of_le_ne_top hE0ne (halpha_bound n)
    have htoReal : (timeSliceEnergyEssSup (0 : Vec3) (t n) (r n)
        (fun w => vec3EuclideanNorm (u w))).toReal ≤ (3 * E0).toReal :=
      (ENNReal.toReal_le_toReal hfin_n hE0ne).mpr (halpha_bound n)
    rw [halpha_eq, hAdef]
    exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (hrpos n).le) ENNReal.toReal_nonneg)
      (mul_le_mul (hrinv_le n) htoReal ENNReal.toReal_nonneg (by positivity)) (by norm_num)
  exact ⟨A, by rw [hAdef]; positivity, hA⟩

/-- The velocity integrand of Theorem A is finite over `Q`. -/
theorem lintegral_cube_lt_top (q : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (h : GlobalEnergyClass u Du p) :
    (∫⁻ z in unitCylinder, ‖u z‖ₑ ^ (3 : ℝ)) < ⊤ := by
  have hsolI := isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol
  obtain ⟨r, t, hrpos, hrlt1, htlt0, htsub, hCsub, hclosure, hunion, hrinv_le⟩ :=
    exists_unitCylinder_exhaustion
  obtain ⟨A, hA0, hA⟩ :=
    exists_alpha_bound_on_exhaustion h hrpos hrlt1 htlt0 htsub hrinv_le
  set G0 : ℝ≥0∞ := ∫⁻ z in unitCylinder, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) with hG0def
  have hG0fin : G0 < ⊤ := h.2.1
  have hbeta_int_bound : ∀ n, (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
      ENNReal.ofReal (spatialGradientSq u Du w)) ≤ 9 * G0 := by
    intro n
    have hCsubUC : parabolicCylinder (0 : Vec3) (t n) (r n) ⊆ unitCylinder :=
      (parabolicCylinder_subset_closure _ _ _).trans (hclosure n)
    calc (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
            ENNReal.ofReal (spatialGradientSq u Du w))
        ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n), 9 * ‖Du w‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (fun w => ofReal_spatialGradientSq_le_nine u Du w)
      _ = 9 * ∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n), ‖Du w‖ₑ ^ (2 : ℝ) :=
          lintegral_const_mul' 9 _ (by norm_num)
      _ ≤ 9 * ∫⁻ w in unitCylinder, ‖Du w‖ₑ ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hCsubUC) (by positivity)
      _ ≤ 9 * ∫⁻ w in unitCylinder, (‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (lintegral_mono (fun w => le_add_self)) (by positivity)
      _ = 9 * G0 := by rw [hG0def]
  set B : ℝ := ((Real.sqrt (1 / 2))⁻¹ * (9 * G0).toReal) ^ (1 / 2 : ℝ) with hBdef
  have hG0ne : (9 : ℝ≥0∞) * G0 ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hG0fin.ne
  have hB : ∀ n, beta u Du ((0 : Vec3), t n) (r n) ≤ B := by
    intro n
    have hbeta_eq : beta u Du ((0 : Vec3), t n) (r n) =
        ((r n)⁻¹ * (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
          ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1 / 2 : ℝ) := rfl
    have hfin_n : (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
        ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤ :=
      ne_top_of_le_ne_top hG0ne (hbeta_int_bound n)
    have htoReal : (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
        ENNReal.ofReal (spatialGradientSq u Du w)).toReal ≤ (9 * G0).toReal :=
      (ENNReal.toReal_le_toReal hfin_n hG0ne).mpr (hbeta_int_bound n)
    rw [hbeta_eq, hBdef]
    exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (hrpos n).le) ENNReal.toReal_nonneg)
      (mul_le_mul (hrinv_le n) htoReal ENNReal.toReal_nonneg (by positivity)) (by norm_num)
  set M : ℝ := gagliardoConstant * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + gagliardoConstant * A
    with hMdef
  have hMbound : ∀ n, gamma u ((0 : Vec3), t n) (r n) ≤ M := by
    intro n
    have hsubn : closure (parabolicCylinder ((0 : Vec3), t n).1 ((0 : Vec3), t n).2 (r n)) ⊆
        spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0) := hclosure n
    have hg := gamma_le_gagliardo_of_sws (z := ((0 : Vec3), t n)) (r := r n) hsolI (hrpos n) hsubn
    have halpha0 : 0 ≤ alpha u ((0 : Vec3), t n) (r n) := alpha_nonneg u _ (hrpos n).le
    have hbeta0 : 0 ≤ beta u Du ((0 : Vec3), t n) (r n) := beta_nonneg u Du _ (hrpos n).le
    have hgc0 : (0 : ℝ) ≤ gagliardoConstant := by unfold gagliardoConstant; positivity
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    have h1 : alpha u ((0 : Vec3), t n) (r n) ^ (1 / 2 : ℝ) ≤ A ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow halpha0 (hA n) (by norm_num)
    have h2 : beta u Du ((0 : Vec3), t n) (r n) ^ (1 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hbeta0 (hB n) (by norm_num)
    have h3 : gagliardoConstant * alpha u ((0 : Vec3), t n) (r n) ^ (1 / 2 : ℝ) *
        beta u Du ((0 : Vec3), t n) (r n) ^ (1 / 2 : ℝ) ≤
        gagliardoConstant * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hgc0) h2 (Real.rpow_nonneg hbeta0 _)
        (mul_nonneg hgc0 (Real.rpow_nonneg hA0 _))
    have h4 : gagliardoConstant * alpha u ((0 : Vec3), t n) (r n) ≤ gagliardoConstant * A :=
      mul_le_mul_of_nonneg_left (hA n) hgc0
    refine hg.trans ?_
    rw [hMdef]
    exact add_le_add h3 h4
  have hM0 : 0 ≤ M := (gamma_nonneg u ((0 : Vec3), t 0) (hrpos 0).le).trans (hMbound 0)
  have hconv2 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x ^ (3 : ℕ)) = ENNReal.ofReal x ^ (3 : ℝ) := by
    intro x hx
    rw [ENNReal.ofReal_pow hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hconv : ∀ w : ParabolicPoint, ‖(vec3EuclideanNorm (u w)) ^ (3 : ℕ)‖ₑ =
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
    intro w
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg (u w)) 3),
      hconv2 _ (vec3EuclideanNorm_nonneg _)]
  have hCdata : ∀ n, AEMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
        (volume.restrict (parabolicCylinder (0 : Vec3) (t n) (r n))) ∧
      (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) < ⊤ := by
    intro n
    obtain ⟨Ω', J, hbox, hcyl⟩ :=
      exists_localBox_of_closure_subset hsol.1 hsol.2.1 (hrpos n) (hclosure n)
    have hint := (origin_velocity_cube_integrable_on_local_box hsolI hbox).mono_set hcyl
    have hfi := hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral
    have heq : (fun w => ‖(vec3EuclideanNorm (u w)) ^ (3 : ℕ)‖ₑ) =
        (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) := funext hconv
    rw [heq] at hfi
    have hmeasbase : AEMeasurable (fun w => (vec3EuclideanNorm (u w)) ^ (3 : ℕ))
        (volume.restrict (parabolicCylinder (0 : Vec3) (t n) (r n))) :=
      hint.aestronglyMeasurable.aemeasurable
    have hcomp := ENNReal.measurable_ofReal.comp_aemeasurable hmeasbase
    refine ⟨hcomp.congr
      (Filter.Eventually.of_forall fun w => hconv2 _ (vec3EuclideanNorm_nonneg (u w))), hfi⟩
  have hcubebound : ∀ n, (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (M ^ 3) := by
    intro n
    have hgc := gamma_cube_eq u ((0 : Vec3), t n) (r n) (hrpos n)
    have hcube_le : gamma u ((0 : Vec3), t n) (r n) ^ 3 ≤ M ^ 3 :=
      pow_le_pow_left₀ (gamma_nonneg u ((0 : Vec3), t n) (hrpos n).le) (hMbound n) 3
    rw [hgc] at hcube_le
    have hrpow_pos : 0 < (r n) ^ (2 : ℝ) := Real.rpow_pos_of_pos (hrpos n) 2
    have hstep : (∫⁻ w in parabolicCylinder (0 : Vec3) (t n) (r n),
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤ (r n) ^ (2 : ℝ) * M ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hcube_le (le_of_lt hrpow_pos)
      rwa [← mul_assoc, ← Real.rpow_add (hrpos n), show (2 : ℝ) + (-2 : ℝ) = 0 by norm_num,
        Real.rpow_zero, one_mul] at h1
    have hfinal : (r n) ^ (2 : ℝ) * M ^ 3 ≤ M ^ 3 := by
      have hrle1 : (r n) ^ (2 : ℝ) ≤ (1 : ℝ) := by
        have hle := Real.rpow_le_rpow (hrpos n).le (hrlt1 n).le (by norm_num : (0 : ℝ) ≤ 2)
        rwa [Real.one_rpow] at hle
      calc (r n) ^ (2 : ℝ) * M ^ 3 ≤ 1 * M ^ 3 :=
            mul_le_mul_of_nonneg_right hrle1 (pow_nonneg hM0 3)
        _ = M ^ 3 := one_mul _
    rw [← ENNReal.ofReal_toReal (hCdata n).2.ne]
    exact ENNReal.ofReal_le_ofReal (hstep.trans hfinal)
  set C : ℕ → Set ParabolicPoint := fun n => parabolicCylinder (0 : Vec3) (t n) (r n)
    with hCdef
  have hCmeas : ∀ n, MeasurableSet (C n) := fun n => measurableSet_parabolicCylinder _ _ _
  have hCmono : Monotone C := monotone_nat_of_le_succ hCsub
  set G : ℕ → ParabolicPoint → ℝ≥0∞ :=
      fun n => (C n).indicator (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
    with hGdef
  have hGmono : Monotone G := by
    intro m n hmn
    simp only [hGdef]
    exact Set.indicator_le_indicator_of_subset (hCmono hmn) (fun w => bot_le)
  have hUCmeas : MeasurableSet unitCylinder := by
    unfold unitCylinder CKN.spaceTimeSet
    exact (isOpen_vec3Ball (0 : Vec3) 1).measurableSet.prod measurableSet_Ioo
  have hsup_eq : ∀ a : ParabolicPoint, ⨆ n, G n a =
      unitCylinder.indicator (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ unitCylinder
    · have haU : a ∈ ⋃ n, C n := by rw [hunion]; exact ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp haU
      apply le_antisymm
      · refine iSup_le fun m => ?_
        simp only [hGdef]
        by_cases hm : a ∈ C m
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ha]
        · rw [Set.indicator_of_notMem hm]; exact bot_le
      · refine le_iSup_of_le n ?_
        simp only [hGdef]
        rw [Set.indicator_of_mem hn, Set.indicator_of_mem ha]
    · have hzero : ∀ n, G n a = 0 := by
        intro n
        simp only [hGdef]
        refine Set.indicator_of_notMem (fun hmem => ha ?_) _
        rw [← hunion]
        exact Set.mem_iUnion.mpr ⟨n, hmem⟩
      rw [Set.indicator_of_notMem ha]
      simp only [hzero, iSup_const]
  have hlim := lintegral_iSup' (μ := volume) (f := G)
    (fun n => (aemeasurable_indicator_iff (hCmeas n)).mpr (hCdata n).1)
    (Filter.Eventually.of_forall (fun x m n hmn => (hGmono hmn) x))
  have hmain : (∫⁻ w in unitCylinder, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      ENNReal.ofReal (M ^ 3) := by
    calc (∫⁻ w in unitCylinder, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
        = ∫⁻ a, unitCylinder.indicator
            (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) a :=
          (lintegral_indicator hUCmeas _).symm
      _ = ∫⁻ a, ⨆ n, G n a := by
          refine lintegral_congr (fun a => ?_)
          exact (hsup_eq a).symm
      _ = ⨆ n, ∫⁻ a, G n a := hlim
      _ = ⨆ n, ∫⁻ w in C n, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
          refine congrArg _ (funext fun n => ?_)
          simp only [hGdef]
          rw [lintegral_indicator (hCmeas n) _]
      _ ≤ ENNReal.ofReal (M ^ 3) := iSup_le (fun n => hcubebound n)
  calc (∫⁻ z in unitCylinder, ‖u z‖ₑ ^ (3 : ℝ))
      ≤ ∫⁻ z in unitCylinder, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) := by
        refine lintegral_mono (fun z => ENNReal.rpow_le_rpow ?_ (by norm_num))
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm (u z))
    _ ≤ ENNReal.ofReal (M ^ 3) := hmain
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The integral of a fixed finite-total-mass nonnegative function over the shrinking
backward time slabs `B(0,1) × (-δ, 0)` tends to `0` as `δ ↓ 0`. -/
theorem tendsto_lintegral_top_slab (F : ParabolicPoint → ℝ≥0∞)
    (hF : (∫⁻ z in unitCylinder, F z) < ⊤) :
    Tendsto (fun δ => ∫⁻ z in (vec3Ball 0 1) ×ˢ Ioo (-δ) 0, F z)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set A : ℝ → Set ParabolicPoint := fun δ => (vec3Ball (0 : Vec3) 1) ×ˢ Ioo (-δ) (0 : ℝ)
    with hAdef
  have hvolA : ∀ δ : ℝ, volume (A δ) = volume (vec3Ball (0 : Vec3) 1) * ENNReal.ofReal δ := by
    intro δ
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
        (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-δ) (0 : ℝ)) = _
    rw [Measure.prod_prod, Real.volume_Ioo, show (0 : ℝ) - (-δ) = δ by ring]
  have hl : Tendsto (fun δ => (volume.restrict unitCylinder) (A δ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have hofReal : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds 0) := by
      have hc : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhds (0 : ℝ))
          (nhds (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal).tendsto 0
      simpa using hc.mono_left nhdsWithin_le_nhds
    have hbne : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := by
      rw [volume_vec3Ball_eq]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    have hupper : Tendsto (fun δ => volume (vec3Ball (0 : Vec3) 1) * ENNReal.ofReal δ)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hofReal (Or.inr hbne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun δ => bot_le) (Eventually.of_forall fun δ => ?_)
    rw [← hvolA δ]
    exact Measure.restrict_apply_le _ _
  have hset := tendsto_setLIntegral_zero (μ := volume.restrict unitCylinder) (f := F) hF.ne hl
  have hmemIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Ioi 0) := by
    rw [mem_nhdsWithin]
    exact ⟨Iio 1, isOpen_Iio, by norm_num, fun x hx => ⟨hx.2, hx.1⟩⟩
  have heq : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Ioi 0), (A δ) ⊆ unitCylinder := by
    filter_upwards [hmemIoo] with δ hδ z hz
    exact ⟨hz.1, Set.Ioo_subset_Ioo_left (by linarith only [hδ.2]) hz.2⟩
  have heq2 : (fun δ => ∫⁻ z in A δ, F z ∂(volume.restrict unitCylinder)) =ᶠ[nhdsWithin (0 : ℝ)
      (Ioi 0)] (fun δ => ∫⁻ z in A δ, F z) := by
    filter_upwards [heq] with δ hδ
    rw [Measure.restrict_restrict_of_subset hδ]
  exact hset.congr' heq2

end CIV
