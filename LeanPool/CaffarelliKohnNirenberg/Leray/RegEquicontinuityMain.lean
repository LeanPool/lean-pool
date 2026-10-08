/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegEquicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Reg Equicontinuity Main

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regEquicontinuity_interval_pressure_bound
    {p : ParabolicPoint → ℝ}
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
      regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P)
    {g : Vec3 → ℝ}
    (hg : MemLp g (ENNReal.ofReal (5 / 2 : ℝ)) volume)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    |∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume| ≤
      P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := by
  let ν : Measure ℝ := volume.restrict (Ioc s t)
  let μ : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod ν
  let Q : Set ParabolicPoint := Set.univ ×ˢ Ioc s t
  have hIocPos : Ioc s t ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact (lt_trans hs hr.1)
  have hMeasure : regUniformPositiveTimeMeasure.restrict Q = μ := by
    change (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ))).restrict (Set.univ ×ˢ Ioc s t) =
      (volume : Measure Vec3).prod (volume.restrict (Ioc s t))
    rw [Measure.restrict_restrict_of_subset
      (Set.prod_mono (Set.Subset.refl Set.univ) hIocPos)]
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioc s t)]
    simp [Measure.restrict_univ]
  have hνfinite : ν Set.univ < ⊤ := by
    simp [ν]
  let : IsFiniteMeasure ν := ⟨hνfinite⟩
  have hgLift : MemLp (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ := by
    change MemLp (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) ((volume : Measure Vec3).prod ν)
    exact hg.comp_fst (volume.restrict (Ioc s t))
  have hgQ : MemLp (fun z : ParabolicPoint => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) (regUniformPositiveTimeMeasure.restrict Q) := by
    rw [hMeasure]
    exact hgLift
  have hProduct := regEquicontinuity_pressure_mul_memLp_one p
    (fun z : ParabolicPoint => g z.1) Q hp hgQ
  let fP : ParabolicPoint → ℝ := fun z => p z * g z.1
  let f : Vec3 × ℝ → ℝ := fun z => p (z.1, z.2) * g z.1
  have hProductIntegrable : Integrable f μ := by
    rw [← hMeasure]
    change Integrable fP
      (regUniformPositiveTimeMeasure.restrict Q)
    exact memLp_one_iff_integrable.mp hProduct.1
  have hProductBound : eLpNorm f 1 μ ≤
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
        eLpNorm (fun z : Vec3 × ℝ => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) μ := by
    rw [← hMeasure]
    change eLpNorm fP 1 (regUniformPositiveTimeMeasure.restrict Q) ≤
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
        eLpNorm (fun z : ParabolicPoint => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) (regUniformPositiveTimeMeasure.restrict Q)
    exact hProduct.2
  have hMass : ν Set.univ = ENNReal.ofReal (t - s) := by
    simp [ν]
  have hMassNe : ν Set.univ ≠ 0 := by
    rw [hMass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hst))
  have hExponent : (ENNReal.ofReal (5 / 2 : ℝ)).toReal⁻¹ = 2 / 5 := by
    norm_num
  have hLiftNorm : eLpNorm (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ =
      ENNReal.ofReal ((t - s) ^ (2 / 5 : ℝ)) *
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
    calc
      eLpNorm (fun z : Vec3 × ℝ => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) μ =
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) (Measure.map Prod.fst μ) := by
          symm
          have hmap : AEStronglyMeasurable g (Measure.map Prod.fst μ) := by
            rw [Measure.map_fst_prod]
            exact hg.aestronglyMeasurable.smul_measure _
          exact eLpNorm_map_measure hmap measurable_fst.aemeasurable
      _ = eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
          ((ν Set.univ) • (volume : Measure Vec3)) := by
            change eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
              (Measure.map Prod.fst ((volume : Measure Vec3).prod ν)) = _
            rw [Measure.map_fst_prod]
      _ = (ν Set.univ) ^ (2 / 5 : ℝ) *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
            rw [eLpNorm_smul_measure_of_ne_zero hMassNe]
            simp [hExponent]
      _ = ENNReal.ofReal ((t - s) ^ (2 / 5 : ℝ)) *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
            rw [hMass, ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hst.le)
              (by norm_num)]
  have hProductRealBound : (eLpNorm f 1 μ).toReal ≤
      P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := by
    have hPfinite : eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure < ⊤ :=
      lt_of_le_of_lt hP ENNReal.ofReal_lt_top
    have hgfinite : eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume < ⊤ :=
      hg.eLpNorm_lt_top
    have hprodFinite : eLpNorm f 1 μ < ⊤ := by
      calc
        eLpNorm f 1 μ ≤
            eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
              eLpNorm (fun z : Vec3 × ℝ => g z.1)
                (ENNReal.ofReal (5 / 2 : ℝ)) μ := hProductBound
        _ < ⊤ := ENNReal.mul_lt_top hPfinite (by
          rw [hLiftNorm]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfinite)
    have hRhsFinite :
        eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
          eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ < ⊤ := by
      exact ENNReal.mul_lt_top hPfinite (by
        rw [hLiftNorm]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfinite)
    have hreal : (eLpNorm f 1 μ).toReal ≤
        (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure).toReal *
          (eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := by
      calc
        (eLpNorm f 1 μ).toReal ≤
            (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
              eLpNorm (fun z : Vec3 × ℝ => g z.1)
                (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal :=
          ENNReal.toReal_mono hRhsFinite.ne hProductBound
        _ = _ := by
          rw [ENNReal.toReal_mul]
    calc
      (eLpNorm f 1 μ).toReal ≤
          (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure).toReal *
            (eLpNorm (fun z : Vec3 × ℝ => g z.1)
              (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := hreal
      _ ≤ P * (eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := by
          gcongr
          calc
            (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
                regUniformPositiveTimeMeasure).toReal ≤
              (ENNReal.ofReal P).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
            _ = P := ENNReal.toReal_ofReal hP0
      _ = P * ((t - s) ^ (2 / 5 : ℝ) *
            (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal) := by
          rw [hLiftNorm, ENNReal.toReal_mul]
          simp [ENNReal.toReal_ofReal (Real.rpow_nonneg
            (sub_nonneg.mpr hst.le) _)]
      _ = P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
            (t - s) ^ (2 / 5 : ℝ) := by ring
  have hAbsIntegral : |∫ z, f z ∂μ| ≤ (eLpNorm f 1 μ).toReal := by
    calc
      |∫ z, f z ∂μ| ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
      _ = ∫ z, ‖f z‖ ∂μ := by simp [Real.norm_eq_abs]
      _ = (eLpNorm f 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hProductIntegrable.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm hProductIntegrable.aestronglyMeasurable]
  have hFubini := integral_prod_symm f hProductIntegrable
  have hInterval : (∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume) =
      ∫ z, f z ∂μ := by
    rw [intervalIntegral.integral_of_le hst.le]
    change (∫ r, ∫ x : Vec3, p (x, r) * g x ∂volume ∂ν) = _
    calc
      (∫ r, ∫ x : Vec3, p (x, r) * g x ∂volume ∂ν) =
          ∫ z : Vec3 × ℝ, f z ∂μ := by
            simpa [f] using hFubini.symm
      _ = ∫ z, f z ∂μ := rfl
  calc
    |∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume| =
        |∫ z, f z ∂μ| := by rw [hInterval]
    _ ≤ (eLpNorm f 1 μ).toReal := hAbsIntegral
    _ ≤ P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := hProductRealBound

private theorem regEquicontinuity_bounded_interval_integral
    {f : ℝ → ℝ} {K s t : ℝ} (hst : s ≤ t) (_hK : 0 ≤ K)
    (hf : ∀ r ∈ uIoc s t, ‖f r‖ ≤ K) :
    |∫ r in s..t, f r ∂volume| ≤ K * (t - s) := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hf
  rw [Real.norm_eq_abs] at hnorm
  simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hnorm

private theorem regEquicontinuity_scalar_holder_modulus
    (F H R Q : ℕ → ℝ → ℝ)
    (s₀ s₁ K P : ℝ) (hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
    (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hFderiv : ∀ n t, 0 < t → HasDerivAt (F n) (H n t) t)
    (hHcont : ∀ n, ContinuousOn (H n) (Ioi (0 : ℝ)))
    (hQcont : ∀ n, ContinuousOn (Q n) (Ioi (0 : ℝ)))
    (hRcont : ∀ n, ContinuousOn (R n) (Ioi (0 : ℝ)))
    (hPairing : ∀ n t, 0 < t → H n t = R n t + Q n t)
    (hRbound : ∀ n t, 0 ≤ t → |R n t| ≤ K)
    (p : ℕ → ParabolicPoint → ℝ) (g : Vec3 → ℝ)
    (hQform : ∀ n t, Q n t = ∫ x : Vec3, p n (x, t) * g x ∂volume)
    (hg : MemLp g (ENNReal.ofReal (5 / 2 : ℝ)) volume)
    (hPressure : ∀ n,
      MemLp (p n) (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure ∧
      eLpNorm (p n) (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
        |F n t - F n s| ≤ A * dist t s + B * (dist t s) ^ θ := by
  have hOrdered : ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ → s < t →
      |F n t - F n s| ≤ K * (t - s) +
        P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
          (t - s) ^ (2 / 5 : ℝ) := by
    intro n s t hs ht hst
    have hIcc : Icc s t ⊆ Ioi (0 : ℝ) :=
      (Icc_subset_Icc hs.1 ht.2).trans hs₀s₁
    have hspos : 0 < s := hIcc ⟨le_rfl, hst.le⟩
    have hHinterval : IntervalIntegrable (H n) volume s t :=
      ((hHcont n).mono hIcc).intervalIntegrable_of_Icc hst.le
    have hQinterval : IntervalIntegrable (Q n) volume s t :=
      ((hQcont n).mono hIcc).intervalIntegrable_of_Icc hst.le
    have hRinterval : IntervalIntegrable (R n) volume s t :=
      ((hRcont n).mono hIcc).intervalIntegrable_of_Icc hst.le
    have hFdiffOn : DifferentiableOn ℝ (F n) (Ioi (0 : ℝ)) := by
      intro r hr
      exact (hFderiv n r hr).differentiableAt.differentiableWithinAt
    have hFcont : ContinuousOn (F n) (Ioi (0 : ℝ)) := hFdiffOn.continuousOn
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hst.le (hFcont.mono hIcc)
      (fun r hr => hFderiv n r (hIcc (Ioo_subset_Icc_self hr))) hHinterval
    have hsplit : (∫ r in s..t, H n r ∂volume) =
        (∫ r in s..t, R n r ∂volume) + (∫ r in s..t, Q n r ∂volume) := by
      calc
        _ = ∫ r in s..t, R n r + Q n r ∂volume := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with r hr
          have hrIoc : r ∈ Ioc s t := by
            simpa [uIoc_of_le hst.le] using hr
          exact hPairing n r (hIcc ⟨hrIoc.1.le, hrIoc.2⟩)
        _ = _ := intervalIntegral.integral_add hRinterval hQinterval
    have hRmod : |∫ r in s..t, R n r ∂volume| ≤ K * (t - s) := by
      apply regEquicontinuity_bounded_interval_integral hst.le hK
      intro r hr
      have hrIoc : r ∈ Ioc s t := by
        simpa [uIoc_of_le hst.le] using hr
      have hrcc : r ∈ Icc s t := ⟨hrIoc.1.le, hrIoc.2⟩
      simpa [Real.norm_eq_abs] using hRbound n r (le_of_lt (hIcc hrcc))
    have hQmod := regEquicontinuity_interval_pressure_bound
      (hPressure n).1 P hP (hPressure n).2 hg hspos hst
    have hQmod' : |∫ r in s..t, Q n r ∂volume| ≤
        P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
          (t - s) ^ (2 / 5 : ℝ) := by
      rw [show (fun r => Q n r) =
          fun r => ∫ x : Vec3, p n (x, r) * g x ∂volume from funext (hQform n)]
      exact hQmod
    calc
      |F n t - F n s| =
          |(∫ r in s..t, R n r ∂volume) + (∫ r in s..t, Q n r ∂volume)| := by
          rw [← hFTC, hsplit]
      _ ≤ |∫ r in s..t, R n r ∂volume| +
          |∫ r in s..t, Q n r ∂volume| := abs_add_le _ _
      _ ≤ K * (t - s) +
          P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
            (t - s) ^ (2 / 5 : ℝ) := add_le_add hRmod hQmod'
  refine ⟨K, P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal,
    2 / 5, hK, mul_nonneg hP ENNReal.toReal_nonneg, by norm_num, ?_⟩
  intro n s t hs ht
  rcases lt_trichotomy s t with hst | hst | hts
  · have h := hOrdered n s t hs ht hst
    simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst.le), mul_assoc] using h
  · subst t
    simp
  · have h := hOrdered n t s ht hs hts
    simpa [abs_sub_comm, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hts.le)] using h

private theorem regEquicontinuity_compact_test_integral_continuous
    (f : ParabolicPoint → ℝ) (g : Vec3 → ℝ)
    (hf : ContinuousOn f (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, f (x, t) * g x ∂volume)
      (Ioi (0 : ℝ)) := by
  let G : ℝ → Vec3 → ℝ := fun t x => f (x, t) * g x
  have hswap : Continuous (fun z : ℝ × Vec3 =>
      parabolicHomeomorph.symm (z.2, z.1)) :=
    parabolicHomeomorph.symm.continuous.comp (by fun_prop)
  have hmaps : Set.MapsTo (fun z : ℝ × Vec3 =>
      parabolicHomeomorph.symm (z.2, z.1))
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3))
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    change ((x, t) : ParabolicPoint) ∈
      (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
    exact ⟨mem_univ _, ht⟩
  have hpull : ContinuousOn (fun z : ℝ × Vec3 => f (z.2, z.1))
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3)) := by
    have hcomp := hf.comp hswap.continuousOn hmaps
    convert hcomp using 1
    rfl
  have hG : ContinuousOn G.uncurry
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3)) := by
    have hg' : ContinuousOn (fun z : ℝ × Vec3 => g z.2)
        (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec3)) :=
      (hg.continuous.comp continuous_snd).continuousOn
    exact hpull.mul hg'
  have hGzero : ∀ t x, t ∈ Ioi (0 : ℝ) → x ∉ tsupport g → G t x = 0 := by
    intro t x ht hx
    simp [G, image_eq_zero_of_notMem_tsupport hx]
  exact continuousOn_integral_of_compact_support
    (μ := volume) (s := Ioi (0 : ℝ)) (k := tsupport g)
    hgc.isCompact hG hGzero

private theorem regEquicontinuity_time_derivative_pairing_continuous
    (U : ParabolicPoint → Vec3) (W : Fin 3 → Vec3 → ℝ)
    (hDtc : ∀ i, ContinuousOn
      (fun z => timePartial (fun y => U y i) z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hWdiff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i))
    (hWc : ∀ i, HasCompactSupport (W i)) :
    ContinuousOn (fun t : ℝ =>
      ∫ x : Vec3, ∑ i : Fin 3, timePartial (fun y => U y i) (x, t) * W i x
        ∂volume) (Ioi (0 : ℝ)) := by
  have hCoordinate : ∀ i : Fin 3, ContinuousOn (fun t : ℝ =>
      ∫ x : Vec3, timePartial (fun y => U y i) (x, t) * W i x ∂volume)
        (Ioi (0 : ℝ)) := by
    intro i
    exact regEquicontinuity_compact_test_integral_continuous
      (fun z => timePartial (fun y => U y i) z) (W i)
      (hDtc i) (hWdiff i) (hWc i)
  apply ContinuousOn.congr (continuousOn_finsetSum (s := Finset.univ)
    (fun i _ => hCoordinate i))
  intro t ht
  have hIntegrable : ∀ i : Fin 3,
      Integrable (fun x : Vec3 =>
        timePartial (fun y => U y i) (x, t) * W i x) := by
    intro i
    exact lerayHopfLimit_integrable_mul_compact
      (lerayHopfLimit_slice_continuous (hDtc i) ht)
      (hWdiff i).continuous (hWc i)
  have hIntegrable' : ∀ i ∈ Finset.univ,
      Integrable (fun x : Vec3 =>
        timePartial (fun y => U y i) (x, t) * W i x) := by
    intro i hi
    exact hIntegrable i
  simp only
  rw [integral_finsetSum (s := Finset.univ) hIntegrable']

private theorem regEquicontinuity_pairing_equation_at_time
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (W : Fin 3 → Vec3 → ℝ)
    (hUc : ∀ i, ContinuousOn (fun z => u z i)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDc : ∀ i j, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDDc : ∀ i j k, ContinuousOn
      (fun z => spatialPartial
        (fun y => spatialPartial (fun x => u x i) j y) k z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hpc : ContinuousOn p (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDpc : ∀ i, ContinuousOn (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDdiff : ∀ z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) → ∀ i j,
      DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hpDiff : ∀ z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (t : ℝ)
    (hJcontDiff : ∀ j, ContDiff ℝ 1 (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, t) j))
    (hJdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ
      (fun y : Vec3 => regUniformMollifiedVelocity ρ ε hε u (y, t) j) x
        (basisVec j) = 0)
    (hPDE : ∀ z, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
          spatialPartial (fun y => u y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (hWdiff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i))
    (hWc : ∀ i, HasCompactSupport (W i)) (ht : 0 < t) :
    (∫ x : Vec3, ∑ i : Fin 3,
      timePartial (fun y => u y i) (x, t) * W i x ∂volume) =
    (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      (u (x, t) i * spatialDeriv (spatialDeriv (W i) j) j x +
        u (x, t) i * regUniformMollifiedVelocity ρ ε hε u (x, t) j *
          spatialDeriv (W i) j x) ∂volume) +
    (∫ x : Vec3, p (x, t) * (∑ i : Fin 3, spatialDeriv (W i) i x) ∂volume) := by
  have hdiff := fun i x =>
    lerayHopfLimit_slice_differentiable (fun z => u z i) (hC1 i) x ht
  have hidentity := regEqui_pairing_equation_ibp
    (fun i x => u (x, t) i)
    (fun i j x => spatialPartial (fun y => u y i) j (x, t))
    (fun i j k x => spatialPartial
      (fun y => spatialPartial (fun x => u x i) j y) k (x, t))
    (fun x => p (x, t))
    (fun i x => spatialPartial (fun y => p y) i (x, t))
    (fun j x => regUniformMollifiedVelocity ρ ε hε u (x, t) j)
    (fun i x => timePartial (fun y => u y i) (x, t)) W
    (fun i => lerayHopfLimit_slice_continuous (hUc i) ht)
    (fun i x => (hdiff i x).2)
    (fun i j x => rfl)
    (fun i j => lerayHopfLimit_slice_continuous (hDc i j) ht)
    (fun i j x => hDdiff (x, t) ⟨mem_univ _, ht⟩ i j)
    (fun i j k x => rfl)
    (fun i j k => lerayHopfLimit_slice_continuous (hDDc i j k) ht)
    (lerayHopfLimit_slice_continuous hpc ht)
    (fun x => hpDiff (x, t) ⟨mem_univ _, ht⟩)
    (fun i x => rfl)
    (fun i => lerayHopfLimit_slice_continuous (hDpc i) ht)
    hJcontDiff hJdiv
    (fun i x => by linarith only [hPDE (x, t) ht i])
    hWdiff hWc
  simpa using hidentity

private theorem regEquicontinuity_sequence_coordinate_bounds
    (ρ : RegMollifierProfile)
    (U : ℕ → ParabolicPoint → Vec3) (a : Vec3 → Vec3)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (hDataMem : MemLp (regUniformSpatialField a) 2 volume)
    (hSlice : ∀ n t, 0 ≤ t → MemLp (fun x : Vec3 => U n (x, t)) 2 volume)
    (hR5 : ∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (U n) t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (U n)
          (fun z i j => spatialPartial (fun y => U n y i) j z) t =
      eLpNorm (regMollifyVector ρ (εseq n) (hseq n).1
        (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)) :
    (∀ n t, 0 ≤ t →
      eLpNorm (fun x : Vec3 => (WithLp.toLp 2 (U n (x, t)) : L2Vec3))
        2 volume ≤ eLpNorm (regUniformSpatialField a) 2 volume) ∧
    (∀ n t, 0 ≤ t → ∀ i : Fin 3,
      MemLp (fun x : Vec3 => U n (x, t) i) 2 volume ∧
      (∫ x : Vec3, U n (x, t) i ^ 2 ∂volume) ≤
        (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2) ∧
    (∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (U n) t) 2 volume ≤
        eLpNorm (regUniformSpatialField a) 2 volume) ∧
    (∀ n t, 0 ≤ t → ∀ j : Fin 3,
      MemLp (fun x : Vec3 => regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
        (U n) (x, t) j) 2 volume ∧
      (∫ x : Vec3,
        regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (x, t) j ^ 2
          ∂volume) ≤ (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2) := by
  let D : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  let Adata : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
  have hUslice : ∀ n t, 0 ≤ t →
      MemLp (regUniformVelocitySlice (U n) t) 2 volume := by
    intro n t ht
    have hcoord : MemLp (fun x : L2Vec3 => U n (WithLp.ofLp x, t)) 2 volume :=
      (hSlice n t ht).comp_measurePreserving
        (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hSliceBound : ∀ n t, 0 ≤ t →
      eLpNorm (fun x : Vec3 => (WithLp.toLp 2 (U n (x, t)) : L2Vec3))
        2 volume ≤ eLpNorm (regUniformSpatialField a) 2 volume := by
    intro n t ht
    have h := lerayHopfLimit_regSlice_uniformBound ρ (εseq n) (hseq n).1 a
      (U n) (fun z i j => D n z i j) hDataMem (hUslice n) (hR5 n) t ht
    simpa [D, regUniformVelocitySlice] using h
  have hUcomponent : ∀ n t, 0 ≤ t → ∀ i : Fin 3,
      MemLp (fun x : Vec3 => U n (x, t) i) 2 volume ∧
      (∫ x : Vec3, U n (x, t) i ^ 2 ∂volume) ≤ Adata ^ 2 := by
    intro n t ht i
    have hL2 : MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume :=
      lerayHopfLimit_toLp_memLp (hSlice n t ht)
    obtain ⟨hmem, hsq⟩ := lerayHopfLimit_integral_component_sq_le hL2 i
    change (∫ x : Vec3,
        (WithLp.toLp 2 (U n (x, t)) : L2Vec3) i ^ 2 ∂volume) ≤
      (eLpNorm (fun x : Vec3 =>
        (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume).toReal ^ 2 at hsq
    have hcoordEq : (fun x : Vec3 => (WithLp.toLp 2 (U n (x, t)) : L2Vec3) i) =
        fun x => U n (x, t) i := by
      funext x
      rfl
    refine ⟨?_, ?_⟩
    · rw [← hcoordEq]
      exact hmem
    · calc
        (∫ x : Vec3, U n (x, t) i ^ 2 ∂volume) =
            ∫ x : Vec3,
              (WithLp.toLp 2 (U n (x, t)) : L2Vec3) i ^ 2 ∂volume := by
                apply integral_congr_ae
                filter_upwards [] with x
                exact congrArg (fun y : ℝ => y ^ 2) (congrFun hcoordEq x).symm
        _ ≤ (eLpNorm (fun x : Vec3 =>
              (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume).toReal ^ 2 := hsq
        _ ≤ Adata ^ 2 := by
          have hnorm : (eLpNorm (fun x : Vec3 =>
              (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume).toReal ≤ Adata := by
            calc
              (eLpNorm (fun x : Vec3 =>
                  (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume).toReal ≤
                  (eLpNorm (regUniformSpatialField a) 2 volume).toReal :=
                ENNReal.toReal_mono hDataMem.eLpNorm_ne_top (hSliceBound n t ht)
              _ = Adata := rfl
          exact pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2
  have hOperatorBound : ∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (U n) t) 2 volume ≤
        eLpNorm (regUniformSpatialField a) 2 volume := by
    intro n t ht
    have hchange : eLpNorm
        (fun x : Vec3 => (WithLp.toLp 2 (U n (x, t)) : L2Vec3)) 2 volume =
        eLpNorm (regUniformVelocitySlice (U n) t) 2 volume := by
      have hS : MemLp (regUniformVelocitySlice (U n) t) 2 volume := hUslice n t ht
      exact eLpNorm_comp_measurePreserving hS.aestronglyMeasurable
        vec3ToL2Vec3_measurePreserving
    rw [← hchange]
    exact hSliceBound n t ht
  have hJcomponent : ∀ n t, 0 ≤ t → ∀ j : Fin 3,
      MemLp (fun x : Vec3 => regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
        (U n) (x, t) j) 2 volume ∧
      (∫ x : Vec3,
        regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (x, t) j ^ 2
          ∂volume) ≤ Adata ^ 2 := by
    intro n t ht j
    obtain ⟨hmem, hsq⟩ := lerayHopfLimit_mollifiedInitial_component_sq_le
      ρ (εseq n) (hseq n).1 (hSlice n t ht) j
    have hmem' : MemLp (fun x : Vec3 =>
        regUniformMollifiedInitial ρ (εseq n) (hseq n).1
          (fun y : Vec3 => U n (y, t)) x j) 2 volume := by
      simpa using hmem
    have hsq' : (∫ x : Vec3,
        regUniformMollifiedInitial ρ (εseq n) (hseq n).1
          (fun y : Vec3 => U n (y, t)) x j ^ 2 ∂volume) ≤
        (eLpNorm (regUniformSpatialField
          (fun x : Vec3 => U n (x, t))) 2 volume).toReal ^ 2 := by
      simpa using hsq
    have hSliceEq :
        regUniformSpatialField (fun x : Vec3 => U n (x, t)) =
          regUniformVelocitySlice (U n) t := by
      funext x
      rfl
    rw [hSliceEq] at hsq'
    have hJfun : (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (x, t) j) =
        fun x => regUniformMollifiedInitial ρ (εseq n) (hseq n).1
          (fun y : Vec3 => U n (y, t)) x j := by
      funext x
      rfl
    have hNorm : eLpNorm
        (regUniformSpatialField (fun x : Vec3 => U n (x, t))) 2 volume ≤
        eLpNorm (regUniformSpatialField a) 2 volume := by
      rw [hSliceEq]
      exact hOperatorBound n t ht
    refine ⟨?_, ?_⟩
    · simpa [regUniformMollifiedVelocity, regUniformMollifiedInitial, hSliceEq] using hmem'
    · calc
        (∫ x : Vec3,
          regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (x, t) j ^ 2
            ∂volume) =
            ∫ x : Vec3,
              regUniformMollifiedInitial ρ (εseq n) (hseq n).1
                (fun y : Vec3 => U n (y, t)) x j ^ 2 ∂volume := by
                  apply integral_congr_ae
                  filter_upwards [] with x
                  exact congrArg (fun y : ℝ => y ^ 2) (congrFun hJfun x)
        _ ≤ (eLpNorm
              (regUniformSpatialField (fun x : Vec3 => U n (x, t))) 2 volume).toReal ^ 2 :=
            hsq'
        _ ≤ Adata ^ 2 := by
          apply pow_le_pow_left₀ ENNReal.toReal_nonneg
          calc
            (eLpNorm
                (regUniformSpatialField (fun x : Vec3 => U n (x, t))) 2 volume).toReal ≤
                (eLpNorm (regUniformSpatialField a) 2 volume).toReal :=
              ENNReal.toReal_mono hDataMem.eLpNorm_ne_top hNorm
            _ = Adata := rfl
  exact ⟨hSliceBound, hUcomponent, hOperatorBound, hJcomponent⟩

private theorem regEquicontinuity_modulus_for_sequence
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (s₀ s₁ : ℝ) (hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
    (w : Vec3 → L2Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w)
    (hSlice : ∀ n t, 0 ≤ t →
      MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume)
    (hSliceDiv : ∀ n t, 0 ≤ t →
      IsWeakDivFreeL2 (fun x : Vec3 => uε a ha (εseq n) (x, t)))
    (hUc : ∀ n i, ContinuousOn
      (fun z => uε a ha (εseq n) z i)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDc : ∀ n i j, ContinuousOn
      (fun z => spatialPartial (fun y => uε a ha (εseq n) y i) j z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDDc : ∀ n i j k, ContinuousOn
      (fun z => spatialPartial
        (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) k z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDtc : ∀ n i, ContinuousOn
      (fun z => timePartial (fun y => uε a ha (εseq n) y i) z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hpc : ∀ n, ContinuousOn (pε a ha (εseq n))
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDpc : ∀ n i, ContinuousOn
      (fun z => spatialPartial (fun y => pε a ha (εseq n) y) i z)
      (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hC1 : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ n i, ContDiffOn ℝ 1 (fun z => uε a ha (εseq n) z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ))))
    (hDdiff : ∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
      ∀ i j, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial
          (fun y => uε a ha (εseq n) y i) j (x, z.2)) z.1)
    (hpDiff : ∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
      DifferentiableAt ℝ (fun x : Vec3 => pε a ha (εseq n) (x, z.2)) z.1)
    (hDtBound : ∀ n δ T, 0 < δ → δ < T → ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ spaceTimeSet Set.univ (Icc δ T), ∀ i,
        |timePartial (fun y => uε a ha (εseq n) y i) z| ≤ M)
    (hPDE : ∀ n z, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => uε a ha (εseq n) y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) j z) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
            (uε a ha (εseq n)) z j *
            spatialPartial (fun y => uε a ha (εseq n) y i) j z) +
        spatialPartial (fun y => pε a ha (εseq n) y) i z = 0)
    (hR5 : ∀ n t, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (uε a ha (εseq n))
          (fun z i j => spatialPartial (fun y => uε a ha (εseq n) y i) j z) t =
      eLpNorm (regMollifyVector ρ (εseq n) (hseq n).1
        (regUniformSpatialField a)) 2 volume ^ (2 : ℕ))
    (P : ℝ) (hP0 : 0 ≤ P)
    (hPressure : ∀ n,
      MemLp (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure ∧
      eLpNorm (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
        |(∫ x : Vec3, ∑ i : Fin 3,
            uε a ha (εseq n) (x, t) i * w x i ∂volume) -
          (∫ x : Vec3, ∑ i : Fin 3,
            uε a ha (εseq n) (x, s) i * w x i ∂volume)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
  let U : ℕ → ParabolicPoint → Vec3 := fun n => uε a ha (εseq n)
  let p : ℕ → ParabolicPoint → ℝ := fun n => pε a ha (εseq n)
  let D : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
    spatialPartial (fun y => U n y i) j z
  let DD : ℕ → ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun n z i j k =>
    spatialPartial (fun y => spatialPartial (fun x => U n x i) j y) k z
  let Dt : ℕ → ParabolicPoint → Vec3 := fun n z i =>
    timePartial (fun y => U n y i) z
  let Dp : ℕ → ParabolicPoint → Vec3 := fun n z i =>
    spatialPartial (fun y => p n y) i z
  let toVec3 : L2Vec3 →L[ℝ] Vec3 :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let w' : Vec3 → Vec3 := fun x => toVec3 (w x)
  let W : Fin 3 → Vec3 → ℝ := fun i x => w' x i
  have hw' : ContDiff ℝ (⊤ : ℕ∞) w' := toVec3.contDiff.comp hw
  have hw'c : HasCompactSupport w' := hwc.comp_left (g := toVec3) rfl
  have hWdiff : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hw'
  have hWc : ∀ i, HasCompactSupport (W i) := by
    intro i
    apply HasCompactSupport.of_support_subset_isCompact hw'c.isCompact
    intro x hx
    have hne : w' x ≠ 0 := by
      intro hzero
      exact (Function.mem_support.mp hx) (by simp [W, hzero])
    exact subset_tsupport w' (Function.mem_support.mpr hne)
  let divW : Vec3 → ℝ := fun x => ∑ i : Fin 3, spatialDeriv (W i) i x
  have hdivWdiff : ContDiff ℝ (⊤ : ℕ∞) divW := by
    unfold divW
    exact ContDiff.sum (s := Finset.univ) (fun i _ =>
      contDiff_spatialDeriv_smooth (hWdiff i) i)
  have hdivWc : HasCompactSupport divW := by
    unfold divW
    exact HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i : Fin 3 => spatialDeriv (W i) i)
      (fun i _ => by
        change HasCompactSupport (fun x => (fderiv ℝ (W i) x) (basisVec i))
        exact (hWc i).fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hdivWmem : MemLp divW (ENNReal.ofReal (5 / 2 : ℝ)) volume :=
    hdivWdiff.continuous.memLp_of_hasCompactSupport hdivWc
  let Adata : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
  have hAdata0 : 0 ≤ Adata := ENNReal.toReal_nonneg
  have hDataMem : MemLp (regUniformSpatialField a) 2 volume :=
    lerayHopfLimit_initialField_memLp a ha.1
  obtain ⟨K, hK0, hK⟩ := lerayHopfLimit_pairing_rhs_bound W hWdiff hWc Adata
  let H : ℕ → ℝ → ℝ := fun n t =>
    ∫ x : Vec3, ∑ i : Fin 3, timePartial (fun y => U n y i) (x, t) * W i x
  let R : ℕ → ℝ → ℝ := fun n t =>
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      (U n (x, t) i * spatialDeriv (spatialDeriv (W i) j) j x +
        U n (x, t) i * regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
          (U n) (x, t) j * spatialDeriv (W i) j x)
  let Q : ℕ → ℝ → ℝ := fun n t =>
    ∫ x : Vec3, p n (x, t) * divW x
  let F : ℕ → ℝ → ℝ := fun n t =>
    ∫ x : Vec3, ∑ i : Fin 3, U n (x, t) i * W i x
  obtain ⟨hSliceBound, hUcomponent, hOperatorBound, hJcomponent⟩ :=
    regEquicontinuity_sequence_coordinate_bounds ρ U a εseq hseq hDataMem hSlice hR5
  have hPressureIntegralContinuous : ∀ n,
      ContinuousOn (fun t : ℝ =>
        ∫ x : Vec3, p n (x, t) * divW x ∂volume) (Ioi (0 : ℝ)) := fun n =>
    regEquicontinuity_compact_test_integral_continuous
      (p n) divW (by simpa [p] using hpc n) hdivWdiff hdivWc
  have hHcont : ∀ n, ContinuousOn (H n) (Ioi (0 : ℝ)) := by
    intro n
    exact regEquicontinuity_time_derivative_pairing_continuous
      (U n) W (fun i => hDtc n i) hWdiff hWc
  have hQcont : ∀ n, ContinuousOn (Q n) (Ioi (0 : ℝ)) := by
    intro n
    exact ContinuousOn.congr (hPressureIntegralContinuous n) (fun t ht => rfl)
  have hFderiv : ∀ n t, 0 < t → HasDerivAt (F n) (H n t) t := by
    intro n t ht
    simpa [F, H, U, W] using
      (lerayHopfLimit_regPairing_hasDerivAt (U n) W hWdiff hWc
        (fun i => hUc n i) (fun i => hDtc n i) (fun i => hC1 n i)
        (fun δ T hδ hδT => hDtBound n δ T hδ hδT) ht)
  have hJcontDiff : ∀ n t, 0 < t → ∀ j : Fin 3,
      ContDiff ℝ 1 (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (x, t) j) :=
    fun n t ht j => (lerayHopfLimit_mollifiedInitial_contDiff ρ (εseq n)
      (hseq n).1 (hSlice n t ht.le) j).of_le (by norm_num)
  have hJdiv : ∀ n t, 0 < t → ∀ x,
      ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 =>
          regUniformMollifiedVelocity ρ (εseq n) (hseq n).1 (U n) (y, t) j)
        x (basisVec j) = 0 := fun n t ht =>
    lerayHopfLimit_mollifiedInitial_divergence_eq_zero
      ρ (εseq n) (hseq n).1 (hSliceDiv n t ht.le)
  have hPairingEquation : ∀ n t, 0 < t → H n t = R n t + Q n t := by
    intro n t ht
    simpa [H, R, Q, divW] using
      (regEquicontinuity_pairing_equation_at_time ρ (εseq n) (hseq n).1
        (U n) (p n) W (fun i => hUc n i) (fun i j => hDc n i j)
        (fun i j k => hDDc n i j k) (hpc n) (fun i => hDpc n i)
        (fun i => hC1 n i) (fun z hz i j => hDdiff n z hz i j)
        (fun z hz => hpDiff n z hz) t (hJcontDiff n t ht) (hJdiv n t ht)
        (fun z hz i => hPDE n z hz i) hWdiff hWc ht)
  have hRpointBound : ∀ n t, 0 ≤ t → |R n t| ≤ K := by
    intro n t ht
    have hbound := hK
      (fun i x => U n (x, t) i)
      (fun j x => regUniformMollifiedVelocity ρ (εseq n) (hseq n).1
        (U n) (x, t) j)
      (fun i => (hUcomponent n t ht i).1)
      (fun j => (hJcomponent n t ht j).1)
      (fun i => (hUcomponent n t ht i).2)
      (fun j => (hJcomponent n t ht j).2)
    simpa [R] using hbound
  have hRcont : ∀ n, ContinuousOn (R n) (Ioi (0 : ℝ)) := by
    intro n
    apply ContinuousOn.congr ((hHcont n).sub (hQcont n))
    intro r hr
    change R n r = H n r - Q n r
    rw [hPairingEquation n r hr]
    ring
  have hWcoord : ∀ i x, W i x = (w x).ofLp i := by
    intro i x
    simp [W, w', toVec3, PiLp.coe_continuousLinearEquiv]
  have hPairingEq : ∀ n t,
      F n t = ∫ x : Vec3, ∑ i : Fin 3,
        uε a ha (εseq n) (x, t) i * w x i ∂volume := by
    intro n t
    apply integral_congr_ae
    filter_upwards [] with x
    calc
      (∑ i : Fin 3, U n (x, t) i * W i x) =
          ∑ i : Fin 3, U n (x, t) i * (w x).ofLp i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hWcoord i x]
      _ = ∑ i : Fin 3, uε a ha (εseq n) (x, t) i * w x i := by
        rfl
  obtain ⟨A, B, θ, hA, hB, hθ, hMod⟩ :=
    regEquicontinuity_scalar_holder_modulus F H R Q s₀ s₁ K P hs₀s₁
      hK0 hP0 hFderiv hHcont hQcont hRcont hPairingEquation
      hRpointBound p divW (fun _ _ => rfl) hdivWmem hPressure
  refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
  intro n s t hs ht
  have h := hMod n s t hs ht
  simpa only [← hPairingEq] using h

/-- The regularized momentum and pressure bounds give the time-pairing
modulus required by `lem:compactness`. -/
theorem regEquicontinuity_modulus
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregData : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1),
      (∀ n t, 0 ≤ t →
        MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume) ∧
      (∀ n t, 0 ≤ t →
        IsWeakDivFreeL2 (fun x : Vec3 => uε a ha (εseq n) (x, t))) ∧
      (∀ n i, ContinuousOn
        (fun z => uε a ha (εseq n) z i)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i j, ContinuousOn
        (fun z => spatialPartial (fun y => uε a ha (εseq n) y i) j z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i j k, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) k z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i, ContinuousOn
        (fun z => timePartial (fun y => uε a ha (εseq n) y i) z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n, ContinuousOn (pε a ha (εseq n))
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n i, ContinuousOn
        (fun z => spatialPartial (fun y => pε a ha (εseq n) y) i z)
        (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
       letI : NormedAddCommGroup ParabolicPoint :=
         inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
       letI : NormedSpace ℝ ParabolicPoint :=
         inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
       ∀ n i, ContDiffOn ℝ 1 (fun z => uε a ha (εseq n) z i)
         (spaceTimeSet Set.univ (Ioi (0 : ℝ)))) ∧
      (∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) → ∀ i j,
        DifferentiableAt ℝ
          (fun x : Vec3 => spatialPartial
            (fun y => uε a ha (εseq n) y i) j (x, z.2)) z.1) ∧
      (∀ n z, z ∈ spaceTimeSet Set.univ (Ioi (0 : ℝ)) →
        DifferentiableAt ℝ
          (fun x : Vec3 => pε a ha (εseq n) (x, z.2)) z.1) ∧
      (∀ n δ T, 0 < δ → δ < T → ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ spaceTimeSet Set.univ (Icc δ T), ∀ i,
          |timePartial (fun y => uε a ha (εseq n) y i) z| ≤ M) ∧
      (∀ n z, 0 < z.2 → ∀ i : Fin 3,
        timePartial (fun y => uε a ha (εseq n) y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => uε a ha (εseq n) x i) j y) j z) +
          (∑ j : Fin 3,
            regUniformMollifiedVelocity ρ (εseq n) (_hseq n).1
              (uε a ha (εseq n)) z j *
              spatialPartial (fun y => uε a ha (εseq n) y i) j z) +
          spatialPartial (fun y => pε a ha (εseq n) y) i z = 0) ∧
      (∀ n t, 0 ≤ t →
        eLpNorm (regUniformVelocitySlice (uε a ha (εseq n)) t) 2 volume ^ (2 : ℕ) +
          2 * regUniformDissipation (uε a ha (εseq n))
            (fun z i j => spatialPartial
              (fun y => uε a ha (εseq n) y i) j z) t =
        eLpNorm (regMollifyVector ρ (εseq n) (_hseq n).1
          (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)))
    (hregPressureBound : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1),
      ∃ P : ℝ, 0 ≤ P ∧ ∀ n,
        MemLp (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
          regUniformPositiveTimeMeasure ∧
        eLpNorm (pε a ha (εseq n)) (ENNReal.ofReal (5 / 3 : ℝ))
          regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (C : Set Vec3) (_hC : IsCompact C) (_hCU : C ⊆ (Set.univ : Set Vec3))
      (s₀ s₁ : ℝ) (_hs₀s₁ : Icc s₀ s₁ ⊆ Ioi (0 : ℝ))
      (w : Vec3 → L2Vec3) (_hw : ContDiff ℝ (⊤ : ℕ∞) w)
      (_hwc : HasCompactSupport w) (_hws : tsupport w ⊆ C),
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc s₀ s₁ → t ∈ Icc s₀ s₁ →
          |(∫ x : Vec3, ∑ i : Fin 3,
              uε a ha (εseq n) (x, t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3,
              uε a ha (εseq n) (x, s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ := by
  intro a ha εseq hseq C hC hCU s₀ s₁ hs₀s₁ w hw hwc hws
  rcases hregData a ha εseq hseq with
    ⟨hSlice, hSliceDiv, hUc, hDc, hDDc, hDtc, hpc, hDpc, hC1,
      hDdiff, hpDiff, hDtBound, hPDE, hR5⟩
  obtain ⟨P, hP0, hPressure⟩ := hregPressureBound a ha εseq hseq
  exact regEquicontinuity_modulus_for_sequence ρ uε pε a ha εseq hseq
    s₀ s₁ hs₀s₁ w hw hwc hSlice hSliceDiv hUc hDc hDDc hDtc
    hpc hDpc hC1 hDdiff hpDiff hDtBound hPDE hR5 P hP0 hPressure

end CKN.Leray

end
