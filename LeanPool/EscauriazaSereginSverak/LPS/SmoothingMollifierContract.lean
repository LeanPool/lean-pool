/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierLemmaAssembly
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpConvolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus

/-!
# Sobolev contraction of normalized convolution

For a smooth compactly supported kernel of mass one, ordered spatial
derivatives commute with convolution, and each differentiated component
contracts in `L²`. This supplies the scale-independent mollifier step in
`eq:lps-Hm-energy`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS

/-- Ordered derivatives of a smooth `L²` field commute with a compact
smooth scalar convolution (`eq:lps-Hm-energy`). -/
theorem lps_wordDeriv_convolution
    {κ f : Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (α : List (Fin 3)) :
    wordDeriv α
      (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution κ (wordDeriv α f)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  induction α generalizing f with
  | nil => rfl
  | cons j α ih =>
      have hweak : HasWeakPartialDerivOn univ j f (spatialDeriv f j) := by
        change HasWeakPartialDerivOn univ j f
          (fun x => (fderiv ℝ f x) (basisVec j))
        exact CKN.HasWeakPartialDerivOn.of_contDiff
          (U := univ) (i := j) (hf.of_le (by simp))
      have hcomm : spatialDeriv
          (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) j =
          convolution κ (spatialDeriv f j)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        funext x
        exact (CKN.Leray.smoothCompactConvolution_spatialDeriv_eq_of_weak
          hκ hκc (hfL2 [])
          ((hfL2 [j]).locallyIntegrable (by norm_num)) j hweak x).2
      have hL2' (β : List (Fin 3)) :
          MemLp (wordDeriv β (spatialDeriv f j)) 2 volume := by
        exact hfL2 (j :: β)
      change wordDeriv α
        (spatialDeriv
          (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) j) = _
      rw [hcomm]
      exact ih (contDiff_wordDeriv hf [j]) hL2'

/-- Normalized nonnegative convolution contracts every ordered
spatial derivative in `L²` (`eq:lps-Hm-energy`). -/
theorem lps_wordDeriv_convolution_eLpNorm_le
    {κ f : Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκone : ∫ x : Vec3, κ x = 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (α : List (Fin 3)) :
    eLpNorm
      (wordDeriv α
        (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume))
      2 volume ≤ eLpNorm (wordDeriv α f) 2 volume := by
  rw [lps_wordDeriv_convolution hκ hκc hf hfL2 α]
  exact CKN.young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    hκnonneg (hκ.continuous.integrable_of_hasCompactSupport hκc)
    hκone hκ.continuous.measurable (hfL2 α).aestronglyMeasurable.aemeasurable

/-- Every ordered derivative of a normalized convolution stays in `L²`
(`eq:lps-Hm-energy`). -/
theorem lps_wordDeriv_convolution_memLp
    {κ f : Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκone : ∫ x : Vec3, κ x = 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (α : List (Fin 3)) :
    MemLp (wordDeriv α
      (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume))
      2 volume := by
  rw [memLp_iff]
  exact (lps_wordDeriv_convolution_eLpNorm_le
    hκ hκc hκnonneg hκone hf hfL2 α).trans_lt
      (hfL2 α).eLpNorm_lt_top

/-- An `L²` seminorm comparison between real fields compares their
quadratic energy integrals (`eq:lps-Hm-energy`). -/
theorem lps_integral_sq_le_of_eLpNorm_le
    {f g : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : eLpNorm f 2 volume ≤ eLpNorm g 2 volume) :
    (∫ x : Vec3, f x ^ 2) ≤ ∫ x : Vec3, g x ^ 2 := by
  have hfFormula : lpNorm f 2 volume = Real.sqrt (∫ x : Vec3, f x ^ 2) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num)
      (by norm_num) hf.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hgFormula : lpNorm g 2 volume = Real.sqrt (∫ x : Vec3, g x ^ 2) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num)
      (by norm_num) hg.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hLp : lpNorm f 2 volume ≤ lpNorm g 2 volume :=
    ENNReal.toReal_mono hg.eLpNorm_ne_top hfg
  rw [hfFormula, hgFormula] at hLp
  have hsq : (Real.sqrt (∫ x : Vec3, f x ^ 2)) ^ 2 ≤
      (Real.sqrt (∫ x : Vec3, g x ^ 2)) ^ 2 := by gcongr
  simpa only [Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))] using hsq

/-- The full ordered integer `H^m` energy contracts under normalized
nonnegative convolution, with constant one at every order
(`eq:lps-Hm-energy`). -/
theorem lps_sobolevNormSq_convolution_le
    {κ f : Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκone : ∫ x : Vec3, κ x = 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α f) 2 volume)
    (m : ℕ) :
    sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ≤
      sobolevNormSqOn m univ (fun α => wordDeriv α f) := by
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  apply Finset.sum_le_sum
  intro α _
  have hnorm := lps_wordDeriv_convolution_eLpNorm_le
    hκ hκc hκnonneg hκone hf hfL2 α
  have hconvMem : MemLp
      (convolution κ (wordDeriv α f)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume := by
    rw [memLp_iff]
    exact (CKN.young_convolution_nonneg_integral_one_of_aemeasurable
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hκnonneg (hκ.continuous.integrable_of_hasCompactSupport hκc)
        hκone hκ.continuous.measurable
        (hfL2 α).aestronglyMeasurable.aemeasurable).trans_lt
          (hfL2 α).eLpNorm_lt_top
  rw [lps_wordDeriv_convolution hκ hκc hf hfL2 α]
  exact lps_integral_sq_le_of_eLpNorm_le hconvMem (hfL2 α)
    (by simpa only [lps_wordDeriv_convolution hκ hκc hf hfL2 α] using hnorm)

end ESS
