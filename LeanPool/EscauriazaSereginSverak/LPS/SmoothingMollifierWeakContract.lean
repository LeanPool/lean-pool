/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierContract
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall

/-!
# Mollifier contraction for weak Sobolev data

The restart datum is an `H^m` equivalence class, not a smooth field.
Transporting each weak derivative through convolution gives the same
scale-independent ordered Sobolev contraction at the initial time.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Every ordered classical derivative of the mollified base field is
convolution of the corresponding specified weak derivative
(`eq:lps-Hm-energy`). -/
theorem lps_wordDeriv_convolution_weak_family
    {κ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    {m : ℕ} (hD : IsSobolevFamilyOn m univ f D)
    (α : List (Fin 3)) (hα : α.length ≤ m) :
    wordDeriv α
      (convolution κ (D []) (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution κ (D α) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  have hmem (β : List (Fin 3)) (hβ : β.length ≤ m) :
      MemLp (D β) 2 volume := by
    simpa only [Measure.restrict_univ] using hD.memL2 β hβ
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α j ih =>
      have hlen : α.length < m := by
        simpa using hα
      have hαm : α.length ≤ m := hlen.le
      have hweak := hD.weak α j hlen
      have hconv (x : Vec3) :=
        (CKN.Leray.smoothCompactConvolution_spatialDeriv_eq_of_weak
          hκ hκc (hmem α hαm)
          ((hmem (α ++ [j]) hα).locallyIntegrable (by norm_num))
          j hweak x).2
      rw [wordDeriv_append, ih hαm]
      funext x
      exact hconv x

/-- Normalized convolution contracts the full ordered `H^m` energy
of a weak Sobolev family (`eq:lps-Hm-energy`). -/
theorem lps_sobolevNormSq_convolution_weak_le
    {κ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκone : ∫ x : Vec3, κ x = 1)
    {m : ℕ} (hD : IsSobolevFamilyOn m univ f D) :
    sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (convolution κ (D []) (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ≤
      sobolevNormSqOn m univ D := by
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  apply Finset.sum_le_sum
  intro α hα
  have hlen : α.length ≤ m := mem_sobolevWords.mp hα
  have hmem : MemLp (D α) 2 volume := by
    simpa only [Measure.restrict_univ] using hD.memL2 α hlen
  have hnorm : eLpNorm
      (convolution κ (D α) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      2 volume ≤ eLpNorm (D α) 2 volume :=
    CKN.young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hκnonneg (hκ.continuous.integrable_of_hasCompactSupport hκc)
      hκone hκ.continuous.measurable hmem.aestronglyMeasurable.aemeasurable
  have hconvMem : MemLp
      (convolution κ (D α) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      2 volume := by
    rw [memLp_iff]
    exact hnorm.trans_lt hmem.eLpNorm_lt_top
  rw [lps_wordDeriv_convolution_weak_family hκ hκc hD α hlen]
  exact lps_integral_sq_le_of_eLpNorm_le hconvMem hmem hnorm

/-- Replacing the Sobolev family's order-zero representative by its
underlying field leaves the mollification unchanged and preserves
the `H^m` contraction (`eq:lps-Hm-energy`). -/
theorem lps_sobolevNormSq_convolution_weak_input_le
    {κ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    (hκone : ∫ x : Vec3, κ x = 1)
    {m : ℕ} (hD : IsSobolevFamilyOn m univ f D) :
    sobolevNormSqOn m univ
      (fun α => wordDeriv α
        (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume)) ≤
      sobolevNormSqOn m univ D := by
  have hzero : D [] =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using hD.zero
  have hconv :
      convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution κ (D []) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    exact MeasureTheory.convolution_congr
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (ae_eq_refl _) hzero.symm
  rw [hconv]
  exact lps_sobolevNormSq_convolution_weak_le
    hκ hκc hκnonneg hκone hD

end ESS
