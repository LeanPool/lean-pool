/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Reg Tails Time Bounds

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The time integral of a nonnegative `L²` quantity is controlled by its
space-time energy and the square root of the slab length. -/
theorem regTails_time_integral_le_of_sq_integral
    {T E : ℝ} (hT : 0 < T) (hE : 0 ≤ E)
    (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) T)))
    (hg0 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), 0 ≤ g t)
    (henergy : ∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume ≤ E ^ 2 / 2) :
    ∫ t in Ioo (0 : ℝ) T, g t ∂volume ≤ E * T ^ (1 / 2 : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    exact memLp_const 1
  have hconst0 : 0 ≤ᵐ[μ] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [] with _
    norm_num
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) ⟨by norm_num, by norm_num, by norm_num⟩
    hconst0 hg0 hconst hg'
  have hmeasure : μ.real Set.univ = T := by
    simp [μ, Measure.real, Real.volume_Ioo, hT.le]
  have hleft : (∫ t : ℝ, (1 : ℝ) * g t ∂μ) =
      ∫ t in Ioo (0 : ℝ) T, g t ∂volume := by
    simp [μ]
  have hright1 : (∫ t : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) = T := by
    simp [hmeasure]
  have hright2 : (∫ t : ℝ, g t ^ (2 : ℝ) ∂μ) ≤ E ^ 2 / 2 := by
    have hpow : (fun t : ℝ => g t ^ (2 : ℝ)) =ᵐ[μ]
        fun t => g t ^ (2 : ℕ) := by
      filter_upwards [] with t
      simp
    have hint : (∫ t : ℝ, g t ^ (2 : ℝ) ∂μ) =
        ∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume := by
      calc
        _ = ∫ t : ℝ, g t ^ (2 : ℕ) ∂μ := integral_congr_ae hpow
        _ = _ := by rfl
    rw [hint]
    exact henergy
  rw [hleft, hright1] at hholder
  calc
    ∫ t in Ioo (0 : ℝ) T, g t ∂volume ≤
        T ^ (1 / 2 : ℝ) * (E ^ 2 / 2) ^ (1 / 2 : ℝ) := by
          calc
            _ ≤ T ^ (1 / 2 : ℝ) *
                (∫ t : ℝ, g t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
              simpa [mul_comm, Real.rpow_one] using hholder
            _ ≤ _ := by
              have hpowerNonneg :
                  0 ≤ᵐ[μ] fun t : ℝ => g t ^ (2 : ℝ) := by
                filter_upwards [] with t
                simpa only [Pi.zero_apply, Real.rpow_ofNat] using sq_nonneg (g t)
              have hnonneg : 0 ≤ ∫ t : ℝ, g t ^ (2 : ℝ) ∂μ :=
                integral_nonneg_of_ae hpowerNonneg
              have hrpow :
                  (∫ t : ℝ, g t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
                    (E ^ 2 / 2) ^ (1 / 2 : ℝ) :=
                Real.rpow_le_rpow hnonneg hright2 (by norm_num)
              exact mul_le_mul_of_nonneg_left hrpow
                (Real.rpow_nonneg hT.le (1 / 2 : ℝ))
    _ ≤ E * T ^ (1 / 2 : ℝ) := by
      have hroot : (E ^ 2 / 2) ^ (1 / 2 : ℝ) ≤ E := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        constructor
        · exact hE
        · nlinarith only [sq_nonneg E]
      calc
        T ^ (1 / 2 : ℝ) * (E ^ 2 / 2) ^ (1 / 2 : ℝ) ≤
            T ^ (1 / 2 : ℝ) * E :=
          mul_le_mul_of_nonneg_left hroot
            (Real.rpow_nonneg hT.le (1 / 2 : ℝ))
        _ = E * T ^ (1 / 2 : ℝ) := by ring

/-- The `3/2` time moment is controlled by the same `L²` energy and the
quarter power of the slab length. -/
theorem regTails_time_rpow_three_halves_le_of_sq_integral
    {T E : ℝ} (hT : 0 < T) (hE : 0 ≤ E)
    (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) T)))
    (hg0 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), 0 ≤ g t)
    (henergy : ∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume ≤ E ^ 2 / 2) :
    ∫ t in Ioo (0 : ℝ) T, g t ^ (3 / 2 : ℝ) ∂volume ≤
      E ^ (3 / 2 : ℝ) * T ^ (1 / 4 : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have hpowMem : MemLp (fun t : ℝ => |g t| ^ (3 / 2 : ℝ))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
    have h := hg'.norm_rpow_div (ENNReal.ofReal (3 / 2 : ℝ))
    have hexp : ENNReal.ofReal (4 / 3 : ℝ) =
        (ENNReal.ofReal 2) / ENNReal.ofReal (3 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < (3 / 2 : ℝ))]
      congr 1
      norm_num
    simpa only [hexp, Real.norm_eq_abs, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      using h
  have hpowMem' : MemLp (fun t : ℝ => g t ^ (3 / 2 : ℝ))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
    apply (memLp_congr_ae ?_).mp hpowMem
    filter_upwards [hg0] with t ht
    rw [abs_of_nonneg ht]
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 4) μ := by
    exact memLp_const 1
  have hconst0 : 0 ≤ᵐ[μ] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [] with _
    norm_num
  have hpow0 : 0 ≤ᵐ[μ] (fun t : ℝ => g t ^ (3 / 2 : ℝ)) := by
    filter_upwards [hg0] with t ht
    exact Real.rpow_nonneg ht _
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 4 / 3) (q := 4) ⟨by norm_num, by norm_num, by norm_num⟩
    hpow0 hconst0 hpowMem' hconst
  have hmeasure : μ.real Set.univ = T := by
    simp [μ, Measure.real, Real.volume_Ioo, hT.le]
  have hleft : (∫ t : ℝ, g t ^ (3 / 2 : ℝ) * (1 : ℝ) ∂μ) =
      ∫ t in Ioo (0 : ℝ) T, g t ^ (3 / 2 : ℝ) ∂volume := by
    simp [μ]
  have hright1 : (∫ t : ℝ, (1 : ℝ) ^ (4 : ℝ) ∂μ) = T := by
    simp [hmeasure]
  have hpow :
      (fun t : ℝ => (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)) =ᵐ[μ]
        fun t => g t ^ (2 : ℝ) := by
    filter_upwards [hg0] with t ht
    rw [← Real.rpow_mul ht]
    congr 1
    norm_num
  have hright2 :
      (∫ t : ℝ, (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) ∂μ) ≤ E ^ 2 / 2 := by
    have hint :
        (∫ t : ℝ, (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) ∂μ) =
          ∫ t : ℝ, g t ^ (2 : ℝ) ∂μ := integral_congr_ae hpow
    rw [hint]
    have hpowNat : (fun t : ℝ => g t ^ (2 : ℝ)) =ᵐ[μ]
        fun t => g t ^ (2 : ℕ) := by
      filter_upwards [] with t
      simp
    have hint' : (∫ t : ℝ, g t ^ (2 : ℝ) ∂μ) =
        ∫ t in Ioo (0 : ℝ) T, g t ^ (2 : ℕ) ∂volume := by
      calc
        _ = ∫ t : ℝ, g t ^ (2 : ℕ) ∂μ := integral_congr_ae hpowNat
        _ = _ := by rfl
    rw [hint']
    exact henergy
  rw [hleft, hright1] at hholder
  have hpowerNonneg :
      0 ≤ᵐ[μ] (fun t : ℝ => (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)) := by
    filter_upwards [hg0] with t ht
    exact Real.rpow_nonneg (Real.rpow_nonneg ht _) _
  have hnonneg : 0 ≤ ∫ t : ℝ,
      (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) ∂μ :=
    integral_nonneg_of_ae hpowerNonneg
  have hholderPower :
      (∫ t : ℝ, (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) ∂μ) ^ (3 / 4 : ℝ) ≤
        E ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (E ^ 2 / 2) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hnonneg hright2 (by norm_num)
      _ ≤ (E ^ 2) ^ (3 / 4 : ℝ) := by
        apply Real.rpow_le_rpow
        · positivity
        · nlinarith only [sq_nonneg E]
        · norm_num
      _ = E ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast E 2]
        calc
          (E ^ (2 : ℝ)) ^ (3 / 4 : ℝ) = E ^ ((2 : ℝ) * (3 / 4 : ℝ)) :=
            (Real.rpow_mul hE _ _).symm
          _ = E ^ (3 / 2 : ℝ) := by congr 1; norm_num
  calc
    ∫ t in Ioo (0 : ℝ) T, g t ^ (3 / 2 : ℝ) ∂volume ≤
        T ^ (1 / 4 : ℝ) * E ^ (3 / 2 : ℝ) := by
          calc
            _ ≤ T ^ (1 / 4 : ℝ) *
                (∫ t : ℝ, (g t ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) ∂μ) ^
                  (3 / 4 : ℝ) := by
              simpa [mul_comm] using hholder
            _ ≤ _ := mul_le_mul_of_nonneg_left hholderPower
              (Real.rpow_nonneg hT.le (1 / 4 : ℝ))
    _ = E ^ (3 / 2 : ℝ) * T ^ (1 / 4 : ℝ) := by ring

end CKN.Leray

end
