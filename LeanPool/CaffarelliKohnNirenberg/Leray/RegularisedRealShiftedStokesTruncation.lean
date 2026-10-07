/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral

/-!
# Truncating the real shifted Stokes integral

The translated real Stokes integrand vanishes after its observation
time, so later integration limits give the same value.
-/

public section

open MeasureTheory
open scoped Interval ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A shifted real Stokes integral only uses elapsed times before its
observation time. -/
theorem mildShiftedStokesIntegral_truncate
    (F : ℝ → RealTensorL2)
    (T t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hInt : IntervalIntegrable
      (mildShiftedStokesIntegrand F t) volume 0 T) :
    (∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ) =
      ∫ τ in (0 : ℝ)..t, mildShiftedStokesIntegrand F t τ := by
  have hzeroMem : (0 : ℝ) ∈ Set.uIcc 0 T := Set.left_mem_uIcc
  have htMem : t ∈ Set.uIcc 0 T := Set.mem_uIcc_of_le ht htT
  have hTMem : T ∈ Set.uIcc 0 T := Set.right_mem_uIcc
  have hIt : IntervalIntegrable
      (mildShiftedStokesIntegrand F t) volume 0 t :=
    hInt.mono_set (Set.uIcc_subset_uIcc hzeroMem htMem)
  have hTt : IntervalIntegrable
      (mildShiftedStokesIntegrand F t) volume t T :=
    hInt.mono_set (Set.uIcc_subset_uIcc htMem hTMem)
  have hzero : (∫ τ in t..T, mildShiftedStokesIntegrand F t τ) = 0 := by
    have hEq : (∫ τ in t..T, mildShiftedStokesIntegrand F t τ) =
        ∫ τ in t..T, (0 : RealVectorL2) := by
      apply intervalIntegral.integral_congr_Ioo_of_le htT
      intro τ hτ
      have hnot : ¬(0 < τ ∧ τ < t) := by
        intro h
        exact (not_lt_of_ge hτ.1.le) h.2
      simp [mildShiftedStokesIntegrand, hnot]
    rw [hEq]
    simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIt hTt
  rw [hzero, add_zero] at hadd
  exact hadd.symm

end CKN.Leray

end
