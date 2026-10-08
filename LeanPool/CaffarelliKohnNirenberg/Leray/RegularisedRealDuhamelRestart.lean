/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealStokesIntegralPropagation
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedShiftedStokesTranslation

/-!
# Restart identity for a real Duhamel expression

The heat semigroup propagates the initial value and the earlier Stokes
integral, leaving only the later Stokes contribution after a restart.
-/

public section

open MeasureTheory
open scoped Interval ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The regularized Duhamel expression has the semigroup restart law
for every continuous uniformly bounded tensor path. -/
theorem regularisedRealDuhamel_restart
    (F : ℝ → RealTensorL2) (hF : Continuous F)
    (C : ℝ) (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C)
    (b : RealVectorL2) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    realHeatOperator q hq
      (realHeatOperator a ha b -
        ∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ) -
      (∫ τ in (0 : ℝ)..q,
        mildShiftedStokesIntegrand F (a + q) τ) =
    realHeatOperator (a + q) (add_nonneg ha hq) b -
      (∫ τ in (0 : ℝ)..(a + q),
        mildShiftedStokesIntegrand F (a + q) τ) := by
  let G := mildShiftedStokesIntegrand F (a + q)
  have haT : a ≤ a + q := by linarith only [hq]
  have hqT : q ≤ a + q := by linarith only [ha]
  have hT : 0 ≤ a + q := add_nonneg ha hq
  have hInt : IntervalIntegrable G volume 0 (a + q) :=
    mildShiftedStokesIntegrand_intervalIntegrable
      F hF C hFC hC (a + q) (a + q) hT
  have hzeroMem : (0 : ℝ) ∈ Set.uIcc 0 (a + q) := Set.left_mem_uIcc
  have hqMem : q ∈ Set.uIcc 0 (a + q) := Set.mem_uIcc_of_le hq hqT
  have hTMem : a + q ∈ Set.uIcc 0 (a + q) := Set.right_mem_uIcc
  have hI0 : IntervalIntegrable G volume 0 q :=
    hInt.mono_set (Set.uIcc_subset_uIcc hzeroMem hqMem)
  have hI1 : IntervalIntegrable G volume q (a + q) :=
    hInt.mono_set (Set.uIcc_subset_uIcc hqMem hTMem)
  have hsplit :
      (∫ τ in (0 : ℝ)..(a + q), G τ) =
      (∫ τ in (0 : ℝ)..q, G τ) +
        ∫ τ in q..(a + q), G τ :=
    (intervalIntegral.integral_add_adjacent_intervals hI0 hI1).symm
  have hheat :
      realHeatOperator q hq (realHeatOperator a ha b) =
        realHeatOperator (a + q) (add_nonneg ha hq) b := by
    simpa only [add_comm a q] using
      (realHeatOperator_add q a hq ha b).symm
  have hlinear :
      realHeatOperator q hq
        (realHeatOperator a ha b -
          ∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ) =
      realHeatOperator q hq (realHeatOperator a ha b) -
        realHeatOperator q hq
          (∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ) := by
    simpa only [← realHeatOperatorCLM_apply] using
      map_sub (realHeatOperatorCLM q hq)
        (realHeatOperator a ha b)
        (∫ τ in (0 : ℝ)..a, mildShiftedStokesIntegrand F a τ)
  rw [hlinear, hheat,
    realHeatOperator_shiftedStokesIntegral F hF C hFC hC a q ha hq,
    mildShiftedStokesIntegral_translate_upper F a q ha hq]
  rw [hsplit]
  abel

end CKN.Leray

end
