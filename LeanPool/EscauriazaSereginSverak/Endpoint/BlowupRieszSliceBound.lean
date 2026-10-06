/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszSliceAE

/-!
# Blowup Riesz Slice Bound

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A uniform bound on the nine tensor-component slice norms gives the
corresponding Riesz pressure slice bound. -/
theorem blowup_rieszPressureSpaceTime_slice_norm_bound
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {a b : ℝ} (M : ℝ)
    (hinput : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      ∀ i j : Fin 3,
        lpNorm (fun x : Vec3 => F i j (x,t))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
      MemLp (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) F hF (x,t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      eLpNorm (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) F hF (x,t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) * (9 * M)) := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  have hSlices := ae_restrict_of_ae (s := Ioo a b)
    (CKN.Leray.rieszPressureSpaceTime_slice_ae_eq
      (3 / 2 : ℝ) (by norm_num) F hF)
  filter_upwards [hSlices, hinput] with t ⟨hFt, hEq⟩ ht
  let C : CKN.Leray.PressureTensorLp (3 / 2 : ℝ) :=
    fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x,t))
  let P := CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C
  have hpMem : MemLp (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF (x,t))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := (Lp.memLp P).ae_eq hEq.symm
  refine ⟨hpMem, ?_⟩
  have hpClass : hpMem.toLp (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF (x,t)) = P := by
    apply Lp.ext
    filter_upwards [hpMem.coeFn_toLp, hEq] with x hx hpx
    exact hx.trans hpx
  have hBoundNonneg : 0 ≤ CKN.Leray.rieszPressureOperatorBound
      (3 / 2 : ℝ) (by norm_num) :=
    (norm_nonneg (CKN.Leray.rieszPressureOperator
      (3 / 2 : ℝ) (by norm_num) 0 0)).trans
      (CKN.Leray.rieszPressureOperator_norm_le (3 / 2 : ℝ)
        (by norm_num) 0 0)
  have hCsum : (∑ i : Fin 3, ∑ j : Fin 3, ‖C i j‖) ≤ 9 * M := by
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, M := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [C, Lp.norm_toLp, lpNorm] using ht i j
      _ = 9 * M := by simp; ring
  have hPbound : ‖P‖ ≤ CKN.Leray.rieszPressureOperatorBound
      (3 / 2 : ℝ) (by norm_num) * (9 * M) := by
    calc
      ‖P‖ ≤ CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖C i j‖ :=
        CKN.Leray.rieszPressureSlice_norm_le (3 / 2 : ℝ) (by norm_num) C
      _ ≤ _ := mul_le_mul_of_nonneg_left hCsum hBoundNonneg
  calc
    eLpNorm (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) F hF (x,t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume =
      ENNReal.ofReal ‖hpMem.toLp (fun x : Vec3 =>
        CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) F hF (x,t))‖ := by
        rw [Lp.norm_toLp]
        exact (ENNReal.ofReal_toReal hpMem.eLpNorm_lt_top.ne).symm
    _ = ENNReal.ofReal ‖P‖ := by rw [hpClass]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hPbound

end ESS
