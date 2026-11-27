/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelCutoff
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Uniform energy control on actual translated kernel boxes

The box has genuine Euclidean six-volume. Translation makes that volume
independent of the two centers. The sixteen Plancherel terms are bounded
using the actual first and mixed directional derivatives, with no extra
rank or kernel-operator hypothesis.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory Set Metric LineDeriv
open scoped SchwartzMap LineDeriv

theorem isCompact_jointKernelBox (a b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    IsCompact (jointKernelBox a b r) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ
    (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))
  have he : jointKernelBox a b r = e.symm '' (closedBall a r ×ˢ closedBall b r) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x.fst, x.snd), hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [he]
  exact ((isCompact_closedBall a r).prod (isCompact_closedBall b r)).image e.symm.continuous

theorem volume_jointKernelBox (a b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (jointKernelBox a b r) = volume (jointKernelBox 0 0 r) := by
  have he : (fun x : JointKernelSpace => x + -(WithLp.toLp 2 (a, b))) ⁻¹'
      jointKernelBox 0 0 r = jointKernelBox a b r := by
    ext x
    change (x.fst - a ∈ closedBall 0 r ∧ x.snd - b ∈ closedBall 0 r) ↔
      (x.fst ∈ closedBall a r ∧ x.snd ∈ closedBall b r)
    simp only [mem_closedBall, dist_eq_norm, sub_zero]
  rw [← he]
  exact measure_preimage_add_right volume _ _

/-- Joint kernel box volume obtained from `volume.real`. -/
def jointKernelBoxVolume : ℝ := volume.real (jointKernelBox 0 0 2)

theorem jointKernelBoxVolume_nonneg : 0 ≤ jointKernelBoxVolume := ENNReal.toReal_nonneg

theorem integral_sq_le_jointKernelBox {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (L : SchwartzMap JointKernelSpace ℂ)
    (hs : tsupport L ⊆ jointKernelBox a b 2)
    (hL : ∀ x ∈ jointKernelBox a b 2, ‖L x‖ ≤ M) :
    (∫ x, ‖L x‖ ^ 2) ≤ M ^ 2 * jointKernelBoxVolume := by
  have he : (∫ x, ‖L x‖ ^ 2) = ∫ x in jointKernelBox a b 2, ‖L x‖ ^ 2 := by
    rw [← integral_indicator (isClosed_jointKernelBox a b 2).measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ jointKernelBox a b 2
      · simp only [indicator_of_mem hx]
      · have hz : L x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (hs h))
        simp only [indicator_of_notMem hx, hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [he]
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure JointKernelSpace)) (isCompact_jointKernelBox a b 2).measure_lt_top
    (f := fun x => ‖L x‖ ^ 2) (C := M ^ 2) (fun x hx => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [hL x hx, norm_nonneg (L x)])
  have hi : 0 ≤ ∫ x in jointKernelBox a b 2, ‖L x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [Real.norm_of_nonneg hi, measureReal_def, volume_jointKernelBox] at h
  exact h

theorem norm_iteratedLineDerivOp_le_iteratedFDeriv {n : ℕ}
    (m : Fin n → JointKernelSpace) (hm : ∀ i, ‖m i‖ ≤ 1)
    (K : SchwartzMap JointKernelSpace ℂ) (x : JointKernelSpace) :
    ‖(∂^{m} K) x‖ ≤ ‖iteratedFDeriv ℝ n K x‖ := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  simpa only [Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ n K x).le_opNorm_mul_prod_of_le hm

theorem norm_jointKernelLeftDirection_le_one (i : Fin 3) : ‖jointKernelLeftDirection i‖ ≤ 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (jointKernelLeftDirection i)
  change ‖jointKernelLeftDirection i‖ ^ 2 =
    ‖EuclideanSpace.basisFun (Fin 3) ℝ i‖ ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 at h
  rw [(EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one i, norm_zero] at h
  nlinarith [norm_nonneg (jointKernelLeftDirection i)]

theorem norm_jointKernelRightDirection_le_one (i : Fin 3) : ‖jointKernelRightDirection i‖ ≤ 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (jointKernelRightDirection i)
  change ‖jointKernelRightDirection i‖ ^ 2 =
    ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + ‖EuclideanSpace.basisFun (Fin 3) ℝ i‖ ^ 2 at h
  rw [(EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one i, norm_zero] at h
  nlinarith [norm_nonneg (jointKernelRightDirection i)]

/-- Only the actual derivatives of orders zero, one and two are used. -/
theorem jointKernelDerivativeEnergy_le {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (K : SchwartzMap JointKernelSpace ℂ)
    (hs : tsupport K ⊆ jointKernelBox a b 2)
    (hK : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n K x‖ ≤ M) :
    jointKernelDerivativeEnergy K ≤ 16 * jointKernelBoxVolume * M ^ 2 := by
  have hline {n : ℕ} (hn : n ≤ 2) (m : Fin n → JointKernelSpace)
      (hm : ∀ i, ‖m i‖ ≤ 1) :
      (∫ x, ‖(∂^{m} K) x‖ ^ 2) ≤ M ^ 2 * jointKernelBoxVolume := by
    apply integral_sq_le_jointKernelBox hM a b _
      ((SchwartzMap.tsupport_iteratedLineDerivOp_subset m K).trans hs)
    intro x hx
    exact (norm_iteratedLineDerivOp_le_iteratedFDeriv m hm K x).trans (hK n hn x hx)
  have h0 : (∫ x, ‖K x‖ ^ 2) ≤ M ^ 2 * jointKernelBoxVolume := by
    apply integral_sq_le_jointKernelBox hM a b K hs
    intro x hx
    simpa only [norm_iteratedFDeriv_zero] using hK 0 (by decide) x hx
  have hL (i : Fin 3) : (∫ x, ‖(∂_{jointKernelLeftDirection i} K) x‖ ^ 2) ≤
      M ^ 2 * jointKernelBoxVolume :=
    hline (n := 1) (by decide) (fun _ => jointKernelLeftDirection i)
      (fun _ => norm_jointKernelLeftDirection_le_one i)
  have hR (j : Fin 3) : (∫ x, ‖(∂_{jointKernelRightDirection j} K) x‖ ^ 2) ≤
      M ^ 2 * jointKernelBoxVolume :=
    hline (n := 1) (by decide) (fun _ => jointKernelRightDirection j)
      (fun _ => norm_jointKernelRightDirection_le_one j)
  have hLR (i j : Fin 3) :
      (∫ x, ‖(∂_{jointKernelLeftDirection i} (∂_{jointKernelRightDirection j} K)) x‖ ^ 2) ≤
        M ^ 2 * jointKernelBoxVolume := by
    exact hline (n := 2) (by decide) ![jointKernelLeftDirection i, jointKernelRightDirection j]
      (by
        intro k
        fin_cases k
        · exact norm_jointKernelLeftDirection_le_one i
        · exact norm_jointKernelRightDirection_le_one j)
  unfold jointKernelDerivativeEnergy mixedKernelDerivativeEnergy
  calc
    _ ≤ (M ^ 2 * jointKernelBoxVolume) +
        (∑ _ : Fin 3, M ^ 2 * jointKernelBoxVolume) +
        (∑ _ : Fin 3, M ^ 2 * jointKernelBoxVolume) +
        ∑ _ : Fin 3, ∑ _ : Fin 3, M ^ 2 * jointKernelBoxVolume :=
      add_le_add (add_le_add (add_le_add h0 (Finset.sum_le_sum fun i _ => hL i))
        (Finset.sum_le_sum fun j _ => hR j))
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hLR i j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end VacuumBellSeparation
