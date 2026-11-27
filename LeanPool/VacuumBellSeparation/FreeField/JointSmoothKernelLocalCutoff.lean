/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelUniformBound

/-!
# Actual cutoff extension from a neighborhood of the kernel patch

Only the original kernel's smoothness on an open neighborhood of the
cutoff box is used. The literal product is globally smooth: outside the
cutoff's topological support it is locally zero. Thus singularities of
the original totalized kernel elsewhere impose no global hypothesis.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Set Metric Filter
open scoped SchwartzMap Topology

-- Cache the canonical norm-bounded scalar action on the actual Euclidean product.
local instance jointLocalCutoffContinuousSMul : ContinuousSMul ℝ JointKernelSpace :=
  IsBoundedSMul.continuousSMul

theorem contDiff_jointSmoothCutoff_mul_on (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => jointSmoothCutoff a b x * H x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (jointSmoothCutoff a b)
  · exact ((jointSmoothCutoff a b).smooth (⊤ : ℕ∞)).contDiffAt.mul
      (hH.contDiffAt (hO.mem_nhds (hbox (tsupport_jointSmoothCutoff_subset a b hx))))
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- Cut off joint local kernel. -/
def cutOffJointLocalKernel (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O) :
    SchwartzMap JointKernelSpace ℂ :=
  ((hasCompactSupport_jointSpatialTestProduct (jointUnitCutoffTest a)
    (jointUnitCutoffTest b)).mul_right (f' := H)).toSchwartzMap
      (contDiff_jointSmoothCutoff_mul_on a b H O hO hbox hH)

@[simp] theorem cutOffJointLocalKernel_apply (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O) (x : JointKernelSpace) :
    cutOffJointLocalKernel a b H O hO hbox hH x = jointSmoothCutoff a b x * H x := rfl

theorem cutOffJointLocalKernel_eq (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O)
    (x : JointKernelSpace) (hx : x.fst ∈ closedBall a 1) (hy : x.snd ∈ closedBall b 1) :
    cutOffJointLocalKernel a b H O hO hbox hH x = H x := by
  rw [cutOffJointLocalKernel_apply, jointSmoothCutoff_eq_one a b x hx hy, one_mul]

theorem tsupport_cutOffJointLocalKernel_subset (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O) :
    tsupport (cutOffJointLocalKernel a b H O hO hbox hH) ⊆ jointKernelBox a b 2 :=
  tsupport_mul_subset_left.trans (tsupport_jointSmoothCutoff_subset a b)

theorem norm_iteratedFDeriv_cutOffJointLocalKernel_le
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (O : Set JointKernelSpace) (hO : IsOpen O) (hbox : jointKernelBox a b 2 ⊆ O)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O) (n : ℕ)
    (x : JointKernelSpace) (hx : x ∈ jointKernelBox a b 2) :
    ‖iteratedFDeriv ℝ n (cutOffJointLocalKernel a b H O hO hbox hH) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i *
        ‖iteratedFDeriv ℝ (n - i) H x‖ := by
  have hχ := (jointSmoothCutoff a b).smooth (⊤ : ℕ∞)
  have hHx := hH.contDiffAt (hO.mem_nhds (hbox hx))
  have he (f : JointKernelSpace → ℂ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (k : ℕ) :
      iteratedFDerivWithin ℝ k f O x = iteratedFDeriv ℝ k f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn (hf.of_le (by simp)) (hbox hx)
  have h := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn hH hO.uniqueDiffOn
    (hbox hx) (n := n) (by simp)
  rw [he _ (hχ.contDiffAt.mul hHx) n] at h
  simp_rw [he _ hχ.contDiffAt, he _ hHx] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_jointSmoothCutoff_le a b i x)
      (Nat.cast_nonneg _)) (norm_nonneg _)

/-- The same fixed cutoff constant works when the original kernel is only
smooth near its patch. All derivatives below are its actual derivatives. -/
theorem norm_iteratedFDeriv_cutOffLocal_le_uniform {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (O : Set JointKernelSpace) (hO : IsOpen O) (hbox : jointKernelBox a b 2 ⊆ O)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M)
    {n : ℕ} (hn : n ≤ 2) {x : JointKernelSpace} (hx : x ∈ jointKernelBox a b 2) :
    ‖iteratedFDeriv ℝ n (cutOffJointLocalKernel a b H O hO hbox hH) x‖ ≤
      jointCutoffSecondOrderBound * M := by
  apply (norm_iteratedFDeriv_cutOffJointLocalKernel_le a b H O hO hbox hH n x hx).trans
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i) ≤
      jointCutoffSecondOrderBound := by
    have h0 := jointCutoffDerivativeBound_nonneg 0
    have h1 := jointCutoffDerivativeBound_nonneg 1
    have h2 := jointCutoffDerivativeBound_nonneg 2
    unfold jointCutoffSecondOrderBound
    interval_cases n <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.cast_ofNat, Nat.choose_one_right, zero_add, one_mul] <;> nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hbound (n - i) (by omega) x hx)
        (mul_nonneg (Nat.cast_nonneg _) (jointCutoffDerivativeBound_nonneg i))
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i) * M :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hM

end VacuumBellSeparation
