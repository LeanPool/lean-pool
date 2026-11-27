/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelForms
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Fixed-size translated cutoffs for the four kernel patches

Each real cutoff is one on its radius-one ball and supported in the
radius-two ball. Their product is an actual Schwartz map on the Euclidean
six-dimensional carrier. Translation preserves every derivative bound;
the constants below are values of one fixed Schwartz seminorm.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Set Metric
open scoped SchwartzMap

/-- Joint unit bump represented by `1`. -/
def jointUnitBump (a : EuclideanSpace ℝ (Fin 3)) : ContDiffBump a :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- Joint unit cutoff test represented by `jointUnitBump a`. -/
def jointUnitCutoffTest (a : EuclideanSpace ℝ (Fin 3)) : SpatialTestFunction :=
  ⟨jointUnitBump a, (jointUnitBump a).contDiff, (jointUnitBump a).hasCompactSupport⟩

theorem jointUnitCutoffTest_eq_one (a x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ closedBall a 1) : (jointUnitCutoffTest a).1 x = 1 :=
  (jointUnitBump a).one_of_mem_closedBall hx

theorem tsupport_jointUnitCutoffTest (a : EuclideanSpace ℝ (Fin 3)) :
    tsupport (jointUnitCutoffTest a).1 = closedBall a 2 :=
  (jointUnitBump a).tsupport_eq

theorem jointUnitCutoffTest_translate (a x : EuclideanSpace ℝ (Fin 3)) :
    (jointUnitCutoffTest a).1 x = (jointUnitCutoffTest 0).1 (x - a) := by
  simp only [jointUnitCutoffTest, ContDiffBump.apply, jointUnitBump, sub_zero]

/-- Joint smooth cutoff obtained from `jointSpatialTestProduct`. -/
def jointSmoothCutoff (a b : EuclideanSpace ℝ (Fin 3)) : SchwartzMap JointKernelSpace ℂ :=
  jointSpatialTestProduct (jointUnitCutoffTest a) (jointUnitCutoffTest b)

@[simp] theorem jointSmoothCutoff_apply (a b : EuclideanSpace ℝ (Fin 3))
    (x : JointKernelSpace) :
    jointSmoothCutoff a b x =
      ((jointUnitCutoffTest a).1 x.fst : ℂ) * ((jointUnitCutoffTest b).1 x.snd : ℂ) := rfl

theorem jointSmoothCutoff_eq_one (a b : EuclideanSpace ℝ (Fin 3))
    (x : JointKernelSpace) (hx : x.fst ∈ closedBall a 1) (hy : x.snd ∈ closedBall b 1) :
    jointSmoothCutoff a b x = 1 := by
  rw [jointSmoothCutoff_apply, jointUnitCutoffTest_eq_one a x.fst hx,
    jointUnitCutoffTest_eq_one b x.snd hy, Complex.ofReal_one, one_mul]

/-- Set of points satisfying the joint kernel box condition with membership specified by `{x |
x.fst ∈ closedBall a r ∧ x.snd ∈ closedBall b r}`. -/
def jointKernelBox (a b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) : Set JointKernelSpace :=
  {x | x.fst ∈ closedBall a r ∧ x.snd ∈ closedBall b r}

theorem isClosed_jointKernelBox (a b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    IsClosed (jointKernelBox a b r) :=
  (isClosed_closedBall.preimage
    (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).continuous).inter
  (isClosed_closedBall.preimage
    (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).continuous)

theorem tsupport_jointSmoothCutoff_subset (a b : EuclideanSpace ℝ (Fin 3)) :
    tsupport (jointSmoothCutoff a b) ⊆ jointKernelBox a b 2 := by
  apply closure_minimal ?_ (isClosed_jointKernelBox a b 2)
  intro x hx
  have hh : ((jointUnitCutoffTest a).1 x.fst : ℂ) ≠ 0 ∧
      ((jointUnitCutoffTest b).1 x.snd : ℂ) ≠ 0 := mul_ne_zero_iff.mp hx
  have ha : x.fst ∈ tsupport (jointUnitCutoffTest a).1 := subset_tsupport _ (by exact_mod_cast hh.1)
  have hb : x.snd ∈ tsupport (jointUnitCutoffTest b).1 := subset_tsupport _ (by exact_mod_cast hh.2)
  exact ⟨by rwa [tsupport_jointUnitCutoffTest] at ha,
    by rwa [tsupport_jointUnitCutoffTest] at hb⟩

theorem jointSmoothCutoff_translate (a b : EuclideanSpace ℝ (Fin 3)) :
    (jointSmoothCutoff a b : JointKernelSpace → ℂ) =
      fun x => jointSmoothCutoff 0 0 (x - WithLp.toLp 2 (a, b)) := by
  funext x
  rw [jointSmoothCutoff_apply, jointSmoothCutoff_apply,
    jointUnitCutoffTest_translate a, jointUnitCutoffTest_translate b]
  rfl

/-- Finite constants come from one actual fixed compact cutoff. -/
def jointCutoffDerivativeBound (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 n (jointSmoothCutoff 0 0)

theorem jointCutoffDerivativeBound_nonneg (n : ℕ) : 0 ≤ jointCutoffDerivativeBound n :=
  apply_nonneg _ _

/-- Uniformity is exact translation invariance, for every derivative order. -/
theorem norm_iteratedFDeriv_jointSmoothCutoff_le (a b : EuclideanSpace ℝ (Fin 3))
    (n : ℕ) (x : JointKernelSpace) :
    ‖iteratedFDeriv ℝ n (jointSmoothCutoff a b) x‖ ≤ jointCutoffDerivativeBound n := by
  rw [jointSmoothCutoff_translate, iteratedFDeriv_comp_sub]
  exact (jointSmoothCutoff 0 0).norm_iteratedFDeriv_le_seminorm ℝ n _

/-- A genuinely smooth scalar kernel times the actual fixed-size cutoff
is Schwartz, regardless of its behavior at spatial infinity. -/
def cutOffJointSmoothKernel (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) : SchwartzMap JointKernelSpace ℂ :=
  ((hasCompactSupport_jointSpatialTestProduct (jointUnitCutoffTest a)
    (jointUnitCutoffTest b)).mul_right (f' := H)).toSchwartzMap
      (((jointSmoothCutoff a b).smooth (⊤ : ℕ∞)).mul hH)

@[simp] theorem cutOffJointSmoothKernel_apply (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (x : JointKernelSpace) :
    cutOffJointSmoothKernel a b H hH x = jointSmoothCutoff a b x * H x := rfl

theorem cutOffJointSmoothKernel_eq (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (x : JointKernelSpace) (hx : x.fst ∈ closedBall a 1) (hy : x.snd ∈ closedBall b 1) :
    cutOffJointSmoothKernel a b H hH x = H x := by
  rw [cutOffJointSmoothKernel_apply, jointSmoothCutoff_eq_one a b x hx hy, one_mul]

theorem norm_iteratedFDeriv_cutOffJointSmoothKernel_le
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (n : ℕ) (x : JointKernelSpace) :
    ‖iteratedFDeriv ℝ n (cutOffJointSmoothKernel a b H hH) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i *
        ‖iteratedFDeriv ℝ (n - i) H x‖ := by
  apply (norm_iteratedFDeriv_mul_le ((jointSmoothCutoff a b).smooth (⊤ : ℕ∞)) hH x (by simp)).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_jointSmoothCutoff_le a b i x)
      (Nat.cast_nonneg _)) (norm_nonneg _)

end VacuumBellSeparation
