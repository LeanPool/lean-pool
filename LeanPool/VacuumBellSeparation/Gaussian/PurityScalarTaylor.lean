/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PurityScalar
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# A genuine scalar Taylor bound on the faithful signed spectrum

The purity scalar is smooth for v>1/2. The even function g(x)=log f_r(|x|)
has a uniform quadratic remainder on each compact signed set a≤|x|≤M,
where a>1/2. Same-sign pairs use the actual Lipschitz derivative on [a,M].
Opposite-sign pairs use their separation by more than one, never a Taylor
expansion across the central interval.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Set
open scoped Topology NNReal ContDiff

/-- Even scalar slope defined as `if 0 ≤ x then deriv f (|x|) else -deriv f (|x|)`. -/
def evenScalarSlope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then deriv f (|x|) else -deriv f (|x|)

theorem abs_evenScalarSlope (f : ℝ → ℝ) (x : ℝ) :
    |evenScalarSlope f x| = |deriv f (|x|)| := by
  unfold evenScalarSlope
  split_ifs <;> simp

theorem hasDerivAt_evenScalar {f : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0) (hf : DifferentiableAt ℝ f (|x|)) :
    HasDerivAt (fun y => f (|y|)) (evenScalarSlope f x) x := by
  by_cases hp : 0 ≤ x
  · have hxpos : 0 < x := lt_of_le_of_ne hp hx.symm
    convert! hf.hasDerivAt.comp x (hasDerivAt_abs_pos hxpos) using 1;
      simp only [evenScalarSlope, ite_eq_left hp, mul_one]
  · convert! hf.hasDerivAt.comp x (hasDerivAt_abs_neg (lt_of_not_ge hp)) using 1;
      simp only [evenScalarSlope, ite_eq_right hp, mul_neg, mul_one]

theorem scalar_remainder_le_of_lipschitz_deriv
    {f : ℝ → ℝ} {a M u v : ℝ} {K : ℝ≥0}
    (hf : ∀ z ∈ Icc a M, DifferentiableAt ℝ f z)
    (hK : LipschitzOnWith K (deriv f) (Icc a M))
    (hu : u ∈ Icc a M) (hv : v ∈ Icc a M) :
    |f v - f u - deriv f u * (v - u)| ≤ (K : ℝ) * (v - u) ^ 2 := by
  have hsub : uIcc u v ⊆ Icc a M := uIcc_subset_Icc hu hv
  have hd (z : ℝ) (hz : z ∈ uIcc u v) :
      HasDerivWithinAt (fun w => f w - deriv f u * w)
        (deriv f z - deriv f u) (uIcc u v) z := by
    convert! ((hf z (hsub hz)).hasDerivAt.sub
      ((hasDerivAt_id z).const_mul (deriv f u))).hasDerivWithinAt using 1;
      simp only [mul_one]
  have hb (z : ℝ) (hz : z ∈ uIcc u v) :
      ‖deriv f z - deriv f u‖ ≤ (K : ℝ) * |v - u| := by
    have h := hK.dist_le_mul z (hsub hz) u hu
    simp only [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (abs_sub_left_of_mem_uIcc hz) K.coe_nonneg)
  have h := (convex_uIcc u v).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb left_mem_uIcc right_mem_uIcc
  have he : (f v - deriv f u * v) - (f u - deriv f u * u) =
      f v - f u - deriv f u * (v - u) := by ring
  rw [he, Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc
    _ ≤ ((K : ℝ) * |v - u|) * |v - u| := h
    _ = _ := by rw [mul_assoc, ← pow_two, sq_abs]

theorem evenScalar_remainder_le_of_compact_bounds
    {f : ℝ → ℝ} {a M K F D : ℝ} (ha : 1 / 2 < a)
    (hK : 0 ≤ K) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hquad : ∀ u ∈ Icc a M, ∀ v ∈ Icc a M,
      |f v - f u - deriv f u * (v - u)| ≤ K * (v - u) ^ 2)
    (hf : ∀ u ∈ Icc a M, |f u| ≤ F)
    (hd : ∀ u ∈ Icc a M, |deriv f u| ≤ D)
    {x y : ℝ} (hx : |x| ∈ Icc a M) (hy : |y| ∈ Icc a M) :
    |f (|y|) - f (|x|) - evenScalarSlope f x * (y - x)| ≤
      (K + 2 * F + D) * (y - x) ^ 2 := by
  have hfar (hsep : 1 ≤ |y - x|) :
      |f (|y|) - f (|x|) - evenScalarSlope f x * (y - x)| ≤
        (K + 2 * F + D) * (y - x) ^ 2 := by
    have hb : |f (|y|) - f (|x|) - evenScalarSlope f x * (y - x)| ≤
        2 * F + D * |y - x| := by
      calc
        _ ≤ |f (|y|) - f (|x|)| + |evenScalarSlope f x * (y - x)| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (f (|y|) - f (|x|)) 0 (evenScalarSlope f x * (y - x))
        _ ≤ (|f (|y|)| + |f (|x|)|) + |evenScalarSlope f x * (y - x)| := by
          exact add_le_add (by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (f (|y|)) 0 (f (|x|))) le_rfl
        _ ≤ (F + F) + D * |y - x| := by
          rw [abs_mul, abs_evenScalarSlope]
          gcongr
          · exact hf _ hy
          · exact hf _ hx
          · exact hd _ hx
        _ = _ := by ring
    have hs : 1 ≤ (y - x) ^ 2 := by nlinarith [sq_abs (y - x)]
    have hl : |y - x| ≤ (y - x) ^ 2 := by nlinarith [sq_abs (y - x)]
    have hF' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * F by positivity)
    have hD' := mul_le_mul_of_nonneg_left hl hD
    have hK' := mul_nonneg hK (sq_nonneg (y - x))
    nlinarith
  have hraise : K * (y - x) ^ 2 ≤ (K + 2 * F + D) * (y - x) ^ 2 := by
    gcongr
    linarith
  by_cases hx0 : 0 ≤ x
  · by_cases hy0 : 0 ≤ y
    · apply le_trans ?_ hraise
      simpa only [evenScalarSlope, ite_eq_left hx0, abs_of_nonneg hx0, abs_of_nonneg hy0]
        using hquad |x| hx |y| hy
    · apply hfar
      rw [abs_of_nonpos (by linarith : y - x ≤ 0)]
      rw [abs_of_nonneg hx0] at hx
      rw [abs_of_neg (lt_of_not_ge hy0)] at hy
      linarith [hx.1, hy.1]
  · by_cases hy0 : 0 ≤ y
    · apply hfar
      rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      rw [abs_of_neg (lt_of_not_ge hx0)] at hx
      rw [abs_of_nonneg hy0] at hy
      linarith [hx.1, hy.1]
    · apply le_trans ?_ hraise
      have h := hquad |x| hx |y| hy
      simp only [evenScalarSlope, ite_eq_right hx0, abs_of_neg (lt_of_not_ge hx0),
        abs_of_neg (lt_of_not_ge hy0)] at h ⊢
      convert h using 1 <;> congr 1 <;> ring

theorem contDiffAt_logPurityFactor {r v : ℝ} (hr : 0 < r) (hv : 1 / 2 < v)
    (n : ℕ∞ω) : ContDiffAt ℝ n (logPurityFactor r) v := by
  have hp : ContDiffAt ℝ n (fun x : ℝ => (x + 1 / 2) ^ r) v :=
    (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (by
      change v + 1 / 2 ≠ 0
      linarith)
  have hm : ContDiffAt ℝ n (fun x : ℝ => (x - 1 / 2) ^ r) v :=
    (contDiffAt_id.sub contDiffAt_const).rpow_const_of_ne (by
      change v - 1 / 2 ≠ 0
      linarith)
  exact (hp.sub hm).log (purityFactor_pos hr hv.le).ne'

theorem contDiffOn_logPurityFactor {r : ℝ} (hr : 0 < r) (n : ℕ∞ω) :
    ContDiffOn ℝ n (logPurityFactor r) (Ioi (1 / 2)) :=
  fun _ hv => (contDiffAt_logPurityFactor hr hv n).contDiffWithinAt

/-- The actual scalar hypothesis needed for the aggregate Hermitian trace
derivative, proved uniformly on a compact faithful signed spectral set. -/
theorem exists_even_logPurityFactor_quadratic_remainder
    {r a M : ℝ} (hr : 0 < r) (ha : 1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ |x| → |x| ≤ M →
      a ≤ |y| → |y| ≤ M →
      |logPurityFactor r (|y|) - logPurityFactor r (|x|) -
          evenScalarSlope (logPurityFactor r) x * (y - x)| ≤ C * (y - x) ^ 2 := by
  have hsub : Icc a M ⊆ Ioi (1 / 2) := fun _ h => ha.trans_le h.1
  have hfd : ContDiffOn ℝ 1 (deriv (logPurityFactor r)) (Icc a M) :=
    ((contDiffOn_logPurityFactor hr 2).deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  obtain ⟨K, hK⟩ := hfd.exists_lipschitzOnWith (by norm_num) (convex_Icc a M) isCompact_Icc
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((contDiffOn_logPurityFactor hr 2).continuousOn).mono hsub)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hfd.continuousOn
  refine ⟨(K : ℝ) + 2 * max F 0 + max D 0, by positivity, ?_⟩
  intro x y hxa hxM hya hyM
  apply evenScalar_remainder_le_of_compact_bounds ha K.coe_nonneg
    (le_max_right _ _) (le_max_right _ _)
    (fun u hu v hv => scalar_remainder_le_of_lipschitz_deriv
      (fun z hz => (contDiffAt_logPurityFactor hr (hsub hz) 2).differentiableAt
        (by norm_num)) hK hu hv)
    (fun u hu => (show |logPurityFactor r u| ≤ F from by
      simpa only [Real.norm_eq_abs] using hF u hu).trans (le_max_left _ _))
    (fun u hu => (show |deriv (logPurityFactor r) u| ≤ D from by
      simpa only [Real.norm_eq_abs] using hD u hu).trans (le_max_left _ _))
    ⟨hxa, hxM⟩ ⟨hya, hyM⟩

end VacuumBellSeparation.Gaussian
