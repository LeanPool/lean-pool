/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicBallMeanValue

/-!
# HarmonicInteriorGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The interior gradient estimate for the coordinate Laplacian on `Vec d`

Mathlib has no interior gradient estimate for harmonic functions outside the
complex plane, and its harmonic layer is stated for `InnerProductSpace R E`, which
the sup-normed carrier `Vec d` does not satisfy.  This module proves the
estimate natively for CoarseGraining's `euclideanCoordLaplacian`, in the
dimensional form

```
  |d_i u (z)| <= C (d) / r * avg_{B (z, r)} |u| .
```

The proof needs neither the divergence theorem nor a surface measure.  It runs
the kernel mean value property of `HarmonicMeanValue` on the harmonic function
`d_i u` and then moves the derivative onto the kernel with the single
integration by parts of `HarmonicGreen`:

1. **`d_i u` is harmonic.**  For a `C^infty` function, CoarseGraining's
   `euclideanCoordThirdDeriv_diag_right_comm` gives `d_j d_j d_i u = d_i d_j
   d_j u` pointwise, so the coordinate Laplacian of `d_i u` is the `i`-th
   coordinate derivative of the coordinate Laplacian of `u`, which vanishes
   identically on the open set where `u` is harmonic.
2. **A `C^1` annulus kernel.**  `posPartSq s = (max 0 s)^2` is `C^1` with
   derivative `2 max 0 s` -- the only delicate point being the corner at the
   origin, where the slope is computed directly -- so
   `gradKernel a b t = posPartSq (t - a) * posPartSq (b - t)` is a `C^1`
   nonnegative kernel supported in `[a, b]`, positive on `(a, b)`, with the
   explicit derivative bound `|gradKernel' | <= 4 (b - a)^3`.
3. **The pairing.**  With `a = r/4` and `b = r/2`, the mean value property gives
   `d_i u (z) * int K = int (d_i u) K`, integration by parts turns the right side
   into `- int u (d_i K)`, and `|d_i K| <= 4 (b - a)^3` on the ball of radius
   `b < r` yields `|d_i u (z)| * int K <= 4 (b - a)^3 * int_{B (z, r)} |u|`.
4. **The scaling.**  The kernel mass is bounded below on the explicit annulus
   `5 r / 16 < |x - z| < 7 r / 16`, where `gradKernel >= (r/16)^4`, by the ball
   volumes of `HarmonicGauge`; the resulting lower bound is proportional to
   `r^(d + 4)`, which is exactly what turns the estimate into the stated
   `C (d) / r` form.  The unit ball volume cancels, leaving the explicit
   admissible constant `4096 / ((7/16)^d - (6/16)^d)`.

## Contents

* `posPartSq`, `hasDerivAt_posPartSq`, `contDiff_posPartSq` -- the `C^1`
  one-sided square.
* `gradKernel`, `gradKernelDeriv`, `hasDerivAt_gradKernel`,
  `pow_four_le_gradKernel`, `abs_gradKernelDeriv_le` -- the `C^1` annulus kernel
  with its lower bound and its derivative bound.
* `euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero` -- **a coordinate
  derivative of a harmonic function is harmonic**.
* `exists_interior_gradient_bound` -- **the interior gradient estimate**.

## Regularity

`exists_interior_gradient_bound` assumes `ContDiff R (top : Nat-infinity) u`.
The third-derivative symmetry it needs is available in CoarseGraining only at
`C^infty` (`euclideanCoordSecondDeriv_comm`,
`euclideanCoordThirdDeriv_diag_right_comm`), so the hypothesis is stated at
that level; harmonic functions are smooth, but this module proves no regularity
theorem and therefore cannot weaken the hypothesis on its own.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

/-! ### The `C^1` one-sided square -/

/-- The square of the positive part: `s ↦ (max 0 s)^2`. -/
noncomputable def posPartSq (s : ℝ) : ℝ := max 0 s * max 0 s

theorem posPartSq_nonneg (s : ℝ) : 0 ≤ posPartSq s :=
  mul_nonneg (le_max_left _ _) (le_max_left _ _)

theorem posPartSq_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : posPartSq s = 0 := by
  simp [posPartSq, max_eq_left hs]

theorem posPartSq_eq_of_nonneg {s : ℝ} (hs : 0 ≤ s) : posPartSq s = s * s := by
  rw [posPartSq, max_eq_right hs]

theorem hasDerivAt_posPartSq (s : ℝ) : HasDerivAt posPartSq (2 * max 0 s) s := by
  rcases lt_trichotomy s 0 with h | h | h
  · have heq : posPartSq =ᶠ[nhds s] fun _ : ℝ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds h) fun t ht =>
        posPartSq_eq_zero_of_nonpos (le_of_lt ht)
    have hz : max (0 : ℝ) s = 0 := max_eq_left h.le
    rw [hz, mul_zero]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
  · subst h
    rw [max_self, mul_zero, hasDerivAt_iff_tendsto_slope]
    have hslope : ∀ t : ℝ, t ≠ 0 → slope posPartSq 0 t = max 0 t := by
      intro t ht
      rw [slope_def_field, posPartSq_eq_zero_of_nonpos le_rfl]
      rcases lt_or_gt_of_ne ht with h1 | h1
      · rw [posPartSq_eq_zero_of_nonpos h1.le, max_eq_left h1.le]
        simp
      · rw [posPartSq_eq_of_nonneg h1.le, max_eq_right h1.le]
        simp only [sub_zero]
        rw [mul_div_assoc, div_self ht, mul_one]
    have hev : (fun t : ℝ => max 0 t) =ᶠ[nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ] slope posPartSq 0 :=
      Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun t ht =>
        (hslope t (by simpa using ht)).symm
    have htend : Filter.Tendsto (fun t : ℝ => max 0 t)
        (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
      have hc : Filter.Tendsto (fun t : ℝ => max 0 t) (nhds (0 : ℝ)) (nhds (max 0 (0 : ℝ))) :=
        (continuous_const.max continuous_id).tendsto 0
      rw [max_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    exact htend.congr' hev
  · have heq : posPartSq =ᶠ[nhds s] fun t : ℝ => t * t :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds h) fun t ht =>
        posPartSq_eq_of_nonneg (le_of_lt ht)
    have hz : max (0 : ℝ) s = s := max_eq_right h.le
    rw [hz]
    have hd : HasDerivAt (fun t : ℝ => t * t) (1 * s + s * 1) s :=
      (hasDerivAt_id s).mul (hasDerivAt_id s)
    have hd' : HasDerivAt (fun t : ℝ => t * t) (2 * s) s := by
      refine hd.congr_deriv ?_
      ring
    exact hd'.congr_of_eventuallyEq heq

theorem contDiff_posPartSq : ContDiff ℝ 1 posPartSq := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hasDerivAt_posPartSq s).differentiableAt, ?_⟩
  have hderiv : deriv posPartSq = fun s : ℝ => 2 * max 0 s :=
    funext fun s => (hasDerivAt_posPartSq s).deriv
  rw [hderiv]
  exact continuous_const.mul (continuous_const.max continuous_id)

/-! ### The `C^1` annulus kernel -/

/-- The `C^1` radial kernel `(max 0 (t - a))^2 (max 0 (b - t))^2` supported in `[a, b]`. -/
noncomputable def gradKernel (a b t : ℝ) : ℝ := posPartSq (t - a) * posPartSq (b - t)

/-- The derivative of `gradKernel`. -/
noncomputable def gradKernelDeriv (a b t : ℝ) : ℝ :=
  2 * max 0 (t - a) * posPartSq (b - t) - posPartSq (t - a) * (2 * max 0 (b - t))

theorem hasDerivAt_gradKernel (a b t : ℝ) :
    HasDerivAt (gradKernel a b) (gradKernelDeriv a b t) t := by
  have h1 : HasDerivAt (fun s : ℝ => posPartSq (s - a)) (2 * max 0 (t - a)) t := by
    simpa using! (hasDerivAt_posPartSq (t - a)).comp t ((hasDerivAt_id t).sub_const a)
  have h2 : HasDerivAt (fun s : ℝ => posPartSq (b - s)) (-(2 * max 0 (b - t))) t := by
    simpa using! (hasDerivAt_posPartSq (b - t)).comp t ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  refine (h1.mul h2).congr_deriv ?_
  rw [gradKernelDeriv]
  ring

theorem contDiff_gradKernel (a b : ℝ) : ContDiff ℝ 1 (gradKernel a b) :=
  (contDiff_posPartSq.comp (contDiff_id.sub contDiff_const)).mul
    (contDiff_posPartSq.comp (contDiff_const.sub contDiff_id))

theorem continuous_gradKernel (a b : ℝ) : Continuous (gradKernel a b) :=
  (contDiff_gradKernel a b).continuous

theorem gradKernel_nonneg (a b t : ℝ) : 0 ≤ gradKernel a b t :=
  mul_nonneg (posPartSq_nonneg _) (posPartSq_nonneg _)

theorem gradKernel_eq_zero_of_le {a b t : ℝ} (ht : t ≤ a) : gradKernel a b t = 0 := by
  rw [gradKernel, posPartSq_eq_zero_of_nonpos (by linarith : t - a ≤ 0), zero_mul]

theorem gradKernel_eq_zero_of_ge {a b t : ℝ} (ht : b ≤ t) : gradKernel a b t = 0 := by
  rw [gradKernel, posPartSq_eq_zero_of_nonpos (by linarith : b - t ≤ 0), mul_zero]

theorem gradKernel_pos {a b t : ℝ} (h1 : a < t) (h2 : t < b) : 0 < gradKernel a b t := by
  have hA : 0 < t - a := by linarith
  have hB : 0 < b - t := by linarith
  rw [gradKernel, posPartSq_eq_of_nonneg hA.le, posPartSq_eq_of_nonneg hB.le]
  positivity

/-- A quantitative lower bound on `gradKernel` well inside its annulus. -/
theorem pow_four_le_gradKernel {a b t c : ℝ} (hc : 0 ≤ c) (h1 : a + c ≤ t) (h2 : t + c ≤ b) :
    c ^ 4 ≤ gradKernel a b t := by
  have hA : 0 ≤ t - a := by linarith
  have hB : 0 ≤ b - t := by linarith
  rw [gradKernel, posPartSq_eq_of_nonneg hA, posPartSq_eq_of_nonneg hB]
  have e1 : c * c ≤ (t - a) * (t - a) := mul_le_mul (by linarith) (by linarith) hc hA
  have e2 : c * c ≤ (b - t) * (b - t) := mul_le_mul (by linarith) (by linarith) hc hB
  have hcc : (0 : ℝ) ≤ c * c := mul_nonneg hc hc
  have := mul_le_mul e1 e2 hcc (le_trans hcc e1)
  nlinarith [this]

/-- The uniform bound on the derivative of `gradKernel`. -/
theorem abs_gradKernelDeriv_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    |gradKernelDeriv a b t| ≤ 4 * (b - a) ^ 3 := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hcube : (0 : ℝ) ≤ 4 * (b - a) ^ 3 := by positivity
  rcases le_or_gt t a with hA | hA
  · rw [gradKernelDeriv, posPartSq_eq_zero_of_nonpos (by linarith : t - a ≤ 0),
      max_eq_left (by linarith : t - a ≤ 0)]
    simpa using hcube
  · rcases le_or_gt b t with hB | hB
    · rw [gradKernelDeriv, posPartSq_eq_zero_of_nonpos (by linarith : b - t ≤ 0),
        max_eq_left (by linarith : b - t ≤ 0)]
      simpa using hcube
    · have hP : 0 < t - a := by linarith
      have hQ : 0 < b - t := by linarith
      rw [gradKernelDeriv, posPartSq_eq_of_nonneg hP.le, posPartSq_eq_of_nonneg hQ.le,
        max_eq_right hP.le, max_eq_right hQ.le]
      have hPb : t - a ≤ b - a := by linarith
      have hQb : b - t ≤ b - a := by linarith
      have e1 : (t - a) * ((b - t) * (b - t)) ≤ (b - a) * ((b - a) * (b - a)) :=
        mul_le_mul hPb (mul_le_mul hQb hQb hQ.le hba) (by positivity) hba
      have e2 : ((t - a) * (t - a)) * (b - t) ≤ ((b - a) * (b - a)) * (b - a) :=
        mul_le_mul (mul_le_mul hPb hPb hP.le hba) hQb hQ.le (by positivity)
      have e1' : (0 : ℝ) ≤ (t - a) * ((b - t) * (b - t)) := by positivity
      have e2' : (0 : ℝ) ≤ ((t - a) * (t - a)) * (b - t) := by positivity
      rw [abs_le]
      constructor <;> nlinarith [e1, e2, e1', e2']

/-! ### Harmonicity of a coordinate derivative -/

private theorem euclideanCoordDeriv_eq_zero_of_eventuallyEq {d : ℕ} {f : Vec d → ℝ} {c : ℝ}
    {x : Vec d} (h : f =ᶠ[nhds x] fun _ : Vec d => c) (i : Fin d) :
    euclideanCoordDeriv i f x = 0 := by
  rw [euclideanCoordDeriv, h.fderiv_eq]
  simp

/-- **A coordinate derivative of a harmonic function is harmonic.** -/
theorem euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {U : Set (Vec d)} (hU : IsOpen U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian u y = 0) {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 := by
  have hstep : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (euclideanCoordDeriv i u) x
        = euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := fun j =>
    euclideanCoordThirdDeriv_diag_right_comm hu i j x
  have hg : ∀ j : Fin d, HasFDerivAt (euclideanCoordSecondDeriv j j u)
      (fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := fun j =>
    ((contDiff_euclideanCoordSecondDeriv hu j j).differentiable (by simp) x).hasFDerivAt
  have hL : HasFDerivAt (fun y : Vec d => ∑ j : Fin d, euclideanCoordSecondDeriv j j u y)
      (∑ j : Fin d, fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := by
    have hres := HasFDerivAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hg j
    have hfun : (∑ j : Fin d, euclideanCoordSecondDeriv j j u)
        = fun y : Vec d => ∑ j : Fin d, euclideanCoordSecondDeriv j j u y := by
      funext y
      simp [Finset.sum_apply]
    rw [hfun] at hres
    exact hres
  have hzero : euclideanCoordDeriv i (euclideanCoordLaplacian u) x = 0 :=
    euclideanCoordDeriv_eq_zero_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hharm) i
  have hsplit : euclideanCoordDeriv i (euclideanCoordLaplacian u) x
      = ∑ j : Fin d, euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := by
    rw [euclideanCoordDeriv,
      show euclideanCoordLaplacian u
        = fun y : Vec d => ∑ j : Fin d, euclideanCoordSecondDeriv j j u y from rfl,
      hL.fderiv]
    simp [euclideanCoordDeriv]
  rw [euclideanCoordLaplacian]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hstep j, ← hsplit, hzero]

/-! ### The interior gradient estimate -/

variable {m : ℕ}

private theorem euclideanCoordDeriv_gradKernel_comp_eq_zero_of_gt {a b : ℝ}
    {z x : Vec (m + 1)} (hx : b < euclideanNorm (x - z)) (i : Fin (m + 1)) :
    euclideanCoordDeriv i (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x
      = 0 := by
  have hopen : IsOpen {y : Vec (m + 1) | b < euclideanNorm (y - z)} :=
    isOpen_lt continuous_const
      (continuous_euclideanNorm.comp (continuous_id.sub continuous_const))
  refine euclideanCoordDeriv_eq_zero_of_eventuallyEq (c := (0 : ℝ))
    (Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy => ?_) i
  exact gradKernel_eq_zero_of_ge (le_of_lt hy)

private theorem abs_euclideanCoordDeriv_gradKernel_comp_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z x : Vec (m + 1)) (i : Fin (m + 1)) :
    |euclideanCoordDeriv i (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x|
      ≤ 4 * (b - a) ^ 3 := by
  have hcube : (0 : ℝ) ≤ 4 * (b - a) ^ 3 := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  by_cases hx : x = z
  · subst hx
    have hzero : euclideanCoordDeriv i
        (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - x))) x = 0 := by
      refine euclideanCoordDeriv_eq_zero_of_eventuallyEq (c := (0 : ℝ))
        (Filter.eventuallyEq_of_mem ((isOpen_euclideanBall x a).mem_nhds
          (mem_euclideanBall_self ha)) fun y hy => ?_) i
      exact gradKernel_eq_zero_of_le
        (le_of_lt ((mem_euclideanBall_iff_euclideanNorm_lt ha.le).mp hy))
    rw [hzero, abs_zero]
    exact hcube
  · have hN : 0 < euclideanNorm (x - z) := euclideanNorm_pos (sub_ne_zero.mpr hx)
    rw [euclideanCoordDeriv_comp_euclideanNorm_sub hx
      (hasDerivAt_gradKernel a b (euclideanNorm (x - z))) i, abs_mul]
    have hcoord : |x i - z i| ≤ euclideanNorm (x - z) := by
      refine abs_le_of_sq_le_sq ?_ hN.le
      rw [← euclideanSqDist_eq_sq_euclideanNorm]
      exact sq_coord_sub_le_euclideanSqDist x z i
    have hratio : |(x i - z i) / euclideanNorm (x - z)| ≤ 1 := by
      rw [abs_div, abs_of_pos hN, div_le_one hN]
      exact hcoord
    calc |gradKernelDeriv a b (euclideanNorm (x - z))|
            * |(x i - z i) / euclideanNorm (x - z)|
        ≤ (4 * (b - a) ^ 3) * 1 :=
          mul_le_mul (abs_gradKernelDeriv_le hab _) hratio (abs_nonneg _) hcube
      _ = 4 * (b - a) ^ 3 := mul_one _

/-- The Green pairing bound behind the interior gradient estimate. -/
private theorem abs_euclideanCoordDeriv_mul_integral_gradKernel_le
    {u : Vec (m + 1) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {r a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hbr : b < r) {z : Vec (m + 1)}
    (hharm : ∀ x ∈ euclideanBall z r, euclideanCoordLaplacian u x = 0) (i : Fin (m + 1)) :
    |euclideanCoordDeriv i u z| * (∫ x, gradKernel a b (euclideanNorm (x - z)) ∂volume)
      ≤ 4 * (b - a) ^ 3 * ∫ x in euclideanBall z r, |u x| ∂volume := by
  have hb : 0 < b := ha.trans hab
  have hr : 0 < r := hb.trans hbr
  have hkb : ∀ s : ℝ, b ≤ s → gradKernel a b s = 0 := fun _ hs => gradKernel_eq_zero_of_ge hs
  have hu1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) u := hu.of_le ENat.LEInfty.out
  have hK1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun x : Vec (m + 1) => gradKernel a b (euclideanNorm (x - z))) := by
    have hone : ((1 : ℕ) : WithTop ℕ∞) = 1 := by norm_num
    rw [hone]
    refine contDiff_radial ha (fun t _ => (contDiff_gradKernel a b).contDiffAt) ?_
    intro t _ ht
    rw [gradKernel_eq_zero_of_le ht.le, gradKernel_eq_zero_of_le ha.le]
  have hKc : HasCompactSupport
      (fun x : Vec (m + 1) => gradKernel a b (euclideanNorm (x - z))) := by
    simpa using hasCompactSupport_mul_radial (u := fun _ : Vec (m + 1) => (1 : ℝ)) hb hkb z
  have hdKcont : Continuous
      (euclideanCoordDeriv i fun x : Vec (m + 1) => gradKernel a b (euclideanNorm (x - z))) :=
    (contDiff_euclideanCoordDeriv_of_contDiff_succ (n := 0) (by exact_mod_cast hK1) i).continuous
  have hdKsupp : HasCompactSupport
      (euclideanCoordDeriv i fun x : Vec (m + 1) => gradKernel a b (euclideanNorm (x - z))) :=
    hasCompactSupport_euclideanCoordDeriv hKc i
  -- the mean value property applied to the harmonic function `∂ᵢ u`
  have hv2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (euclideanCoordDeriv i u) :=
    (contDiff_euclideanCoordDeriv hu i).of_le ENat.LEInfty.out
  have hvharm : ∀ x ∈ euclideanClosedBall z b,
      euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 := by
    intro x hx
    exact euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero hu (isOpen_euclideanBall z r) hharm
      (euclideanClosedBall_subset_euclideanBall hb.le hbr hx) i
  have hmom : 0 < radialMoment m (gradKernel a b) b :=
    radialMoment_pos_of_pos_on (continuous_gradKernel a b) (gradKernel_nonneg a b) ha hab le_rfl
      fun t ht1 ht2 => gradKernel_pos ht1 ht2
  have hmvp : ∫ x, euclideanCoordDeriv i u x * gradKernel a b (euclideanNorm (x - z)) ∂volume
      = euclideanCoordDeriv i u z * ∫ x, gradKernel a b (euclideanNorm (x - z)) ∂volume :=
    integral_mul_radial_eq_mul_integral_of_harmonic hv2 (continuous_gradKernel a b) ha hab
      (fun _ hs => gradKernel_eq_zero_of_le hs) (fun _ hs => gradKernel_eq_zero_of_ge hs)
      hmom hvharm
  -- one integration by parts moves the derivative onto the kernel
  have hibp : ∫ x, u x * euclideanCoordDeriv i
        (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x ∂volume
      = -∫ x, euclideanCoordDeriv i u x * gradKernel a b (euclideanNorm (x - z)) ∂volume :=
    integral_mul_euclideanCoordDeriv_eq_neg_of_contDiff_one hu1 hK1 hKc i
  -- the resulting kernel bound
  have habsint : Integrable (fun x : Vec (m + 1) => |u x * euclideanCoordDeriv i
      (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x|) volume :=
    ((hu.continuous.mul hdKcont).integrable_of_hasCompactSupport hdKsupp.mul_left).abs
  have hindint : Integrable
      (fun x : Vec (m + 1) => 4 * (b - a) ^ 3
        * Set.indicator (euclideanBall z r) (fun y : Vec (m + 1) => |u y|) x) volume := by
    refine Integrable.const_mul ?_ _
    refine (integrable_indicator_iff (isOpen_euclideanBall z r).measurableSet).mpr ?_
    exact (((ContinuousOn.integrableOn_compact (isCompact_euclideanClosedBall z hr.le)
      hu.continuous.abs.continuousOn)).mono_set
      (by simpa [abs_of_nonneg hr.le] using euclideanBall_subset_euclideanClosedBall_abs z r))
  have hptw : ∀ x : Vec (m + 1), |u x * euclideanCoordDeriv i
      (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x|
      ≤ 4 * (b - a) ^ 3
        * Set.indicator (euclideanBall z r) (fun y : Vec (m + 1) => |u y|) x := by
    intro x
    rw [abs_mul]
    by_cases hx : x ∈ euclideanBall z r
    · rw [Set.indicator_of_mem hx, mul_comm (4 * (b - a) ^ 3) |u x|]
      exact mul_le_mul_of_nonneg_left
        (abs_euclideanCoordDeriv_gradKernel_comp_le ha hab.le z x i) (abs_nonneg _)
    · have hnorm : r ≤ euclideanNorm (x - z) := by
        by_contra hcon
        exact hx ((mem_euclideanBall_iff_euclideanNorm_lt hr.le).mpr (not_le.mp hcon))
      rw [euclideanCoordDeriv_gradKernel_comp_eq_zero_of_gt (lt_of_lt_of_le hbr hnorm) i,
        Set.indicator_of_notMem hx, abs_zero, mul_zero, mul_zero]
  have hcalc : |∫ x, u x * euclideanCoordDeriv i
        (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x ∂volume|
      ≤ 4 * (b - a) ^ 3 * ∫ x in euclideanBall z r, |u x| ∂volume := by
    calc |∫ x, u x * euclideanCoordDeriv i
            (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x ∂volume|
        ≤ ∫ x, |u x * euclideanCoordDeriv i
            (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x| ∂volume :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, 4 * (b - a) ^ 3
            * Set.indicator (euclideanBall z r) (fun y : Vec (m + 1) => |u y|) x ∂volume :=
          integral_mono habsint hindint hptw
      _ = 4 * (b - a) ^ 3 * ∫ x in euclideanBall z r, |u x| ∂volume := by
          rw [integral_const_mul, integral_indicator (isOpen_euclideanBall z r).measurableSet]
  have hInt : 0 ≤ ∫ x, gradKernel a b (euclideanNorm (x - z)) ∂volume :=
    integral_nonneg fun x => gradKernel_nonneg a b _
  have hchain : |euclideanCoordDeriv i u z| * (∫ x, gradKernel a b (euclideanNorm (x - z)) ∂volume)
      = |∫ x, u x * euclideanCoordDeriv i
        (fun y : Vec (m + 1) => gradKernel a b (euclideanNorm (y - z))) x ∂volume| := by
    rw [hibp, hmvp, abs_neg, abs_mul, abs_of_nonneg hInt]
  rw [hchain]
  exact hcalc

/-- The scale-explicit lower bound for the mass of the annulus kernel. -/
private theorem integral_gradKernel_comp_ge {r : ℝ} (hr : 0 < r) (z : Vec (m + 1)) :
    ((((7 : ℝ) / 16) ^ (m + 1) - ((6 : ℝ) / 16) ^ (m + 1))
        * Book.Ch01.euclideanUnitBallVolume (m + 1)) * r ^ (m + 1) * (r / 16) ^ 4
      ≤ ∫ x, gradKernel (r / 4) (r / 2) (euclideanNorm (x - z)) ∂volume := by
  have hkb : ∀ s : ℝ, r / 2 ≤ s → gradKernel (r / 4) (r / 2) s = 0 :=
    fun _ hs => gradKernel_eq_zero_of_ge hs
  have hKint : Integrable
      (fun x : Vec (m + 1) => gradKernel (r / 4) (r / 2) (euclideanNorm (x - z))) volume :=
    integrable_radial (continuous_gradKernel _ _) (by linarith) hkb z
  set A : Set (Vec (m + 1)) :=
    euclideanBall z (7 * r / 16) \ euclideanClosedBall z (5 * r / 16) with hA
  have hAmeas : MeasurableSet A :=
    (isOpen_euclideanBall z (7 * r / 16)).measurableSet.diff
      (isClosed_euclideanClosedBall z (5 * r / 16)).measurableSet
  have h1 : ∫ x in A, gradKernel (r / 4) (r / 2) (euclideanNorm (x - z)) ∂volume
      ≤ ∫ x, gradKernel (r / 4) (r / 2) (euclideanNorm (x - z)) ∂volume :=
    setIntegral_le_integral hKint
      (Filter.Eventually.of_forall fun x => gradKernel_nonneg _ _ _)
  have h2 : (volume A).toReal * (r / 16) ^ 4
      ≤ ∫ x in A, gradKernel (r / 4) (r / 2) (euclideanNorm (x - z)) ∂volume := by
    have hconst : ∫ _x in A, (r / 16) ^ 4 ∂volume = (volume A).toReal * (r / 16) ^ 4 := by
      rw [setIntegral_const, measureReal_def, smul_eq_mul]
    rw [← hconst]
    refine setIntegral_mono_on (integrableOn_const ?_) hKint.integrableOn hAmeas ?_
    · exact ne_top_of_le_ne_top (volume_euclideanBall_ne_top z (7 * r / 16))
        (measure_mono Set.sdiff_subset)
    · intro x hx
      have hx1 : euclideanNorm (x - z) < 7 * r / 16 :=
        (mem_euclideanBall_iff_euclideanNorm_lt (by linarith)).mp hx.1
      have hx2 : ¬ euclideanNorm (x - z) ≤ 5 * r / 16 := fun h =>
        hx.2 ((mem_euclideanClosedBall_iff_euclideanNorm_le (by linarith)).mpr h)
      refine pow_four_le_gradKernel (by linarith) ?_ ?_
      · linarith [not_le.mp hx2]
      · linarith
  have h3 : (7 * r / 16) ^ (m + 1) * Book.Ch01.euclideanUnitBallVolume (m + 1)
      - (6 * r / 16) ^ (m + 1) * Book.Ch01.euclideanUnitBallVolume (m + 1)
      ≤ (volume A).toReal := by
    have hsub : euclideanBall z (7 * r / 16) ⊆ A ∪ euclideanClosedBall z (5 * r / 16) := by
      intro x hx
      by_cases h : x ∈ euclideanClosedBall z (5 * r / 16)
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    have hcl : volume (euclideanClosedBall z (5 * r / 16))
        ≤ volume (euclideanBall z (6 * r / 16)) :=
      measure_mono (euclideanClosedBall_subset_euclideanBall (by linarith) (by linarith))
    have hcomb : volume (euclideanBall z (7 * r / 16))
        ≤ volume A + volume (euclideanBall z (6 * r / 16)) :=
      le_trans (le_trans (measure_mono hsub) (measure_union_le _ _)) (add_le_add (le_refl (volume A)) hcl)
    have hfinA : volume A ≠ ⊤ :=
      ne_top_of_le_ne_top (volume_euclideanBall_ne_top z (7 * r / 16))
        (measure_mono Set.sdiff_subset)
    have hfinC : volume (euclideanBall z (6 * r / 16)) ≠ ⊤ :=
      volume_euclideanBall_ne_top z (6 * r / 16)
    have htoReal := ENNReal.toReal_mono (by simp [hfinA, hfinC]) hcomb
    rw [ENNReal.toReal_add hfinA hfinC,
      volume_euclideanBall_toReal z (by linarith : (0 : ℝ) < 7 * r / 16),
      volume_euclideanBall_toReal z (by linarith : (0 : ℝ) < 6 * r / 16)] at htoReal
    linarith
  have hpow : (0 : ℝ) ≤ (r / 16) ^ 4 := by positivity
  have hrewrite : (7 * r / 16) ^ (m + 1) * Book.Ch01.euclideanUnitBallVolume (m + 1)
      - (6 * r / 16) ^ (m + 1) * Book.Ch01.euclideanUnitBallVolume (m + 1)
      = (((7 : ℝ) / 16) ^ (m + 1) - ((6 : ℝ) / 16) ^ (m + 1))
        * Book.Ch01.euclideanUnitBallVolume (m + 1) * r ^ (m + 1) := by
    rw [show (7 * r / 16 : ℝ) = (7 / 16) * r by ring, show (6 * r / 16 : ℝ) = (6 / 16) * r by ring,
      mul_pow, mul_pow]
    ring
  rw [hrewrite] at h3
  have h4 := mul_le_mul_of_nonneg_right h3 hpow
  linarith [h1, h2, h4]

/-- **The interior gradient estimate for the coordinate Laplacian on `Vec d`.** -/
theorem exists_interior_gradient_bound {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → ∀ r : ℝ, 0 < r →
      ∀ z : Vec d, (∀ x ∈ euclideanBall z r, euclideanCoordLaplacian u x = 0) →
        ∀ i : Fin d, |euclideanCoordDeriv i u z|
          ≤ C / r * ((∫ x in euclideanBall z r, |u x| ∂volume)
            / (volume (euclideanBall z r)).toReal) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hκ : (0 : ℝ) < ((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1) := by
    have hlt : ((6 : ℝ) / 16) ^ (n + 1) < ((7 : ℝ) / 16) ^ (n + 1) :=
      (pow_lt_pow_iff_left₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)).mpr (by norm_num)
    linarith
  refine ⟨4096 / (((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1)), by positivity, ?_⟩
  intro u hu r hr z hharm i
  have hω : 0 < Book.Ch01.euclideanUnitBallVolume (n + 1) := euclideanUnitBallVolume_pos (n + 1)
  have hRpos : (0 : ℝ) < r ^ (n + 1) := pow_pos hr _
  have hkey := abs_euclideanCoordDeriv_mul_integral_gradKernel_le hu
    (by linarith : (0 : ℝ) < r / 4) (by linarith : r / 4 < r / 2)
    (by linarith : r / 2 < r) hharm i
  have hlow := integral_gradKernel_comp_ge hr z
  have hLpos : (0 : ℝ) < ((((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1))
      * Book.Ch01.euclideanUnitBallVolume (n + 1)) * r ^ (n + 1) * (r / 16) ^ 4 := by
    have : (0 : ℝ) < (r / 16) ^ 4 := by positivity
    have h2 : (0 : ℝ) < (((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1))
        * Book.Ch01.euclideanUnitBallVolume (n + 1) := mul_pos hκ hω
    positivity
  have habs : 0 ≤ |euclideanCoordDeriv i u z| := abs_nonneg _
  have hstep : |euclideanCoordDeriv i u z|
      * (((((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1))
          * Book.Ch01.euclideanUnitBallVolume (n + 1)) * r ^ (n + 1) * (r / 16) ^ 4)
      ≤ 4 * (r / 2 - r / 4) ^ 3 * ∫ x in euclideanBall z r, |u x| ∂volume :=
    le_trans (mul_le_mul_of_nonneg_left hlow habs) hkey
  rw [volume_euclideanBall_toReal z hr]
  set I : ℝ := ∫ x in euclideanBall z r, |u x| ∂volume with hIdef
  set R : ℝ := r ^ (n + 1) with hRdef
  set W : ℝ := Book.Ch01.euclideanUnitBallVolume (n + 1) with hWdef
  set K₀ : ℝ := ((7 : ℝ) / 16) ^ (n + 1) - ((6 : ℝ) / 16) ^ (n + 1) with hK₀def
  have hEq : 4096 / K₀ / r * (I / (R * W))
      = 4 * (r / 2 - r / 4) ^ 3 * I / (K₀ * W * R * (r / 16) ^ 4) := by
    field_simp
    ring
  rw [hEq, le_div_iff₀ hLpos]
  exact hstep

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
