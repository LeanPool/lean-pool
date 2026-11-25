/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialPoissonOrigin
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LeviForm

/-!
# Radial Poisson potentials on the standard complex model

The one-variable Poisson primitive constructed in the preceding modules is
pulled back by the squared norm.  We first prove the genuine real Hessian and
Levi formulas for an arbitrary smooth profile `G (‖x‖²)`.  Summing the Levi
form over the standard complex coordinate frame then turns the one-variable
ODE `4 (s G'' + n G') = g` into the required kernel difference.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.RadialLeviPreimage

open FirstPass
open FirstPass.MongeAmpere
open HolomorphicPullback
open RadialPoissonCertificate
open RadialPoissonSlope
open RadialPoissonPrimitive
open RadialPoissonOrigin

section RadialCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real Hessian of a smooth profile pulled back by the squared norm. -/
theorem realHessian_comp_norm_sq {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (x v w : H) :
    realHessian (fun y : H => G (‖y‖ ^ 2)) x v w =
      4 * deriv (deriv G) (‖x‖ ^ 2) * inner ℝ x v * inner ℝ x w +
        2 * deriv G (‖x‖ ^ 2) * inner ℝ v w := by
  let q : H → ℝ := fun y => ‖y‖ ^ 2
  have hq : ContDiff ℝ 2 q := contDiff_norm_sq ℝ
  have hGdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hqdiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hfirst : fderiv ℝ (fun y : H => G (q y)) =
      fun y => (deriv G (q y)) • fderiv ℝ q y := by
    funext y
    change fderiv ℝ (G ∘ q) y = _
    rw [fderiv_comp y (hGdiff (q y)) (hqdiff y)]
    ext a
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      smul_eq_mul, fderiv_eq_deriv_mul]
  have hc : HasFDerivAt (fun y : H => deriv G (q y))
      ((deriv (deriv G) (q x)) • fderiv ℝ q x) x := by
    simpa only [Function.comp_def] using
      ((hG.differentiable_deriv_two (q x)).hasDerivAt.comp_hasFDerivAt x
        (hqdiff x).hasFDerivAt)
  have hDq : HasFDerivAt (fun y : H => fderiv ℝ q y)
      (fderiv ℝ (fderiv ℝ q) x) x :=
    ((hq.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x).hasFDerivAt
  rw [realHessian_eq_fderiv, hfirst]
  change (fderiv ℝ ((fun y : H => deriv G (q y)) •
    fun y : H => fderiv ℝ q y) x) v w = _
  rw [(hc.smul hDq).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul]
  rw [show fderiv ℝ q x v = 2 * inner ℝ x v by
        simp [q, fderiv_norm_sq_apply, innerSL_apply_apply],
      show fderiv ℝ q x w = 2 * inner ℝ x w by
        simp [q, fderiv_norm_sq_apply, innerSL_apply_apply],
      show fderiv ℝ (fderiv ℝ q) x v w = 2 * inner ℝ v w by
        simpa [q, realHessian_eq_fderiv] using realHessian_norm_sq x v w]
  ring

end RadialCalculus

section ComplexRadialCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The underlying real inner product induced by the complex inner product. -/
local instance localRealInnerProductSpace : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

/-- The Levi form of a smooth squared-radius profile. -/
theorem leviForm_comp_norm_sq {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (x v : H) :
    leviForm (fun y : H => G (‖y‖ ^ 2)) x v =
      deriv G (‖x‖ ^ 2) * ‖v‖ ^ 2 +
        deriv (deriv G) (‖x‖ ^ 2) * ‖inner ℂ x v‖ ^ 2 := by
  have hpair : (inner ℝ x v) ^ 2 +
      (inner ℝ x (Complex.I • v)) ^ 2 = ‖inner ℂ x v‖ ^ 2 := by
    change (inner ℂ x v).re ^ 2 +
      (inner ℂ x (Complex.I • v)).re ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [inner_smul_right, Complex.I_mul_re, neg_sq]
    ring
  simp only [leviForm, realHessian_comp_norm_sq hG,
    real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  rw [← hpair]
  ring

end ComplexRadialCalculus

section CoordinateTrace

variable {n : ℕ}

@[simp]
theorem norm_coordinateVector (j : Fin n) :
    ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

/-- Parseval's identity for the standard complex coordinate frame, in the
orientation needed by the radial Levi formula. -/
theorem sum_norm_inner_coordinateVector_sq (x : ComplexModel n) :
    ∑ j : Fin n, ‖inner ℂ x (coordinateVector j)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [coordinateVector, PiLp.inner_apply]

/-- Trace of the Levi form in the standard complex orthonormal frame. -/
def coordinateLeviTrace (u : ComplexModel n → ℝ) (x : ComplexModel n) : ℝ :=
  ∑ j : Fin n, leviForm u x (coordinateVector j)

/-- The coordinate Levi trace of a smooth squared-radius profile is the
one-variable radial operator `s G'' + n G'`. -/
theorem coordinateLeviTrace_comp_norm_sq {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) (x : ComplexModel n) :
    coordinateLeviTrace (fun y : ComplexModel n => G (‖y‖ ^ 2)) x =
      (n : ℝ) * deriv G (‖x‖ ^ 2) +
        ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) := by
  rw [coordinateLeviTrace]
  simp_rw [leviForm_comp_norm_sq hG]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_norm_inner_coordinateVector_sq]
  simp only [norm_coordinateVector, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end CoordinateTrace

/-! ## The explicit scale-difference potential -/

/-- The radial Poisson potential for an increasing pair of explicit kernel
scales, normalized at the outer squared radius of the first scale. -/
noncomputable def explicitRadialPoissonPotential {n : ℕ}
    (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : ComplexModel n) : ℝ :=
  radialPoissonPrimitive n
    (explicitRadialKernelSqDifference (n := n) R hR a b)
    ((R / ((a : ℝ) + 1)) ^ 2) (‖x‖ ^ 2)

/-- The explicit radial Poisson potential is globally smooth, including at
the origin. -/
theorem explicitRadialPoissonPotential_contDiff {n : ℕ} (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (explicitRadialPoissonPotential (n := n) R hR a b) := by
  exact (radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiff
      hn R hR a b ((R / ((a : ℝ) + 1)) ^ 2)).comp
    (contDiff_norm_sq ℝ)

/-- For increasing scale indices, the explicit radial Poisson potential is
nonnegative everywhere. -/
theorem explicitRadialPoissonPotential_nonneg {n : ℕ} (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b)
    (x : ComplexModel n) :
    0 ≤ explicitRadialPoissonPotential R hR a b x := by
  let A : ℝ := (R / ((a : ℝ) + 1)) ^ 2
  let s : ℝ := ‖x‖ ^ 2
  change 0 ≤ radialPoissonPrimitive n
    (explicitRadialKernelSqDifference (n := n) R hR a b) A s
  by_cases hsA : s ≤ A
  · apply radialPoissonPrimitive_nonneg hsA
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [radialPoissonSlope, radialWeightedCumulative]
    · have htpos : 0 < t := lt_of_le_of_ne
        ((sq_nonneg ‖x‖).trans ht.1) (Ne.symm ht0)
      exact radialPoissonSlope_explicitRadialKernelSqDifference_nonpos
        hn R hR hab htpos
  · rw [radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_zero_of_outer
      hn R hR hab (le_of_not_ge hsA)]

/-- The potential vanishes at and beyond the first scale's outer radius. -/
theorem explicitRadialPoissonPotential_eq_zero_of_outer {n : ℕ}
    (hn : 0 < n) (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b)
    {x : ComplexModel n} (hx : R / ((a : ℝ) + 1) ≤ ‖x‖) :
    explicitRadialPoissonPotential R hR a b x = 0 := by
  apply radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_zero_of_outer
    hn R hR hab
  exact (sq_le_sq₀ (by positivity) (norm_nonneg x)).mpr hx

/-- For increasing scale indices, the explicit Poisson potential has compact
support contained in the closed ball of the first scale's outer radius. -/
theorem explicitRadialPoissonPotential_hasCompactSupport {n : ℕ}
    (hn : 0 < n) (R : ℝ) (hR : 0 < R) {a b : ℕ} (hab : a ≤ b) :
    HasCompactSupport
      (explicitRadialPoissonPotential (n := n) R hR a b) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ComplexModel n) (R / ((a : ℝ) + 1)))
  intro x hx
  simp only [mem_closedBall, dist_zero_right]
  by_contra hnorm
  have hrx : R / ((a : ℝ) + 1) ≤ ‖x‖ := le_of_not_ge hnorm
  exact hx (explicitRadialPoissonPotential_eq_zero_of_outer
    hn R hR hab hrx)

/-- Away from the origin, four times the standard coordinate Levi trace of
the Poisson potential is exactly the one-variable kernel difference. -/
theorem four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_of_ne_zero
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    {x : ComplexModel n} (hx : x ≠ 0) :
    4 * coordinateLeviTrace
      (explicitRadialPoissonPotential R hR a b) x =
        explicitRadialKernelSqDifference (n := n) R hR a b (‖x‖ ^ 2) := by
  let g : ℝ → ℝ :=
    explicitRadialKernelSqDifference (n := n) R hR a b
  let A : ℝ := (R / ((a : ℝ) + 1)) ^ 2
  let G : ℝ → ℝ := radialPoissonPrimitive n g A
  have hGinfty : ContDiff ℝ (⊤ : ℕ∞) G :=
    radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiff
      hn R hR a b A
  have hG2 : ContDiff ℝ 2 G := hGinfty.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hs : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  change 4 * coordinateLeviTrace (fun y : ComplexModel n => G (‖y‖ ^ 2)) x =
    g (‖x‖ ^ 2)
  rw [coordinateLeviTrace_comp_norm_sq hG2]
  calc
    4 * ((n : ℝ) * deriv G (‖x‖ ^ 2) +
        ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2)) =
      4 * (‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) +
        (n : ℝ) * deriv G (‖x‖ ^ 2)) := by ring
    _ = g (‖x‖ ^ 2) :=
      radialPoissonPrimitive_ode hn
        (explicitRadialKernelSqDifference_contDiff R hR a b).continuous
        hA hs

/-- The same trace identity written as a difference of the two spatial
normalized kernels. -/
theorem four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_of_ne_zero_eq_kernel_sub
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    {x : ComplexModel n} (hx : x ≠ 0) :
    4 * coordinateLeviTrace
      (explicitRadialPoissonPotential R hR a b) x =
        explicitRadialKernel R hR a x - explicitRadialKernel R hR b x := by
  rw [four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_of_ne_zero
      hn R hR a b hx,
    explicitRadialKernel_sub_eq_sqDifference_norm_sq]

/-- The derivative of the one-variable primitive at the removable origin is
the limiting Poisson slope.  This is obtained from the exact affine formula
on the flat inner region, rather than by assigning a value to the original
`0 / 0` quotient. -/
theorem deriv_radialPoissonPrimitive_explicitRadialKernelSqDifference_zero
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ) (A : ℝ) :
    deriv (radialPoissonPrimitive n
      (explicitRadialKernelSqDifference (n := n) R hR a b) A) 0 =
        explicitRadialKernelSqDifference (n := n) R hR a b 0 /
          (4 * (n : ℝ)) := by
  let g : ℝ → ℝ :=
    explicitRadialKernelSqDifference (n := n) R hR a b
  let k : ℝ := g 0 / (4 * (n : ℝ))
  let G : ℝ → ℝ := radialPoissonPrimitive n g A
  let δ : ℝ := min
    ((shrinkingBump (E := ComplexModel n) R hR a).rIn ^ 2)
    ((shrinkingBump (E := ComplexModel n) R hR b).rIn ^ 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR a).rIn_pos)
      (sq_pos_of_pos
        (shrinkingBump (E := ComplexModel n) R hR b).rIn_pos)
  have hevent : G =ᶠ[𝓝 0] fun s => G 0 + k * s := by
    filter_upwards [Iio_mem_nhds hδ] with s hs
    exact radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_affine
      hn R hR a b A hs
  have hlinear : HasDerivAt (fun s : ℝ => G 0 + k * s) k 0 :=
    (hasDerivAt_const_mul (x := 0) k).const_add (G 0)
  change deriv G 0 = k
  exact (hlinear.congr_of_eventuallyEq hevent).deriv

/-- Four times the standard coordinate Levi trace equals the kernel
difference at every point, including the origin. -/
theorem four_mul_coordinateLeviTrace_explicitRadialPoissonPotential
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    4 * coordinateLeviTrace
      (explicitRadialPoissonPotential R hR a b) x =
        explicitRadialKernelSqDifference (n := n) R hR a b (‖x‖ ^ 2) := by
  by_cases hx : x = 0
  · subst x
    let g : ℝ → ℝ :=
      explicitRadialKernelSqDifference (n := n) R hR a b
    let A : ℝ := (R / ((a : ℝ) + 1)) ^ 2
    let G : ℝ → ℝ := radialPoissonPrimitive n g A
    have hGinfty : ContDiff ℝ (⊤ : ℕ∞) G :=
      radialPoissonPrimitive_explicitRadialKernelSqDifference_contDiff
        hn R hR a b A
    have hG2 : ContDiff ℝ 2 G := hGinfty.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hderiv : deriv G 0 = g 0 / (4 * (n : ℝ)) :=
      deriv_radialPoissonPrimitive_explicitRadialKernelSqDifference_zero
        hn R hR a b A
    change 4 * coordinateLeviTrace
      (fun y : ComplexModel n => G (‖y‖ ^ 2)) 0 = g (‖(0 : ComplexModel n)‖ ^ 2)
    rw [coordinateLeviTrace_comp_norm_sq hG2]
    norm_num only [norm_zero, zero_pow]
    rw [hderiv]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  · exact
      four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_of_ne_zero
        hn R hR a b hx

/-- Global spatial form of the trace identity. -/
theorem four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_eq_kernel_sub
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    4 * coordinateLeviTrace
      (explicitRadialPoissonPotential R hR a b) x =
        explicitRadialKernel R hR a x - explicitRadialKernel R hR b x := by
  rw [four_mul_coordinateLeviTrace_explicitRadialPoissonPotential
      hn R hR a b x,
    explicitRadialKernel_sub_eq_sqDifference_norm_sq]

end SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
