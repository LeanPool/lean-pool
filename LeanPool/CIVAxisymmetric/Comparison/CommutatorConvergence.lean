/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.CommutatorL2
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Convergence of the commutator of DiPerna and Lions

Step 1 of `lem:aniso:comparison` is the vanishing, as `ε → 0`, of the commutator `R_ε` of
`eq:aniso:comparison:mollified` in `L²` of every ball. The argument runs in three stages.

For a smooth `g` the two integrals defining `R_ε` recombine, after one integration by parts
against the kernel and one use of the weak divergence of `b`, into

`R_ε = ∑ᵢ bᵢ (η_ε * ∂ᵢg) - η_ε * (∑ᵢ bᵢ ∂ᵢg)`,

so that when `g` is in addition compactly supported both terms are mollifications of
continuous compactly supported functions. Each converges uniformly to its own limit and the
two limits cancel, the error being controlled by the modulus of continuity of `∇g` and of
`b·∇g` at scale `ε`.

The general case follows from the linearity of `R_ε` in `g` together with the `L²` bound of
`eq:aniso:comparison:mollified`, applied to `g - φ` with `φ` a smooth compactly supported
approximation of `g` in `L²` of the enlarged ball. Such a `φ` comes from the density of
continuous compactly supported functions in `L²`, made smooth by a uniform approximation and
returned to compact support by a bump equal to one on the ball.
-/

public section

open MeasureTheory CKN
open scoped NNReal Topology

noncomputable section

namespace CIV

variable {m : ℕ}

private theorem continuous_kernelSub (ε : ℝ) (x : Vec m) :
    Continuous fun y : Vec m => mollifierKernel m ε (x - y) :=
  (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_const.sub continuous_id)

private theorem hasCompactSupport_kernelSub {ε : ℝ} (hε : 0 < ε) (x : Vec m) :
    HasCompactSupport fun y : Vec m => mollifierKernel m ε (x - y) := by
  refine HasCompactSupport.intro (isCompact_closedBall x ε) fun y hy => ?_
  refine mollifierKernel_eq_zero hε ?_
  have hd : ε < dist y x := by
    simpa [Metric.mem_closedBall, not_le] using hy
  rw [dist_eq_norm] at hd
  rw [← norm_neg, neg_sub]
  exact hd.le

private theorem hasCompactSupport_fderivKernelSub {ε : ℝ} (hε : 0 < ε) (x v : Vec m) :
    HasCompactSupport fun y : Vec m => fderiv ℝ (mollifierKernel m ε) (x - y) v := by
  refine HasCompactSupport.intro (isCompact_closedBall x ε) fun y hy => ?_
  refine fderiv_mollifierKernel_eq_zero hε ?_ v
  have hd : ε < dist y x := by
    simpa [Metric.mem_closedBall, not_le] using hy
  rw [dist_eq_norm] at hd
  rw [← norm_neg, neg_sub]
  exact hd

private theorem integral_kernelSub_mul_const {ε : ℝ} (hε : 0 < ε) (x : Vec m) (c : ℝ) :
    (∫ y : Vec m, mollifierKernel m ε (x - y) * c) = c := by
  rw [integral_mul_const, integral_sub_left_eq_self (mollifierKernel m ε) volume x,
    integral_mollifierKernel hε, one_mul]

private theorem integrable_kernelSub_mul {ε : ℝ} (hε : 0 < ε) {f : Vec m → ℝ}
    (hf : Continuous f) (x : Vec m) :
    Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * f y) volume :=
  ((continuous_kernelSub ε x).mul hf).integrable_of_hasCompactSupport
    ((hasCompactSupport_kernelSub hε x).mul_right)

/-- Uniform convergence of the mollification of a continuous function: if `f` varies by at
most `δ` over distances below `ε`, then `η_ε * f` differs from `f` by at most `δ`. -/
theorem abs_integral_mollifierKernel_mul_sub_le {ε δ : ℝ} (hε : 0 < ε)
    {f : Vec m → ℝ} (hf : Continuous f)
    (hmod : ∀ y z : Vec m, ‖y - z‖ < ε → |f y - f z| ≤ δ) (x : Vec m) :
    |(∫ y : Vec m, mollifierKernel m ε (x - y) * f y) - f x| ≤ δ := by
  have hint1 : Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * f y) volume :=
    integrable_kernelSub_mul hε hf x
  have hint2 : Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * f x) volume :=
    integrable_kernelSub_mul hε continuous_const x
  have hsplit : (∫ y : Vec m, mollifierKernel m ε (x - y) * f y) - f x
      = ∫ y : Vec m, (mollifierKernel m ε (x - y) * f y - mollifierKernel m ε (x - y) * f x) := by
    rw [integral_sub hint1 hint2, integral_kernelSub_mul_const hε x (f x)]
  have hpt : ∀ y : Vec m,
      ‖mollifierKernel m ε (x - y) * f y - mollifierKernel m ε (x - y) * f x‖
        ≤ mollifierKernel m ε (x - y) * δ := by
    intro y
    have hker : 0 ≤ mollifierKernel m ε (x - y) := mollifierKernel_nonneg hε _
    have heq : mollifierKernel m ε (x - y) * f y - mollifierKernel m ε (x - y) * f x
        = mollifierKernel m ε (x - y) * (f y - f x) := by ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg hker]
    by_cases hxy : ‖y - x‖ < ε
    · exact mul_le_mul_of_nonneg_left (hmod y x hxy) hker
    · have hzero : mollifierKernel m ε (x - y) = 0 := by
        refine mollifierKernel_eq_zero hε ?_
        rw [← norm_neg, neg_sub]
        exact not_lt.mp hxy
      rw [hzero, zero_mul, zero_mul]
  have hmaj : Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * δ) volume :=
    integrable_kernelSub_mul hε continuous_const x
  have hint3 : Integrable
      (fun y : Vec m => mollifierKernel m ε (x - y) * f y
        - mollifierKernel m ε (x - y) * f x) volume := hint1.sub hint2
  calc |(∫ y : Vec m, mollifierKernel m ε (x - y) * f y) - f x|
      = |∫ y : Vec m,
          (mollifierKernel m ε (x - y) * f y - mollifierKernel m ε (x - y) * f x)| := by
        rw [hsplit]
    _ ≤ ∫ y : Vec m,
          ‖mollifierKernel m ε (x - y) * f y - mollifierKernel m ε (x - y) * f x‖ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := (volume : Measure (Vec m)))
            (fun y : Vec m => mollifierKernel m ε (x - y) * f y
              - mollifierKernel m ε (x - y) * f x)
    _ ≤ ∫ y : Vec m, mollifierKernel m ε (x - y) * δ :=
        integral_mono hint3.norm hmaj hpt
    _ = δ := integral_kernelSub_mul_const hε x δ


/-! ### Integration by parts against the kernel -/

private theorem continuous_fderivApply {g : Vec m → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : Vec m) : Continuous fun y : Vec m => fderiv ℝ g y v :=
  (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hg.continuous_fderiv (by simp))

private theorem continuous_fderivKernelSub (ε : ℝ) (x v : Vec m) :
    Continuous fun y : Vec m => fderiv ℝ (mollifierKernel m ε) (x - y) v :=
  (continuous_fderiv_mollifierKernel ε v).comp (continuous_const.sub continuous_id)

private theorem fderiv_kernelSub_apply {ε : ℝ} (x y v : Vec m) :
    fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z)) y v
      = -fderiv ℝ (mollifierKernel m ε) (x - y) v := by
  have hinner : HasFDerivAt (fun z : Vec m => x - z)
      (-(ContinuousLinearMap.id ℝ (Vec m))) y := (hasFDerivAt_id y).const_sub x
  have houter : HasFDerivAt (mollifierKernel m ε)
      (fderiv ℝ (mollifierKernel m ε) (x - y)) (x - y) :=
    (differentiable_mollifierKernel ε (x - y)).hasFDerivAt
  have hcomp : HasFDerivAt (fun z : Vec m => mollifierKernel m ε (x - z))
      ((fderiv ℝ (mollifierKernel m ε) (x - y)).comp
        (-(ContinuousLinearMap.id ℝ (Vec m)))) y := houter.comp y hinner
  rw [hcomp.fderiv]
  simp

private theorem contDiff_kernelSub (ε : ℝ) (x : Vec m) :
    ContDiff ℝ (⊤ : ℕ∞) fun z : Vec m => mollifierKernel m ε (x - z) :=
  (contDiff_mollifierKernel (m := m) ε).comp (contDiff_const.sub contDiff_id)

/-- Integration by parts moving the derivative from the kernel onto a smooth function. -/
private theorem integral_mul_fderiv_kernelSub {ε : ℝ} (hε : 0 < ε) {g : Vec m → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v : Vec m) :
    (∫ y : Vec m, g y * fderiv ℝ (mollifierKernel m ε) (x - y) v)
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * fderiv ℝ g y v := by
  have hgcont : Continuous g := hg.continuous
  have hgderiv : Continuous fun y : Vec m => fderiv ℝ g y v := continuous_fderivApply hg v
  have hkderiv : Continuous fun y : Vec m => fderiv ℝ (mollifierKernel m ε) (x - y) v :=
    continuous_fderivKernelSub ε x v
  have hf'g : Integrable
      (fun y : Vec m => fderiv ℝ g y v * mollifierKernel m ε (x - y)) volume :=
    (hgderiv.mul (continuous_kernelSub ε x)).integrable_of_hasCompactSupport
      ((hasCompactSupport_kernelSub hε x).mul_left)
  have hfg' : Integrable
      (fun y : Vec m => g y * fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z)) y v)
      volume := by
    have hbase : Integrable
        (fun y : Vec m => g y * -fderiv ℝ (mollifierKernel m ε) (x - y) v) volume :=
      (hgcont.mul hkderiv.neg).integrable_of_hasCompactSupport
        ((hasCompactSupport_fderivKernelSub hε x v).neg.mul_left)
    refine hbase.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [fderiv_kernelSub_apply]
  have hfg : Integrable (fun y : Vec m => g y * mollifierKernel m ε (x - y)) volume :=
    (hgcont.mul (continuous_kernelSub ε x)).integrable_of_hasCompactSupport
      ((hasCompactSupport_kernelSub hε x).mul_left)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Vec m))) (f := g)
    (g := fun z : Vec m => mollifierKernel m ε (x - z)) (v := v) hf'g hfg' hfg
    (fun y _ => (hg.differentiable (by simp)).differentiableAt)
    (fun y _ => ((contDiff_kernelSub ε x).differentiable (by simp)).differentiableAt)
  have hleft : (∫ y : Vec m,
      g y * fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z)) y v)
      = -∫ y : Vec m, g y * fderiv ℝ (mollifierKernel m ε) (x - y) v := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [fderiv_kernelSub_apply]
    ring
  rw [hleft, neg_eq_iff_eq_neg, neg_neg] at hibp
  rw [hibp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring


/-! ### The commutator for a smooth function -/

private theorem hasCompactSupport_sumFderivKernelSub {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    (c : Vec m → Vec m) :
    HasCompactSupport fun y : Vec m =>
      ∑ i, c y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
  refine HasCompactSupport.intro (isCompact_closedBall x ε) fun y hy => ?_
  refine Finset.sum_eq_zero fun i _ => ?_
  have hd : ε < dist y x := by
    simpa [Metric.mem_closedBall, not_le] using hy
  rw [dist_eq_norm] at hd
  have hzero : fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) = 0 := by
    refine fderiv_mollifierKernel_eq_zero hε ?_ (basisVec i)
    rw [← norm_neg, neg_sub]
    exact hd
  rw [hzero, mul_zero]

private theorem continuous_sumFderivKernelSub (ε : ℝ) (x : Vec m) {c : Vec m → Vec m}
    (hc : Continuous c) :
    Continuous fun y : Vec m =>
      ∑ i, c y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hc).mul (continuous_fderivKernelSub ε x (basisVec i))

private theorem integrable_driftFderivKernel {ε : ℝ} (hε : 0 < ε) {b : Vec m → Vec m}
    {g : Vec m → ℝ} (hb : Continuous b) (hg : Continuous g) (x : Vec m) :
    Integrable (fun y : Vec m =>
      g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
  (hg.mul (continuous_sumFderivKernelSub ε x hb)).integrable_of_hasCompactSupport
    ((hasCompactSupport_sumFderivKernelSub hε x b).mul_left)

private theorem integrable_kernelDriftFderiv {ε : ℝ} (hε : 0 < ε) {b : Vec m → Vec m}
    {g : Vec m → ℝ} (hb : Continuous b) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec m) :
    Integrable (fun y : Vec m =>
      mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i)) volume :=
  ((continuous_kernelSub ε x).mul (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hb).mul
        (continuous_fderivApply hg (basisVec i)))).integrable_of_hasCompactSupport
    ((hasCompactSupport_kernelSub hε x).mul_right)

/-- The weak divergence of `b` tested against `η_ε(x - ·) g`. -/
private theorem integral_kernelSub_mul_divb_mul {ε : ℝ} (hε : 0 < ε) {b : Vec m → Vec m}
    {divb g : Vec m → ℝ} (hb : Continuous b)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec m) :
    (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y))
      = (∫ y : Vec m,
            g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
        - ∫ y : Vec m,
            mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i) := by
  have hkc : ContDiff ℝ (⊤ : ℕ∞) fun z : Vec m => mollifierKernel m ε (x - z) :=
    contDiff_kernelSub ε x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec m => mollifierKernel m ε (x - y) * g y :=
    hkc.mul hg
  have hψc : HasCompactSupport fun y : Vec m => mollifierKernel m ε (x - y) * g y :=
    (hasCompactSupport_kernelSub hε x).mul_right
  have hderiv : ∀ (y v : Vec m),
      fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z) * g z) y v
        = mollifierKernel m ε (x - y) * fderiv ℝ g y v
          - g y * fderiv ℝ (mollifierKernel m ε) (x - y) v := by
    intro y v
    have h1 : HasFDerivAt (fun z : Vec m => mollifierKernel m ε (x - z))
        (fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z)) y) y :=
      ((hkc.differentiable (by simp)) y).hasFDerivAt
    have h2 : HasFDerivAt g (fderiv ℝ g y) y := ((hg.differentiable (by simp)) y).hasFDerivAt
    have hmul : HasFDerivAt (fun z : Vec m => mollifierKernel m ε (x - z) * g z)
        (mollifierKernel m ε (x - y) • fderiv ℝ g y
          + g y • fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z)) y) y := h1.mul h2
    rw [hmul.fderiv]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, fderiv_kernelSub_apply]
    ring
  have hsum : ∀ y : Vec m,
      ∑ i, b y i * fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z) * g z) y (basisVec i)
        = mollifierKernel m ε (x - y) * (∑ i, b y i * fderiv ℝ g y (basisVec i))
          - g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    intro y
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hderiv y (basisVec i)]
    ring
  have hP : Integrable (fun y : Vec m =>
      g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
    integrable_driftFderivKernel hε hb hg.continuous x
  have hQ : Integrable (fun y : Vec m =>
      mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i)) volume :=
    integrable_kernelDriftFderiv hε hb hg x
  have hweakapp := hweak _ hψ hψc
  have hright : (∫ y : Vec m,
      ∑ i, b y i * fderiv ℝ (fun z : Vec m => mollifierKernel m ε (x - z) * g z) y (basisVec i))
      = (∫ y : Vec m,
          mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i))
        - ∫ y : Vec m,
          g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    rw [← integral_sub hQ hP]
    exact integral_congr_ae (Filter.Eventually.of_forall hsum)
  have hleft : (∫ y : Vec m, divb y * (mollifierKernel m ε (x - y) * g y))
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  rw [hleft, hright] at hweakapp
  rw [hweakapp]
  ring


/-- For a smooth `g` the commutator collapses to the difference between the drift applied to
the mollified gradient of `g` and the mollification of the drift applied to that gradient.
This is the form of `eq:aniso:comparison:mollified` in which both terms converge. -/
theorem diPernaLionsCommutator_eq_of_contDiff {ε : ℝ} (hε : 0 < ε) {b : Vec m → Vec m}
    {divb g : Vec m → ℝ} (hb : Continuous b)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec m) :
    diPernaLionsCommutator m ε b divb g x
      = (∑ i, b x i * ∫ y : Vec m, mollifierKernel m ε (x - y) * fderiv ℝ g y (basisVec i))
        - ∫ y : Vec m,
            mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i) := by
  have hA : Integrable (fun y : Vec m =>
      g y * ∑ i, b x i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
    integrable_driftFderivKernel hε continuous_const hg.continuous x
  have hB : Integrable (fun y : Vec m =>
      g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume :=
    integrable_driftFderivKernel hε hb hg.continuous x
  have hU : (∫ y : Vec m,
      g y * ∑ i, b x i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = ∑ i, b x i * ∫ y : Vec m,
          mollifierKernel m ε (x - y) * fderiv ℝ g y (basisVec i) := by
    have hpt : ∀ y : Vec m,
        g y * ∑ i, b x i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
          = ∑ i, b x i * (g y * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) := by
      intro y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hterm : ∀ i : Fin m, Integrable (fun y : Vec m =>
        b x i * (g y * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))) volume := by
      intro i
      refine ((continuous_const.mul (hg.continuous.mul
        (continuous_fderivKernelSub ε x (basisVec i)))).integrable_of_hasCompactSupport ?_)
      exact ((hasCompactSupport_fderivKernelSub hε x (basisVec i)).mul_left).mul_left
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_finsetSum _ fun i _ => hterm i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_mul_fderiv_kernelSub hε hg x (basisVec i)]
  have hsplit : (∫ y : Vec m,
      g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = (∫ y : Vec m,
            g y * ∑ i, b x i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
        - ∫ y : Vec m,
            g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    rw [← integral_sub hA hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show g y * ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
        = g y * ∑ i, b x i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
          - g y * ∑ i, b y i * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [diPernaLionsCommutator, hsplit, integral_kernelSub_mul_divb_mul hε hb hweak hg x, hU]
  ring


/-! ### The uniform bound on the commutator of a smooth function -/

private theorem continuous_driftFderiv {b : Vec m → Vec m} {g : Vec m → ℝ}
    (hb : Continuous b) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous fun y : Vec m => ∑ i, b y i * fderiv ℝ g y (basisVec i) :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hb).mul (continuous_fderivApply hg (basisVec i))

/-- The commutator of a smooth function is controlled by the modulus of continuity of its
gradient and of the drift applied to that gradient, at scale `ε`. -/
private theorem abs_diPernaLionsCommutator_le_of_contDiff {ε δ : ℝ} (hε : 0 < ε)
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hb : Continuous b)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hmod1 : ∀ (i : Fin m) (y z : Vec m), ‖y - z‖ < ε →
      |fderiv ℝ g y (basisVec i) - fderiv ℝ g z (basisVec i)| ≤ δ)
    (hmod2 : ∀ y z : Vec m, ‖y - z‖ < ε →
      |(∑ i, b y i * fderiv ℝ g y (basisVec i))
        - ∑ i, b z i * fderiv ℝ g z (basisVec i)| ≤ δ)
    (x : Vec m) :
    |diPernaLionsCommutator m ε b divb g x| ≤ ((m : ℝ) * ‖b x‖ + 1) * δ := by
  have hAi : ∀ i : Fin m,
      |(∫ y : Vec m, mollifierKernel m ε (x - y) * fderiv ℝ g y (basisVec i))
        - fderiv ℝ g x (basisVec i)| ≤ δ := fun i =>
    abs_integral_mollifierKernel_mul_sub_le hε (continuous_fderivApply hg (basisVec i))
      (hmod1 i) x
  have hW : |(∫ y : Vec m,
      mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i))
        - ∑ i, b x i * fderiv ℝ g x (basisVec i)| ≤ δ :=
    abs_integral_mollifierKernel_mul_sub_le hε (continuous_driftFderiv hb hg) hmod2 x
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hW
  set A : Fin m → ℝ := fun i =>
    ∫ y : Vec m, mollifierKernel m ε (x - y) * fderiv ℝ g y (basisVec i) with hA_def
  set W : ℝ := ∫ y : Vec m,
    mollifierKernel m ε (x - y) * ∑ i, b y i * fderiv ℝ g y (basisVec i) with hW_def
  set D : Fin m → ℝ := fun i => fderiv ℝ g x (basisVec i) with hD_def
  have hid : (∑ i, b x i * A i) - W
      = (∑ i, b x i * (A i - D i)) - (W - ∑ i, b x i * D i) := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => mul_sub (b x i) (A i) (D i)),
      Finset.sum_sub_distrib]
    ring
  have hfirst : |∑ i, b x i * (A i - D i)| ≤ (m : ℝ) * ‖b x‖ * δ := by
    have hstep : ∀ i : Fin m, |b x i * (A i - D i)| ≤ ‖b x‖ * δ := by
      intro i
      rw [abs_mul]
      have hbi : |b x i| ≤ ‖b x‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (b x) i
      exact mul_le_mul hbi (hAi i) (abs_nonneg _) (norm_nonneg _)
    calc |∑ i, b x i * (A i - D i)|
        ≤ ∑ i, |b x i * (A i - D i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, ‖b x‖ * δ := Finset.sum_le_sum fun i _ => hstep i
      _ = (m : ℝ) * ‖b x‖ * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsecond : |W - ∑ i, b x i * D i| ≤ δ := hW
  have htri : |(∑ i, b x i * (A i - D i)) - (W - ∑ i, b x i * D i)|
      ≤ |∑ i, b x i * (A i - D i)| + |W - ∑ i, b x i * D i| := by
    have h := abs_add_le (∑ i, b x i * (A i - D i)) (-(W - ∑ i, b x i * D i))
    rw [abs_neg] at h
    calc |(∑ i, b x i * (A i - D i)) - (W - ∑ i, b x i * D i)|
        = |(∑ i, b x i * (A i - D i)) + -(W - ∑ i, b x i * D i)| := by
          rw [sub_eq_add_neg]
      _ ≤ |∑ i, b x i * (A i - D i)| + |W - ∑ i, b x i * D i| := h
  have hfinal : ((m : ℝ) * ‖b x‖ + 1) * δ = (m : ℝ) * ‖b x‖ * δ + δ := by ring
  rw [diPernaLionsCommutator_eq_of_contDiff hε hb hweak hg x, hid, hfinal]
  linarith only [htri, hfirst, hsecond]


/-! ### Convergence of the commutator of a smooth function -/

/-- Step 1 of `lem:aniso:comparison`: for a smooth compactly supported `g` the commutator
`R_ε` of `eq:aniso:comparison:mollified` tends to zero in `L²` of every ball. -/
theorem tendsto_diPernaLionsCommutator_sq_integral_of_contDiff {R : ℝ} {Λ : NNReal}
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivbm : AEStronglyMeasurable divb volume)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Filter.Tendsto (fun ε : ℝ => ∫ x in Metric.closedBall (0 : Vec m) R,
        diPernaLionsCommutator m ε b divb g x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hb : Continuous b := hlip.continuous
  have hsMeas : MeasurableSet (Metric.closedBall (0 : Vec m) R) := measurableSet_closedBall
  have hsFin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec m) R)) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) R).measure_ne_top
  set V : ℝ := volume.real (Metric.closedBall (0 : Vec m) R) with hV_def
  have hVnn : 0 ≤ V := measureReal_nonneg
  set Bc : ℝ := ‖b 0‖ + (Λ : ℝ) * max R 0 with hBc_def
  have hBcnn : 0 ≤ Bc := by positivity
  have hbx : ∀ x ∈ Metric.closedBall (0 : Vec m) R, ‖b x‖ ≤ Bc := by
    intro x hx
    have hxR : ‖x‖ ≤ max R 0 := by
      have : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      exact this.trans (le_max_left _ _)
    have hdist : ‖b x - b 0‖ ≤ (Λ : ℝ) * ‖x‖ := by
      simpa [dist_eq_norm] using hlip.dist_le_mul x 0
    have htri : ‖b x‖ ≤ ‖b 0‖ + ‖b x - b 0‖ := norm_le_norm_add_norm_sub' (b x) (b 0)
    have hstep : (Λ : ℝ) * ‖x‖ ≤ (Λ : ℝ) * max R 0 :=
      mul_le_mul_of_nonneg_left hxR Λ.coe_nonneg
    linarith only [htri, hdist, hstep]
  set C : ℝ := (m : ℝ) * Bc + 1 with hC_def
  have hCpos : 0 < C := by positivity
  have hgradCont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hgradCs : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  have hu1 : UniformContinuous (fderiv ℝ g) :=
    hgradCs.uniformContinuous_of_continuous hgradCont
  have hhCont : Continuous fun y : Vec m => ∑ i, b y i * fderiv ℝ g y (basisVec i) :=
    continuous_driftFderiv hb hg
  have hhCs : HasCompactSupport fun y : Vec m => ∑ i, b y i * fderiv ℝ g y (basisVec i) := by
    refine hgradCs.mono' fun y hy => ?_
    rw [Function.mem_support] at hy
    by_contra hcon
    have hz : fderiv ℝ g y = 0 := image_eq_zero_of_notMem_tsupport hcon
    refine hy ?_
    rw [hz]
    simp
  have hu2 : UniformContinuous fun y : Vec m => ∑ i, b y i * fderiv ℝ g y (basisVec i) :=
    hhCs.uniformContinuous_of_continuous hhCont
  have hbasis : ∀ i : Fin m, ‖basisVec (d := m) i‖ ≤ 1 := by
    intro i
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [basisVec_apply]
    split_ifs <;> simp
  rw [Metric.tendsto_nhds]
  intro θ hθ
  set δ : ℝ := Real.sqrt (θ / (V * C ^ 2 + 1)) with hδ_def
  have hden : 0 < V * C ^ 2 + 1 := by positivity
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ ^ 2 = θ / (V * C ^ 2 + 1) :=
    Real.sq_sqrt (by positivity)
  have hkey : V * (C * δ) ^ 2 < θ := by
    have hexp : V * (C * δ) ^ 2 = V * C ^ 2 * (θ / (V * C ^ 2 + 1)) := by
      have hfac : V * (C * δ) ^ 2 = V * C ^ 2 * δ ^ 2 := by ring
      rw [hfac, hδsq]
    rw [hexp, ← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith only [hθ, hVnn, sq_nonneg C]
  obtain ⟨r1, hr1, H1⟩ := Metric.uniformContinuous_iff.mp hu1 δ hδpos
  obtain ⟨r2, hr2, H2⟩ := Metric.uniformContinuous_iff.mp hu2 δ hδpos
  have hrpos : 0 < min r1 r2 := lt_min hr1 hr2
  filter_upwards [Ioo_mem_nhdsGT hrpos] with ε hεmem
  obtain ⟨hεpos, hεlt⟩ := hεmem
  have hmod1 : ∀ (i : Fin m) (y z : Vec m), ‖y - z‖ < ε →
      |fderiv ℝ g y (basisVec i) - fderiv ℝ g z (basisVec i)| ≤ δ := by
    intro i y z hyz
    have hd : dist y z < r1 := by
      rw [dist_eq_norm]
      exact hyz.trans (hεlt.trans_le (min_le_left _ _))
    have hn : ‖fderiv ℝ g y - fderiv ℝ g z‖ < δ := by
      rw [← dist_eq_norm]
      exact H1 hd
    have happ : |fderiv ℝ g y (basisVec i) - fderiv ℝ g z (basisVec i)|
        ≤ ‖fderiv ℝ g y - fderiv ℝ g z‖ * ‖basisVec (d := m) i‖ := by
      have hle := (fderiv ℝ g y - fderiv ℝ g z).le_opNorm (basisVec i)
      simpa [Real.norm_eq_abs] using hle
    have hstep : ‖fderiv ℝ g y - fderiv ℝ g z‖ * ‖basisVec (d := m) i‖ ≤ δ * 1 :=
      mul_le_mul hn.le (hbasis i) (norm_nonneg _) hδpos.le
    rw [mul_one] at hstep
    exact happ.trans hstep
  have hmod2 : ∀ y z : Vec m, ‖y - z‖ < ε →
      |(∑ i, b y i * fderiv ℝ g y (basisVec i))
        - ∑ i, b z i * fderiv ℝ g z (basisVec i)| ≤ δ := by
    intro y z hyz
    have hd : dist y z < r2 := by
      rw [dist_eq_norm]
      exact hyz.trans (hεlt.trans_le (min_le_right _ _))
    have := H2 hd
    rw [Real.dist_eq] at this
    exact this.le
  have hptwise : ∀ x ∈ Metric.closedBall (0 : Vec m) R,
      |diPernaLionsCommutator m ε b divb g x| ≤ C * δ := by
    intro x hx
    refine (abs_diPernaLionsCommutator_le_of_contDiff hεpos hb hweak hg hmod1 hmod2 x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hδpos.le
    have hstep : (m : ℝ) * ‖b x‖ ≤ (m : ℝ) * Bc :=
      mul_le_mul_of_nonneg_left (hbx x hx) (Nat.cast_nonneg m)
    rw [hC_def]
    linarith only [hstep]
  have hRmeas : AEStronglyMeasurable
      (fun x : Vec m => diPernaLionsCommutator m ε b divb g x) volume :=
    aestronglyMeasurable_diPernaLionsCommutator ε hb hdivbm hg.continuous.aestronglyMeasurable
  have hint : IntegrableOn (fun x : Vec m => diPernaLionsCommutator m ε b divb g x ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
    refine (integrable_const ((C * δ) ^ 2)).mono'
      ((hRmeas.pow 2).mono_measure Measure.restrict_le_self) ?_
    refine (ae_restrict_iff' hsMeas).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h1, h2⟩ := abs_le.mp (hptwise x hx)
    exact sq_le_sq' h1 h2
  have hle : (∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb g x ^ 2) ≤ V * (C * δ) ^ 2 := by
    calc (∫ x in Metric.closedBall (0 : Vec m) R,
        diPernaLionsCommutator m ε b divb g x ^ 2)
        ≤ ∫ _x in Metric.closedBall (0 : Vec m) R, (C * δ) ^ 2 := by
          refine setIntegral_mono_on hint (integrable_const _) hsMeas fun x hx => ?_
          obtain ⟨h1, h2⟩ := abs_le.mp (hptwise x hx)
          exact sq_le_sq' h1 h2
      _ = V * (C * δ) ^ 2 := by
          rw [setIntegral_const, smul_eq_mul]
  have hnn : 0 ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb g x ^ 2 :=
    integral_nonneg fun _x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hle.trans_lt hkey


/-! ### Linearity of the commutator in the transported function -/

private theorem exists_abs_bound_of_hasCompactSupport {f : Vec m → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |f y| ≤ C := by
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have hy' : |f y| ≤ C := by simpa [Real.norm_eq_abs] using hC y hy
    exact hy'.trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]
    exact le_max_right _ _

private theorem integrable_bddMul {M : ℝ} {f S : Vec m → ℝ}
    (hS : Integrable S volume) (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ᵐ y ∂(volume : Measure (Vec m)), |f y| ≤ M) :
    Integrable (fun y : Vec m => f y * S y) volume := by
  refine hS.bdd_mul (c := M) hfm ?_
  filter_upwards [hf] with y hy
  simpa [Real.norm_eq_abs] using hy

private theorem integrable_commutatorGradTerm {ε M : ℝ} (hε : 0 < ε) {b : Vec m → Vec m}
    {g : Vec m → ℝ} (hb : Continuous b)
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M)
    (hgm : AEStronglyMeasurable g volume) (x : Vec m) :
    Integrable (fun y : Vec m =>
      g y * ∑ i, (b x i - b y i)
        * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)) volume := by
  have hcont : Continuous fun y : Vec m =>
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
    continuous_finsetSum _ fun i _ =>
      (continuous_const.sub ((continuous_apply i).comp hb)).mul
        (continuous_fderivKernelSub ε x (basisVec i))
  have hcs : HasCompactSupport fun y : Vec m =>
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
    hasCompactSupport_sumFderivKernelSub hε x fun y => b x - b y
  exact integrable_bddMul (hcont.integrable_of_hasCompactSupport hcs) hgm hg

private theorem integrable_commutatorDivTerm {ε M : ℝ} (hε : 0 < ε) {Λ : NNReal}
    {divb g : Vec m → ℝ} (hdivb : ∀ y, |divb y| ≤ Λ)
    (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M)
    (hgm : AEStronglyMeasurable g volume) (x : Vec m) :
    Integrable (fun y : Vec m => mollifierKernel m ε (x - y) * (divb y * g y)) volume := by
  have hbase : Integrable
      (fun y : Vec m => divb y * g y * mollifierKernel m ε (x - y)) volume := by
    refine integrable_bddMul (M := (Λ : ℝ) * M)
      ((continuous_kernelSub ε x).integrable_of_hasCompactSupport
        (hasCompactSupport_kernelSub hε x)) (hdivbm.mul hgm) ?_
    filter_upwards [hg] with y hy
    rw [abs_mul]
    exact mul_le_mul (hdivb y) hy (abs_nonneg _) Λ.coe_nonneg
  exact hbase.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)

/-- The commutator only depends on the a.e. class of the transported function. -/
private theorem diPernaLionsCommutator_congr_ae {ε : ℝ} {b : Vec m → Vec m}
    {divb g1 g2 : Vec m → ℝ} (h : g1 =ᵐ[volume] g2) (x : Vec m) :
    diPernaLionsCommutator m ε b divb g1 x = diPernaLionsCommutator m ε b divb g2 x := by
  have h1 : (∫ y : Vec m, g1 y *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = ∫ y : Vec m, g2 y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  have h2 : (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g1 y))
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g2 y) := by
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  rw [diPernaLionsCommutator, diPernaLionsCommutator, h1, h2]

/-- The commutator is linear in the transported function: the commutator of a difference is
the difference of the commutators. -/
private theorem diPernaLionsCommutator_sub {ε M1 M2 : ℝ} (hε : 0 < ε) {Λ : NNReal}
    {b : Vec m → Vec m} {divb g1 g2 : Vec m → ℝ} (hb : Continuous b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg1 : ∀ᵐ y ∂(volume : Measure (Vec m)), |g1 y| ≤ M1)
    (hg1m : AEStronglyMeasurable g1 volume)
    (hg2 : ∀ᵐ y ∂(volume : Measure (Vec m)), |g2 y| ≤ M2)
    (hg2m : AEStronglyMeasurable g2 volume) (x : Vec m) :
    diPernaLionsCommutator m ε b divb (fun y => g1 y - g2 y) x
      = diPernaLionsCommutator m ε b divb g1 x
        - diPernaLionsCommutator m ε b divb g2 x := by
  have hA1 := integrable_commutatorGradTerm hε hb hg1 hg1m x
  have hA2 := integrable_commutatorGradTerm hε hb hg2 hg2m x
  have hB1 := integrable_commutatorDivTerm hε hdivb hdivbm hg1 hg1m x
  have hB2 := integrable_commutatorDivTerm hε hdivb hdivbm hg2 hg2m x
  have hAsplit : (∫ y : Vec m, (g1 y - g2 y) *
      ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = (∫ y : Vec m, g1 y *
          ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
        - ∫ y : Vec m, g2 y *
          ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) := by
    rw [← integral_sub hA1 hA2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (g1 y - g2 y) *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
      = g1 y * (∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
        - g2 y * ∑ i, (b x i - b y i)
            * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i)
    ring
  have hBsplit : (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * (g1 y - g2 y)))
      = (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g1 y))
        - ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g2 y) := by
    rw [← integral_sub hB1 hB2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show mollifierKernel m ε (x - y) * (divb y * (g1 y - g2 y))
      = mollifierKernel m ε (x - y) * (divb y * g1 y)
        - mollifierKernel m ε (x - y) * (divb y * g2 y)
    ring
  simp only [diPernaLionsCommutator]
  rw [hAsplit, hBsplit]
  ring


/-! ### Approximation by smooth compactly supported functions -/

/-- Density of smooth compactly supported functions in `L²` of a ball: a bounded measurable
function is approximated there, to any accuracy, by a smooth compactly supported one. -/
theorem exists_contDiff_hasCompactSupport_integral_sq_sub_le {R M : ℝ} {g : Vec m → ℝ}
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M)
    (hgm : AEStronglyMeasurable g volume) {θ : ℝ} (hθ : 0 < θ) :
    ∃ φ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∫ y in Metric.closedBall (0 : Vec m) R, (g y - φ y) ^ 2) ≤ θ := by
  set s : Set (Vec m) := Metric.closedBall (0 : Vec m) R with hs_def
  have hsMeas : MeasurableSet s := measurableSet_closedBall
  have hsCompact : IsCompact s := isCompact_closedBall (0 : Vec m) R
  have hsFin : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.2 hsCompact.measure_ne_top
  set V : ℝ := volume.real s with hV_def
  have hVnn : 0 ≤ V := measureReal_nonneg
  have hgnorm : ∀ᵐ y ∂(volume.restrict s), ‖g y‖ ≤ M := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hg] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hGmem : MemLp (s.indicator g) 2 volume :=
    (memLp_indicator_iff_restrict hsMeas).mpr (MemLp.of_bound hgm.restrict M hgnorm)
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hGmem' : MemLp (s.indicator g) (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [htwo]; exact hGmem
  obtain ⟨f, hfcs, hfbound, hfcont, hfmem⟩ :=
    hGmem'.exists_hasCompactSupport_integral_rpow_sub_le (p := (2 : ℝ)) two_pos
      (by positivity : (0 : ℝ) < θ / 4)
  have hrpow : ∀ a : ℝ, ‖a‖ ^ (2 : ℝ) = a ^ 2 := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hfbound2 : (∫ y : Vec m, (s.indicator g y - f y) ^ 2) ≤ θ / 4 := by
    have heq : (∫ y : Vec m, ‖s.indicator g y - f y‖ ^ (2 : ℝ))
        = ∫ y : Vec m, (s.indicator g y - f y) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => hrpow _)
    rw [heq] at hfbound
    exact hfbound
  have hfmem2 : MemLp f 2 volume := by rw [← htwo]; exact hfmem
  have hdiffint : Integrable (fun y : Vec m => (s.indicator g y - f y) ^ 2) volume :=
    (hGmem.sub hfmem2).integrable_sq
  have hgfint : IntegrableOn (fun y : Vec m => (g y - f y) ^ 2) s volume := by
    refine (hdiffint.integrableOn).congr_fun (fun y hy => ?_) hsMeas
    simp only [Set.indicator_of_mem hy]
  have hstep1 : (∫ y in s, (g y - f y) ^ 2) ≤ θ / 4 := by
    have hcongr : (∫ y in s, (g y - f y) ^ 2)
        = ∫ y in s, (s.indicator g y - f y) ^ 2 := by
      refine setIntegral_congr_fun hsMeas fun y hy => ?_
      rw [Set.indicator_of_mem hy]
    rw [hcongr]
    exact le_trans (setIntegral_le_integral hdiffint
      (Filter.Eventually.of_forall fun y => sq_nonneg _)) hfbound2
  -- the smooth uniform approximation of the continuous approximant
  have hfunif : UniformContinuous f := hfcs.uniformContinuous_of_continuous hfcont
  set η : ℝ := Real.sqrt (θ / (4 * (V + 1))) with hη_def
  have hηpos : 0 < η := Real.sqrt_pos.mpr (by positivity)
  have hηsq : η ^ 2 = θ / (4 * (V + 1)) := Real.sq_sqrt (by positivity)
  obtain ⟨u, hu, husmall⟩ := hfunif.exists_contDiff_dist_le hηpos
  -- a smooth cutoff equal to one on the ball
  obtain ⟨χ, hχSmooth, hχCs, hχOne⟩ :
      ∃ χ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ
        ∧ ∀ y ∈ s, χ y = 1 := by
    have h1 : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h2 : max R 1 < max R 1 + 1 := by linarith only []
    refine ⟨((⟨max R 1, max R 1 + 1, h1, h2⟩ : ContDiffBump (0 : Vec m)) : Vec m → ℝ),
      ContDiffBump.contDiff _, ContDiffBump.hasCompactSupport _, fun y hy => ?_⟩
    refine ContDiffBump.one_of_mem_closedBall _ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyR : ‖y‖ ≤ R := by
      simpa [hs_def, Metric.mem_closedBall, dist_zero_right] using hy
    exact hyR.trans (le_max_left _ _)
  refine ⟨fun y => χ y * u y, hχSmooth.mul hu, hχCs.mul_right, ?_⟩
  have hφCont : Continuous fun y : Vec m => χ y * u y :=
    hχSmooth.continuous.mul hu.continuous
  have hφCs : HasCompactSupport fun y : Vec m => χ y * u y := hχCs.mul_right
  obtain ⟨Cφ, hCφnn, hCφ⟩ := exists_abs_bound_of_hasCompactSupport hφCont hφCs
  have hfφCont : Continuous fun y : Vec m => (f y - χ y * u y) ^ 2 :=
    (hfcont.sub hφCont).pow 2
  have hfφInt : IntegrableOn (fun y : Vec m => (f y - χ y * u y) ^ 2) s volume :=
    hfφCont.continuousOn.integrableOn_compact hsCompact
  have hstep2 : (∫ y in s, (f y - χ y * u y) ^ 2) ≤ V * η ^ 2 := by
    have hpt : ∀ y ∈ s, (f y - χ y * u y) ^ 2 ≤ η ^ 2 := by
      intro y hy
      rw [hχOne y hy, one_mul]
      have hd := husmall y
      rw [Real.dist_eq] at hd
      have habs : |f y - u y| ≤ η := by
        rw [abs_sub_comm]
        exact hd.le
      calc (f y - u y) ^ 2 = |f y - u y| ^ 2 := (sq_abs _).symm
        _ ≤ η ^ 2 := by gcongr
    calc (∫ y in s, (f y - χ y * u y) ^ 2)
        ≤ ∫ _y in s, η ^ 2 :=
          setIntegral_mono_on hfφInt (integrable_const _) hsMeas hpt
      _ = V * η ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  have hgφInt : IntegrableOn (fun y : Vec m => (g y - χ y * u y) ^ 2) s volume := by
    refine (integrable_const ((M + Cφ) ^ 2)).mono'
      (((hgm.sub hφCont.aestronglyMeasurable).pow 2).mono_measure
        Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_of_ae hg] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have habs : |g y - χ y * u y| ≤ M + Cφ :=
      (abs_sub _ _).trans (add_le_add hy (hCφ y))
    calc (g y - χ y * u y) ^ 2 = |g y - χ y * u y| ^ 2 := (sq_abs _).symm
      _ ≤ (M + Cφ) ^ 2 := by gcongr
  have hsumInt : IntegrableOn (fun y : Vec m =>
      2 * (g y - f y) ^ 2 + 2 * (f y - χ y * u y) ^ 2) s volume :=
    (hgfint.const_mul 2).add (hfφInt.const_mul 2)
  have hcomb : ∀ y ∈ s, (g y - χ y * u y) ^ 2
      ≤ 2 * (g y - f y) ^ 2 + 2 * (f y - χ y * u y) ^ 2 := by
    intro y _
    nlinarith only [sq_nonneg ((g y - f y) - (f y - χ y * u y))]
  have hkey : V * η ^ 2 ≤ θ / 4 := by
    have hmul : η ^ 2 * (4 * (V + 1)) = θ := by
      rw [hηsq]
      field_simp
    have h4 : θ / 4 = η ^ 2 * (V + 1) := by
      rw [← hmul]
      ring
    rw [h4]
    nlinarith only [sq_nonneg η]
  calc (∫ y in s, (g y - χ y * u y) ^ 2)
      ≤ ∫ y in s, (2 * (g y - f y) ^ 2 + 2 * (f y - χ y * u y) ^ 2) :=
        setIntegral_mono_on hgφInt hsumInt hsMeas hcomb
    _ = 2 * (∫ y in s, (g y - f y) ^ 2) + 2 * ∫ y in s, (f y - χ y * u y) ^ 2 := by
        rw [integral_add (hgfint.const_mul 2) (hfφInt.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ θ := by linarith only [hstep1, hstep2, hkey]


/-! ### Convergence of the commutator of a bounded measurable function -/

private theorem integrableOn_sq_diPernaLionsCommutator {ε M R : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    {Λ : NNReal} {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ y, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) :
    IntegrableOn (fun x : Vec m => diPernaLionsCommutator m ε b divb g x ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
  have hsFin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec m) R)) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) R).measure_ne_top
  have hRmeas : AEStronglyMeasurable
      (fun x : Vec m => diPernaLionsCommutator m ε b divb g x) volume :=
    aestronglyMeasurable_diPernaLionsCommutator ε hlip.continuous hdivbm hgm
  refine (integrable_const (((Λ : ℝ) * M * (mollifierGradConst m + 1)) ^ 2)).mono'
    ((hRmeas.pow 2).mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨h1, h2⟩ :=
    abs_le.mp (abs_diPernaLionsCommutator_le hε hM hlip hdivb hdivbm hg hgm x)
  exact sq_le_sq' h1 h2

private theorem exists_stronglyMeasurable_bound {M : ℝ} (hM : 0 ≤ M) {g : Vec m → ℝ}
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M)
    (hgm : AEStronglyMeasurable g volume) :
    ∃ g' : Vec m → ℝ, (∀ y, |g' y| ≤ M) ∧ AEStronglyMeasurable g' volume
      ∧ g =ᵐ[volume] g' := by
  classical
  obtain ⟨h, hhmeas, hae⟩ := hgm
  have hmeas : Measurable h := hhmeas.measurable
  have habs : Measurable fun y : Vec m => |h y| := continuous_abs.measurable.comp hmeas
  have hset : MeasurableSet {y : Vec m | |h y| ≤ M} :=
    measurableSet_le habs measurable_const
  refine ⟨fun y => if |h y| ≤ M then h y else 0, ?_, ?_, ?_⟩
  · intro y
    show |if |h y| ≤ M then h y else 0| ≤ M
    split_ifs with hy
    · exact hy
    · rw [abs_zero]
      exact hM
  · exact (StronglyMeasurable.ite hset hhmeas stronglyMeasurable_const).aestronglyMeasurable
  · filter_upwards [hae, hg] with y hy1 hy2
    have hy3 : |h y| ≤ M := by rw [← hy1]; exact hy2
    have hif : (if |h y| ≤ M then h y else 0) = h y :=
      ite_eq_left_iff.mpr fun hcond => absurd hy3 hcond
    show g y = if |h y| ≤ M then h y else 0
    rw [hif]
    exact hy1

private theorem tendsto_sq_integral_of_forall_abs_le {Λ : NNReal} {M R : ℝ}
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hM : 0 ≤ M) (hg : ∀ y, |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ x in Metric.closedBall (0 : Vec m) R,
        diPernaLionsCommutator m ε b divb g x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hb : Continuous b := hlip.continuous
  have hsMeas : MeasurableSet (Metric.closedBall (0 : Vec m) R) := measurableSet_closedBall
  have ht1Fin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec m) (R + 1))) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) (R + 1)).measure_ne_top
  have hgae : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M := Filter.Eventually.of_forall hg
  rw [Metric.tendsto_nhds]
  intro θ hθ
  set C1 : ℝ := (Λ : ℝ) * (mollifierGradConst m + 1) with hC1_def
  have hC1nn : 0 ≤ C1 :=
    mul_nonneg Λ.coe_nonneg (add_nonneg mollifierGradConst_nonneg zero_le_one)
  obtain ⟨φ, hφSmooth, hφCs, hφApprox⟩ :=
    exists_contDiff_hasCompactSupport_integral_sq_sub_le (R := R + 1) (M := M) hgae hgm
      (θ := θ / (4 * (C1 ^ 2 + 1))) (by positivity)
  obtain ⟨Cφ, hCφnn, hCφ⟩ :=
    exists_abs_bound_of_hasCompactSupport hφSmooth.continuous hφCs
  have hφm : AEStronglyMeasurable φ volume :=
    hφSmooth.continuous.aestronglyMeasurable
  have hPbound : ∀ y, |g y - φ y| ≤ M + Cφ := fun y =>
    (abs_sub _ _).trans (add_le_add (hg y) (hCφ y))
  have hPm : AEStronglyMeasurable (fun y : Vec m => g y - φ y) volume := hgm.sub hφm
  have hMC : 0 ≤ M + Cφ := add_nonneg hM hCφnn
  have hPsqInt : IntegrableOn (fun y : Vec m => (g y - φ y) ^ 2)
      (Metric.closedBall (0 : Vec m) (R + 1)) volume := by
    refine (integrable_const ((M + Cφ) ^ 2)).mono'
      ((hPm.pow 2).mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h1, h2⟩ := abs_le.mp (hPbound y)
    exact sq_le_sq' h1 h2
  have hDnn : (0 : ℝ) ≤ θ / (4 * (C1 ^ 2 + 1)) := by positivity
  have hDeq : (C1 ^ 2 + 1) * (θ / (4 * (C1 ^ 2 + 1))) = θ / 4 := by
    field_simp
  have hfinal : 2 * (C1 ^ 2 * (θ / (4 * (C1 ^ 2 + 1)))) ≤ θ / 2 := by
    have h1 : C1 ^ 2 * (θ / (4 * (C1 ^ 2 + 1)))
        ≤ (C1 ^ 2 + 1) * (θ / (4 * (C1 ^ 2 + 1))) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hDnn
    rw [hDeq] at h1
    linarith only [h1]
  have hA := tendsto_diPernaLionsCommutator_sq_integral_of_contDiff (R := R) hlip hdivbm hweak
    hφSmooth hφCs
  rw [Metric.tendsto_nhds] at hA
  filter_upwards [hA (θ / 4) (by positivity), Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)]
    with ε hAe hεmem
  obtain ⟨hεpos, hεlt⟩ := hεmem
  have hnn : 0 ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb g x ^ 2 := integral_nonneg fun _x => sq_nonneg _
  have hnnφ : 0 ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb φ x ^ 2 := integral_nonneg fun _x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnnφ] at hAe
  have hsqbound : ∀ x : Vec m, diPernaLionsCommutator m ε b divb g x ^ 2
      ≤ 2 * diPernaLionsCommutator m ε b divb φ x ^ 2
        + 2 * diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2 := by
    intro x
    have hsub := diPernaLionsCommutator_sub (M1 := M) (M2 := Cφ) hεpos hb hdivb hdivbm
      hgae hgm (Filter.Eventually.of_forall hCφ) hφm x
    have hdec : diPernaLionsCommutator m ε b divb g x
        = diPernaLionsCommutator m ε b divb φ x
          + diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x := by
      linarith only [hsub]
    rw [hdec]
    nlinarith only [sq_nonneg (diPernaLionsCommutator m ε b divb φ x
      - diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x)]
  have hIg := integrableOn_sq_diPernaLionsCommutator (R := R) hεpos hM hlip hdivb hdivbm hg hgm
  have hIφ := integrableOn_sq_diPernaLionsCommutator (R := R) hεpos hCφnn hlip hdivb hdivbm
    hCφ hφm
  have hIP := integrableOn_sq_diPernaLionsCommutator (R := R) hεpos hMC hlip hdivb hdivbm
    hPbound hPm
  have hIsum : IntegrableOn (fun x : Vec m =>
      2 * diPernaLionsCommutator m ε b divb φ x ^ 2
        + 2 * diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := (hIφ.const_mul 2).add (hIP.const_mul 2)
  have hstep : (∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb g x ^ 2)
      ≤ 2 * (∫ x in Metric.closedBall (0 : Vec m) R,
            diPernaLionsCommutator m ε b divb φ x ^ 2)
        + 2 * ∫ x in Metric.closedBall (0 : Vec m) R,
            diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2 := by
    calc (∫ x in Metric.closedBall (0 : Vec m) R,
        diPernaLionsCommutator m ε b divb g x ^ 2)
        ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
            (2 * diPernaLionsCommutator m ε b divb φ x ^ 2
              + 2 * diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2) :=
          setIntegral_mono_on hIg hIsum hsMeas fun x _ => hsqbound x
      _ = 2 * (∫ x in Metric.closedBall (0 : Vec m) R,
              diPernaLionsCommutator m ε b divb φ x ^ 2)
            + 2 * ∫ x in Metric.closedBall (0 : Vec m) R,
              diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2 := by
          rw [integral_add (hIφ.const_mul 2) (hIP.const_mul 2), integral_const_mul,
            integral_const_mul]
  have hL2 := integral_sq_diPernaLionsCommutator_le (R := R) (M := M + Cφ) hεpos hMC hlip
    hdivb hdivbm hPbound hPm
  rw [← hC1_def] at hL2
  have hmono : (∫ y in Metric.closedBall (0 : Vec m) (R + ε), (g y - φ y) ^ 2)
      ≤ ∫ y in Metric.closedBall (0 : Vec m) (R + 1), (g y - φ y) ^ 2 := by
    refine setIntegral_mono_set hPsqInt
      (Filter.Eventually.of_forall fun _y => sq_nonneg _) ?_
    have hsub : Metric.closedBall (0 : Vec m) (R + ε)
        ⊆ Metric.closedBall (0 : Vec m) (R + 1) :=
      Metric.closedBall_subset_closedBall (by linarith only [hεlt])
    exact LE.le.eventuallySubset hsub
  have hBbound : (∫ x in Metric.closedBall (0 : Vec m) R,
      diPernaLionsCommutator m ε b divb (fun y => g y - φ y) x ^ 2)
      ≤ C1 ^ 2 * (θ / (4 * (C1 ^ 2 + 1))) := by
    refine hL2.trans ?_
    refine mul_le_mul_of_nonneg_left (hmono.trans hφApprox) (sq_nonneg C1)
  linarith only [hstep, hAe, hBbound, hfinal]

/-- Step 1 of `lem:aniso:comparison`: the DiPerna–Lions commutator `R_ε` of
`eq:aniso:comparison:mollified` converges to zero in `L²` of every ball as `ε → 0`, for every
bounded measurable `g` and every Lipschitz drift with bounded weak divergence. -/
theorem tendsto_diPernaLionsCommutator_sq_integral {Λ : NNReal} {M R : ℝ}
    {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hweak : ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y : Vec m, divb y * ψ y
        = -∫ y : Vec m, ∑ i, b y i * fderiv ℝ ψ y (basisVec i))
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M)
    (hgm : AEStronglyMeasurable g volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ x in Metric.closedBall (0 : Vec m) R,
        diPernaLionsCommutator m ε b divb g x ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 ≤ M := by
    obtain ⟨y, hy⟩ := hg.exists
    exact (abs_nonneg _).trans hy
  obtain ⟨g', hg'bound, hg'meas, hgg'⟩ := exists_stronglyMeasurable_bound hM hg hgm
  have heq : ∀ (ε : ℝ) (x : Vec m),
      diPernaLionsCommutator m ε b divb g x = diPernaLionsCommutator m ε b divb g' x :=
    fun ε x => diPernaLionsCommutator_congr_ae hgg' x
  simp only [heq]
  exact tendsto_sq_integral_of_forall_abs_le hlip hdivb hdivbm hweak hM hg'bound hg'meas

end CIV
