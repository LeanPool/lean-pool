/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalExtend
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifyChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMollifySwap
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderData

/-!
# HomCGFinalSmoothTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The smooth-test approximation of a Hölder field

## What this file supplies

The **second half** of the second "absent analytic input": mollification of the
McShane extension of `HomCGFinalExtend`, preserving the sup bound and the
Hölder bound EXACTLY (no constant is paid), and converging back to the original
field on the set where the data lives.

For a mollifier density `ψ` (the `IsMollifierDensity`, i.e. a smooth
compactly supported probability density) and a globally `α`-Hölder, globally
sup-bounded field `G`, the coordinatewise convolution `convolutionVec ψ G` of
`HomMollifySwap` satisfies

```text
  ‖(G ⋆ ψ)(x)‖ ≤ B,   [G ⋆ ψ]_{C^{0,α}(ℝ^d)} ≤ K,   ‖(G ⋆ ψ)(x) - G(x)‖ ≤ K r^{α}
```

whenever `‖G‖ ≤ B`, `[G]_{C^{0,α}} ≤ K` and `supp ψ ⊆ closedBall 0 r`.  The
first two are the mass-one superposition principle: writing the convolution in
its swapped form `∫ G(x-t) ψ(t) dt`, each estimate holds under the integral and
`∫ψ = 1` carries it through.  All three are constant-free; only the mollifier's
radius enters, and only in the third.

`cgSmoothApprox` composes this with the McShane extension: for a field `φ` that
is sup-bounded by `K_sup` and `α`-Hölder by `K_Höl` **on `A` alone**, it
produces a sequence of GLOBALLY `C^∞` fields obeying the same two bounds
globally and converging to `φ` pointwise on `A`.  That is exactly the test-class
input the smooth dual needs.
-/

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open scoped Convolution

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The swapped form of the coordinatewise convolution -/

/-- `(G ⋆ ψ)(x)_i = ∫ G(x - t)_i ψ(t) dt`. -/
theorem convolutionVec_apply_swap (psi : Vec d → ℝ) (G : Vec d → Vec d)
    (x : Vec d) (i : Fin d) :
    convolutionVec psi G x i = ∫ t, G (x - t) i * psi t := by
  rw [convolutionVec_apply, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- The swapped integrand is integrable: continuous times compactly supported. -/
private theorem integrable_shift_mul {psi : Vec d → ℝ} (hpsi : IsMollifierDensity psi)
    {G : Vec d → Vec d} (hG : Continuous G) (x : Vec d) (i : Fin d) :
    Integrable (fun t => G (x - t) i * psi t) volume := by
  have hshift : Continuous fun t : Vec d => G (x - t) i :=
    (continuous_apply i).comp (hG.comp (continuous_const.sub continuous_id))
  have hcont : Continuous fun t : Vec d => G (x - t) i * psi t := hshift.mul hpsi.continuous
  have hsupp : HasCompactSupport fun t : Vec d => G (x - t) i * psi t :=
    HasCompactSupport.mul_left (f := fun t : Vec d => G (x - t) i) hpsi.compactSupport
  exact hcont.integrable_of_hasCompactSupport hsupp

/-! ## 2. The sup bound survives -/

/-- **`‖G ⋆ ψ‖ ≤ B` whenever `‖G‖ ≤ B`.** -/
theorem norm_convolutionVec_le {psi : Vec d → ℝ} (hpsi : IsMollifierDensity psi)
    {G : Vec d → Vec d} (hG : Continuous G) {B : ℝ} (hB : 0 ≤ B)
    (hGB : ∀ y, ‖G y‖ ≤ B) (x : Vec d) : ‖convolutionVec psi G x‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
  rw [convolutionVec_apply_swap, Real.norm_eq_abs]
  have hint := integrable_shift_mul hpsi hG x i
  have hbound : ∀ t, |G (x - t) i * psi t| ≤ B * psi t := by
    intro t
    rw [abs_mul, abs_of_nonneg (hpsi.nonneg t)]
    have h1 : |G (x - t) i| ≤ B := by
      have h := norm_le_pi_norm (G (x - t)) i
      rw [Real.norm_eq_abs] at h
      exact h.trans (hGB _)
    exact mul_le_mul_of_nonneg_right h1 (hpsi.nonneg t)
  calc |∫ t, G (x - t) i * psi t| ≤ ∫ t, |G (x - t) i * psi t| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, B * psi t := integral_mono hint.abs (hpsi.integrable.const_mul B) hbound
    _ = B * ∫ t, psi t := integral_const_mul B psi
    _ = B := by rw [hpsi.integral_eq_one, mul_one]

/-! ## 3. The Hölder bound survives -/

/-- **`[G ⋆ ψ]_{C^{0,α}} ≤ K` whenever `[G]_{C^{0,α}} ≤ K` on all of `Vec d`.** -/
theorem holderSeminormBoundOn_univ_convolutionVec {psi : Vec d → ℝ}
    (hpsi : IsMollifierDensity psi) {G : Vec d → Vec d} (hG : Continuous G)
    {alpha K : ℝ} (hK : 0 ≤ K)
    (hGH : HolderSeminormBoundOn Set.univ alpha K G) :
    HolderSeminormBoundOn Set.univ alpha K (convolutionVec psi G) := by
  intro x _ y _
  have hrhs : (0 : ℝ) ≤ K * ‖x - y‖ ^ alpha :=
    mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) alpha)
  refine (pi_norm_le_iff_of_nonneg hrhs).2 fun i => ?_
  rw [Pi.sub_apply, convolutionVec_apply_swap, convolutionVec_apply_swap, Real.norm_eq_abs]
  have hx := integrable_shift_mul hpsi hG x i
  have hy := integrable_shift_mul hpsi hG y i
  have hbound : ∀ t, |G (x - t) i * psi t - G (y - t) i * psi t| ≤
      K * ‖x - y‖ ^ alpha * psi t := by
    intro t
    have hdiff : G (x - t) i * psi t - G (y - t) i * psi t =
        (G (x - t) i - G (y - t) i) * psi t := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (hpsi.nonneg t)]
    have h1 : |G (x - t) i - G (y - t) i| ≤ K * ‖(x - t) - (y - t)‖ ^ alpha := by
      have h := norm_le_pi_norm (G (x - t) - G (y - t)) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact h.trans (hGH (x - t) (Set.mem_univ _) (y - t) (Set.mem_univ _))
    have hxy : (x - t) - (y - t) = x - y := by abel
    rw [hxy] at h1
    exact mul_le_mul_of_nonneg_right h1 (hpsi.nonneg t)
  rw [← integral_sub hx hy]
  calc |∫ t, (G (x - t) i * psi t - G (y - t) i * psi t)|
      ≤ ∫ t, |G (x - t) i * psi t - G (y - t) i * psi t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, K * ‖x - y‖ ^ alpha * psi t :=
        integral_mono (hx.sub hy).abs (hpsi.integrable.const_mul _) hbound
    _ = K * ‖x - y‖ ^ alpha * ∫ t, psi t := integral_const_mul _ psi
    _ = K * ‖x - y‖ ^ alpha := by rw [hpsi.integral_eq_one, mul_one]

/-! ## 4. The mollification is smooth -/

/-- **`G ⋆ ψ` is globally `C^∞`.** -/
theorem contDiff_convolutionVec {psi : Vec d → ℝ} (hpsi : IsMollifierDensity psi)
    {G : Vec d → Vec d} (hG : Continuous G) :
    ContDiff ℝ (⊤ : ℕ∞) (convolutionVec psi G) := by
  rw [contDiff_pi]
  intro i
  have hloc : LocallyIntegrable (fun y => G y i) volume :=
    ((continuous_apply i).comp hG).locallyIntegrable
  exact contDiff_convolution_mollifier hloc hpsi

/-! ## 5. The mollification converges back -/

/-- **`‖G ⋆ ψ - G‖ ≤ K r^{α}`** when `ψ` is supported in the closed ball of
radius `r`. -/
theorem norm_convolutionVec_sub_le {psi : Vec d → ℝ} (hpsi : IsMollifierDensity psi)
    {r : ℝ} (hr : 0 ≤ r) (hsupp : ∀ t, psi t ≠ 0 → ‖t‖ ≤ r)
    {G : Vec d → Vec d} (hG : Continuous G) {alpha K : ℝ} (hK : 0 ≤ K)
    (ha0 : 0 ≤ alpha) (hGH : HolderSeminormBoundOn Set.univ alpha K G) (x : Vec d) :
    ‖convolutionVec psi G x - G x‖ ≤ K * r ^ alpha := by
  have hrhs : (0 : ℝ) ≤ K * r ^ alpha := mul_nonneg hK (Real.rpow_nonneg hr alpha)
  refine (pi_norm_le_iff_of_nonneg hrhs).2 fun i => ?_
  rw [Pi.sub_apply, convolutionVec_apply_swap, Real.norm_eq_abs]
  have hx := integrable_shift_mul hpsi hG x i
  have hc : Integrable (fun t : Vec d => G x i * psi t) volume :=
    hpsi.integrable.const_mul _
  have hconst : ∫ t, G x i * psi t = G x i := by
    rw [integral_const_mul, hpsi.integral_eq_one, mul_one]
  have hbound : ∀ t, |G (x - t) i * psi t - G x i * psi t| ≤ K * r ^ alpha * psi t := by
    intro t
    have hdiff : G (x - t) i * psi t - G x i * psi t =
        (G (x - t) i - G x i) * psi t := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (hpsi.nonneg t)]
    rcases eq_or_ne (psi t) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    have ht : ‖t‖ ≤ r := hsupp t h0
    have h1 : |G (x - t) i - G x i| ≤ K * ‖(x - t) - x‖ ^ alpha := by
      have h := norm_le_pi_norm (G (x - t) - G x) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact h.trans (hGH (x - t) (Set.mem_univ _) x (Set.mem_univ _))
    have hnorm : ‖(x - t) - x‖ = ‖t‖ := by
      rw [sub_sub_cancel_left, norm_neg]
    rw [hnorm] at h1
    have h2 : ‖t‖ ^ alpha ≤ r ^ alpha := Real.rpow_le_rpow (norm_nonneg _) ht ha0
    have h3 : K * ‖t‖ ^ alpha ≤ K * r ^ alpha := mul_le_mul_of_nonneg_left h2 hK
    exact mul_le_mul_of_nonneg_right (h1.trans h3) (hpsi.nonneg t)
  rw [← hconst, ← integral_sub hx hc]
  calc |∫ t, (G (x - t) i * psi t - G x i * psi t)|
      ≤ ∫ t, |G (x - t) i * psi t - G x i * psi t| := abs_integral_le_integral_abs
    _ ≤ ∫ t, K * r ^ alpha * psi t :=
        integral_mono (hx.sub hc).abs (hpsi.integrable.const_mul _) hbound
    _ = K * r ^ alpha * ∫ t, psi t := integral_const_mul _ psi
    _ = K * r ^ alpha := by rw [hpsi.integral_eq_one, mul_one]

/-! ## 6. The mollifier radii of `mollifyBump` -/

/-- The normalized bump of radius `1/(k+1)` is supported in that closed ball. -/
theorem norm_le_of_normed_mollifyBump_ne_zero (k : ℕ) {t : Vec d}
    (ht : ((mollifyBump (d := d) k).normed volume) t ≠ 0) :
    ‖t‖ ≤ 1 / ((k : ℝ) + 1) := by
  have hmem : t ∈ Function.support ((mollifyBump (d := d) k).normed volume) := ht
  rw [ContDiffBump.support_normed_eq, mollifyBump_rOut] at hmem
  have hdist : dist t (0 : Vec d) < 1 / ((k : ℝ) + 1) := Metric.mem_ball.mp hmem
  rw [dist_zero_right] at hdist
  exact hdist.le

/-- The mollifier radii tend to zero at every positive Hölder exponent. -/
theorem tendsto_mollifyRadius_rpow {alpha K : ℝ} (halpha : 0 < alpha) :
    Filter.Tendsto (fun k : ℕ => K * (1 / ((k : ℝ) + 1)) ^ alpha) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : ContinuousAt (fun u : ℝ => u ^ alpha) 0 :=
    Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)
  have h3 := h2.tendsto.comp h1
  rw [Real.zero_rpow (ne_of_gt halpha)] at h3
  have h4 := h3.const_mul K
  rw [mul_zero] at h4
  exact h4

/-! ## 7. The composed smooth approximation -/

/-- **The smooth approximation of a field that is Hölder on `A` alone.**
McShane extension, then mollification at radius `1/(k+1)`. -/
def cgSmoothApprox (A : Set (Vec d)) (Ksup KHol alpha : ℝ) (phi : Vec d → Vec d)
    (k : ℕ) : Vec d → Vec d :=
  convolutionVec ((mollifyBump (d := d) k).normed volume)
    (holderExtend A Ksup KHol alpha phi)

/-- The McShane extension is continuous. -/
private theorem continuous_holderExtend {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup) :
    Continuous (holderExtend A Ksup KHol alpha phi) := by
  refine continuousOn_univ.mp ?_
  exact Schauder.continuousOn_of_holderSeminormBoundOn hKHol halpha
    (holderSeminormBoundOn_univ_holderExtend hKHol halpha.le ha1 hA hsup)

/-- **The approximation is globally `C^∞`.** -/
theorem contDiff_cgSmoothApprox {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cgSmoothApprox A Ksup KHol alpha phi k) :=
  contDiff_convolutionVec (isMollifierDensity_mollifyBump k)
    (continuous_holderExtend hKHol halpha ha1 hA hsup)

/-- **The approximation obeys the sup bound of the data, everywhere.** -/
theorem norm_cgSmoothApprox_le {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKsup : 0 ≤ Ksup) (hKHol : 0 ≤ KHol) (halpha : 0 < alpha)
    (ha1 : alpha ≤ 1) (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup)
    (k : ℕ) (x : Vec d) : ‖cgSmoothApprox A Ksup KHol alpha phi k x‖ ≤ Ksup :=
  norm_convolutionVec_le (isMollifierDensity_mollifyBump k)
    (continuous_holderExtend hKHol halpha ha1 hA hsup) hKsup
    (fun y => norm_holderExtend_le hKsup y) x

/-- **The approximation obeys the Hölder bound of the data, everywhere.** -/
theorem holderSeminormBoundOn_univ_cgSmoothApprox {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup) (k : ℕ) :
    HolderSeminormBoundOn Set.univ alpha KHol (cgSmoothApprox A Ksup KHol alpha phi k) :=
  holderSeminormBoundOn_univ_convolutionVec (isMollifierDensity_mollifyBump k)
    (continuous_holderExtend hKHol halpha ha1 hA hsup) hKHol
    (holderSeminormBoundOn_univ_holderExtend hKHol halpha.le ha1 hA hsup)

/-- **The approximation converges to the data on `A`.** -/
theorem tendsto_cgSmoothApprox {A : Set (Vec d)} {Ksup KHol alpha : ℝ}
    {phi : Vec d → Vec d} (hKHol : 0 ≤ KHol) (halpha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : A.Nonempty) (hsup : ∀ x ∈ A, ‖phi x‖ ≤ Ksup)
    (hhol : HolderSeminormBoundOn A alpha KHol phi) {x : Vec d} (hx : x ∈ A) :
    Filter.Tendsto (fun k => cgSmoothApprox A Ksup KHol alpha phi k x) Filter.atTop
      (nhds (phi x)) := by
  have hext : holderExtend A Ksup KHol alpha phi x = phi x :=
    holderExtend_eq_of_mem hKHol (ne_of_gt halpha) hsup hhol hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
    (tendsto_mollifyRadius_rpow (K := KHol) halpha)
  rw [← hext]
  exact norm_convolutionVec_sub_le (isMollifierDensity_mollifyBump k)
    (le_of_lt (one_div_pos.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) k])))
    (fun t ht => norm_le_of_normed_mollifyBump_ne_zero k ht)
    (continuous_holderExtend hKHol halpha ha1 hA hsup) hKHol halpha.le
    (holderSeminormBoundOn_univ_holderExtend hKHol halpha.le ha1 hA hsup) x

end

end Algsuperdiff.Section4.Provider.Homogenization
