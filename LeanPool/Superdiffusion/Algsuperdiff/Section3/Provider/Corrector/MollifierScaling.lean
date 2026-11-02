/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.Mollification
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# MollifierScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: scaled smoothing densities with an explicit sup-norm bound

The decorrelation bound of
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`
(`integral_normSq_mollify_le_of_covariance_support`) is quantified by the sup
norm of the smoothing density: for a probability density `κ` bounded by `M`,

`E[|A_κ X|²] ≤ M · |B_ρ| · E[|X|²]`.

Using it therefore requires a *family* of probability densities whose sup norms
tend to `0`.  `Algsuperdiff/Section3/Provider/Corrector/Mollification.lean`
already builds smooth compactly supported probability densities at every scale
(`Mollifier.ofRadius`), but the `Mollifier` structure records no sup bound.
This file supplies the missing bound, with the explicit dimensional constant
`1`:

* `productDensity` — the `d`-fold tensor product of a one-dimensional bump at
  scale `r`, i.e. `x ↦ ∏ i, φ_r(x i)`.  It is nonnegative, smooth, compactly
  supported in `B_r(0)`, integrable, of unit mass
  (`integral_productDensity`, by Fubini) and bounded by `1 / r ^ d`
  (`productDensity_le`).  It is packaged as a `Mollifier` by
  `Mollifier.ofProduct`.

The product density is recorded in addition to `Mollifier.ofRadius` because its
tensor structure is what makes the telescoping divergence kernel of
`Algsuperdiff/Section3/Provider/Corrector/DivergenceKernel.lean` work: there the
same one-dimensional factor `scaledBump` appears at two different scales.

**Disclosure.**  Nothing in this file realizes any source node.  It is a
quantitative refinement of the smoothing toolkit and claims no node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### A scaled one-dimensional bump -/

section OneDim

variable {r : ℝ}

/-- Mathlib's smooth bump function on the line with inner radius `r/2` and outer
radius `r`. -/
def lineBump (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, by linarith, by linarith⟩

@[simp] theorem lineBump_rIn (hr : 0 < r) : (lineBump hr).rIn = r / 2 := rfl

@[simp] theorem lineBump_rOut (hr : 0 < r) : (lineBump hr).rOut = r := rfl

/-- The one-dimensional smooth compactly supported probability density at
scale `r`. -/
def scaledBump (hr : 0 < r) : ℝ → ℝ := (lineBump hr).normed volume

theorem scaledBump_nonneg (hr : 0 < r) (t : ℝ) : 0 ≤ scaledBump hr t :=
  ContDiffBump.nonneg_normed _ t

theorem contDiff_scaledBump (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (scaledBump hr) :=
  ContDiffBump.contDiff_normed _

theorem continuous_scaledBump (hr : 0 < r) : Continuous (scaledBump hr) :=
  (contDiff_scaledBump hr).continuous

theorem support_scaledBump (hr : 0 < r) :
    Function.support (scaledBump hr) = Metric.ball (0 : ℝ) r := by
  have h := ContDiffBump.support_normed_eq (μ := (volume : Measure ℝ)) (f := lineBump hr)
  rwa [lineBump_rOut] at h

theorem integral_scaledBump (hr : 0 < r) : ∫ t, scaledBump hr t = 1 :=
  ContDiffBump.integral_normed _

/-- The one-dimensional density vanishes outside the interval `(-r, r)`. -/
theorem scaledBump_eq_zero (hr : 0 < r) {t : ℝ} (ht : r ≤ |t|) : scaledBump hr t = 0 := by
  by_contra hne
  have hmem : t ∈ Metric.ball (0 : ℝ) r := by
    rw [← support_scaledBump hr]
    exact hne
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  linarith

/-- **The sup-norm bound for the one-dimensional density.** -/
theorem scaledBump_le (hr : 0 < r) (t : ℝ) : scaledBump hr t ≤ 1 / r := by
  have hval : volume.real (Metric.closedBall (0 : ℝ) (r / 2)) = r := by
    rw [measureReal_def, Real.volume_closedBall,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * (r / 2))]
    ring
  have h := ContDiffBump.normed_le_div_measure_closedBall_rIn (lineBump hr)
    (μ := (volume : Measure ℝ)) t
  rw [lineBump_rIn, hval] at h
  exact h

/-! ### The scaled product density on `Vec d` -/

/-- The scaled product density on `Vec d`: the `d`-fold tensor product of the
one-dimensional bump at scale `r`. -/
def productDensity (d : ℕ) (hr : 0 < r) : Vec d → ℝ :=
  fun x => ∏ i : Fin d, scaledBump hr (x i)

theorem productDensity_nonneg (d : ℕ) (hr : 0 < r) (x : Vec d) :
    0 ≤ productDensity d hr x :=
  Finset.prod_nonneg fun i _ => scaledBump_nonneg hr (x i)

theorem contDiff_productDensity (d : ℕ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (productDensity d hr) :=
  contDiff_prod fun i _ => (contDiff_scaledBump hr).comp (contDiff_apply ℝ ℝ i)

theorem continuous_productDensity (d : ℕ) (hr : 0 < r) :
    Continuous (productDensity d hr) :=
  (contDiff_productDensity d hr).continuous

/-- The product density vanishes outside the sup-norm ball of radius `r`. -/
theorem productDensity_eq_zero_of_le (d : ℕ) (hr : 0 < r) {x : Vec d} (hx : r ≤ ‖x‖) :
    productDensity d hr x = 0 := by
  classical
  by_contra hne
  have hall : ∀ i : Fin d, ‖x i‖ < r := by
    intro i
    by_contra hi
    push Not at hi
    refine hne (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    exact scaledBump_eq_zero hr (by rwa [Real.norm_eq_abs] at hi)
  have hlt : ‖x‖ < r := (pi_norm_lt_iff hr).2 hall
  linarith

theorem support_productDensity_subset (d : ℕ) (hr : 0 < r) :
    Function.support (productDensity d hr) ⊆ Metric.ball (0 : Vec d) r := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hle
  push Not at hle
  exact hx (productDensity_eq_zero_of_le d hr hle)

theorem hasCompactSupport_productDensity (d : ℕ) (hr : 0 < r) :
    HasCompactSupport (productDensity d hr) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) r) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  push Not at hx
  exact productDensity_eq_zero_of_le d hr hx.le

theorem integrable_productDensity (d : ℕ) (hr : 0 < r) :
    Integrable (productDensity d hr) volume :=
  (continuous_productDensity d hr).integrable_of_hasCompactSupport
    (hasCompactSupport_productDensity d hr)

/-- **The product density is a probability density.**  This is Fubini on the
finite product `Vec d = Fin d → ℝ`. -/
theorem integral_productDensity (d : ℕ) (hr : 0 < r) :
    ∫ x, productDensity d hr x = 1 := by
  have h : ∫ x : Fin d → ℝ, ∏ i : Fin d, scaledBump hr (x i)
      = (∫ t, scaledBump hr t) ^ Fintype.card (Fin d) :=
    integral_fintype_prod_volume_eq_pow (𝕜 := ℝ) (ι := Fin d) (scaledBump hr)
  calc ∫ x, productDensity d hr x
      = ∫ x : Fin d → ℝ, ∏ i : Fin d, scaledBump hr (x i) := rfl
    _ = (∫ t, scaledBump hr t) ^ Fintype.card (Fin d) := h
    _ = 1 := by rw [integral_scaledBump hr, one_pow]

/-- **The sup-norm bound for the product density**, with dimensional constant
`1`: `‖κ_r‖_∞ ≤ r^{-d}`. -/
theorem productDensity_le (d : ℕ) (hr : 0 < r) (x : Vec d) :
    productDensity d hr x ≤ 1 / r ^ d := by
  classical
  have h : ∏ i : Fin d, scaledBump hr (x i) ≤ ∏ _i : Fin d, (1 / r) :=
    Finset.prod_le_prod₀ (fun i _ => scaledBump_nonneg hr (x i))
      (fun i _ => scaledBump_le hr (x i))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc productDensity d hr x = ∏ i : Fin d, scaledBump hr (x i) := rfl
    _ ≤ (1 / r) ^ d := h
    _ = 1 / r ^ d := by rw [div_pow, one_pow]

/-- The scaled product density packaged as a `Mollifier`. -/
def Mollifier.ofProduct (d : ℕ) (hr : 0 < r) : Mollifier d where
  toFun := productDensity d hr
  radius := r
  nonneg := productDensity_nonneg d hr
  smooth := contDiff_productDensity d hr
  compactSupport := hasCompactSupport_productDensity d hr
  integral_eq_one := integral_productDensity d hr
  support_subset := support_productDensity_subset d hr

end OneDim

end

end Algsuperdiff.Section3.Provider.Corrector
