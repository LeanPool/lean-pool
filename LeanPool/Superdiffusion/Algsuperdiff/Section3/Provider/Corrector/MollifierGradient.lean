/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.GradientIdentification

/-!
# MollifierGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: mollified fields have strong horizontal gradients

`Algsuperdiff/Section3/Provider/Corrector/GradientIdentification.lean` proves the
*reverse* identification `mollifyGrad_ae_eq_mollify`: **if** a stationary scalar
`φ` already possesses a strong horizontal gradient `F`, then
`mollifyGrad κ φ = mollify κ F` almost surely.  That statement presupposes the
existence of the gradient, so it cannot produce new members of the stationary
potential subspace.

This file proves the *forward* direction, which needs no such hypothesis:

`hasHorizontalGradient_toLp_mollify` — for **every** `φ ∈ L²(Ω)` and every smooth
compactly supported kernel `κ`, the mollification `A_κ φ` lies in the domain of
the horizontal gradient and its gradient is `mollifyGrad κ φ`.

Smoothing therefore *creates* differentiability along the translation action, so
every mollified stationary scalar contributes a member of
`horizontalGradientRange`, hence of `stationaryPotentialSubspace`.

The proof is elementary; no ergodic theorem, no resolvent and no semigroup theory
is used.  Two ingredients:

* the **kernel translation identity** `mollify_kernelShift`:
  `A_κ X (z +ᵥ ω) = A_{κ(· + z)} X (ω)`.  It is the change of variables
  `y ↦ y + z` under the translation-invariant Lebesgue measure of `Vec d`, and it
  holds for every sample with no integrability hypothesis;

* the **`L¹`-contraction** `norm_toLp_mollify_le`:
  `‖A_ν X‖_{L²(Ω)} ≤ ‖ν‖_{L¹} ‖X‖_{L²(Ω)}`, which is `integral_normSq_mollify_le`
  after taking square roots.

Combining them, the increment of the Koopman orbit of `A_κ φ` minus its candidate
derivative is the mollification of `φ` by the second-order Taylor remainder
`ν_t = κ(· + t e_i) − κ − t ∂_iκ` of the *kernel*, whose `L¹` norm is `O(t²)`
(`exists_integral_abs_kernel_taylor_le`, proved by two applications of the mean
value inequality, using that `∂_i∂_iκ` is bounded and that everything in sight is
supported in one fixed ball).  Hence the difference quotient converges in
`L²(Ω)`, which is exactly `HasHorizontalGradient`.

**Disclosure.**  Nothing in this file realizes any source node.  It supplies the
forward gradient identification for mollified stationary scalars and claims no
node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### An elementary comparison -/

/-- Squaring is monotone on the nonnegative reals. -/
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  by_contra hcon
  push Not at hcon
  nlinarith [h, hb, hcon]

/-! ### Translated kernels -/

section KernelShift

variable {d : ℕ}

/-- The kernel translated by `z`, namely `κ(· + z)`. -/
def kernelShift (κ : Vec d → ℝ) (z : Vec d) : Vec d → ℝ := fun y => κ (y + z)

theorem continuous_kernelShift {κ : Vec d → ℝ} (hκ : Continuous κ) (z : Vec d) :
    Continuous (kernelShift κ z) :=
  hκ.comp (continuous_id.add continuous_const)

theorem integrable_kernelShift {κ : Vec d → ℝ} (hκ : Integrable κ volume) (z : Vec d) :
    Integrable (kernelShift κ z) volume :=
  hκ.comp_add_right z

/-- **Translating the sample is translating the kernel.**  This is the change of
variables `y ↦ y + z` under the translation-invariant Lebesgue measure; it holds
for every sample, with no integrability hypothesis. -/
theorem mollify_kernelShift {Ω : Type*} [AddAction (Vec d) Ω] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Vec d → ℝ) (X : Ω → E) (z : Vec d) (ω : Ω) :
    mollify (kernelShift κ z) X ω = mollify κ X (z +ᵥ ω) := by
  have hstep : ∀ y : Vec d, kernelShift κ z y • X ((-y) +ᵥ ω)
      = (fun w : Vec d => κ w • X ((z - w) +ᵥ ω)) (y + z) := by
    intro y
    change κ (y + z) • X ((-y) +ᵥ ω) = κ (y + z) • X ((z - (y + z)) +ᵥ ω)
    rw [show z - (y + z) = -y by abel]
  have hshift : ∀ w : Vec d, κ w • X ((z - w) +ᵥ ω) = κ w • X ((-w) +ᵥ (z +ᵥ ω)) := by
    intro w
    rw [vadd_vadd, show (-w) + z = z - w by abel]
  calc mollify (kernelShift κ z) X ω
      = ∫ y, (fun w : Vec d => κ w • X ((z - w) +ᵥ ω)) (y + z) :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = ∫ w, κ w • X ((z - w) +ᵥ ω) :=
        integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun w : Vec d => κ w • X ((z - w) +ᵥ ω)) z
    _ = mollify κ X (z +ᵥ ω) :=
        integral_congr_ae (Filter.Eventually.of_forall hshift)

end KernelShift

/-! ### Smoothness and support of the kernel derivative -/

section KernelDeriv

variable {d : ℕ}

/-- The partial derivative of a smooth kernel is smooth.  (The same statement for
`coordDeriv` is `contDiff_coordDeriv` of
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`; the two
functions agree, but that file is not in this import closure.) -/
theorem contDiff_kernelDeriv {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelDeriv κ i) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ κ) := by
    have h := hκ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    simpa using h
  exact hd.clm_apply contDiff_const

/-- A partial derivative does not enlarge the closed support. -/
theorem tsupport_kernelDeriv_subset (κ : Vec d → ℝ) (i : Fin d) :
    tsupport (kernelDeriv κ i) ⊆ tsupport κ := by
  refine le_trans (closure_mono ?_) (tsupport_fderiv_subset ℝ (f := κ))
  intro x hx
  simp only [Function.mem_support, kernelDeriv, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro hzero
  exact hx (by simp [hzero])

end KernelDeriv

/-! ### The second-order Taylor bound for the kernel -/

section Taylor

variable {d : ℕ}

/-- The coordinate line `s ↦ y + s • e_i` has derivative `e_i`. -/
theorem hasDerivAt_coordLine (y : Vec d) (i : Fin d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => y + s • (Pi.single i (1 : ℝ) : Vec d))
      (Pi.single i (1 : ℝ) : Vec d) s := by
  simpa using ((hasDerivAt_id s).smul_const (Pi.single i (1 : ℝ) : Vec d)).const_add y

/-- The derivative of a smooth kernel along the `i`-th coordinate line is `∂_iκ`. -/
theorem hasDerivAt_comp_coordLine {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d)
    (y : Vec d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => κ (y + s • (Pi.single i (1 : ℝ) : Vec d)))
      (kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d))) s := by
  have hf : HasFDerivAt κ (fderiv ℝ κ (y + s • (Pi.single i (1 : ℝ) : Vec d)))
      (y + s • (Pi.single i (1 : ℝ) : Vec d)) :=
    ((hκ.differentiable (by simp)).differentiableAt).hasFDerivAt
  exact hf.comp_hasDerivAt s (hasDerivAt_coordLine y i s)

/-- **The mean value bound for the first partial derivative along its own
axis.** -/
theorem abs_kernelDeriv_sub_le {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d)
    {M : ℝ} (hM : ∀ z : Vec d, |kernelDeriv (kernelDeriv κ i) i z| ≤ M) (y : Vec d) (u : ℝ) :
    |kernelDeriv κ i (y + u • (Pi.single i (1 : ℝ) : Vec d)) - kernelDeriv κ i y| ≤ M * |u| := by
  have hd : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d)))
        (kernelDeriv (kernelDeriv κ i) i (y + s • (Pi.single i (1 : ℝ) : Vec d))) s :=
    fun s => hasDerivAt_comp_coordLine (contDiff_kernelDeriv hκ i) i y s
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ‖kernelDeriv (kernelDeriv κ i) i (y + s • (Pi.single i (1 : ℝ) : Vec d))‖ ≤ M := by
    intro s _
    rw [Real.norm_eq_abs]
    exact hM _
  have hmvt : ‖kernelDeriv κ i (y + u • (Pi.single i (1 : ℝ) : Vec d))
      - kernelDeriv κ i (y + (0 : ℝ) • (Pi.single i (1 : ℝ) : Vec d))‖ ≤ M * ‖u - (0 : ℝ)‖ :=
    (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d)))
      (f' := fun s : ℝ =>
        kernelDeriv (kernelDeriv κ i) i (y + s • (Pi.single i (1 : ℝ) : Vec d)))
      (fun s _ => (hd s).hasDerivWithinAt) hbound (Set.mem_univ 0) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using hmvt

/-- **The second-order Taylor bound along a coordinate axis.** -/
theorem abs_kernel_taylor_le {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d)
    {M : ℝ} (hM : ∀ z : Vec d, |kernelDeriv (kernelDeriv κ i) i z| ≤ M) (y : Vec d) (t : ℝ) :
    |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y| ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hd : ∀ s : ℝ,
      HasDerivAt
        (fun s : ℝ => κ (y + s • (Pi.single i (1 : ℝ) : Vec d)) - s * kernelDeriv κ i y)
        (kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d)) - kernelDeriv κ i y) s := by
    intro s
    have h2 : HasDerivAt (fun s : ℝ => s * kernelDeriv κ i y) (kernelDeriv κ i y) s := by
      simpa using (hasDerivAt_id s).mul_const (kernelDeriv κ i y)
    exact (hasDerivAt_comp_coordLine hκ i y s).sub h2
  have hbound : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ‖kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d)) - kernelDeriv κ i y‖
        ≤ M * |t| := by
    intro s hs
    have hst : |s| ≤ |t| := by
      rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1]
        exact le_trans h2 (le_abs_self t)
      · rw [abs_of_nonpos h2]
        have hneg := neg_abs_le t
        linarith
    rw [Real.norm_eq_abs]
    exact le_trans (abs_kernelDeriv_sub_le hκ i hM y s)
      (mul_le_mul_of_nonneg_left hst hM0)
  have hmvt : ‖(κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - t * kernelDeriv κ i y)
      - (κ (y + (0 : ℝ) • (Pi.single i (1 : ℝ) : Vec d)) - (0 : ℝ) * kernelDeriv κ i y)‖
      ≤ M * |t| * ‖t - (0 : ℝ)‖ :=
    (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => κ (y + s • (Pi.single i (1 : ℝ) : Vec d)) - s * kernelDeriv κ i y)
      (f' := fun s : ℝ =>
        kernelDeriv κ i (y + s • (Pi.single i (1 : ℝ) : Vec d)) - kernelDeriv κ i y)
      (fun s _ => (hd s).hasDerivWithinAt) hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at hmvt
  calc |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y|
      = |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - t * kernelDeriv κ i y - κ y| := by
        congr 1
        ring
    _ ≤ M * |t| * |t| := hmvt
    _ = M * t ^ 2 := by
        rw [mul_assoc, abs_mul_abs_self]
        ring

/-- The Taylor remainder of a smooth kernel is continuous. -/
theorem continuous_kernelTaylor {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d)
    (t : ℝ) :
    Continuous fun y : Vec d =>
      κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y :=
  ((hκ.continuous.comp (continuous_id.add continuous_const)).sub hκ.continuous).sub
    (continuous_const.mul (continuous_kernelDeriv hκ i))

/-- The Taylor remainder of a smooth compactly supported kernel is integrable. -/
theorem integrable_kernelTaylor {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) (t : ℝ) :
    Integrable (fun y : Vec d =>
      κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y) volume := by
  have hκint : Integrable κ volume :=
    hκ.continuous.integrable_of_hasCompactSupport hκc
  have h1 : Integrable
      (fun y : Vec d => κ (y + t • (Pi.single i (1 : ℝ) : Vec d))) volume :=
    integrable_kernelShift hκint (t • (Pi.single i (1 : ℝ) : Vec d))
  exact (h1.sub hκint).sub ((integrable_kernelDeriv hκc hκ i).const_mul t)

/-- **The `L¹` Taylor bound for the kernel.**  There is a constant `C` with
`∫ |κ(· + t e_i) − κ − t ∂_iκ| ≤ C t²` for every `|t| ≤ 1`.  This is what makes
the Koopman difference quotient of a mollification converge in `L²(Ω)`. -/
theorem exists_integral_abs_kernel_taylor_le {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 →
      (∫ y, |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y|)
        ≤ C * t ^ 2 := by
  classical
  -- a uniform bound on the second partial derivative
  obtain ⟨M, hMnorm⟩ :=
    (continuous_kernelDeriv (contDiff_kernelDeriv hκ i) i).bounded_above_of_compact_support
      (hasCompactSupport_kernelDeriv (hasCompactSupport_kernelDeriv hκc i) i)
  have hM : ∀ z : Vec d, |kernelDeriv (kernelDeriv κ i) i z| ≤ M := by
    intro z
    have h := hMnorm z
    rwa [Real.norm_eq_abs] at h
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- a ball containing the support
  have hcompact : IsCompact (tsupport κ) := hκc
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : Vec d)
  have hR' : tsupport κ ⊆ Metric.closedBall (0 : Vec d) (max R 0) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hκzero : ∀ y : Vec d, max R 0 < ‖y‖ → κ y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h := hR' hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    linarith
  have hκ₁zero : ∀ y : Vec d, max R 0 < ‖y‖ → kernelDeriv κ i y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h := hR' (tsupport_kernelDeriv_subset κ i hmem)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    linarith
  have hbasis : ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    rw [Real.norm_eq_abs, Pi.single_apply]
    split_ifs with hj
    · rw [abs_one]
    · rw [abs_zero]
      exact zero_le_one
  have hKmeas : MeasurableSet (Metric.closedBall (0 : Vec d) (max R 0 + 1)) :=
    measurableSet_closedBall
  have hKfin : volume (Metric.closedBall (0 : Vec d) (max R 0 + 1)) ≠ ⊤ :=
    (measure_closedBall_lt_top).ne
  have hV0 : (0 : ℝ) ≤ volume.real (Metric.closedBall (0 : Vec d) (max R 0 + 1)) :=
    ENNReal.toReal_nonneg
  refine ⟨M * volume.real (Metric.closedBall (0 : Vec d) (max R 0 + 1)),
    mul_nonneg hM0 hV0, fun t ht => ?_⟩
  have hsmall : ‖t • (Pi.single i (1 : ℝ) : Vec d)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖(Pi.single i (1 : ℝ) : Vec d)‖ ≤ |t| * 1 :=
          mul_le_mul_of_nonneg_left hbasis (abs_nonneg t)
      _ ≤ 1 := by rw [mul_one]; exact ht
  have hvanish : ∀ y : Vec d, y ∉ Metric.closedBall (0 : Vec d) (max R 0 + 1) →
      |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y| = 0 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    push Not at hy
    have h1 : κ y = 0 := hκzero y (by linarith)
    have h2 : kernelDeriv κ i y = 0 := hκ₁zero y (by linarith)
    have h3 : max R 0 < ‖y + t • (Pi.single i (1 : ℝ) : Vec d)‖ := by
      have hnorm := norm_sub_norm_le y (-(t • (Pi.single i (1 : ℝ) : Vec d)))
      rw [sub_neg_eq_add, norm_neg] at hnorm
      linarith
    rw [hκzero _ h3, h1, h2]
    simp
  have hcont : Continuous fun y : Vec d =>
      |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y| :=
    (continuous_kernelTaylor hκ i t).abs
  have hsupp : HasCompactSupport fun y : Vec d =>
      |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y| :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) (max R 0 + 1)) hvanish
  have hint : Integrable (fun y : Vec d =>
      |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y|) volume :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hindic : Integrable (Set.indicator (Metric.closedBall (0 : Vec d) (max R 0 + 1))
      (fun _ : Vec d => M * t ^ 2)) volume :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin)
  have hle : ∀ y : Vec d,
      |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y|
        ≤ Set.indicator (Metric.closedBall (0 : Vec d) (max R 0 + 1))
            (fun _ : Vec d => M * t ^ 2) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : Vec d) (max R 0 + 1)
    · rw [Set.indicator_of_mem hy]
      exact abs_kernel_taylor_le hκ i hM y t
    · rw [Set.indicator_of_notMem hy, hvanish y hy]
  calc (∫ y, |κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y|)
      ≤ ∫ y, Set.indicator (Metric.closedBall (0 : Vec d) (max R 0 + 1))
          (fun _ : Vec d => M * t ^ 2) y := integral_mono hint hindic hle
    _ = M * volume.real (Metric.closedBall (0 : Vec d) (max R 0 + 1)) * t ^ 2 := by
        rw [integral_indicator_const (M * t ^ 2) hKmeas, smul_eq_mul]
        ring

end Taylor

/-! ### The `L¹`-contraction bound in `L²(Ω)` -/

section Contraction

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The `L¹`-contraction bound.**  Mollification by a kernel of total mass
`‖κ‖₁` has operator norm at most `‖κ‖₁` on `L²(Ω)`.  This is
`integral_normSq_mollify_le` after taking square roots. -/
theorem norm_toLp_mollify_le {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X : Ω → ℝ} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ‖(memLp_two_mollify hκc hκi hXm hX).toLp (mollify κ X)‖
      ≤ (∫ y, |κ y|) * ‖hX.toLp X‖ := by
  have h := integral_normSq_mollify_le (μ := μ) hκc hκi hXm hX
  rw [integral_normSq_eq_norm_sq_toLp (memLp_two_mollify hκc hκi hXm hX),
    integral_normSq_eq_norm_sq_toLp hX] at h
  have h0 : (0 : ℝ) ≤ ∫ y, |κ y| := integral_nonneg fun y => abs_nonneg _
  refine le_of_sq_le_sq_of_nonneg ?_ (mul_nonneg h0 (norm_nonneg _))
  calc ‖(memLp_two_mollify hκc hκi hXm hX).toLp (mollify κ X)‖ ^ 2
      ≤ (∫ y, |κ y|) ^ 2 * ‖hX.toLp X‖ ^ 2 := h
    _ = ((∫ y, |κ y|) * ‖hX.toLp X‖) ^ 2 := by ring

end Contraction

/-! ### The forward horizontal gradient of a mollification -/

section Forward

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The Taylor remainder of a mollification.**  The Koopman translate of
`A_κ φ` minus `A_κ φ` minus `t` times `A_{κ₁} φ` is exactly the mollification of
`φ` by the kernel remainder `κ(· + t e_i) − κ − t κ₁`. -/
theorem koopman_toLp_mollify_sub_sub_smul {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {κ₁ : Vec d → ℝ} (hκ₁c : Continuous κ₁)
    (hκ₁i : Integrable κ₁ volume) {ν : Vec d → ℝ} (hνc : Continuous ν)
    (hνi : Integrable ν volume) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ 2 μ) (i : Fin d) (t : ℝ)
    (hν : ∀ y : Vec d,
      ν y = κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * κ₁ y) :
    koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
        ((memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ))
      - (memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ)
      - t • (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify κ₁ φ)
      = (memLp_two_mollify hνc hνi hφm hφ).toLp (mollify ν φ) := by
  classical
  refine Lp.ext ?_
  filter_upwards
    [Lp.coeFn_sub
      (koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
          ((memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ))
        - (memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ))
      (t • (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify κ₁ φ)),
    Lp.coeFn_sub
      (koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
        ((memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ)))
      ((memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ)),
    Lp.coeFn_smul t ((memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify κ₁ φ)),
    coeFn_koopman_toLp (memLp_two_mollify hκc hκi hφm hφ)
      (t • (Pi.single i (1 : ℝ) : Vec d)),
    (memLp_two_mollify hκc hκi hφm hφ).coeFn_toLp,
    (memLp_two_mollify hκ₁c hκ₁i hφm hφ).coeFn_toLp,
    (memLp_two_mollify hνc hνi hφm hφ).coeFn_toLp,
    ae_integrable_smul_comp_vadd (μ := μ)
      (continuous_kernelShift hκc (t • (Pi.single i (1 : ℝ) : Vec d)))
      (integrable_kernelShift hκi (t • (Pi.single i (1 : ℝ) : Vec d))) hφm hφ,
    ae_integrable_smul_comp_vadd (μ := μ) hκc hκi hφm hφ,
    ae_integrable_smul_comp_vadd (μ := μ) hκ₁c hκ₁i hφm hφ]
    with ω h1 h2 h3 h4 h5 h6 h7 hi1 hi2 hi3
  have hsplit : ∀ y : Vec d,
      ν y • φ ((-y) +ᵥ ω)
        = (kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω)
            - κ y • φ ((-y) +ᵥ ω)) - t * (κ₁ y • φ ((-y) +ᵥ ω)) := by
    intro y
    change ν y * φ ((-y) +ᵥ ω)
      = (κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) * φ ((-y) +ᵥ ω) - κ y * φ ((-y) +ᵥ ω))
        - t * (κ₁ y * φ ((-y) +ᵥ ω))
    rw [hν y]
    ring
  have e1 : (∫ y, ν y • φ ((-y) +ᵥ ω))
      = ∫ y, ((kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω)
          - κ y • φ ((-y) +ᵥ ω)) - t * (κ₁ y • φ ((-y) +ᵥ ω))) :=
    integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have e2 : (∫ y, ((kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω)
          - κ y • φ ((-y) +ᵥ ω)) - t * (κ₁ y • φ ((-y) +ᵥ ω))))
      = (∫ y, (kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω)
          - κ y • φ ((-y) +ᵥ ω)))
        - ∫ y, t * (κ₁ y • φ ((-y) +ᵥ ω)) :=
    integral_sub (hi1.sub hi2) (hi3.const_mul t)
  have e3 : (∫ y, (kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω)
          - κ y • φ ((-y) +ᵥ ω)))
      = (∫ y, kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω))
        - ∫ y, κ y • φ ((-y) +ᵥ ω) :=
    integral_sub hi1 hi2
  have e4 : (∫ y, t * (κ₁ y • φ ((-y) +ᵥ ω))) = t * ∫ y, κ₁ y • φ ((-y) +ᵥ ω) :=
    integral_const_mul t _
  have e5 : (∫ y, kernelShift κ (t • (Pi.single i (1 : ℝ) : Vec d)) y • φ ((-y) +ᵥ ω))
      = mollify κ φ ((t • (Pi.single i (1 : ℝ) : Vec d)) +ᵥ ω) :=
    mollify_kernelShift κ φ (t • (Pi.single i (1 : ℝ) : Vec d)) ω
  have hrhs : mollify ν φ ω
      = mollify κ φ ((t • (Pi.single i (1 : ℝ) : Vec d)) +ᵥ ω) - mollify κ φ ω
        - t * mollify κ₁ φ ω := by
    change (∫ y, ν y • φ ((-y) +ᵥ ω)) = _
    rw [e1, e2, e3, e4, e5]
    rfl
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2]
  simp only [Pi.sub_apply]
  rw [h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h4, h5, h6, h7, hrhs]

/-- The quantitative form of `koopman_toLp_mollify_sub_sub_smul`: the increment of
the Koopman orbit minus the candidate derivative is controlled by the `L¹` norm
of the kernel remainder. -/
theorem norm_koopman_toLp_mollify_sub_sub_smul_le {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {κ₁ : Vec d → ℝ} (hκ₁c : Continuous κ₁)
    (hκ₁i : Integrable κ₁ volume) {ν : Vec d → ℝ} (hνc : Continuous ν)
    (hνi : Integrable ν volume) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ 2 μ) (i : Fin d) (t : ℝ)
    (hν : ∀ y : Vec d,
      ν y = κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * κ₁ y) :
    ‖koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
        ((memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ))
      - (memLp_two_mollify hκc hκi hφm hφ).toLp (mollify κ φ)
      - t • (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify κ₁ φ)‖
      ≤ (∫ y, |ν y|) * ‖hφ.toLp φ‖ := by
  rw [koopman_toLp_mollify_sub_sub_smul hκc hκi hκ₁c hκ₁i hνc hνi hφm hφ i t hν]
  exact norm_toLp_mollify_le hνc hνi hφm hφ

/-- **The forward gradient identification, with the kernel data as parameters.**
The two hypotheses `hκcont` and `hκint` are consequences of `hκ` and `hκc`
(`ContDiff.continuous` and `Continuous.integrable_of_hasCompactSupport`); they
appear as parameters only so that the `MemLp` proof terms occurring in the
statement stay opaque during the proof.  The consequence with those proofs
supplied is `hasHorizontalGradient_toLp_mollify` below. -/
theorem hasHorizontalGradient_toLp_mollify_of_continuous {κ : Vec d → ℝ}
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκcont : Continuous κ) (hκint : Integrable κ volume)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    HasHorizontalGradient (μ := μ)
      ((memLp_two_mollify hκcont hκint hφm hφ).toLp (mollify κ φ))
      ((memLp_two_mollifyGrad hκc hκ hφm hφ).toLp (mollifyGrad κ φ)) := by
  classical
  intro i
  have hκ₁c : Continuous (kernelDeriv κ i) := continuous_kernelDeriv hκ i
  have hκ₁i : Integrable (kernelDeriv κ i) volume := integrable_kernelDeriv hκc hκ i
  -- the `i`-th coordinate of the mollified gradient
  have hcoord : vectorL2Coord (μ := μ) i
      ((memLp_two_mollifyGrad hκc hκ hφm hφ).toLp (mollifyGrad κ φ))
      = (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify (kernelDeriv κ i) φ) := by
    rw [vectorL2Coord_toLp (stronglyMeasurable_mollifyGrad hκ hφm)
      (memLp_two_mollifyGrad hκc hκ hφm hφ) i]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun _ => rfl)
  rw [hcoord]
  obtain ⟨C, hC0, hC⟩ := exists_integral_abs_kernel_taylor_le hκc hκ i
  refine hasDerivAt_iff_isLittleO.2 ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hB0 : (0 : ℝ) ≤ ‖hφ.toLp φ‖ := norm_nonneg _
  have hCB : (0 : ℝ) < C * ‖hφ.toLp φ‖ + 1 := by
    have := mul_nonneg hC0 hB0
    linarith
  have hCBne : C * ‖hφ.toLp φ‖ + 1 ≠ 0 := ne_of_gt hCB
  have hδ0 : (0 : ℝ) < min 1 (c / (C * ‖hφ.toLp φ‖ + 1)) :=
    lt_min one_pos (div_pos hc hCB)
  have hnb : ∀ᶠ t : ℝ in nhds (0 : ℝ), |t| < min 1 (c / (C * ‖hφ.toLp φ‖ + 1)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ0] with t htt
    have h := Metric.mem_ball.1 htt
    rwa [Real.dist_eq, sub_zero] at h
  filter_upwards [hnb] with t ht
  have ht1 : |t| ≤ 1 := le_of_lt (lt_of_lt_of_le ht (min_le_left _ _))
  have ht2 : |t| < c / (C * ‖hφ.toLp φ‖ + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  -- the quantitative bound at this `t`
  have hbound := norm_koopman_toLp_mollify_sub_sub_smul_le (μ := μ) hκcont hκint hκ₁c hκ₁i
    (ν := fun y => κ (y + t • (Pi.single i (1 : ℝ) : Vec d)) - κ y - t * kernelDeriv κ i y)
    (continuous_kernelTaylor hκ i t) (integrable_kernelTaylor hκc hκ i t) hφm hφ i t
    (fun _ => rfl)
  have htaylor := hC t ht1
  have hstep : ‖koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
      ((memLp_two_mollify hκcont hκint hφm hφ).toLp (mollify κ φ))
      - (memLp_two_mollify hκcont hκint hφm hφ).toLp (mollify κ φ)
      - t • (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify (kernelDeriv κ i) φ)‖
      ≤ C * t ^ 2 * ‖hφ.toLp φ‖ :=
    le_trans hbound (mul_le_mul_of_nonneg_right htaylor hB0)
  -- the arithmetic
  have hprod : (C * ‖hφ.toLp φ‖ + 1) * |t| < c := by
    have h := mul_lt_mul_of_pos_left ht2 hCB
    have he : (C * ‖hφ.toLp φ‖ + 1) * (c / (C * ‖hφ.toLp φ‖ + 1)) = c := by
      field_simp
    linarith
  have hfin : C * ‖hφ.toLp φ‖ * |t| ≤ c := by
    have := abs_nonneg t
    nlinarith [hprod, this]
  have hsq : t ^ 2 = |t| * |t| := by
    rw [abs_mul_abs_self]
    ring
  simp only [sub_zero, zero_smul, koopman_zero, Real.norm_eq_abs]
  calc ‖koopman (μ := μ) (t • (Pi.single i (1 : ℝ) : Vec d))
        ((memLp_two_mollify hκcont hκint hφm hφ).toLp (mollify κ φ))
        - (memLp_two_mollify hκcont hκint hφm hφ).toLp (mollify κ φ)
        - t • (memLp_two_mollify hκ₁c hκ₁i hφm hφ).toLp (mollify (kernelDeriv κ i) φ)‖
      ≤ C * t ^ 2 * ‖hφ.toLp φ‖ := hstep
    _ = C * ‖hφ.toLp φ‖ * |t| * |t| := by rw [hsq]; ring
    _ ≤ c * |t| := mul_le_mul_of_nonneg_right hfin (abs_nonneg t)

/-- **The forward gradient identification.**  For *every* stationary
square-integrable scalar `φ` and every smooth compactly supported kernel `κ`, the
mollification `A_κ φ` has a strong horizontal gradient, namely `mollifyGrad κ φ`.
No hypothesis on `φ` beyond membership in `L²(Ω)` is used: smoothing creates
differentiability along the translation action.

This is the converse direction of `mollifyGrad_ae_eq_mollify`
(`Algsuperdiff/Section3/Provider/Corrector/GradientIdentification.lean`), which
assumes the gradient of `φ` to exist. -/
theorem hasHorizontalGradient_toLp_mollify {κ : Vec d → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ} (hφm : StronglyMeasurable φ)
    (hφ : MemLp φ 2 μ) :
    HasHorizontalGradient (μ := μ)
      ((memLp_two_mollify hκ.continuous
        (hκ.continuous.integrable_of_hasCompactSupport hκc) hφm hφ).toLp (mollify κ φ))
      ((memLp_two_mollifyGrad hκc hκ hφm hφ).toLp (mollifyGrad κ φ)) :=
  hasHorizontalGradient_toLp_mollify_of_continuous hκc hκ hκ.continuous
    (hκ.continuous.integrable_of_hasCompactSupport hκc) hφm hφ

/-- **Mollified gradients lie in the stationary potential subspace.**  An
immediate consequence: the mollified gradient of any stationary `L²` scalar is a
member of `horizontalGradientRange`, hence of `stationaryPotentialSubspace`. -/
theorem toLp_mollifyGrad_mem_stationaryPotentialSubspace {κ : Vec d → ℝ}
    (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {φ : Ω → ℝ}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    (memLp_two_mollifyGrad hκc hκ hφm hφ).toLp (mollifyGrad κ φ)
      ∈ stationaryPotentialSubspace (μ := μ) (d := d) :=
  Submodule.le_topologicalClosure (horizontalGradientRange (μ := μ) (d := d))
    ⟨_, hasHorizontalGradient_toLp_mollify hκc hκ hφm hφ⟩

end Forward

end

end Algsuperdiff.Section3.Provider.Corrector
