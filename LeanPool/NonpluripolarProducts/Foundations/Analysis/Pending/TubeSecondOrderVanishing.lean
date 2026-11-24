/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LeviFormHolomorphicComp

/-!
# Second-order vanishing of a tube function, and the cross terms of a partition of unity

Source: Copy-4, step 6 of the proof of `prop:principalization`, where `r_W²` is *the
square of the distance to `W` with respect to a Riemannian metric on `Y`* — a single
function on a neighbourhood of `W`, whereas the flattening of `W` is only local.  The
standard construction patches the chart tubes `r_i²` with a partition of unity
`Σ χ_i = 1`, and the point of the patching is that it does not disturb the Levi form
**along `W`**:

  `ddᶜ (Σ χ_i r_i²) = Σ χ_i ddᶜ r_i²`   at every point of `W`,

because each `r_i²` vanishes there to second order, so the cross terms
`dχ_i ⊗ d(r_i²)` and `r_i² ddᶜ χ_i` all drop out.  This file proves that cancellation.

* `fderiv_eq_zero_of_nonneg_of_eq_zero`: a nonnegative differentiable function has
  vanishing differential at each of its zeros.  For a tube function this is the whole
  of "vanishes to second order": the value is `0` by construction and the differential
  is then free.
* `realHessian_mul_of_eq_zero_of_fderiv_eq_zero` and
  `leviForm_mul_of_eq_zero_of_fderiv_eq_zero`: at a point where `g` and `dg` vanish,
  `D²(f g) = f · D²g` and hence `L(f g) = f · L(g)`.  Both cross terms of the Leibniz
  rule carry a factor `dg`, and the remaining `g · D²f` carries a factor `g`.
* `leviForm_finsetSum_mul`: the partition-of-unity statement, for a finite family with
  a common zero.  Semipositivity and the kernel are then inherited from the summands:
  `leviForm_finsetSum_mul_nonneg` and
  `leviForm_eq_zero_of_leviForm_finsetSum_mul_eq_zero` (the latter needs one index with
  `0 < χ_i x`, which is exactly what a partition of unity supplies).
* `fderiv_planeDistSq_comp_eq_zero`: the chart tube `r² ∘ F` of
  `Pending.LeviFormHolomorphicComp` satisfies the hypothesis at each of its zeros.

All hypotheses are at the level of the GERM at `x` (`ContDiffAt`, `∀ᶠ y in 𝓝 x`),
because that is what the chart picture supplies: `r_i²` is defined only on the `i`-th
flattening chart.

**What this file does NOT do.**  It says nothing about the summands `χ_i r_i²` being
globally defined.  In the real construction `χ_i` is supported in the `i`-th chart and
`χ_i r_i²` is extended by zero, and the extension being `C²` is a separate (easy but
unwritten) step; at a point `x` outside the `i`-th chart the hypotheses below are then
satisfied by the zero function rather than by `r_i²`.  Nothing here uses the
modification or any deferred input.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.TubeSecondOrderVanishing

open FirstPass PlaneTubePositivity LeviFormHolomorphicComp

noncomputable section

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A locally nonnegative function has vanishing differential at each of its
zeros.** -/
theorem fderiv_eq_zero_of_nonneg_of_eq_zero {g : E → ℝ} {x : E}
    (hg : ∀ᶠ y in 𝓝 x, 0 ≤ g y) (hx : g x = 0) : fderiv ℝ g x = 0 := by
  have hmin : IsLocalMin g x := hg.mono fun y hy => by rw [hx]; exact hy
  exact hmin.fderiv_eq_zero

/-- **The Leibniz rule at a second-order zero.**  Where `g` and `dg` vanish, the real
Hessian of `f g` is `f` times that of `g`: the two cross terms carry a factor `dg` and
the fourth term carries a factor `g`. -/
theorem realHessian_mul_of_eq_zero_of_fderiv_eq_zero
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hg0 : g x = 0) (hdg : fderiv ℝ g x = 0) (v w : E) :
    realHessian (fun y => f y * g y) x v w = f x * realHessian g x v w := by
  have hfe : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hge : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g y := hg.eventually (by simp)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hprod : fderiv ℝ (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    filter_upwards [hfe, hge] with y hfy hgy
    exact fderiv_mul (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have h1 : HasFDerivAt (fun y => f y • fderiv ℝ g y)
      (f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) x :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt.smul hDg.hasFDerivAt
  have h2 : HasFDerivAt (fun y => g y • fderiv ℝ f y)
      (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) x :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.smul hDf.hasFDerivAt
  have h3 : HasFDerivAt (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y)
      ((f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
        (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))) x :=
    h1.add h2
  rw [realHessian_eq_fderiv, hprod.fderiv_eq, h3.fderiv]
  simp [hg0, hdg, realHessian_eq_fderiv]

end Real

section Levi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]

/-- **The Levi form at a second-order zero.** -/
theorem leviForm_mul_of_eq_zero_of_fderiv_eq_zero
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hg0 : g x = 0) (hdg : fderiv ℝ g x = 0) (v : E) :
    leviForm (fun y => f y * g y) x v = f x * leviForm g x v := by
  simp only [leviForm,
    realHessian_mul_of_eq_zero_of_fderiv_eq_zero hf hg hg0 hdg]
  ring

/-- **The patched tube has the patched Levi form along the submanifold.**  For a finite
family of nonnegative `C²` tube functions with a common zero at `x`, the Levi form of
`Σ χ_i g_i` at `x` is `Σ χ_i(x) · L(g_i)(x)`: no cross term survives. -/
theorem leviForm_finsetSum_mul {ι : Type*} (s : Finset ι)
    {χ g : ι → E → ℝ} {x : E}
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x) (hg : ∀ i, ContDiffAt ℝ 2 (g i) x)
    (hg0 : ∀ i, ∀ᶠ y in 𝓝 x, 0 ≤ g i y) (hgx : ∀ i, g i x = 0) (v : E) :
    leviForm (fun y => ∑ i ∈ s, χ i y * g i y) x v =
      ∑ i ∈ s, χ i x * leviForm (g i) x v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hj ih =>
      have hsum : ContDiffAt ℝ 2 (fun y => ∑ i ∈ t, χ i y * g i y) x :=
        ContDiffAt.sum fun i _ => (hχ i).mul (hg i)
      have hfun : (fun y => ∑ i ∈ insert j t, χ i y * g i y) =
          (fun y => χ j y * g j y) + (fun y => ∑ i ∈ t, χ i y * g i y) := by
        funext y; simp [Finset.sum_insert hj]
      rw [hfun, leviForm_add ((hχ j).mul (hg j)) hsum, ih,
        leviForm_mul_of_eq_zero_of_fderiv_eq_zero (hχ j) (hg j) (hgx j)
          (fderiv_eq_zero_of_nonneg_of_eq_zero (hg0 j) (hgx j)),
        Finset.sum_insert hj]

/-- The patched tube is semipositive along the submanifold whenever the weights are
nonnegative and each chart tube is. -/
theorem leviForm_finsetSum_mul_nonneg {ι : Type*} (s : Finset ι)
    {χ g : ι → E → ℝ} {x : E} (v : E)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x) (hg : ∀ i, ContDiffAt ℝ 2 (g i) x)
    (hg0 : ∀ i, ∀ᶠ y in 𝓝 x, 0 ≤ g i y) (hgx : ∀ i, g i x = 0)
    (hχ0 : ∀ i, 0 ≤ χ i x) (hlev : ∀ i, 0 ≤ leviForm (g i) x v) :
    0 ≤ leviForm (fun y => ∑ i ∈ s, χ i y * g i y) x v := by
  rw [leviForm_finsetSum_mul s hχ hg hg0 hgx v]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hχ0 i) (hlev i)

/-- **The kernel of the patched tube is the intersection of the kernels over the
indices that are actually switched on.**  One index with `0 < χ_i x` and a
vanishing summand forces `leviForm (g i) x v = 0`; this is the direction a
partition of unity supplies. -/
theorem leviForm_eq_zero_of_leviForm_finsetSum_mul_eq_zero {ι : Type*} {s : Finset ι}
    {χ g : ι → E → ℝ} {x : E} {v : E}
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x) (hg : ∀ i, ContDiffAt ℝ 2 (g i) x)
    (hg0 : ∀ i, ∀ᶠ y in 𝓝 x, 0 ≤ g i y) (hgx : ∀ i, g i x = 0)
    (hχ0 : ∀ i, 0 ≤ χ i x) (hlev : ∀ i, 0 ≤ leviForm (g i) x v)
    (hzero : leviForm (fun y => ∑ i ∈ s, χ i y * g i y) x v = 0)
    {j : ι} (hj : j ∈ s) (hχj : 0 < χ j x) :
    leviForm (g j) x v = 0 := by
  rw [leviForm_finsetSum_mul s hχ hg hg0 hgx v] at hzero
  have hnn : ∀ i ∈ s, 0 ≤ χ i x * leviForm (g i) x v :=
    fun i _ => mul_nonneg (hχ0 i) (hlev i)
  have hj0 : χ j x * leviForm (g j) x v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero j hj
  exact (mul_eq_zero.mp hj0).resolve_left hχj.ne'

end Levi

/-! ### The chart tube of a holomorphic flattening -/

variable {k n j : ℕ}

/-- The chart tube `r² ∘ F` vanishes to second order at each of its zeros. -/
theorem fderiv_planeDistSq_comp_eq_zero {F : ComplexModel k → ComplexModel n}
    {z : ComplexModel k} (hz : planeDistSq n j (F z) = 0) :
    fderiv ℝ (fun y => planeDistSq n j (F y)) z = 0 :=
  fderiv_eq_zero_of_nonneg_of_eq_zero
    (Filter.Eventually.of_forall fun y => planeDistSq_nonneg (F y)) hz

end

end SGPT.Foundations.Analysis.Pending.TubeSecondOrderVanishing
