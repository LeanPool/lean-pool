/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SemiconcaveHessianBound
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SemiconcaveSecondDifference
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# `C^{1,1}` regularity and almost-everywhere second-order expansions

Let `F j` be `C²` functions on `ℂⁿ` converging pointwise on a ball `B` to `u`, with uniformly
bounded values and uniformly bounded second derivatives `‖D²(F j)‖ ≤ M` on `B`.  Then

* `u` is differentiable on `B` and `|u y - u x - Du x (y - x)| ≤ M ‖y - x‖²` there;
* consequently `Du` is Lipschitz on a smaller ball;
* by Rademacher's theorem `Du` is differentiable almost everywhere, and at every such point
  `u` admits a second-order (Peano) expansion with the symmetric bilinear form
  `A = D(Du)(x)`.

The limit argument starts with smooth approximants and a Hessian bound, as in the final
step of the proof of [Błocki's Proposition 2.3.3](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=51).
It also supplies the almost-everywhere Taylor expansion used in the proof of Theorem 2.3.1.
-/

@[expose] public section

noncomputable section

open Set Filter Metric Asymptotics MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- A second-order Peano expansion of `u` at `x` with linear part `L` and quadratic part `A`. -/
def HasPeanoExpansionAt (u : ComplexModel n → ℝ) (x : ComplexModel n)
    (L : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ComplexModel n),
    |u (x + h) - u x - L h - A h h / 2| ≤ ε * ‖h‖ ^ 2

/-- A functional bounded on a ball has controlled operator norm. -/
theorem opNorm_le_of_le_on_ball {T : ComplexModel n →L[ℝ] ℝ} {d B : ℝ} (hd : 0 < d)
    (hB : 0 ≤ B) (h : ∀ x : ComplexModel n, ‖x‖ ≤ d → |T x| ≤ B) : ‖T‖ ≤ 2 * B / d := by
  refine ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hd (by positivity)
    (by norm_num) fun x hx1 hx2 ↦ ?_
  have hx1' : d / 2 ≤ ‖x‖ := by simpa using hx1
  have := h x hx2.le
  rw [Real.norm_eq_abs]
  have : 2 * B / d * (d / 2) ≤ 2 * B / d * ‖x‖ := by
    refine mul_le_mul_of_nonneg_left hx1' (by positivity)
  have hBd : 2 * B / d * (d / 2) = B := by field_simp
  rw [hBd] at this
  linarith [h x hx2.le]

/-- Second-order Taylor bound from a bound on the second derivative.  This is
the `U = univ` case of
`Pending.SemiconcaveSecondDifference.abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on`. -/
theorem abs_sub_fderiv_le_of_norm_second_le {f : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f)
    {s : Set (ComplexModel n)} (hs : Convex ℝ s) {M : ℝ}
    (hM : ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {x y : ComplexModel n} (hx : x ∈ s)
    (hy : y ∈ s) : |f y - f x - fderiv ℝ f x (y - x)| ≤ M * ‖y - x‖ ^ 2 :=
  abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on isOpen_univ hf.contDiffOn hs
    (subset_univ s) hM hx hy

/-- The limit of `C²` functions with uniformly bounded second derivatives is differentiable,
with the same second-order Taylor bound. -/
theorem differentiableAt_and_taylor_of_tendsto {c : ComplexModel n} {ρ M C : ℝ}
    (hM0 : 0 ≤ M) {F : ℕ → ComplexModel n → ℝ} {u : ComplexModel n → ℝ}
    (hF : ∀ j, ContDiff ℝ 2 (F j))
    (hM : ∀ j, ∀ y ∈ ball c ρ, ‖fderiv ℝ (fderiv ℝ (F j)) y‖ ≤ M)
    (hC : ∀ j, ∀ y ∈ ball c ρ, |F j y| ≤ C)
    (hconv : ∀ y ∈ ball c ρ, Tendsto (fun j ↦ F j y) atTop (𝓝 (u y))) :
    ∀ x ∈ ball c ρ, DifferentiableAt ℝ u x ∧
      ∀ y ∈ ball c ρ, |u y - u x - fderiv ℝ u x (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
  have _ : ProperSpace (ComplexModel n →L[ℝ] ℝ) := FiniteDimensional.proper ℝ _
  have hball : Convex ℝ (ball c ρ) := convex_ball c ρ
  -- Taylor bound for each `F j`
  have htaylor : ∀ j, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      |F j y - F j x - fderiv ℝ (F j) x (y - x)| ≤ M * ‖y - x‖ ^ 2 := fun j x hx y hy ↦
    abs_sub_fderiv_le_of_norm_second_le (hF j) hball (hM j) hx hy
  -- a limit functional at each point
  have hkey : ∀ x ∈ ball c ρ, ∃ T : ComplexModel n →L[ℝ] ℝ,
      ∀ y ∈ ball c ρ, |u y - u x - T (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
    intro x hx
    obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, ∀ h : ComplexModel n, ‖h‖ ≤ r → x + h ∈ ball c ρ := by
      refine ⟨(ρ - dist x c) / 2, by simp only [mem_ball] at hx; linarith, fun h hh ↦ ?_⟩
      simp only [mem_ball] at hx ⊢
      calc dist (x + h) c ≤ dist (x + h) x + dist x c := dist_triangle _ _ _
        _ = ‖h‖ + dist x c := by simp [dist_eq_norm]
        _ ≤ (ρ - dist x c) / 2 + dist x c := by linarith
        _ < ρ := by linarith
    have hbd : ∀ j, ‖fderiv ℝ (F j) x‖ ≤ 2 * (2 * |C| + M * r ^ 2) / r := by
      intro j
      refine opNorm_le_of_le_on_ball hr (by positivity) fun h hh ↦ ?_
      have hxh : x + h ∈ ball c ρ := hrsub h hh
      have h1 := htaylor j x hx (x + h) hxh
      simp only [add_sub_cancel_left] at h1
      have h2 : |F j (x + h)| ≤ C := hC j _ hxh
      have h3 : |F j x| ≤ C := hC j _ hx
      have h4 : M * ‖h‖ ^ 2 ≤ M * r ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hM0
      have h2' : |F j (x + h)| ≤ |C| := le_trans h2 (le_abs_self C)
      have h3' : |F j x| ≤ |C| := le_trans h3 (le_abs_self C)
      have := abs_le.mp h1
      have := abs_le.mp h2'
      have := abs_le.mp h3'
      rw [abs_le]
      constructor <;> linarith
    obtain ⟨T, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded
      (s := closedBall (0 : ComplexModel n →L[ℝ] ℝ) (2 * (2 * |C| + M * r ^ 2) / r))
      isBounded_closedBall (x := fun j ↦ fderiv ℝ (F j) x)
      (fun j ↦ by simpa [mem_closedBall_zero_iff] using hbd j)
    refine ⟨T, fun y hy ↦ ?_⟩
    have hlim : Tendsto (fun k ↦ F (φ k) y - F (φ k) x - fderiv ℝ (F (φ k)) x (y - x)) atTop
        (𝓝 (u y - u x - T (y - x))) := by
      refine (((hconv y hy).comp hφ.tendsto_atTop).sub
        ((hconv x hx).comp hφ.tendsto_atTop)).sub ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous.tendsto T).comp hT
    have := le_of_tendsto (hlim.abs) (Eventually.of_forall fun k ↦ htaylor (φ k) x hx y hy)
    exact this
  intro x hx
  obtain ⟨T, hT⟩ := hkey x hx
  have hdiff : HasFDerivAt u T x := by
    rw [hasFDerivAt_iff_isLittleO]
    refine (isLittleO_iff).2 fun {ε} hε ↦ ?_
    have hnb : ball c ρ ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    have hsmall : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ ε / (M + 1) := by
      have hcont : Tendsto (fun y : ComplexModel n ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
        have : Continuous fun y : ComplexModel n ↦ ‖y - x‖ :=
          continuous_norm.comp (continuous_id.sub continuous_const)
        simpa using this.tendsto' x 0 (by simp)
      exact hcont.eventually_le_const (by positivity)
    filter_upwards [hnb, hsmall] with y hy hy2
    have h1 := hT y hy
    have hnn : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    have hstep : M * ‖y - x‖ ≤ ε := by
      have h2 : M * ‖y - x‖ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hy2 hM0
      have h3 : M * (ε / (M + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hM1]
        nlinarith
      linarith
    simp only [Real.norm_eq_abs]
    calc |u y - u x - T (y - x)| ≤ M * ‖y - x‖ ^ 2 := h1
      _ = (M * ‖y - x‖) * ‖y - x‖ := by ring
      _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hstep hnn
  refine ⟨hdiff.differentiableAt, fun y hy ↦ ?_⟩
  rw [hdiff.fderiv]
  exact hT y hy

/-- The second-order Taylor bound makes the derivative Lipschitz on a smaller ball. -/
theorem norm_fderiv_sub_le_of_taylor {u : ComplexModel n → ℝ} {c : ComplexModel n} {ρ M : ℝ}
    (hM0 : 0 ≤ M)
    (hT : ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ, |u y - u x - fderiv ℝ u x (y - x)| ≤ M * ‖y - x‖ ^ 2)
    {x y : ComplexModel n} (hx : x ∈ ball c (ρ / 4)) (hy : y ∈ ball c (ρ / 4)) :
    ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ 12 * M * ‖x - y‖ := by
  have hxρ : x ∈ ball c ρ := by
    have h1 := mem_ball.mp hx
    have h2 : (0 : ℝ) ≤ dist x c := dist_nonneg
    exact mem_ball.mpr (by linarith)
  have hyρ : y ∈ ball c ρ := by
    have h1 := mem_ball.mp hy
    have h2 : (0 : ℝ) ≤ dist y c := dist_nonneg
    exact mem_ball.mpr (by linarith)
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hd | hd
  · have hxy : x = y := by
      have : ‖x - y‖ = 0 := hd.symm
      simpa [sub_eq_zero] using this
    subst hxy
    simp
  set d := ‖x - y‖ with hd_def
  have hdxy : d < ρ / 2 := by
    have h1 := mem_ball.mp hx
    have h2 := mem_ball.mp hy
    have : d = dist x y := by rw [hd_def, dist_eq_norm]
    rw [this]
    calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
      _ = dist x c + dist y c := by rw [dist_comm c y]
      _ < ρ / 4 + ρ / 4 := add_lt_add h1 h2
      _ = ρ / 2 := by ring
  have hmem : ∀ h : ComplexModel n, ‖h‖ ≤ d → x + h ∈ ball c ρ := by
    intro h hh
    have h1 := mem_ball.mp hx
    simp only [mem_ball]
    calc dist (x + h) c ≤ dist (x + h) x + dist x c := dist_triangle _ _ _
      _ = ‖h‖ + dist x c := by simp [dist_eq_norm]
      _ < ρ / 2 + ρ / 4 := add_lt_add_of_le_of_lt (le_trans hh hdxy.le) h1
      _ < ρ := by linarith
  refine le_trans (opNorm_le_of_le_on_ball (B := 6 * M * d ^ 2) hd (by positivity)
    fun h hh ↦ ?_) ?_
  · have hxh : x + h ∈ ball c ρ := hmem h hh
    have e1 := hT x hxρ (x + h) hxh
    have e2 := hT y hyρ (x + h) hxh
    have e3 := hT y hyρ x hxρ
    simp only [add_sub_cancel_left] at e1
    have hid : (fderiv ℝ u y - fderiv ℝ u x) h =
        (u (x + h) - u x - fderiv ℝ u x h) -
          (u (x + h) - u y - fderiv ℝ u y (x + h - y)) +
          (u x - u y - fderiv ℝ u y (x - y)) := by
      have : fderiv ℝ u y (x + h - y) - fderiv ℝ u y (x - y) = fderiv ℝ u y h := by
        rw [← map_sub]
        congr 1
        abel
      simp only [_root_.sub_apply]
      linarith [this]
    have hb1 : |u (x + h) - u x - fderiv ℝ u x h| ≤ M * d ^ 2 := by
      refine le_trans e1 ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hM0
    have hnorm2 : ‖x + h - y‖ ≤ 2 * d := by
      calc ‖x + h - y‖ = ‖(x - y) + h‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖h‖ := norm_add_le _ _
        _ ≤ d + d := by linarith
        _ = 2 * d := by ring
    have hb2 : |u (x + h) - u y - fderiv ℝ u y (x + h - y)| ≤ M * (2 * d) ^ 2 := by
      refine le_trans e2 ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm2 2) hM0
    have hb3 : |u x - u y - fderiv ℝ u y (x - y)| ≤ M * d ^ 2 := e3
    rw [hid]
    have := abs_le.mp hb1
    have := abs_le.mp hb2
    have := abs_le.mp hb3
    rw [abs_le]
    constructor <;> nlinarith
  · rw [div_le_iff₀ hd]
    have : d = ‖x - y‖ := hd_def
    nlinarith [hd, hM0]

/-- **Almost-everywhere second-order expansion.**  At almost every point of the smaller ball,
the limit `u` has a Peano expansion with a symmetric quadratic part. -/
theorem ae_exists_hasPeanoExpansion {c : ComplexModel n} {ρ M C : ℝ} (hM0 : 0 ≤ M)
    {F : ℕ → ComplexModel n → ℝ} {u : ComplexModel n → ℝ}
    (hF : ∀ j, ContDiff ℝ 2 (F j))
    (hM : ∀ j, ∀ y ∈ ball c ρ, ‖fderiv ℝ (fderiv ℝ (F j)) y‖ ≤ M)
    (hC : ∀ j, ∀ y ∈ ball c ρ, |F j y| ≤ C)
    (hconv : ∀ y ∈ ball c ρ, Tendsto (fun j ↦ F j y) atTop (𝓝 (u y))) :
    ∀ᵐ x : ComplexModel n, x ∈ ball c (ρ / 4) →
      ∃ A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ, (∀ v w, A v w = A w v) ∧
        HasPeanoExpansionAt u x (fderiv ℝ u x) A := by
  obtain hdt := differentiableAt_and_taylor_of_tendsto hM0 hF hM hC hconv
  have hdiff : ∀ x ∈ ball c ρ, DifferentiableAt ℝ u x := fun x hx ↦ (hdt x hx).1
  have hT : ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      |u y - u x - fderiv ℝ u x (y - x)| ≤ M * ‖y - x‖ ^ 2 := fun x hx ↦ (hdt x hx).2
  have hlip : LipschitzOnWith (Real.toNNReal (12 * M)) (fderiv ℝ u) (ball c (ρ / 4)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), norm_sub_rev x y]
    exact norm_fderiv_sub_le_of_taylor hM0 hT hy hx
  filter_upwards [hlip.ae_differentiableWithinAt_of_mem] with x hx hxball
  have hxρ : x ∈ ball c ρ := by
    have h1 := mem_ball.mp hxball
    have h2 : (0 : ℝ) ≤ dist x c := dist_nonneg
    exact mem_ball.mpr (by linarith)
  have hdA : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hx hxball).differentiableAt (isOpen_ball.mem_nhds hxball)
  set A := fderiv ℝ (fderiv ℝ u) x with hA_def
  have hA : HasFDerivAt (fderiv ℝ u) A x := hdA.hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 x, HasFDerivAt u (fderiv ℝ u y) y := by
    filter_upwards [isOpen_ball.mem_nhds hxρ] with y hy using (hdiff y hy).hasFDerivAt
  have hsymm : ∀ v w, A v w = A w v :=
    second_derivative_symmetric_of_eventually hev hA
  refine ⟨A, hsymm, ?_⟩
  intro ε hε
  -- the derivative of `u` is approximated by `A` near `x`
  have hlittle : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ u y - fderiv ℝ u x - A (y - x)‖ ≤ ε * ‖y - x‖ := by
    have := (hasFDerivAt_iff_isLittleO.mp hA)
    have h2 := (isLittleO_iff.mp this) hε
    filter_upwards [h2] with y hy
    simpa using hy
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.mp (hlittle.and (isOpen_ball.mem_nhds
    hxρ))
  have hballmem : ∀ h : ComplexModel n, ‖h‖ < δ → x + h ∈ ball x δ := by
    intro h hh
    simpa [dist_eq_norm] using hh
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexModel n) hδ] with h hh
  have hhnorm : ‖h‖ < δ := by simpa using hh
  rcases eq_or_lt_of_le (norm_nonneg h) with h0 | h0
  · have : h = 0 := by simpa [eq_comm] using norm_eq_zero.mp h0.symm
    subst this
    simp
  -- mean value on the closed ball of radius ‖h‖
  set φ : ComplexModel n → ℝ := fun z ↦ u z - fderiv ℝ u x z - 2⁻¹ * (A (z - x) (z - x))
    with hφ_def
  have hquad : ∀ y : ComplexModel n,
      HasFDerivAt (fun z : ComplexModel n ↦ A (z - x) (z - x))
        (A (y - x) + A.flip (y - x)) y := by
    intro y
    have h1 : HasFDerivAt (fun z : ComplexModel n ↦ z - x)
        (ContinuousLinearMap.id ℝ (ComplexModel n)) y := (hasFDerivAt_id y).sub_const x
    have h2 : HasFDerivAt (fun z : ComplexModel n ↦ A (z - x))
        (A.comp (ContinuousLinearMap.id ℝ (ComplexModel n))) y := A.hasFDerivAt.comp y h1
    have h3 := h2.clm_apply h1
    simpa using h3
  have hφ' : ∀ y ∈ closedBall x ‖h‖,
      HasFDerivWithinAt φ (fderiv ℝ u y - fderiv ℝ u x - A (y - x)) (closedBall x ‖h‖) y := by
    intro y hy
    have hyball : y ∈ ball x δ := by
      have : dist y x ≤ ‖h‖ := by simpa [dist_eq_norm] using hy
      exact mem_ball.mpr (lt_of_le_of_lt this hhnorm)
    have hyρ : y ∈ ball c ρ := (hδball y hyball).2
    have hdu : HasFDerivAt u (fderiv ℝ u y) y := (hdiff y hyρ).hasFDerivAt
    have hqq : HasFDerivAt (fun z : ComplexModel n ↦ 2⁻¹ * (A (z - x) (z - x)))
        (A (y - x)) y := by
      have hq := (hquad y).const_mul (2⁻¹ : ℝ)
      have hfl : A.flip (y - x) = A (y - x) := by
        ext w
        simp [ContinuousLinearMap.flip_apply, hsymm]
      rw [hfl] at hq
      have hhalf : (2⁻¹ : ℝ) • (A (y - x) + A (y - x)) = A (y - x) := by
        ext w
        simp
        ring
      rwa [hhalf] at hq
    have : HasFDerivAt φ (fderiv ℝ u y - fderiv ℝ u x - A (y - x)) y :=
      (hdu.sub (fderiv ℝ u x).hasFDerivAt).sub hqq
    exact this.hasFDerivWithinAt
  have hbound : ∀ y ∈ closedBall x ‖h‖,
      ‖fderiv ℝ u y - fderiv ℝ u x - A (y - x)‖ ≤ ε * ‖h‖ := by
    intro y hy
    have hyball : y ∈ ball x δ := by
      have : dist y x ≤ ‖h‖ := by simpa [dist_eq_norm] using hy
      exact mem_ball.mpr (lt_of_le_of_lt this hhnorm)
    have h1 := (hδball y hyball).1
    have h2 : ‖y - x‖ ≤ ‖h‖ := by simpa [dist_eq_norm] using hy
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hε.le)
  have hmv := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hφ' hbound (mem_closedBall_self (norm_nonneg h))
    (by simp [dist_eq_norm] : x + h ∈ closedBall x ‖h‖)
  have hval : φ (x + h) - φ x = u (x + h) - u x - fderiv ℝ u x h - A h h / 2 := by
    simp only [hφ_def, map_add, add_sub_cancel_left, sub_self, map_zero]
    simp
    ring
  rw [hval, Real.norm_eq_abs] at hmv
  calc |u (x + h) - u x - fderiv ℝ u x h - A h h / 2| ≤ ε * ‖h‖ * ‖x + h - x‖ := hmv
    _ = ε * ‖h‖ ^ 2 := by simp [add_sub_cancel_left]; ring

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
