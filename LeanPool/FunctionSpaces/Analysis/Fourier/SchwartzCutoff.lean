/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Test functions in the Schwartz space

Let `V` be a real normed space; in the section on cut-offs, `V` is a finite-dimensional real inner
product space, such as `ℝ^d`. A real test function `φ ∈ 𝓓(Ω, ℝ)` on an open set `Ω ⊆ V` is a
complex Schwartz function on `V` (`Rd.testSchwartz`), with the same iterated directional
derivatives `∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}` (`Rd.iteratedLineDerivOp_testSchwartz`) and the same
derivative (`Rd.fderiv_testSchwartz_apply`); conversely a compactly supported complex Schwartz
function with support in `Ω` is `a + i b` for real test functions `a`, `b` on `Ω`
(`Rd.exists_testSchwartz_eq_of_tsupport_subset`).

* **Directional derivatives commute** on Schwartz functions (`SchwartzMap.lineDerivOp_comm`, by
  Mathlib's symmetry of second derivatives) and on test functions
  (`TestFunction.lineDerivOp_comm`).
* **The transpose formula** `∂^v T(φ) = (-1)^k T(∂^v φ)` holds for distributions on `Ω`
  (`Distribution.iteratedLineDerivOp_apply_apply`) and for tempered distributions
  (`TemperedDistribution.iteratedLineDerivOp_apply_apply`); Mathlib differentiates them by
  `∂_w T(φ) = T(-∂_w φ)`.
* **Cut-offs converge in the Schwartz space**: `χ(x/(n+1)) u(x) → u` in `𝓢(V, ℂ)` for the smooth
  cut-off `χ = Rd.cutoff 1 2`, with every seminorm of the difference at most `C/(n+1)` for an
  explicit `C` (`Rd.seminorm_sub_cutoffMul_le`, `Rd.tendsto_cutoffMul`). Hence a tempered
  distribution that vanishes on all test functions is zero (`Rd.eq_zero_of_testSchwartz`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped SchwartzMap LineDeriv Distributions

/-! ### Commuting directional derivatives -/

namespace LineDeriv

variable {V E : Type*} [LineDeriv V E E]

/-- If directional derivatives commute pairwise, `∂_a ∂_b x = ∂_b ∂_a x`, then a directional
derivative commutes with every iterated one: `∂_a ∂^v x = ∂^v ∂_a x`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm_of
    (h : ∀ (a b : V) (x : E), ∂_{a} (∂_{b} x) = ∂_{b} (∂_{a} x)) {k : ℕ} (a : V)
    (v : Fin k → V) (x : E) : ∂_{a} (∂^{v} x) = ∂^{v} (∂_{a} x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, h, ih]

end LineDeriv

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A directional derivative commutes with every iterated directional derivative of a Schwartz
function: `∂_a ∂^v u = ∂^v ∂_a u`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm {k : ℕ} (u : 𝓢(E, F)) (a : E) (v : Fin k → E) :
    ∂_{a} (∂^{v} u) = ∂^{v} (∂_{a} u) :=
  LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of (fun a b x => lineDerivOp_comm x a b) a v u

end SchwartzMap

/-! ### Test functions as Schwartz functions -/

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A real test function `φ` on an open set `Ω` as a complex Schwartz function on `V`,
`x ↦ (φ x : ℂ)`: it is smooth with compact support (Mathlib's
`HasCompactSupport.toSchwartzMap`). -/
noncomputable def testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((φ x : ℝ) : ℂ))
    (φ.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

/-- The values of `Rd.testSchwartz φ` are those of `φ`. -/
@[simp]
theorem testSchwartz_apply {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (x : V) :
    testSchwartz φ x = ((φ x : ℝ) : ℂ) :=
  rfl

/-- The directional derivative of a test function is the derivative of the function:
`∂_a φ(x) = Dφ(x) a`. -/
theorem lineDerivOp_testFunction_apply {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (a x : V) :
    (∂_{a} φ) x = fderiv ℝ φ x a := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ le_top]

/-- Passing to complex values commutes with directional derivatives:
`∂_a (φ : ℂ) = (∂_a φ : ℂ)`. -/
theorem lineDerivOp_testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (a : V) :
    ∂_{a} (testSchwartz φ) = testSchwartz (∂_{a} φ) := by
  ext x
  have hd : HasFDerivAt (fun y => ((φ y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, testSchwartz_apply,
    lineDerivOp_testFunction_apply]
  exact congrArg (fun L : V →L[ℝ] ℂ => L a) hd.fderiv

/-- The derivative of a real test function as a complex function:
`D(φ : ℂ)(x) w = (∂_w φ)(x)`. -/
theorem fderiv_testSchwartz_apply {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (x w : V) :
    fderiv ℝ (testSchwartz φ) x w = (((∂_{w} φ) x : ℝ) : ℂ) := by
  rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv, lineDerivOp_testSchwartz, testSchwartz_apply]

/-- Passing to complex values commutes with iterated directional derivatives:
`∂^v (φ : ℂ) = (∂^v φ : ℂ)`. -/
theorem iteratedLineDerivOp_testSchwartz {Ω : Opens V} {k : ℕ} (φ : 𝓓(Ω, ℝ)) (v : Fin k → V) :
    ∂^{v} (testSchwartz φ) = testSchwartz (∂^{v} φ) := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_testSchwartz]

/-- Two test functions (possibly on different open sets) with the same values have iterated
directional derivatives with the same values. -/
theorem coe_iteratedLineDerivOp_eq {Ω Ω' : Opens V} {k : ℕ} {φ : 𝓓(Ω, ℝ)} {ψ : 𝓓(Ω', ℝ)}
    (h : (φ : V → ℝ) = ψ) (v : Fin k → V) : ((∂^{v} φ : 𝓓(Ω, ℝ)) : V → ℝ) = ∂^{v} ψ := by
  have hs : testSchwartz φ = testSchwartz ψ := by
    ext x
    simp [h]
  have h' := congrArg (fun u : 𝓢(V, ℂ) => (u : V → ℂ)) (congrArg (∂^{v} ·) hs)
  simp only [iteratedLineDerivOp_testSchwartz] at h'
  funext x
  have hx := congrFun h' x
  simp only [testSchwartz_apply, Complex.ofReal_inj] at hx
  exact hx

/-- A smooth compactly supported complex function `w` (given as a Schwartz function) whose support
lies in the open set `Ω` is `Re w + i Im w` with real test functions `Re w`, `Im w` on `Ω`. -/
theorem exists_testSchwartz_eq_of_tsupport_subset {Ω : Opens V} (w : 𝓢(V, ℂ))
    (hw : HasCompactSupport w) (hwΩ : tsupport w ⊆ Ω) :
    ∃ a b : 𝓓(Ω, ℝ), w = testSchwartz a + Complex.I • testSchwartz b := by
  refine ⟨⟨fun x => (w x).re, Complex.reCLM.contDiff.comp (w.smooth ⊤),
    hw.comp_left Complex.zero_re, (tsupport_comp_subset Complex.zero_re _).trans hwΩ⟩,
    ⟨fun x => (w x).im, Complex.imCLM.contDiff.comp (w.smooth ⊤), hw.comp_left Complex.zero_im,
      (tsupport_comp_subset Complex.zero_im _).trans hwΩ⟩, ?_⟩
  ext x
  apply Complex.ext <;> simp <;> rfl

/-- A smooth compactly supported complex function `w` (given as a Schwartz function) is
`Re w + i Im w` with real test functions `Re w`, `Im w` on `V`. -/
theorem exists_testSchwartz_eq (w : 𝓢(V, ℂ)) (hw : HasCompactSupport w) :
    ∃ a b : 𝓓((⊤ : Opens V), ℝ), w = testSchwartz a + Complex.I • testSchwartz b :=
  exists_testSchwartz_eq_of_tsupport_subset w hw (by simp)

end Rd

namespace TestFunction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens V}

/-- Directional derivatives of a test function commute: `∂_a ∂_b φ = ∂_b ∂_a φ`, read off the
complex Schwartz function `Rd.testSchwartz φ` (`SchwartzMap.lineDerivOp_comm`). -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, ℝ)) (a b : V) : ∂_{a} (∂_{b} φ) = ∂_{b} (∂_{a} φ) := by
  have h := SchwartzMap.lineDerivOp_comm (Rd.testSchwartz φ) a b
  simp only [Rd.lineDerivOp_testSchwartz] at h
  ext x
  have hx := congrArg (fun u : 𝓢(V, ℂ) => u x) h
  simp only [Rd.testSchwartz_apply, Complex.ofReal_inj] at hx
  exact hx

/-- A directional derivative commutes with every iterated directional derivative of a test
function: `∂_a ∂^v φ = ∂^v ∂_a φ`. -/
theorem lineDerivOp_iteratedLineDerivOp_comm {k : ℕ} (φ : 𝓓(Ω, ℝ)) (a : V) (v : Fin k → V) :
    ∂_{a} (∂^{v} φ) = ∂^{v} (∂_{a} φ) :=
  LineDeriv.lineDerivOp_iteratedLineDerivOp_comm_of (fun a b x => lineDerivOp_comm x a b) a v φ

end TestFunction

/-! ### Iterated derivatives of distributions -/

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens V}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **transpose formula** for iterated derivatives of a distribution on `Ω`: for directions
`v = (v_0, …, v_{k-1})`, `∂^v T (φ) = (-1)^k T(∂^v φ)` for every test function `φ`. Mathlib
defines `∂_w T (φ) = T(-∂_w φ)` (`Distribution.lineDerivOp_apply_apply`); the order of the
derivatives on `φ` is irrelevant because they commute
(`TestFunction.lineDerivOp_iteratedLineDerivOp_comm`). -/
theorem iteratedLineDerivOp_apply_apply {k : ℕ} (T : 𝓓'(Ω, F)) (φ : 𝓓(Ω, ℝ)) (v : Fin k → V) :
    ∂^{v} T φ = ((-1 : ℝ) ^ k) • T (∂^{v} φ) := by
  induction k generalizing T φ with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left v T, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_succ_left v φ, LineDeriv.iteratedLineDerivOp_neg,
      ← TestFunction.lineDerivOp_iteratedLineDerivOp_comm, map_neg, smul_neg, pow_succ,
      mul_neg_one, neg_smul]

end Distribution

/-! ### Iterated derivatives of tempered distributions -/

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The **transpose formula** for iterated derivatives of a tempered distribution: for directions
`v = (v_0, …, v_{k-1})`, `∂^v T (u) = T((-1)^k ∂^v u)` for every Schwartz function `u`. Mathlib
defines `∂_w T (u) = T(-∂_w u)` (`TemperedDistribution.lineDerivOp_apply_apply`); the order of
the derivatives on `u` is irrelevant because they commute
(`SchwartzMap.lineDerivOp_iteratedLineDerivOp_comm`). -/
theorem iteratedLineDerivOp_apply_apply {k : ℕ} (T : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) (v : Fin k → E) :
    ∂^{v} T u = T (((-1 : ℂ) ^ k) • ∂^{v} u) := by
  induction k generalizing T u with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left v T, lineDerivOp_apply_apply, ih,
      LineDeriv.iteratedLineDerivOp_succ_left v u, LineDeriv.iteratedLineDerivOp_neg,
      ← SchwartzMap.lineDerivOp_iteratedLineDerivOp_comm, pow_succ, mul_neg_one, smul_neg,
      neg_smul]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The distributional derivative `∂^v S_u` of the tempered distribution `S_u` of a Schwartz
function `u` is the tempered distribution `S_{∂^v u}` of its classical derivative `∂^v u` (the
iterated form of Mathlib's `TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq`). -/
theorem iteratedLineDerivOp_toTemperedDistributionCLM_eq {k : ℕ} (u : 𝓢(E, F)) (v : Fin k → E) :
    ∂^{v} (SchwartzMap.toTemperedDistributionCLM E F μ u) =
      SchwartzMap.toTemperedDistributionCLM E F μ (∂^{v} u) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_toTemperedDistributionCLM_eq]

end TemperedDistribution

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Cutting Schwartz functions off -/

/-- The product of the rescaled cut-off `x ↦ χ(x/(n+1))`, `χ = Rd.cutoff 1 2`, with any function
has compact support. This function-level form enters the definition of `Rd.cutoffMul`. -/
theorem hasCompactSupport_cutoff_smul_mul (n : ℕ) (u : V → ℂ) :
    HasCompactSupport fun x => cutoff 1 2 one_pos one_lt_two (((n : ℝ) + 1)⁻¹ • x) * u x := by
  have h := ((hasCompactSupport_cutoff (V := V) one_pos one_lt_two).comp_smul
    (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).mul_right (f' := u)
  exact h

/-- The **cut-off** of a Schwartz function `u` at radius `n + 1`: `x ↦ χ(x/(n+1)) u(x)` with the
smooth cut-off `χ = Rd.cutoff 1 2` (equal to `1` on the closed unit ball and to `0` outside the
ball of radius `2`), a smooth function with compact support. -/
noncomputable def cutoffMul (n : ℕ) (u : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  HasCompactSupport.toSchwartzMap (hasCompactSupport_cutoff_smul_mul n u)
    (((contDiff_cutoff one_pos one_lt_two).comp (contDiff_const_smul _)).mul (u.smooth ⊤))

/-- The values of the cut-off: `cutoffMul n u x = χ(x/(n+1)) u(x)`. -/
theorem cutoffMul_apply (n : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    cutoffMul n u x = cutoff 1 2 one_pos one_lt_two (((n : ℝ) + 1)⁻¹ • x) * u x :=
  rfl

/-- The cut-off of a Schwartz function has compact support. -/
theorem hasCompactSupport_cutoffMul (n : ℕ) (u : 𝓢(V, ℂ)) : HasCompactSupport (cutoffMul n u) :=
  hasCompactSupport_cutoff_smul_mul n u

/-- The cut-off at radius `n + 1` agrees with `u` near every point of the open ball of radius
`n + 1`. -/
theorem cutoffMul_eventuallyEq (u : 𝓢(V, ℂ)) {n : ℕ} {x : V} (hx : ‖x‖ < n + 1) :
    (cutoffMul n u : V → ℂ) =ᶠ[𝓝 x] u := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
  have hy' : ‖((n : ℝ) + 1)⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity), mul_one]
    exact (mem_ball_zero_iff.1 hy).le
  rw [cutoffMul_apply, cutoff_eq_one one_pos one_lt_two hy', one_mul]

/-- For `0 ≤ c ≤ 1` the derivatives of the rescaled cut-off `x ↦ χ(c x)` are bounded by the
Schwartz seminorms `p_{0,i}(χ) = sup ‖D^i χ‖` of `χ = Rd.cutoffSchwartz 1 2`, because
`D^i (χ(c ·))(x) = c^i D^i χ(c x)` (Mathlib's `iteratedFDeriv_comp_const_smul`). -/
theorem norm_iteratedFDeriv_cutoff_comp_smul_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (i : ℕ)
    (x : V) :
    ‖iteratedFDeriv ℝ i (fun y => cutoff 1 2 one_pos one_lt_two (c • y)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) := by
  rw [iteratedFDeriv_comp_const_smul c
    ((contDiff_cutoff one_pos one_lt_two).of_le (mod_cast le_top)), norm_smul, norm_pow,
    Real.norm_of_nonneg hc0]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0 hc1)).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
      (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) i (c • x))

/-- The **Leibniz bound** for the cut-off: `‖D^m (χ_n u)(x)‖ ≤ ∑_{i ≤ m} C(m,i) p_{0,i}(χ)
‖D^(m-i) u(x)‖`, uniformly in `n` (Mathlib's `norm_iteratedFDeriv_mul_le`). -/
theorem norm_iteratedFDeriv_cutoffMul_le (n m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖iteratedFDeriv ℝ m (cutoffMul n u) x‖ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
        ‖iteratedFDeriv ℝ (m - i) u x‖ := by
  have hc0 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hc1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  refine (norm_iteratedFDeriv_mul_le
    ((contDiff_cutoff one_pos one_lt_two).comp (contDiff_const_smul ((n : ℝ) + 1)⁻¹))
    (u.smooth ⊤) x (mod_cast le_top)).trans ?_
  gcongr with i hi
  exact norm_iteratedFDeriv_cutoff_comp_smul_le hc0 hc1 i x

/-- The pointwise bound for the `m`-th derivative of `u - χ_n u`:
`B(x) = ‖D^m u(x)‖ + ∑_{i ≤ m} C(m,i) p_{0,i}(χ) ‖D^(m-i) u(x)‖`, the derivative of `u` plus the
Leibniz bound of `Rd.norm_iteratedFDeriv_cutoffMul_le`, with `χ = Rd.cutoffSchwartz 1 2`. -/
noncomputable def cutoffMulBound (m : ℕ) (u : 𝓢(V, ℂ)) (x : V) : ℝ :=
  ‖iteratedFDeriv ℝ m u x‖ + ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
      ‖iteratedFDeriv ℝ (m - i) u x‖

/-- The derivatives of `u - χ_n u` are bounded by the pointwise bound `Rd.cutoffMulBound`,
uniformly in `n`. -/
theorem norm_iteratedFDeriv_sub_cutoffMul_le (n m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖iteratedFDeriv ℝ m (u - cutoffMul n u) x‖ ≤ cutoffMulBound m u x := by
  have hsub : ((u - cutoffMul n u : 𝓢(V, ℂ)) : V → ℂ) = u - cutoffMul n u := rfl
  rw [hsub, iteratedFDeriv_sub_apply ((u.smooth ⊤).of_le (mod_cast le_top)).contDiffAt
    (((cutoffMul n u).smooth ⊤).of_le (mod_cast le_top)).contDiffAt, cutoffMulBound]
  exact (norm_sub_le _ _).trans (add_le_add_right (norm_iteratedFDeriv_cutoffMul_le n m u x) _)

/-- All derivatives of `u - χ_n u` vanish on the open ball of radius `n + 1`, where the cut-off
is `1`. -/
theorem iteratedFDeriv_sub_cutoffMul_eq_zero (u : 𝓢(V, ℂ)) {n : ℕ} {x : V} (hx : ‖x‖ < n + 1)
    (m : ℕ) : iteratedFDeriv ℝ m (u - cutoffMul n u) x = 0 := by
  have h : ((u - cutoffMul n u : 𝓢(V, ℂ)) : V → ℂ) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [cutoffMul_eventuallyEq u hx] with y hy
    simp [hy]
  rw [(h.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply]

/-- The constant of the cut-off estimate `Rd.seminorm_sub_cutoffMul_le`:
`p_{k+1,m}(u) + ∑_{i ≤ m} C(m,i) p_{0,i}(χ) p_{k+1,m-i}(u)` in the Schwartz seminorms of `u` and
of the cut-off `χ = Rd.cutoffSchwartz 1 2`. -/
noncomputable def cutoffMulConst (k m : ℕ) (u : 𝓢(V, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ (k + 1) m u + ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
      SchwartzMap.seminorm ℝ (k + 1) (m - i) u

/-- The constant of the cut-off estimate is nonnegative. -/
theorem cutoffMulConst_nonneg (k m : ℕ) (u : 𝓢(V, ℂ)) : 0 ≤ cutoffMulConst k m u := by
  unfold cutoffMulConst
  positivity

/-- The pointwise form of the cut-off estimate: `‖x‖^(k+1) B(x) ≤ Rd.cutoffMulConst k m u` for
the pointwise bound `B = Rd.cutoffMulBound m u`. -/
theorem norm_pow_succ_mul_cutoffMulBound_le (k m : ℕ) (u : 𝓢(V, ℂ)) (x : V) :
    ‖x‖ ^ (k + 1) * cutoffMulBound m u x ≤ cutoffMulConst k m u := by
  rw [cutoffMulBound, mul_add, Finset.mul_sum, cutoffMulConst]
  refine add_le_add (SchwartzMap.le_seminorm ℝ (k + 1) m u x) (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_comm, mul_assoc]
  gcongr
  rw [mul_comm]
  exact SchwartzMap.le_seminorm ℝ (k + 1) (m - i) u x

/-- **The cut-off estimate**: the Schwartz seminorm `p_{k,m}(u - χ_n u)` is at most
`Rd.cutoffMulConst k m u / (n + 1)`, because `u - χ_n u` vanishes on the ball of radius `n + 1`
and `‖x‖^k ≤ ‖x‖^(k+1)/(n+1)` outside it. -/
theorem seminorm_sub_cutoffMul_le (k m n : ℕ) (u : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℝ k m (u - cutoffMul n u) ≤ cutoffMulConst k m u / ((n : ℝ) + 1) := by
  have hC := cutoffMulConst_nonneg k m u
  refine SchwartzMap.seminorm_le_bound ℝ k m _ (by positivity) fun x => ?_
  rcases lt_or_ge ‖x‖ (n + 1) with hx | hx
  · rw [iteratedFDeriv_sub_cutoffMul_eq_zero u hx, norm_zero, mul_zero]
    positivity
  rw [le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (u - cutoffMul n u) x‖ * ((n : ℝ) + 1)
      ≤ ‖x‖ ^ k * cutoffMulBound m u x * ‖x‖ := by
        have hB := norm_iteratedFDeriv_sub_cutoffMul_le n m u x
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) hx (by positivity)
          (mul_nonneg (by positivity) ((norm_nonneg _).trans hB))
    _ = ‖x‖ ^ (k + 1) * cutoffMulBound m u x := by ring
    _ ≤ cutoffMulConst k m u := norm_pow_succ_mul_cutoffMulBound_le k m u x

/-- **The cut-offs converge in the Schwartz space**: `χ_n u → u` in `𝓢(V, ℂ)`, since every
Schwartz seminorm of `u - χ_n u` is `O(1/(n+1))` (`Rd.seminorm_sub_cutoffMul_le`, Mathlib's
`schwartz_withSeminorms`). Hence smooth compactly supported functions are dense in
`𝓢(V, ℂ)`. -/
theorem tendsto_cutoffMul (u : 𝓢(V, ℂ)) :
    Tendsto (fun n : ℕ => cutoffMul n u) atTop (𝓝 u) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ u]
  rintro ⟨k, m⟩ ε hε
  have h0 : Tendsto (fun n : ℕ => cutoffMulConst k m u / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with n hn
  rw [SchwartzMap.schwartzSeminormFamily_apply, map_sub_rev]
  exact (seminorm_sub_cutoffMul_le k m n u).trans_lt hn

/-- **Test functions determine tempered distributions**: a tempered distribution on `V` that
vanishes on all real test functions is zero. The cut-offs `Rd.cutoffMul n u` of a Schwartz
function `u` are combinations of test functions (`Rd.exists_testSchwartz_eq`) and converge to `u`
in `𝓢(V, ℂ)` (`Rd.tendsto_cutoffMul`). -/
theorem eq_zero_of_testSchwartz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : 𝓢'(V, F)} (h : ∀ φ : 𝓓((⊤ : Opens V), ℝ), T (testSchwartz φ) = 0) : T = 0 := by
  ext1 u
  have hn : ∀ n : ℕ, T (cutoffMul n u) = 0 := fun n => by
    obtain ⟨a, b, hab⟩ := exists_testSchwartz_eq (cutoffMul n u) (hasCompactSupport_cutoffMul n u)
    rw [hab, map_add, map_smul, h, h, smul_zero, add_zero]
  have ht : Tendsto (fun n : ℕ => T (cutoffMul n u)) atTop (𝓝 (T u)) :=
    ((map_continuous T).tendsto u).comp (tendsto_cutoffMul u)
  simp only [hn] at ht
  simpa using tendsto_nhds_unique ht tendsto_const_nhds

end Rd
