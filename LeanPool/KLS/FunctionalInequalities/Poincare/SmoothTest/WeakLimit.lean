/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Poincaré bounds under weak limits

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 2, p. 5: the Poincaré bound of a weakly
convergent family of laws passes to the limit. For a fixed compactly supported smooth test the
integrals of `f`, `f²` and `‖∇f‖²` are integrals of bounded continuous functions, so the inequality
`Var f ≤ C ∫‖∇f‖²` survives weak convergence with converging constants
(`variance_le_mul_energy_of_tendsto`). The extension from compactly supported tests to all
admissible tests and the transfer to the literature constant of a log-concave limit are added as
they
are proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Poincare.SmoothTest

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Weak passage of the Poincaré inequality on a compactly supported smooth test**: if `μ_j → μ`
weakly, `C_j → C` and `Var_{μ_j} f ≤ C_j ∫‖∇f‖² dμ_j`, then `Var_μ f ≤ C ∫‖∇f‖² dμ`. -/
theorem variance_le_mul_energy_of_tendsto {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto μs atTop (𝓝 μ)) {Cseq : ℕ → ℝ} {C : ℝ} (hC : Tendsto Cseq atTop (𝓝 C))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h : ∀ j, variance f (μs j : Measure E) ≤ Cseq j * energy (μs j : Measure E) f) :
    variance f (μ : Measure E) ≤ C * energy (μ : Measure E) f := by
      obtain ⟨Bf, hBf⟩ := hc.exists_bound_of_continuous hf.continuous
      let gf : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous Bf hBf
      have hfc : HasCompactSupport (fun x => f x ^ 2) := by
        apply hc.mono
        intro x hx
        by_contra hfx
        have hzero : f x = 0 := by
          simpa [Function.mem_support] using hfx
        exact hx (by simp [hzero])
      have hfs : Continuous (fun x => f x ^ 2) := by
        convert hf.continuous.pow 2 using 1
      obtain ⟨Bf2, hBf2⟩ := hfc.exists_bound_of_continuous hfs
      let gf2 : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup
          (fun x => f x ^ 2) hfs Bf2 hBf2
      have hfd : Continuous (fderiv ℝ f) :=
        hf.continuous_fderiv (by simp)
      have hgradc : HasCompactSupport (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
        apply (hc.fderiv ℝ).mono
        intro x hx
        by_contra hdf
        have hzero : fderiv ℝ f x = 0 := by
          simpa [Function.mem_support] using hdf
        exact hx (by simp [hzero])
      have hgrads : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
        convert hfd.norm.pow 2 using 1
      obtain ⟨Bg, hBg⟩ := hgradc.exists_bound_of_continuous hgrads
      let gg : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup
          (fun x => ‖fderiv ℝ f x‖ ^ 2) hgrads Bg hBg
      have hfi :
          Tendsto (fun j => ∫ x, f x ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
        simpa [gf] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gf)
      have hf2i :
          Tendsto (fun j => ∫ x, f x ^ 2 ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, f x ^ 2 ∂(μ : Measure E))) := by
        simpa [gf2] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gf2)
      have hgi :
          Tendsto (fun j => ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E))) := by
        simpa [gg] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gg)
      have hmem (ν : ProbabilityMeasure E) :
          MemLp f 2 (ν : Measure E) := by
        apply MemLp.of_bound (μ := (ν : Measure E)) (p := (2 : ENNReal))
        · exact gf.continuous.aestronglyMeasurable
        · filter_upwards [] with x
          exact hBf x
      have hvar (ν : ProbabilityMeasure E) :
          variance f (ν : Measure E) =
            (∫ x, f x ^ 2 ∂(ν : Measure E)) -
              (∫ x, f x ∂(ν : Measure E)) ^ 2 := by
        exact variance_eq_sub (hmem ν)
      have hleft :
          Tendsto
            (fun j =>
              (∫ x, f x ^ 2 ∂(μs j : Measure E)) -
                (∫ x, f x ∂(μs j : Measure E)) ^ 2)
            atTop
            (𝓝
              ((∫ x, f x ^ 2 ∂(μ : Measure E)) -
                (∫ x, f x ∂(μ : Measure E)) ^ 2)) := by
        exact hf2i.sub (hfi.pow 2)
      have hright :
          Tendsto
            (fun j =>
              Cseq j * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E))
            atTop
            (𝓝
              (C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E))) := by
        exact hC.mul hgi
      have h' :
          ∀ j, variance f (μs j : Measure E) ≤
            Cseq j * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E) := by
        intro j
        rw [← energy_eq_fderiv]
        exact h j
      have hlimineq :
          (∫ x, f x ^ 2 ∂(μ : Measure E)) -
              (∫ x, f x ∂(μ : Measure E)) ^ 2
            ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E) := by
        apply le_of_tendsto_of_tendsto' hleft hright
        intro j
        rw [← hvar (μs j)]
        exact h' j
      calc
        variance f (μ : Measure E) =
            (∫ x, f x ^ 2 ∂(μ : Measure E)) -
              (∫ x, f x ∂(μ : Measure E)) ^ 2 := hvar μ
        _ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E) := hlimineq
        _ = C * energy (μ : Measure E) f := by
          rw [energy_eq_fderiv]

section Cutoff

variable [FiniteDimensional ℝ E]

/-- A `C^∞` function with compact support is an admissible test for every finite measure. -/
theorem Admissible.of_contDiff_hasCompactSupport {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Admissible μ f := by
    refine
      { smooth' := hf
        memLp_two := ?_
        energy_integrable := ?_ }
    · obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf.continuous
      exact
        MemLp.of_bound hf.continuous.aestronglyMeasurable C
          (Filter.Eventually.of_forall hC)
    · have hgrad : Continuous (gradient f) := by
        change
          Continuous
            (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
        exact
          (InnerProductSpace.toDual ℝ E).symm.continuous.comp
            (hf.continuous_fderiv (by simp))
      have henergy : Continuous (fun x => ‖gradient f x‖ ^ 2) :=
        hgrad.norm.pow 2
      have hfd : HasCompactSupport (fun x => fderiv ℝ f x) :=
        hc.fderiv ℝ
      have hsub :
          Function.support (fun x => ‖gradient f x‖ ^ 2) ⊆
            Function.support (fun x => fderiv ℝ f x) := by
        intro x hx hfx
        apply hx
        simp [gradient, hfx]
      exact henergy.integrable_of_hasCompactSupport (hfd.mono hsub)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma scaled_eq_one_of_ceil_le (x : E) (n : ℕ)
    (hR : 0 < (n : ℝ) + 1) (hn : Nat.ceil ‖x‖ ≤ n) :
    Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x = 1 := by
  apply Energy.Euclidean.LipschitzApproximation.scaled_eq_one hR
  calc
    ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The first and second integrals of the cutoffs `f χ_{n+1}` converge to those of `f`:
`∫ χ_{n+1} f → ∫ f` and `∫ (χ_{n+1} f)² → ∫ f²` (no `L²`-norm convergence is exported). -/
theorem tendsto_integral_scaled_mul {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    Tendsto
        (fun n : ℕ =>
          ∫ x, Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x ∂μ)
        atTop (𝓝 (∫ x, f x ∂μ)) ∧
      Tendsto
        (fun n : ℕ =>
          ∫ x, (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2 ∂μ)
        atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
  have hmeas₁ :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) μ := by
    intro n
    have hχ :
      AEStronglyMeasurable (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) μ :=
      (Energy.Euclidean.LipschitzApproximation.contDiff_scaled
          ((n : ℝ) + 1)).continuous.aestronglyMeasurable
    exact hχ.mul hf.aestronglyMeasurable
  have hbound₁ :
    ∀ n : ℕ,
      ∀ᵐ x ∂μ, ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ ≤ ‖f x‖ := by
    intro n
    filter_upwards [] with x
    have hχ₀ : 0 ≤ Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x :=
      Energy.Euclidean.LipschitzApproximation.scaled_nonneg ((n : ℝ) + 1) x
    have hχ₁ : Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x ≤ 1 :=
      Energy.Euclidean.LipschitzApproximation.scaled_le_one ((n : ℝ) + 1) x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hχ₀]
    exact mul_le_of_le_one_left (norm_nonneg _) hχ₁
  have hlim₁ :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun n : ℕ => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x)
        atTop (𝓝 (f x)) := by
    filter_upwards [] with x
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
    intro n hn
    have hR : 0 < (n : ℝ) + 1 := by positivity
    rw [scaled_eq_one_of_ceil_le x n hR hn]
    simp
  have hfirst :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun x => ‖f x‖)
      (F_measurable := hmeas₁) (bound_integrable := (hf.integrable one_le_two).norm) (h_bound :=
      hbound₁) (h_lim := hlim₁)
  have hmeas₂ :
    ∀ n : ℕ,
      AEStronglyMeasurable
        (fun x => (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2)
        μ := by
    intro n
    have hχ :
      AEStronglyMeasurable (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)) μ :=
      (Energy.Euclidean.LipschitzApproximation.contDiff_scaled
          ((n : ℝ) + 1)).continuous.aestronglyMeasurable
    exact (hχ.mul hf.aestronglyMeasurable).pow 2
  have hbound₂ :
    ∀ n : ℕ,
      ∀ᵐ x ∂μ,
        ‖(Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2‖ ≤
          f x ^ 2 := by
    intro n
    filter_upwards [] with x
    have hχ₀ : 0 ≤ Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x :=
      Energy.Euclidean.LipschitzApproximation.scaled_nonneg ((n : ℝ) + 1) x
    have hχ₁ : Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x ≤ 1 :=
      Energy.Euclidean.LipschitzApproximation.scaled_le_one ((n : ℝ) + 1) x
    have hnorm :
      ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ ≤ ‖f x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hχ₀]
      exact mul_le_of_le_one_left (norm_nonneg _) hχ₁
    rw [norm_pow]
    calc
      ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
        calc
          ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ ^ 2 =
              ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ *
                ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ := by
            ring
          _ ≤ ‖f x‖ * ‖Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x‖ :=
            mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
          _ ≤ ‖f x‖ * ‖f x‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
          _ = ‖f x‖ ^ 2 := by ring
      _ = f x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hlim₂ :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun n : ℕ =>
          (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x) ^ 2)
        atTop (𝓝 (f x ^ 2)) := by
    filter_upwards [] with x
    refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
    intro n hn
    have hR : 0 < (n : ℝ) + 1 := by positivity
    rw [scaled_eq_one_of_ceil_le x n hR hn]
    simp
  have hsecond :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun x => f x ^ 2)
      (F_measurable := hmeas₂)
      (bound_integrable := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf)
      (h_bound := hbound₂) (h_lim := hlim₂)
  exact ⟨hfirst, hsecond⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Inside the ball the cutoff does not change the gradient. -/
theorem norm_gradient_scaled_mul_sq_eq {R : ℝ} (hR : 0 < R) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : ‖x‖ < R) :
    ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 =
      ‖gradient f x‖ ^ 2 := by
    rw [Energy.Euclidean.LipschitzApproximation.gradient_scaled_mul hf,
      Energy.Euclidean.LipschitzApproximation.scaled_eq_one hR hx.le]
    have h0 : gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x = 0 := by
      unfold gradient
      rw [Energy.Euclidean.LipschitzApproximation.fderiv_scaled_eq_zero hR hx]
      simp
    rw [h0]
    simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- Everywhere the cutoff gradient is dominated by `2‖∇f‖² + 2 (M/R)² f²`. -/
theorem norm_gradient_scaled_mul_sq_le {R M : ℝ} (hR : 0 < R)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(Energy.Euclidean.LipschitzApproximation.bump (E := E))) x‖ ≤ M)
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    ‖gradient (fun y => Energy.Euclidean.LipschitzApproximation.scaled R y * f y) x‖ ^ 2 ≤
      2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
    rw [Energy.Euclidean.LipschitzApproximation.gradient_scaled_mul hf]
    have hs_nonneg :
        0 ≤ Energy.Euclidean.LipschitzApproximation.scaled R x :=
      Energy.Euclidean.LipschitzApproximation.scaled_nonneg R x
    have hs_le_one :
        Energy.Euclidean.LipschitzApproximation.scaled R x ≤ 1 :=
      Energy.Euclidean.LipschitzApproximation.scaled_le_one R x
    have hM0 : 0 ≤ M := by
      exact le_trans (norm_nonneg _) (hM (0 : E))
    have hq : 0 ≤ M / R := div_nonneg hM0 hR.le
    have hgrad :
        ‖gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
          M / R := by
      calc
        ‖gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x‖ =
            ‖fderiv ℝ (Energy.Euclidean.LipschitzApproximation.scaled R) x‖ :=
          (norm_fderiv_eq_norm_gradient
            (Energy.Euclidean.LipschitzApproximation.scaled R) x).symm
        _ ≤ R⁻¹ * M :=
          Energy.Euclidean.LipschitzApproximation.norm_fderiv_scaled_le hR hM x
        _ = M / R := by
          rw [inv_mul_eq_div]
    have ha :
        ‖Energy.Euclidean.LipschitzApproximation.scaled R x • gradient f x‖ ≤
          ‖gradient f x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_nonneg]
      calc
        Energy.Euclidean.LipschitzApproximation.scaled R x * ‖gradient f x‖ ≤
            1 * ‖gradient f x‖ :=
          mul_le_mul_of_nonneg_right hs_le_one (norm_nonneg _)
        _ = ‖gradient f x‖ := by ring
    have hb :
        ‖f x • gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
          (M / R) * |f x| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |f x| * ‖gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x‖ ≤
            |f x| * (M / R) :=
          mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)
        _ = (M / R) * |f x| := by ring
    let A : ℝ := ‖gradient f x‖
    let B : ℝ := (M / R) * |f x|
    let N : ℝ :=
      ‖Energy.Euclidean.LipschitzApproximation.scaled R x • gradient f x +
          f x • gradient (Energy.Euclidean.LipschitzApproximation.scaled R) x‖
    have hsum : N ≤ A + B := by
      dsimp [N, A, B]
      exact le_trans (norm_add_le _ _) (add_le_add ha hb)
    have hA : 0 ≤ A := by
      dsimp [A]
      exact norm_nonneg _
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hq (abs_nonneg _)
    have hN : 0 ≤ N := by
      dsimp [N]
      exact norm_nonneg _
    have hsq : N ^ 2 ≤ (A + B) ^ 2 := by
      have h₁ : 0 ≤ A + B - N := sub_nonneg.mpr hsum
      have h₂ : 0 ≤ A + B + N := by linarith
      have h₃ : 0 ≤ (A + B - N) * (A + B + N) :=
        mul_nonneg h₁ h₂
      nlinarith
    have hquad :
        (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
      dsimp [B]
      nlinarith [sq_nonneg (A - (M / R) * |f x|), sq_abs (f x)]
    calc
      N ^ 2 ≤ (A + B) ^ 2 := hsq
      _ ≤ 2 * A ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := hquad
      _ = 2 * ‖gradient f x‖ ^ 2 + 2 * (M / R) ^ 2 * f x ^ 2 := by
        rfl

/-- The energies of the cutoffs `f χ_{n+1}` converge to the energy of `f` for an admissible `f`. -/
theorem tendsto_energy_scaled_mul {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : Admissible μ f) :
    Tendsto (fun n : ℕ =>
        energy μ (fun x => Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) x * f x))
      atTop (𝓝 (energy μ f)) := by
    unfold energy
    obtain ⟨M, hM0, hM⟩ :=
      Energy.Euclidean.LipschitzApproximation.exists_bound_fderiv_bump (E := E)
    have hsq : Integrable (fun x : E => f x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hf.memLp_two.aestronglyMeasurable).1 hf.memLp_two
    have hbound :
        Integrable
          (fun x : E => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2) μ :=
      (hf.energy_integrable.const_mul 2).add (hsq.const_mul (2 * M ^ 2))
    have hmeas :
        ∀ n : ℕ, AEStronglyMeasurable
          (fun x : E =>
            ‖gradient
                (fun y =>
                  Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                    f y) x‖ ^ 2) μ := by
      intro n
      let g : E → ℝ :=
        fun y =>
          Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y * f y
      have hg : ContDiff ℝ ∞ g := by
        dsimp [g]
        exact
          (Energy.Euclidean.LipschitzApproximation.contDiff_scaled
            ((n : ℝ) + 1)).mul hf.smooth'
      have hgf : Continuous (fderiv ℝ g) :=
        hg.continuous_fderiv (by simp)
      have hgrad : Continuous (gradient g) := by
        change
          Continuous
            (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g x))
        exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hgf
      have hc : Continuous (fun x => ‖gradient g x‖ ^ 2) :=
        (hgrad.norm).pow 2
      exact hc.aestronglyMeasurable
    have hdom :
        ∀ n : ℕ, ∀ᵐ x ∂μ,
          ‖‖gradient
              (fun y =>
                Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2‖ ≤
            2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
      intro n
      filter_upwards [] with x
      have hR : 0 < (n : ℝ) + 1 := by positivity
      have hfd : DifferentiableAt ℝ f x :=
        (hf.smooth'.differentiable (by simp)) x
      have hi := norm_gradient_scaled_mul_sq_le
        (f := f) (R := (n : ℝ) + 1) hR hM hfd
      have hdiv : M / ((n : ℝ) + 1) ≤ M := by
        exact div_le_self hM0 (by linarith)
      have hnonneg : 0 ≤ M / ((n : ℝ) + 1) := by
        exact div_nonneg hM0 (le_of_lt hR)
      have hsqdiv :
          (M / ((n : ℝ) + 1)) ^ 2 ≤ M ^ 2 := by
        have h := mul_self_le_mul_self hnonneg hdiv
        simpa [pow_two] using h
      have hi' :
          ‖gradient
              (fun y =>
                Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2 ≤
            2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
        calc
          ‖gradient
              (fun y =>
                Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                  f y) x‖ ^ 2 ≤
              2 * ‖gradient f x‖ ^ 2 +
                2 * (M / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 := hi
          _ ≤ 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2 := by
            gcongr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hi'
    have hlim :
        ∀ᵐ x ∂μ,
          Tendsto
            (fun n : ℕ =>
              ‖gradient
                  (fun y =>
                    Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) y *
                      f y) x‖ ^ 2)
            atTop (𝓝 (‖gradient f x‖ ^ 2)) := by
      filter_upwards [] with x
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) ?_
      intro n hn
      have hceil : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := by
        exact Nat.le_ceil _
      have hn' : (Nat.ceil ‖x‖ : ℝ) ≤ n := by
        exact_mod_cast hn
      have hx : ‖x‖ < (n : ℝ) + 1 := by
        linarith
      have hR : 0 < (n : ℝ) + 1 := by positivity
      have hfd : DifferentiableAt ℝ f x :=
        (hf.smooth'.differentiable (by simp)) x
      exact
        norm_gradient_scaled_mul_sq_eq
          (f := f) (R := (n : ℝ) + 1) hR hfd hx
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun x : E => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * f x ^ 2)
        hmeas hbound hdom hlim

/-- **A Poincaré bound on compactly supported admissible tests extends to all admissible tests**
(BKL Section 2, cutoff extension). -/
theorem Holds.of_compactSupport {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : E → ℝ, Admissible μ f → HasCompactSupport f → variance f μ ≤ C * energy μ f) :
    Holds μ C := by
    refine
      { probability := inferInstance
        constant_nonneg := hC
        variance_le := ?_ }
    intro f hf
    let χ (n : ℕ) : E → ℝ :=
      Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1)
    let g (n : ℕ) : E → ℝ := fun x => χ n x * f x
    have hadm (n : ℕ) : Admissible μ (g n) := by
      change
        Admissible μ
          (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) * f)
      exact
        Admissible.of_contDiff_hasCompactSupport
          ((Energy.Euclidean.LipschitzApproximation.contDiff_scaled _).mul hf.smooth')
          ((Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled
            (by positivity)).mul_right)
    have hcs (n : ℕ) : HasCompactSupport (g n) := by
      change
        HasCompactSupport
          (Energy.Euclidean.LipschitzApproximation.scaled ((n : ℝ) + 1) * f)
      exact
        (Energy.Euclidean.LipschitzApproximation.hasCompactSupport_scaled
          (by positivity)).mul_right
    have hlim :=
      tendsto_integral_scaled_mul (μ := μ) hf.memLp_two
    have h1 :
        Tendsto
          (fun n : ℕ => ∫ x, χ n x * f x ∂μ)
          atTop (𝓝 (∫ x, f x ∂μ)) := by
      simpa [χ] using hlim.1
    have h2 :
        Tendsto
          (fun n : ℕ => ∫ x, (χ n x * f x) ^ 2 ∂μ)
          atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
      simpa [χ] using hlim.2
    have hv :
        (fun n : ℕ => variance (g n) μ) =
          (fun n : ℕ =>
            (∫ x, (χ n x * f x) ^ 2 ∂μ) -
              (∫ x, χ n x * f x ∂μ) ^ 2) := by
      funext n
      rw [variance_eq_sub (hadm n).memLp_two]
      rfl
    have hvar :
        Tendsto (fun n : ℕ => variance (g n) μ)
          atTop (𝓝 (variance f μ)) := by
      rw [hv, variance_eq_sub hf.memLp_two]
      exact h2.sub (h1.pow 2)
    have henergy :
        Tendsto (fun n : ℕ => C * energy μ (g n))
          atTop (𝓝 (C * energy μ f)) := by
      have hE :
          Tendsto (fun n : ℕ => energy μ (g n))
            atTop (𝓝 (energy μ f)) := by
        simpa [g, χ] using (tendsto_energy_scaled_mul (μ := μ) hf)
      simpa using hE.const_mul C
    exact
      le_of_tendsto_of_tendsto' hvar henergy
        (fun n => h (g n) (hadm n) (hcs n))

end Cutoff

end FunctionalInequalities.Poincare.SmoothTest
