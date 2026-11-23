/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedMain
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRegular
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPGlobal
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerMain
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedCutoffs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Parallel gradient of first eigenfunctions (Workstream A, unconditional) -/

@[expose] public section

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- Every smooth `L²` eigenfunction of `-𝓛` with eigenvalue `ρ` under `CD(ρ,∞)` has parallel
gradient (hypotheses of `riemannian_gaussian_splitting`; `hgap` is not needed). -/
theorem manifold_eigenfunction_parallel_gradient {V : M → ℝ} (hV : MSmooth F V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (_hgap : mSpectralGap F μ = ρ) {f : M → ℝ}
    (hf : IsMEigenfunction F μ V ρ f) (x : M) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 := by
  let : SigmaCompactSpace M := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  exact manifold_eigenfunction_parallel_gradient_of_inputs F hV hμ hρ.le
    (weightedIBP_of_isWeightedVolume_of_sigmaCompact F hV hμ) (weightedRegular V hV)
    (weightedBochnerIneq_of_CD F hV hCD) (weightedCutoffs_of_complete F) hf x

omit [MeasurableSpace F] [BorelSpace F] [IsRiemannianManifold 𝓘(ℝ, F) M]
  [ConnectedSpace M] [CompleteSpace M] in
/-- A constant gradient pairing of two eigenfunctions is their weighted energy pairing. -/
theorem constant_carre_eq_eigenfunction_pairing {μ : Measure M} [IsProbabilityMeasure μ]
    {V f g : M → ℝ} {ρ pairing bound : ℝ} (hbound : 0 ≤ bound)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hCut : WeightedCutoffs F M)
    (hf : IsMEigenfunction F μ V ρ f) (hg : IsMEigenfunction F μ V ρ g)
    (hconstant : ∀ x, carre F f g x = pairing) (hgradient : ∀ x, ‖mgrad F g x‖ ≤ bound) :
    pairing = ρ * ∫ x, f x * g x ∂μ := by
  obtain ⟨χ, hχ, hlim⟩ := hCut
  have htendsto (u : M → ℝ) (hu : Integrable u μ) :
      Tendsto (fun n => ∫ x, χ n x * u x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖u x‖)
      (fun n => (hχ n).1.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable) hu.norm
    · intro n
      exact Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul, Real.norm_of_nonneg ((hχ n).2.2 x).1]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right ((hχ n).2.2 x).2.1 (norm_nonneg (u x))
    · exact Eventually.of_forall fun x => tendsto_const_nhds.congr'
        ((hlim x).mono fun n hn => by simp only [Pi.mul_apply, hn, one_mul])
  let errorTerm (n : ℕ) (x : M) := f x * carre F (χ n) g x
  have hcontinuous n : Continuous (errorTerm n) := hf.1.continuous.mul
    (hReg.1 _ _ (hχ n).1 hg.1).continuous
  have hsmall n x : ‖errorTerm n x‖ ≤ 1 / ((n : ℝ) + 1) * (bound * ‖f x‖) := by
    rw [show ‖errorTerm n x‖ = ‖f x‖ * |carre F (χ n) g x| from by
      simp [errorTerm, norm_mul, Real.norm_eq_abs]]
    have h := (abs_carre_le F (χ n) g x).trans
      (mul_le_mul ((hχ n).2.2 x).2.2 (hgradient x) (norm_nonneg _) (by positivity))
    calc ‖f x‖ * |carre F (χ n) g x| ≤ ‖f x‖ * (1 / ((n : ℝ) + 1) * bound) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring
  have hdom : Integrable (fun x => bound * ‖f x‖) μ :=
    ((hf.2.1.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable le_rfl).norm.const_mul bound
  have hmajorant n x : ‖errorTerm n x‖ ≤ bound * ‖f x‖ := (hsmall n x).trans (by
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hn (mul_nonneg hbound (norm_nonneg (f x))))
  have hintegrable n : Integrable (errorTerm n) μ :=
    hdom.mono' (hcontinuous n).aestronglyMeasurable (Eventually.of_forall (hmajorant n))
  have hzero : Tendsto (fun n => ∫ x, errorTerm n x ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
        (fun x => bound * ‖f x‖) (fun n => (hcontinuous n).aestronglyMeasurable) hdom
        (fun n => Eventually.of_forall (hmajorant n)) (Eventually.of_forall fun x =>
          squeeze_zero_norm (fun n => hsmall n x)
            (by simpa only [zero_mul] using
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (bound * ‖f x‖))))
  have hfg := hf.2.1.integrable_mul hg.2.1
  have henergy n : (∫ x, χ n x * pairing ∂μ) + (∫ x, errorTerm n x ∂μ) =
      ρ * ∫ x, χ n x * (f x * g x) ∂μ := by
    have hip := hIBP (χ n * f) g ((hχ n).1.mul hf.1) hg.1 (hχ n).2.1.mul_right
    have heq : ∀ x, carre F (χ n * f) g x = χ n x * pairing + errorTerm n x := by
      intro x
      rw [carre_mul_left F (hχ n).1 hf.1, hconstant]
    have hci : Integrable (fun x => χ n x * pairing) μ :=
      ((hχ n).1.continuous.mul continuous_const).integrable_of_hasCompactSupport
        (hχ n).2.1.mul_right
    simp_rw [heq] at hip
    rw [integral_add hci (hintegrable n)] at hip
    rw [hip, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, hg.2.2 x]
    ring
  have hleft := (htendsto (fun _ => pairing) (integrable_const pairing)).add hzero
  have hright := (htendsto (fun x => f x * g x) hfg).const_mul ρ
  have hEq := tendsto_nhds_unique (hleft.congr (fun n => henergy n)) hright
  simpa using hEq

end Final

end CutCur
