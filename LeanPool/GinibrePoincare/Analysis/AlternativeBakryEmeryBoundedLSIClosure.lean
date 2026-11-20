/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBoundedLSIClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.StrongConvexBoundedLipschitzLSIExtension
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGradientBasis
/-!
# Alternative Bakry Emery bounded LSI closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_boundedLipschitz_gradient_lsi_of_compact`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The smooth bump on `E` centred at `0`, equal to `1` on the ball of radius `1` and supported
in the ball of radius `2`. -/
def bakryBoundedSpatialBump : ContDiffBump (0 : E) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The spatial cutoff `A ↦ φ ((k + 1)⁻¹ • A)`, where `φ` is `bakryBoundedSpatialBump`; it
equals `1` on the ball of radius `k + 1`. -/
def bakryBoundedSpatialCutoff (k : ℕ) (A : E) : ℝ :=
  bakryBoundedSpatialBump E (((k : ℝ) + 1)⁻¹ • A)

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_smooth (k : ℕ) : ContDiff ℝ ∞ (bakryBoundedSpatialCutoff E k) :=
  (bakryBoundedSpatialBump E).contDiff.comp (by fun_prop)

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_compact (k : ℕ) : HasCompactSupport (bakryBoundedSpatialCutoff E
    k) := by
  exact (bakryBoundedSpatialBump E).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹) (inv_ne_zero (by positivity)))

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_mem_unit (k : ℕ) (A : E) :
    0 ≤ bakryBoundedSpatialCutoff E k A ∧ bakryBoundedSpatialCutoff E k A ≤ 1 :=
  ⟨(bakryBoundedSpatialBump E).nonneg, (bakryBoundedSpatialBump E).le_one⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_tendsto (A : E) :
    Tendsto (fun k => bakryBoundedSpatialCutoff E k A) atTop (nhds 1) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx := hi.smul_const A
  have hz : bakryBoundedSpatialBump E (0 : E) = 1 :=
    (bakryBoundedSpatialBump E).one_of_mem_closedBall (by simp [bakryBoundedSpatialBump])
  simpa [bakryBoundedSpatialCutoff, hz, Function.comp_def] using
    ((bakryBoundedSpatialBump E).continuous.continuousAt.tendsto.comp hx)

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_fderiv (k : ℕ) (A H : E) :
    fderiv ℝ (bakryBoundedSpatialCutoff E k) A H =
      ((k : ℝ) + 1)⁻¹ * fderiv ℝ (bakryBoundedSpatialBump E : E → ℝ)
        (((k : ℝ) + 1)⁻¹ • A) H := by
  have hd := (((bakryBoundedSpatialBump E).contDiff (n := 1)).differentiable (by norm_num)
    (((k : ℝ) + 1)⁻¹ • A)).hasFDerivAt.comp A
      ((hasFDerivAt_id A).const_smul (((k : ℝ) + 1)⁻¹))
  unfold bakryBoundedSpatialCutoff
  simpa [bakryBoundedSpatialCutoff, Function.comp_def, ContinuousLinearMap.comp_apply,
    map_smul, smul_eq_mul] using congrArg (fun L : E →L[ℝ] ℝ => L H) hd.fderiv

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_derivative_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (A H : E),
      |fderiv ℝ (bakryBoundedSpatialCutoff E k) A H| ≤ M / ((k : ℝ) + 1) * ‖H‖ := by
  obtain ⟨M, hM⟩ := ((bakryBoundedSpatialBump E).contDiff (n := 1)).continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support ((bakryBoundedSpatialBump E).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro k A H
  rw [bakryBoundedSpatialCutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hnorm := (fderiv ℝ (bakryBoundedSpatialBump E : E → ℝ)
    (((k : ℝ) + 1)⁻¹ • A)).le_opNorm H
  have hh : |fderiv ℝ (bakryBoundedSpatialBump E : E → ℝ)
      (((k : ℝ) + 1)⁻¹ • A) H| ≤ M * ‖H‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg H))
  calc
    _ ≤ ((k : ℝ) + 1)⁻¹ * (M * ‖H‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
theorem bakryBoundedSpatialCutoff_derivative_tendsto (A H : E) :
    Tendsto (fun k => fderiv ℝ (bakryBoundedSpatialCutoff E k) A H) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := bakryBoundedSpatialCutoff_derivative_bound E
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa using hM k A H)
  simpa [div_eq_mul_inv] using (hi.const_mul M).mul_const ‖H‖

/-- Spatial cutoff closure of a compact C¹ LSI for a finite-dimensional
Hilbert probability measure. All cutoff and entropy limits are proved here. -/
theorem bakryEmery_boundedC1_lsi_of_compact {ι : Type*} [Fintype ι]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ι → E) (c : ℝ)
    (hcore : ∀ f : E → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      squareEntropy μ f ≤ c * ∫ x, directionalEnergy d f x ∂μ)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (K : ℝ≥0) (hK : LipschitzWith K f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy μ f ≤ c * ∫ x, directionalEnergy d f x ∂μ := by
  classical
  let F : ℕ → E → ℝ := fun n x => bakryBoundedSpatialCutoff E n x * f x
  have hF n : ContDiff ℝ 1 (F n) := (bakryBoundedSpatialCutoff_smooth E n).of_le (by simp) |>.mul hf
  have hcF n : HasCompactSupport (F n) := (bakryBoundedSpatialCutoff_compact E n).mul_right
  have hFb n x : ‖F n x‖ ≤ C := by
    have hu := bakryBoundedSpatialCutoff_mem_unit E n x
    calc
      _ = |bakryBoundedSpatialCutoff E n x| * ‖f x‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul (by simpa [abs_of_nonneg hu.1] using hu.2) (hC x)
        (norm_nonneg _) (by linarith [norm_nonneg (f x), hC x])
      _ = C := one_mul C
  have hlim x : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    simpa [F] using (bakryBoundedSpatialCutoff_tendsto E x).mul_const (f x)
  obtain ⟨M, hM0, hM⟩ := bakryBoundedSpatialCutoff_derivative_bound E
  have hD n x i : fderiv ℝ (F n) x (d i) =
      f x * fderiv ℝ (bakryBoundedSpatialCutoff E n) x (d i) +
      bakryBoundedSpatialCutoff E n x * fderiv ℝ f x (d i) := by
    change fderiv ℝ (bakryBoundedSpatialCutoff E n * f) x (d i) = _
    rw [fderiv_mul ((bakryBoundedSpatialCutoff_smooth E n).differentiable (by simp) x)
      (hf.differentiable one_ne_zero x)]
    simp [add_apply]
    ring
  have hDb n x i : |fderiv ℝ (F n) x (d i)| ≤ (C*M+(K : ℝ))*‖d i‖ := by
    have hu := bakryBoundedSpatialCutoff_mem_unit E n x
    have hd := hM n x (d i)
    have hinv : M / ((n : ℝ)+1) ≤ M := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hd' := hd.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg (d i)))
    have hdf : |fderiv ℝ f x (d i)| ≤ (K : ℝ)*‖d i‖ := by
      exact ((fderiv ℝ f x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hK) (norm_nonneg _))
    rw [hD]
    calc
      _ ≤ |f x| *|fderiv ℝ (bakryBoundedSpatialCutoff E n) x (d i)| +
          |bakryBoundedSpatialCutoff E n x| *|fderiv ℝ f x (d i)| := by
        simpa [abs_mul] using abs_add_le
          (f x*fderiv ℝ (bakryBoundedSpatialCutoff E n) x (d i))
          (bakryBoundedSpatialCutoff E n x*fderiv ℝ f x (d i))
      _ ≤ C*(M*‖d i‖)+1*((K : ℝ)*‖d i‖) := add_le_add
        (mul_le_mul (by simpa [Real.norm_eq_abs] using hC x) hd' (abs_nonneg _)
          (by linarith [hC x, norm_nonneg (f x)]))
        (mul_le_mul (by simpa [abs_of_nonneg hu.1] using hu.2) hdf (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hmass : Tendsto (fun n => ∫ x, F n x^2 ∂μ) atTop (𝓝 (∫ x, f x^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C^2)
      (fun n => ((hF n).continuous.pow 2).aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Eventually.of_forall (fun x => by
        have hb := hFb n x
        rw [Real.norm_eq_abs] at hb
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change F n x ^ 2 ≤ C ^ 2
        nlinarith [sq_abs (F n x), abs_nonneg (F n x)])
    · exact Eventually.of_forall (fun x => (hlim x).pow 2)
  have he : Tendsto (fun n => ∫ x, directionalEnergy d (F n) x ∂μ) atTop
      (𝓝 (∫ x, directionalEnergy d f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => ∑ i, ((C*M+(K : ℝ))*‖d i‖)^2)
    · intro n
      apply Continuous.aestronglyMeasurable
      exact continuous_finsetSum _ (fun i hi =>
        (((hF n).continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2)
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      apply Finset.sum_le_sum
      intro i hi
      have hb := hDb n x i
      have hp : 0 ≤ (C*M+(K : ℝ))*‖d i‖ := (abs_nonneg _).trans hb
      nlinarith [sq_abs (fderiv ℝ (F n) x (d i)), abs_nonneg (fderiv ℝ (F n) x (d i))]
    · apply Eventually.of_forall
      intro x
      apply tendsto_finsetSum
      intro i hi
      simp_rw [hD]
      have hl := ((bakryBoundedSpatialCutoff_derivative_tendsto E x (d i)).const_mul (f x)).add
        ((bakryBoundedSpatialCutoff_tendsto E x).mul_const (fderiv ℝ f x (d i)))
      simpa using hl.pow 2
  exact (squareEntropy_le_of_ae_tendsto μ F f _ _
    (fun n => (hF n).continuous.aestronglyMeasurable) hf.continuous.aestronglyMeasurable
    (fun n => (continuous_square_mul_log (hF n).continuous).integrable_of_hasCompactSupport
      (compactSupport_square_mul_log (hcF n)))
    (Eventually.of_forall hlim) hmass (he.const_mul c)
    (fun n => hcore (F n) (hF n) (hcF n))).2

/-- Concrete Hilbert gradient version of the compact-core closure, with the
Haar absolute continuity needed only for genuine nonsmooth mollification. -/
theorem bakryEmery_boundedLipschitz_gradient_lsi_of_compact
    (η : Measure E) [η.IsAddHaarMeasure] (μ : Measure E) [IsProbabilityMeasure μ]
    (hac : μ ≪ η) (c : ℝ)
    (hcore : ∀ f : E → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      squareEntropy μ f ≤ c * ∫ x, ‖gradient f x‖^2 ∂μ)
    (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy μ f ≤ c * ∫ x, ‖gradient f x‖^2 ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hc : ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      squareEntropy μ g ≤ c * ∫ x, directionalEnergy b g x ∂μ := by
    intro g hg hgc
    simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using hcore g hg hgc
  have hb := boundedLipschitz_lsi_of_C1 η μ hac b c
    (fun g hg K hK C hC => bakryEmery_boundedC1_lsi_of_compact E μ b c hc g hg K hK C hC)
    f hf C hC
  simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using hb

end
end GinibrePoincare
