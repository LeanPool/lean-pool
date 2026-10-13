/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LocalControlMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Majorant

/-!
# Summability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Almost-sure summability of lower local-control tails

The Gaussian maximum estimate carries an explicit dimensional prefactor.  It
is retained in `expectedCubeMajorant`; this is an internal proof majorant, not
a normalization of a source-facing cutoff object.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The summable expectation majorant for one lower shell.  The dimensional
Gaussian-maximum factor is displayed explicitly rather than hidden. -/
def expectedCubeMajorant (d : ℕ) (gamma : ℝ) (m ell : ℤ) (r : ℕ) : ℝ :=
  gaussianMaximumDimConst d * cubeMajorant gamma m ell r

theorem summable_expectedCubeMajorant {gamma : ℝ} (hgamma : 0 < gamma)
    (m ell : ℤ) : Summable (expectedCubeMajorant d gamma m ell) := by
  exact (summable_cubeMajorant hgamma m ell).mul_left _

private theorem integral_localCubeControl_zero_le_dim_majorant
    (M : ABKModel d) (q : ℤ) :
    ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
      gaussianMaximumDimConst d * Real.sqrt (1 + max (q : ℝ) 0) := by
  rcases le_total 0 q with hq | hq
  · have hqcast : (q.toNat : ℝ) = (q : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hq
    have hqreal : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    calc
      ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
          gaussianMaximumDimConst d * Real.sqrt (1 + q.toNat) :=
        integral_localCubeControl_under_zeroShellLaw_le_of_nonneg M q hq
      _ = gaussianMaximumDimConst d * Real.sqrt (1 + (q : ℝ)) := by rw [hqcast]
      _ = gaussianMaximumDimConst d * Real.sqrt (1 + max (q : ℝ) 0) := by
        rw [max_eq_left hqreal]
  · calc
      ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
          ∫ j, localCubeControl 0 j ∂(ShellField.zeroShellLaw M.P).toMeasure := by
        apply integral_mono
        · exact integrable_localCubeControl_under_zeroShellLaw M q
        · exact integrable_localCubeControl_under_zeroShellLaw M 0
        · intro j
          exact localCubeControl_le_localCubeControl_zero q hq j
      _ ≤ gaussianMaximumDimConst d := by
        simpa [gaussianMaximumDimConst] using
          integral_localCubeControl_under_zeroShellLaw_le_of_nonneg M 0 le_rfl
      _ = gaussianMaximumDimConst d * Real.sqrt (1 + max (q : ℝ) 0) := by
        rw [max_eq_right (by exact_mod_cast hq)]
        norm_num

private theorem integrable_localCubeControl_shell
    (M : ABKModel d) (ell n : ℤ) :
    Integrable (fun omega : ShellSeq d => localCubeControl ell (omega n))
      M.P.toMeasure := by
  let a : ℝ := Real.rpow 3 (M.gamma * (n : ℝ))
  let q : ℤ := ell - n
  let f : ShellSeq d → ℝ := fun omega => localCubeControl ell (omega n)
  let g : ShellField d → ℝ := fun j => a * localCubeControl q j
  have hf : Measurable f :=
    (measurable_localCubeControl ell).comp (measurable_pi_apply n)
  have hg : Measurable g :=
    measurable_const.mul (measurable_localCubeControl q)
  have hg_int : Integrable g (ShellField.zeroShellLaw M.P).toMeasure := by
    simpa [g] using (integrable_localCubeControl_under_zeroShellLaw M q).const_mul a
  have hid_g : Integrable id (Measure.map g (ShellField.zeroShellLaw M.P).toMeasure) := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable hg.aemeasurable).mpr
    simpa only [Function.comp_apply] using! hg_int
  have hmap : Measure.map f M.P.toMeasure =
      Measure.map g (ShellField.zeroShellLaw M.P).toMeasure := by
    simpa [f, g, a, q] using map_localCubeControl_shell_eq_zero M ell n
  have hid_f : Integrable id (Measure.map f M.P.toMeasure) := by
    rw [hmap]
    exact hid_g
  simpa only [Function.comp_apply] using!
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mp hid_f

private theorem integral_localCubeControl_shell_le_expectedCubeMajorant
    (M : ABKModel d) (m ell : ℤ) (r : ℕ) :
    ∫ omega : ShellSeq d, localCubeControl ell (omega (m - r)) ∂M.P.toMeasure ≤
      expectedCubeMajorant d M.gamma m ell r := by
  let n : ℤ := m - r
  let q : ℤ := ell - n
  let a : ℝ := Real.rpow 3 (M.gamma * (n : ℝ))
  let f : ShellSeq d → ℝ := fun omega => localCubeControl ell (omega n)
  let g : ShellField d → ℝ := fun j => a * localCubeControl q j
  have hf : Measurable f :=
    (measurable_localCubeControl ell).comp (measurable_pi_apply n)
  have hg : Measurable g := measurable_const.mul (measurable_localCubeControl q)
  have hfi := integrable_localCubeControl_shell M ell n
  have hgi : Integrable g (ShellField.zeroShellLaw M.P).toMeasure := by
    simpa [g] using (integrable_localCubeControl_under_zeroShellLaw M q).const_mul a
  have hmap : Measure.map f M.P.toMeasure =
      Measure.map g (ShellField.zeroShellLaw M.P).toMeasure := by
    simpa [f, g, a, q] using map_localCubeControl_shell_eq_zero M ell n
  have heq : (∫ omega, f omega ∂M.P.toMeasure) =
      ∫ j, g j ∂(ShellField.zeroShellLaw M.P).toMeasure := by
    calc
      (∫ omega, f omega ∂M.P.toMeasure) = ∫ x, id x ∂Measure.map f M.P.toMeasure := by
        simpa only [Function.comp_apply] using!
          (integral_map hf.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ x, id x ∂Measure.map g (ShellField.zeroShellLaw M.P).toMeasure := by rw [hmap]
      _ = ∫ j, g j ∂(ShellField.zeroShellLaw M.P).toMeasure := by
        simpa only [Function.comp_apply] using!
          integral_map hg.aemeasurable measurable_id.aestronglyMeasurable
  have hzero := integral_localCubeControl_zero_le_dim_majorant M q
  have ha : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  calc
    ∫ omega : ShellSeq d, localCubeControl ell (omega (m - r)) ∂M.P.toMeasure =
        ∫ omega, f omega ∂M.P.toMeasure := by rfl
    _ = ∫ j, g j ∂(ShellField.zeroShellLaw M.P).toMeasure := heq
    _ = a * ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure := by
      simpa [g] using integral_const_mul a (localCubeControl q)
    _ ≤ a * (gaussianMaximumDimConst d * Real.sqrt (1 + max (q : ℝ) 0)) := by
      exact mul_le_mul_of_nonneg_left hzero ha
    _ = expectedCubeMajorant d M.gamma m ell r := by
      have hn : (n : ℝ) = (m : ℝ) - (r : ℝ) := by
        dsimp [n]
        push_cast
        ring
      have hq : (q : ℝ) = (ell : ℝ) - ((m : ℝ) - (r : ℝ)) := by
        dsimp [q, n]
        push_cast
        ring
      have hpow : Real.rpow 3 (M.gamma * (n : ℝ)) =
          Real.rpow 3 (M.gamma * (m : ℝ) - M.gamma * (r : ℝ)) := by
        congr 1
        rw [hn]
        ring
      simp only [expectedCubeMajorant, cubeMajorant, a, hpow, hq]
      ring_nf

private theorem ae_summable_of_summable_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → Ω → ℝ)
    (hF_meas : ∀ r, Measurable (F r)) (hF_nonneg : ∀ r omega, 0 ≤ F r omega)
    (hF_int : ∀ r, Integrable (F r) μ)
    (hF_sum : Summable (fun r => ∫ omega, F r omega ∂μ)) :
    ∀ᵐ omega ∂μ, Summable (fun r => F r omega) := by
  have hlin : ∑' r, ∫⁻ omega, ENNReal.ofReal (F r omega) ∂μ ≠ ⊤ := by
    calc
      ∑' r, ∫⁻ omega, ENNReal.ofReal (F r omega) ∂μ =
          ∑' r, ENNReal.ofReal (∫ omega, F r omega ∂μ) := by
        congr with r
        exact (ofReal_integral_eq_lintegral_ofReal (hF_int r)
          (Filter.Eventually.of_forall fun omega => hF_nonneg r omega)).symm
      _ = ENNReal.ofReal (∑' r, ∫ omega, F r omega ∂μ) := by
        exact (ENNReal.ofReal_tsum_of_nonneg
          (fun r => integral_nonneg fun omega => hF_nonneg r omega) hF_sum).symm
      _ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlin' : ∫⁻ omega, ∑' r, ENNReal.ofReal (F r omega) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun r => (hF_meas r).aemeasurable.ennreal_ofReal]
    exact hlin
  have hfinite : ∀ᵐ omega ∂μ, ∑' r, ENNReal.ofReal (F r omega) < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun r =>
      (hF_meas r).aemeasurable.ennreal_ofReal) hlin'
  filter_upwards [hfinite] with omega homega
  have hs : Summable (fun r => ((F r omega).toNNReal : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg (hF_nonneg _ omega)] using homega.ne
  simpa [Real.toNNReal_of_nonneg (hF_nonneg _ omega)] using hs

private theorem ae_lowerTailBounded (M : ABKModel d) (ell m : ℤ) :
    ∀ᵐ omega ∂M.P.toMeasure, LowerTailBounded ell m omega := by
  let F : ℕ → ShellSeq d → ℝ := fun r omega =>
    localCubeControl ell (omega (m - r))
  have hmeas : ∀ r, Measurable (F r) := fun r =>
    (measurable_localCubeControl ell).comp (measurable_pi_apply _)
  have hnonneg : ∀ r omega, 0 ≤ F r omega := fun r omega =>
    localCubeControl_nonneg ell (omega (m - r))
  have hint : ∀ r, Integrable (F r) M.P.toMeasure := fun r =>
    integrable_localCubeControl_shell M ell (m - r)
  have hbound : ∀ r, (∫ omega, F r omega ∂M.P.toMeasure) ≤
      expectedCubeMajorant d M.gamma m ell r := fun r =>
    integral_localCubeControl_shell_le_expectedCubeMajorant M m ell r
  have hsum : Summable (fun r => ∫ omega, F r omega ∂M.P.toMeasure) := by
    apply Summable.of_nonneg_of_le
    · intro r
      exact integral_nonneg fun omega => hnonneg r omega
    · exact hbound
    · exact summable_expectedCubeMajorant M.shellPrefix.gamma_pos m ell
  filter_upwards [ae_summable_of_summable_integrals M.P.toMeasure F hmeas hnonneg hint hsum]
    with omega hs
  obtain ⟨C, hC⟩ := exists_nat_ge (∑' r, F r omega)
  refine ⟨C, ?_⟩
  intro q
  have hqsum : ∑ r ∈ Finset.range q, F r omega ≤ ∑' r, F r omega := by
    exact hs.sum_le_tsum (Finset.range q) (fun r _ => hnonneg r omega)
  have hpartial : lowerTailPartialSum ell m q omega ≤ ∑' r, F r omega := by
    simpa [lowerTailPartialSum, F] using hqsum
  exact hpartial.trans hC

/-- The exact deterministic lower-tail-good condition holds almost surely
under the canonical shell law. -/
theorem ae_lowerTailGood (M : ABKModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, LowerTailGood omega := by
  rw [show LowerTailGood = fun omega : ShellSeq d =>
      ∀ ell : ℤ, ∀ m : ℤ, LowerTailBounded ell m omega by rfl]
  exact ae_all_iff.2 fun ell => ae_all_iff.2 fun m => ae_lowerTailBounded M ell m

end

end Algsuperdiff.Section3.Cutoff
