/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.StrictReserveTraceInterpolation
public import LeanPool.VacuumBellSeparation.Gaussian.NuclearSandwichContinuity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Actual reserve nuclear interpolation including zero spectrum

Regularize R by R+epsilon I. Positive-power CFC continuity on the entire
nonnegative cone and the proved nuclear sandwich modulus pass the genuine
strict-positive three-lines inequality to the limit. No bounded inverse of
R, imaginary power at zero, finite rank, or spectral gap is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter Set
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reserve regularization given by `R + ε • 1`. -/
def reserveRegularization (R : E →L[ℂ] E) (ε : ℝ) : E →L[ℂ] E := R + ε • 1

theorem reserveRegularization_strict {R : E →L[ℂ] E} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) : IsStrictlyPositive (reserveRegularization R ε) := by
  have hp : IsStrictlyPositive (ε • (1 : E →L[ℂ] E)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isStrictlyPositive_algebraMap (A := E →L[ℂ] E) hε)
  exact hp.of_le (le_add_of_nonneg_left hR)

theorem reserveRegularization_tendsto (R : E →L[ℂ] E) :
    Tendsto (reserveRegularization R) (𝓝[>] (0 : ℝ)) (𝓝 R) := by
  have hc : Continuous (reserveRegularization R) := by unfold reserveRegularization; fun_prop
  simpa only [reserveRegularization, zero_smul, add_zero] using
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem continuousOn_positiveOperator_rpow {p : ℝ} (hp : 0 < p) :
    ContinuousOn (fun A : E →L[ℂ] E => A ^ p) {A | 0 ≤ A} := by
  have h := CFC.continuousOn_nnrpow (A := E →L[ℂ] E) (NNReal.mk p hp.le : ℝ≥0)
  have hpow (T : E →L[ℂ] E) : T ^ (NNReal.mk p hp.le : NNReal) = T ^ p :=
    CFC.nnrpow_eq_rpow (a := T) (show (0 : NNReal) < NNReal.mk p hp.le from hp)
  simpa only [hpow] using h

theorem reserveRegularization_rpow_tendsto {R : E →L[ℂ] E}
    (hR : 0 ≤ R) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => reserveRegularization R ε ^ p) (𝓝[>] (0 : ℝ)) (𝓝 (R ^ p)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ reserveRegularization R ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (reserveRegularization_strict hR hε).nonneg
  have hlim : Tendsto (reserveRegularization R) (𝓝[>] (0 : ℝ))
      (𝓝[{A : E →L[ℂ] E | 0 ≤ A}] R) :=
    tendsto_nhdsWithin_iff.mpr ⟨reserveRegularization_tendsto R, he⟩
  exact (continuousOn_positiveOperator_rpow hp R hR).tendsto.comp hlim

theorem reserveRegularization_nuclear_trace_tendsto {R B : E →L[ℂ] E}
    (hR : 0 ≤ R) (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B)
    (htB : operatorTraceNorm B < ∞) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ =>
      (operatorTraceNorm (reserveRegularization R ε ^ p * B * reserveRegularization R ε ^
        p)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (operatorTraceNorm (R ^ p * B * R ^ p)).toReal) :=
  tendsto_nuclear_sandwich_toReal (fun _ => CFC.rpow_nonneg.isSelfAdjoint)
    CFC.rpow_nonneg.isSelfAdjoint hcB hB htB (reserveRegularization_rpow_tendsto hR hp)

/-- The manuscript's genuine nuclear interpolation inequality. A zero
spectral endpoint, an actual kernel, and arbitrary Hilbert dimension are
all permitted. The exponents are strictly between the two edges. -/
theorem operatorTraceNorm_reserve_interpolation {R B : E →L[ℂ] E}
    (hR : 0 ≤ R) (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B)
    (htB : operatorTraceNorm B < ∞) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    operatorTraceNorm (R ^ ((1 - θ) / 2) * B * R ^ ((1 - θ) / 2)) ≤
      operatorTraceNorm (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ)) ^ (1 - θ) *
        operatorTraceNorm B ^ θ := by
  have hp : 0 < (1 - θ) / 2 := div_pos (sub_pos.mpr hθ.2) (by norm_num)
  have hZlim := reserveRegularization_nuclear_trace_tendsto hR hcB hB htB hp
  have hGlim := reserveRegularization_nuclear_trace_tendsto hR hcB hB htB
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hRlim := (((Real.continuous_rpow_const (sub_nonneg.mpr hθ.2.le)).tendsto _).comp hGlim).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (operatorTraceNorm B).toReal ^ θ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((operatorTraceNorm B).toReal ^ θ)))
  have hreal : (operatorTraceNorm (R ^ ((1 - θ) / 2) * B * R ^ ((1 - θ) / 2))).toReal ≤
      (operatorTraceNorm (R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ))).toReal ^ (1 - θ) *
        (operatorTraceNorm B).toReal ^ θ := by
    apply le_of_tendsto_of_tendsto hZlim hRlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hRe := reserveRegularization_strict hR hε
    have htG := operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB
      (show IsSelfAdjoint (reserveRegularization R ε ^
        (1 / 2 : ℝ)) from CFC.rpow_nonneg.isSelfAdjoint)
    have hh := operatorTraceNorm_strict_reserve_interpolation hRe hcB hB htB ⟨hθ.1.le, hθ.2.le⟩
    have hf : operatorTraceNorm
        (reserveRegularization R ε ^ (1 / 2 : ℝ) * B * reserveRegularization R ε ^ (1 / 2 : ℝ)) ^
          (1 - θ) * operatorTraceNorm B ^ θ ≠ ∞ :=
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ.2.le) htG.ne)
        (ENNReal.rpow_lt_top_of_nonneg hθ.1.le htB.ne)).ne
    have hr := ENNReal.toReal_mono hf hh
    simpa only [Function.comp_apply, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr
  have htZ := operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB
    (show IsSelfAdjoint (R ^ ((1 - θ) / 2)) from CFC.rpow_nonneg.isSelfAdjoint)
  have htG := operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB
    (show IsSelfAdjoint (R ^ (1 / 2 : ℝ)) from CFC.rpow_nonneg.isSelfAdjoint)
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_toReal htZ.ne,
    ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr hθ.2.le),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ.1.le,
    ENNReal.ofReal_toReal htG.ne, ENNReal.ofReal_toReal htB.ne] at h
  exact h

/-- The actual interpolated factor and both its algebraic and nuclear
properties. The same operator Z is used in every conclusion. -/
theorem exists_interpolated_reserve_factor {R B G : E →L[ℂ] E}
    (hR : 0 ≤ R) (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B)
    (htB : operatorTraceNorm B < ∞) (hG : R ^ (1 / 2 : ℝ) * B * R ^ (1 / 2 : ℝ) = G)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ∃ Z : E →L[ℂ] E, IsCompactOperator Z ∧ IsSelfAdjoint Z ∧
      R ^ (θ / 2) * Z * R ^ (θ / 2) = G ∧
      operatorTraceNorm Z ≤ operatorTraceNorm G ^ (1 - θ) * operatorTraceNorm B ^ θ ∧
      operatorTraceNorm Z < ∞ := by
  let S := R ^ ((1 - θ) / 2)
  let Z := S * B * S
  have hS : IsSelfAdjoint S := CFC.rpow_nonneg.isSelfAdjoint
  refine ⟨Z, (hcB.clm_comp S).comp_clm S, selfAdjoint_sandwich_isSelfAdjoint hB hS,
    ?_, ?_, operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB hS⟩
  · exact (reserve_power_interpolation_factorization hR B ⟨hθ.1.le, hθ.2.le⟩).trans hG
  · simpa only [hG] using operatorTraceNorm_reserve_interpolation hR hcB hB htB hθ

end VacuumBellSeparation.Gaussian
