/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRenyiInterpolation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Finite interpolation with semidefinite input

Mixing the positive input with the strictly positive reference preserves
the trace bound and gives a strictly positive input. Actual matrix-norm
continuity, including positive-power CFC at singular semidefinite matrices,
then proves the same interpolation inequality in the limit epsilon->0+.
No injectivity of the input or uniform bound on its inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter Set
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite reference mixture given by `(1 / (1 + ε)) • ρ + (ε / (1 + ε)) • σ`. -/
def finiteReferenceMixture (ρ σ : Matrix ι ι ℂ) (ε : ℝ) : Matrix ι ι ℂ :=
  (1 / (1 + ε)) • ρ + (ε / (1 + ε)) • σ

omit [Fintype ι] [DecidableEq ι] in
theorem finiteReferenceMixture_posDef {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) {ε : ℝ} (hε : 0 < ε) :
    (finiteReferenceMixture ρ σ ε).PosDef := by
  have hd : 0 < 1 + ε := by linarith
  exact Matrix.PosDef.posSemidef_add (hρ.smul (one_div_pos.mpr hd).le)
    (hσ.smul (div_pos hε hd))

omit [DecidableEq ι] in
theorem finiteReferenceMixture_trace (ρ σ : Matrix ι ι ℂ) (ε : ℝ) :
    (finiteReferenceMixture ρ σ ε).trace.re =
      (1 / (1 + ε)) * ρ.trace.re + (ε / (1 + ε)) * σ.trace.re := by
  change Complex.reCLM (finiteReferenceMixture ρ σ ε).trace = _
  rw [finiteReferenceMixture, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    map_add, map_smul, map_smul]
  rfl

omit [DecidableEq ι] in
theorem finiteReferenceMixture_trace_le {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.trace.re ≤ 1) (hσ : σ.trace.re ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (finiteReferenceMixture ρ σ ε).trace.re ≤ 1 := by
  have hd : 0 < 1 + ε := by linarith
  rw [finiteReferenceMixture_trace]
  calc
    _ ≤ (1 / (1 + ε)) * 1 + (ε / (1 + ε)) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hρ (one_div_pos.mpr hd).le)
        (mul_le_mul_of_nonneg_left hσ (div_nonneg hε hd.le))
    _ = 1 := by field_simp [hd.ne']

omit [Fintype ι] [DecidableEq ι] in
theorem finiteReferenceMixture_tendsto (ρ σ : Matrix ι ι ℂ) :
    Tendsto (finiteReferenceMixture ρ σ) (𝓝[>] (0 : ℝ)) (𝓝 ρ) := by
  have hc : ContinuousAt (finiteReferenceMixture ρ σ) (0 : ℝ) := by
    unfold finiteReferenceMixture
    fun_prop (disch := norm_num)
  simpa only [finiteReferenceMixture, add_zero, div_one, one_smul, zero_smul] using
    hc.tendsto.mono_left nhdsWithin_le_nhds

theorem continuousOn_positiveMatrix_rpow {p : ℝ} (hp : 0 < p) :
    ContinuousOn (fun A : Matrix ι ι ℂ => A ^ p) {A | 0 ≤ A} := by
  have h := CFC.continuousOn_nnrpow (A := Matrix ι ι ℂ) (NNReal.mk p hp.le : ℝ≥0)
  have hpow (T : Matrix ι ι ℂ) : T ^ (NNReal.mk p hp.le : NNReal) = T ^ p :=
    CFC.nnrpow_eq_rpow (a := T) (show (0 : NNReal) < NNReal.mk p hp.le from hp)
  simpa only [hpow] using h

theorem tendsto_positiveMatrix_power_trace {α : Type*} {l : Filter α}
    {A : α → Matrix ι ι ℂ} {B : Matrix ι ι ℂ} (hB : B.PosSemidef)
    (hlim : Tendsto A l (𝓝 B)) (hA : ∀ᶠ x in l, (A x).PosSemidef)
    {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x => ((A x) ^ p).trace.re) l (𝓝 (B ^ p).trace.re) := by
  have hw : Tendsto A l (𝓝[{X : Matrix ι ι ℂ | 0 ≤ X}] B) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hA.mono fun _ h => h.nonneg⟩
  have hpow : Tendsto (fun x => (A x) ^ p) l (𝓝 (B ^ p)) :=
    Filter.Tendsto.comp (continuousOn_positiveMatrix_rpow hp B hB.nonneg) hw
  have hc : Continuous (fun X : Matrix ι ι ℂ => X.trace.re) := by
    unfold Matrix.trace
    fun_prop
  exact (hc.tendsto _).comp hpow

theorem finiteRenyiSandwich_posSemidef {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (τ : ℝ) : (finiteRenyiSandwich ρ σ τ).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact conjugate_nonneg_of_nonneg hρ.nonneg CFC.rpow_nonneg

theorem finiteRenyiSandwich_referenceMixture_tendsto (ρ σ : Matrix ι ι ℂ) (τ : ℝ) :
    Tendsto (fun ε => finiteRenyiSandwich (finiteReferenceMixture ρ σ ε) σ τ)
      (𝓝[>] (0 : ℝ)) (𝓝 (finiteRenyiSandwich ρ σ τ)) := by
  exact (tendsto_const_nhds.mul (finiteReferenceMixture_tendsto ρ σ)).mul tendsto_const_nhds

/-- The finite comparison needed for reference spectral compressions,
with semidefinite input and both genuine compression trace bounds. -/
theorem finite_semidefinite_sandwichedRenyi_interpolation {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) (hρt : ρ.trace.re ≤ 1) (hσt : σ.trace.re ≤ 1)
    {r : ℝ} (hr : 2 ≤ r) :
    ((finiteRenyiSandwich ρ σ (1 / 2)) ^ (2 : ℝ)).trace.re ≤
      ((finiteRenyiSandwich ρ σ ((r - 1) / r)) ^ r).trace.re ^ (1 / (r - 1)) := by
  have hr₀ : 0 < r := by linarith
  have he : 0 < 1 / (r - 1) := one_div_pos.mpr (by linarith)
  have hm : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (finiteReferenceMixture ρ σ ε).PosDef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact finiteReferenceMixture_posDef hρ hσ hε
  have htwo := tendsto_positiveMatrix_power_trace (finiteRenyiSandwich_posSemidef hρ (1 / 2))
    (finiteRenyiSandwich_referenceMixture_tendsto ρ σ (1 / 2))
    (hm.mono fun ε h => (finiteRenyiSandwich_posDef h hσ (1 / 2)).posSemidef)
    (by norm_num : (0 : ℝ) < 2)
  have hhigh := tendsto_positiveMatrix_power_trace
    (finiteRenyiSandwich_posSemidef hρ ((r - 1) / r))
    (finiteRenyiSandwich_referenceMixture_tendsto ρ σ ((r - 1) / r))
    (hm.mono fun ε h => (finiteRenyiSandwich_posDef h hσ ((r - 1) / r)).posSemidef) hr₀
  apply le_of_tendsto_of_tendsto htwo
    (((Real.continuous_rpow_const he.le).tendsto _).comp hhigh)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact finite_sandwichedRenyi_interpolation (finiteReferenceMixture_posDef hρ hσ hε) hσ
    (finiteReferenceMixture_trace_le hρt hσt hε.le) hr

end VacuumBellSeparation.Gaussian
