/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalEquilibriumOriginal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumFactorization

/-!
# Brownian orthogonal equilibrium original

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_equilibrium_center_relative_processes_independent`.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance instBorelBrownianOrthogonalEquilibriumOriginal55 (n : ℕ) :
    MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalEquilibriumOriginal57 : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The shared path constructor agrees at every time with the original canonical
 Brownian solution, for any initial law `ν` that is almost surely collision-free. -/
theorem ginibre_independentInitial_path_eq_original {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ p : Configuration n × Ω ∂ν.prod P, ∀ t : ℝ,
      ginibreEquilibriumPath α z₀ hz₀ B p t =
        ginibreBrownianMaximalProcess n α p.1 B (Real.toNNReal t) p.2 := by
  classical
  have hm : Measurable (fun p : Configuration n × Ω =>
      (ginibreFreeInitialVersion z₀ hz₀ p.1, ginibreBrownianFullContinuousNoise n B α p.2)) :=
    ((ginibreFreeInitialVersion_measurable z₀ hz₀).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd)
  have hL : ∀ᵐ p : Configuration n × Ω ∂ν.prod P,
      ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α p.2).val
        (ginibreFreeInitialVersion z₀ hz₀ p.1).val = ⊤ := by
    apply (Measure.ae_prod_iff_ae_ae ((ginibreDriven_global_joint_measurableSet hn α).preimage
        hm)).mpr
    exact Eventually.of_forall fun z =>
      ginibreBrownianMaximalLifetime_top_ae hn α _ (ginibreFreeInitialVersion z₀ hz₀ z).property B P
          hB hind
  have hC : ∀ᵐ p : Configuration n × Ω ∂ν.prod P, CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage
        measurable_fst)).mpr
    exact hν.mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hL, hC] with p hL hC
  intro t
  have hv : ginibreFreeInitialVersion z₀ hz₀ p.1 = ⟨p.1, hC⟩ := by
    simp [ginibreFreeInitialVersion, hC]
  have hL' : ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α p.2).val p.1
      = ⊤ := by
    simpa only [hv] using hL
  simp only [ginibreEquilibriumPath, ginibreDrivenGlobalPathElement, hv, dite_eq_left hL',
    ContinuousMap.coe_mk, ginibreBrownianMaximalProcess]

/-- The equilibrium path version agrees at every time with the original canonical
 Brownian solution initialized from the actual Ginibre sample. -/
theorem ginibre_equilibrium_path_eq_original {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, ∀ t : ℝ,
      ginibreEquilibriumPath α z₀ hz₀ B p t =
        ginibreBrownianMaximalProcess n α p.1 B (Real.toNNReal t) p.2 :=
  ginibre_independentInitial_path_eq_original hn _ (ginibre_ae_collisionFree n hn) α z₀ hz₀ B P
    hB hind

/-- Actual original Brownian whole-process independence with initial law exactly
 Ginibre; no assumption of stationarity or stochastic factorization is used. -/
theorem ginibreBrownian_equilibrium_center_relative_processes_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => fun t : ℝ≥0 =>
      coordinateSum (ginibreBrownianMaximalProcess n α p.1 B t p.2))
      (fun p => fun t : ℝ≥0 => recenteredConfiguration n
        (ginibreBrownianMaximalProcess n α p.1 B t p.2)) ((ginibreMeasure n).prod P) := by
  have hS : Measurable (fun X : C(ℝ, ℂ) => fun t : ℝ≥0 => X (t : ℝ)) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const (t : ℝ)).measurable
  have hW : Measurable (fun X : C(ℝ, Configuration n) => fun t : ℝ≥0 => X (t : ℝ)) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const (t : ℝ)).measurable
  have h := (ginibre_equilibrium_center_relative_paths_independent hn α z₀ hz₀ B P hB hind).comp hS
      hW
  apply h.congr
  · filter_upwards [ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hind] with p hp
    funext t
    simp only [Function.comp_def, ginibrePathCenter, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      coordinateSumCLM_apply, hp, Real.toNNReal_coe]
  · filter_upwards [ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hind] with p hp
    funext t
    simp only [Function.comp_def, ginibrePathRecenter, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk,
      recenteredCLM_apply, hp, Real.toNNReal_coe]

end
end GinibrePoincare
