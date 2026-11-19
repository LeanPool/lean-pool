/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalEquilibriumFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumPaths

/-!
# Brownian orthogonal equilibrium factorization

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibre_equilibrium_center_relative_paths_independent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalEquilibriumFactorization57 :
    MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- Almost sure center factorization of the shared path constructor started from any
initial law `ν` that is almost surely collision-free. -/
theorem ginibre_independentInitial_path_center {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[ν.prod P]
      (fun p => ginibreOUPathElement n α
        (coordinateSum p.1, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α
            p.2))) := by
  classical
  have hS := (ginibrePathCenter_measurable n).comp
    (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  have hU := (ginibreOUPathElement_measurable n α).comp
    (((measurable_coordinateSum n).comp measurable_fst).prodMk
      (((ginibreContinuousNoiseCenter_continuous n).measurable.comp
        (ginibreBrownianFullContinuousNoise_measurable n B P hB α)).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hS hU)).mpr
  filter_upwards [hν] with z hz
  have hv : ginibreFreeInitialVersion z₀ hz₀ z = ⟨z, hz⟩ := by
    simp [ginibreFreeInitialVersion, hz]
  simpa only [Function.comp_def, ginibreEquilibriumPath, hv] using
    ginibreBrownian_global_path_center hn α z hz B P hB hind

/-- Almost sure relative factorization of the shared path constructor started from any
initial law `ν` that is almost surely collision-free. -/
theorem ginibre_independentInitial_path_recenter {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[ν.prod P] ginibreRelativeEquilibriumPath α z₀ hz₀ B := by
  classical
  have hS := (ginibrePathRecenter_measurable n).comp
    (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  have hU := ginibreRelativeEquilibriumPath_measurable hn α z₀ hz₀ B P hB
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hS hU)).mpr
  filter_upwards [hν] with z hz
  have hv : ginibreFreeInitialVersion z₀ hz₀ z = ⟨z, hz⟩ := by
    simp [ginibreFreeInitialVersion, hz]
  have hw : ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
      (recenteredConfiguration n z) = ⟨recenteredConfiguration n z, collisionFree_recentered hz⟩ :=
          by
    simp [ginibreFreeInitialVersion, collisionFree_recentered hz]
  simpa only [Function.comp_def, ginibreEquilibriumPath, ginibreRelativeEquilibriumPath, hv, hw]
      using
    ginibreBrownian_global_path_recenter hn α z hz B P hB hind

/-- Almost sure center factorization for the actual equilibrium-initialized path. -/
theorem ginibre_equilibrium_path_center {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[(ginibreMeasure n).prod P]
      (fun p => ginibreOUPathElement n α
        (coordinateSum p.1, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α
            p.2))) :=
  ginibre_independentInitial_path_center hn _ (ginibre_ae_collisionFree n hn) α z₀ hz₀ B P hB
    hind

/-- Almost sure relative factorization for the actual equilibrium-initialized path. -/
theorem ginibre_equilibrium_path_recenter {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[(ginibreMeasure n).prod P] ginibreRelativeEquilibriumPath α z₀ hz₀ B :=
  ginibre_independentInitial_path_recenter hn _ (ginibre_ae_collisionFree n hn) α z₀ hz₀ B P hB
    hind

/-- Independence of the entire center and relative paths initialized from the
 actual Ginibre measure and driven by the original independent Brownian family. -/
theorem ginibre_equilibrium_center_relative_paths_independent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B
        p))
      (fun p => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      ((ginibreMeasure n).prod P) :=
  (ginibre_equilibrium_OU_relative_functionals_independent hn α z₀ hz₀ B P hB hind).congr
    (ginibre_equilibrium_path_center hn α z₀ hz₀ B P hB hind).symm
    (ginibre_equilibrium_path_recenter hn α z₀ hz₀ B P hB hind).symm

end
end GinibrePoincare
