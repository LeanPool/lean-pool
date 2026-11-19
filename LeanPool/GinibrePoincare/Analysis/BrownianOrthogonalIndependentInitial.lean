/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalIndependentInitial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumOriginal

/-! # Whole-path independence for independent initial projections

The initial probability law `ν` is collision-free almost everywhere, and
its center and relative projections are assumed independent. The sampling
measure is `ν.prod P`, so initial state and original Brownian noise are
independent as well. Gaussian orthogonality gives independence of the
center and relative noise paths.

First combine these facts into independence of the two input pairs:
(initial center, center noise) and (initial relative state, relative noise).
Compose with the measurable OU and relative solution maps. The next two
lemmas identify these functionals almost everywhere with the projected
original path; independence transfers through those equalities. A further
identity compares the continuous path version with the maximal process on
one full-measure event for every time.

Names containing `EquilibriumPath` designate the shared path constructor;
the main results here allow any `ν` satisfying the stated projection and
collision conditions. The fixed free state `z₀` defines that constructor
on exceptional initial states and does not restrict `ν` to equilibrium. -/

@[expose] public section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance independentInitialConfigurationPathSpace (n : ℕ) : MeasurableSpace C(ℝ, Configuration
    n) := borel _
local instance independentInitialConfigurationPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n)
    := ⟨rfl⟩
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance independentInitialCenterPathSpace : MeasurableSpace C(ℝ, ℂ) := borel _
local instance independentInitialCenterPathBorel : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The actual Ginibre initial center and its Brownian noise are independent of
 the actual initial relative configuration and its entire relative noise path. -/
theorem ginibre_independentInitial_center_relative_inputs_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) [IsProbabilityMeasure
        ν]
    (_ : ∀ᵐ z ∂ν, CollisionFree z)
    (hνind : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) :
    IndepFun
      (fun p => (coordinateSum p.1,
        ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      (fun p => (recenteredConfiguration n p.1,
        ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      (ν.prod P) := by
  
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  apply independent_pairs_on_product_measure ν P
    (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n)
    (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
    (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω))
  · convert (coordinateSumCLM n).continuous.measurable using 1
    funext z
    exact (coordinateSumCLM_apply n z).symm
  · convert (recenteredCLM n).continuous.measurable using 1
    funext z
    exact (recenteredCLM_apply n z).symm
  · exact (ginibreContinuousNoiseCenter_continuous n).measurable.comp hN
  · exact (ginibreContinuousNoiseRecenter_continuous n).measurable.comp hN
  · exact hνind
  · exact brownianFamily_actual_continuous_center_recenter_noise_independent hn B P hB hind α

/-- The equilibrium-initialized center and relative canonical functionals are independent. -/
theorem ginibre_independentInitial_OU_relative_functionals_independent {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (hνind : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ)
        (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibreOUPathElement n α
      (coordinateSum p.1, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α
          p.2)))
      (ginibreRelativeEquilibriumPath α z₀ hz₀ B) (ν.prod P) := by
  have hrel : Measurable (fun p : Configuration n × GinibreContinuousNoise n =>
      ginibreDrivenGlobalPathElement α
        (ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
            p.1, p.2)) :=
    (ginibreDrivenGlobalPathElement_measurable hn α).comp
      (((ginibreFreeInitialVersion_measurable _ _).comp measurable_fst).prodMk measurable_snd)
  exact (ginibre_independentInitial_center_relative_inputs_independent hn ν hν hνind B P hB hind
      α).comp
    (ginibreOUPathElement_measurable n α) hrel

/-- Almost sure center factorization for the actual equilibrium-initialized path. -/
theorem ginibre_independentInitial_path_center {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n))
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (_ : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ≥0) (z₀
        : Configuration n) (hz₀ : CollisionFree z₀)
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

/-- Almost sure relative factorization for the actual equilibrium-initialized path. -/
theorem ginibre_independentInitial_path_recenter {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n))
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (_ : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ≥0) (z₀
        : Configuration n) (hz₀ : CollisionFree z₀)
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

/-- Independence of the entire center and relative paths initialized from the
 actual Ginibre measure and driven by the original independent Brownian family. -/
theorem ginibre_independentInitial_center_relative_paths_independent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (hνind : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ≥0)
        (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B
        p))
      (fun p => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      (ν.prod P) :=
  (ginibre_independentInitial_OU_relative_functionals_independent hn ν hν hνind α z₀ hz₀ B P hB
      hind).congr
    (ginibre_independentInitial_path_center hn ν hν hνind α z₀ hz₀ B P hB hind).symm
    (ginibre_independentInitial_path_recenter hn ν hν hνind α z₀ hz₀ B P hB hind).symm

/-- The equilibrium path version agrees at every time with the original canonical
 Brownian solution initialized from the actual Ginibre sample. -/
theorem ginibre_independentInitial_path_eq_original {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n))
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (_ : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ≥0) (z₀
        : Configuration n) (hz₀ : CollisionFree z₀)
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
    exact (hν).mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hL, hC] with p hL hC
  intro t
  have hv : ginibreFreeInitialVersion z₀ hz₀ p.1 = ⟨p.1, hC⟩ := by
    simp [ginibreFreeInitialVersion, hC]
  have hL' : ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α p.2).val p.1
      = ⊤ := by
    simpa only [hv] using hL
  simp only [ginibreEquilibriumPath, ginibreDrivenGlobalPathElement, hv, dite_eq_left hL',
    ContinuousMap.coe_mk, ginibreBrownianMaximalProcess]

/-- Actual original Brownian whole-process independence with initial law exactly
 Ginibre; no assumption of stationarity or stochastic factorization is used. -/
theorem ginibreBrownian_independentInitial_center_relative_processes_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (ν : Measure (Configuration n)) [IsProbabilityMeasure
        ν]
    (hν : ∀ᵐ z ∂ν, CollisionFree z)
    (hνind : IndepFun (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n) ν) (α : ℝ≥0)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => fun t : ℝ≥0 =>
      coordinateSum (ginibreBrownianMaximalProcess n α p.1 B t p.2))
      (fun p => fun t : ℝ≥0 => recenteredConfiguration n
        (ginibreBrownianMaximalProcess n α p.1 B t p.2)) (ν.prod P) := by
  have hS : Measurable (fun X : C(ℝ, ℂ) => fun t : ℝ≥0 => X (t : ℝ)) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const (t : ℝ)).measurable
  have hW : Measurable (fun X : C(ℝ, Configuration n) => fun t : ℝ≥0 => X (t : ℝ)) := by
    apply Measurable.of_eval
    intro t
    exact (continuous_eval_const (t : ℝ)).measurable
  have h := (ginibre_independentInitial_center_relative_paths_independent hn ν hν hνind α z₀ hz₀ B P
      hB hind).comp hS hW
  apply h.congr
  · filter_upwards [ginibre_independentInitial_path_eq_original hn ν hν hνind α z₀ hz₀ B P hB hind]
      with p hp
    funext t
    simp only [Function.comp_def, ginibrePathCenter, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      coordinateSumCLM_apply, hp, Real.toNNReal_coe]
  · filter_upwards [ginibre_independentInitial_path_eq_original hn ν hν hνind α z₀ hz₀ B P hB hind]
      with p hp
    funext t
    simp only [Function.comp_def, ginibrePathRecenter, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk,
      recenteredCLM_apply, hp, Real.toNNReal_coe]

end
end GinibrePoincare
