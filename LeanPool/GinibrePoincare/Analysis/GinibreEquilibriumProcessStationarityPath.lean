/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEquilibriumProcessStationarityPath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEquilibriumProcessStationarityJoint

/-!
# Ginibre equilibrium process stationarity path

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownian_equilibrium_original_whole_future_stationary`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance ginibreStationarityRealPathMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n)
    := borel _
local instance ginibreStationarityRealPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ≥0, Configuration n)`. -/
local instance ginibreStationarityPositivePathMeasurable (n : ℕ) : MeasurableSpace C(ℝ≥0,
    Configuration n) := borel _
local instance ginibreStationarityPositivePathBorel (n : ℕ) : BorelSpace C(ℝ≥0, Configuration n) :=
    ⟨rfl⟩

/-- The canonical global driven path `ginibreDrivenGlobalPathElement α p` restricted to
nonnegative times. -/
def ginibreCanonicalPositivePath {n : ℕ} (α : ℝ)
    (p : {z : Configuration n // CollisionFree z } × GinibreContinuousNoise n) : C(ℝ≥0,
        Configuration
        n)
        :=
  (ginibreDrivenGlobalPathElement α p).comp ⟨fun t=>(t : ℝ), continuous_subtype_val⟩

/-- The nonnegative-time canonical path started from the collision-free version of `p.1` and
driven by the Brownian noise of `B` at the sample `p.2`. -/
def ginibreEquilibriumPositivePath {Ω : Type*} {n : ℕ} (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (p : Configuration n × Ω) : C(ℝ≥0, Configuration n) :=
  ginibreCanonicalPositivePath α (ginibreStationaryFreeInitial n p.1,
    ginibreBrownianFullContinuousNoise n B α p.2)

/-- The path `ginibreEquilibriumPositivePath α B p` shifted in time by `s`, i.e.
`t ↦ X (s + t)`. -/
def ginibreEquilibriumShiftedPositivePath {Ω : Type*} {n : ℕ} (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (p : Configuration n × Ω) : C(ℝ≥0, Configuration
        n) :=
  (ginibreEquilibriumPositivePath α B p).comp ⟨fun t=>s+t, continuous_const.add continuous_id⟩

theorem ginibreCanonicalPositivePath_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) :
    Measurable (ginibreCanonicalPositivePath (n:=n) α) :=
  (ContinuousMap.continuous_precomp _).measurable.comp
    (ginibreDrivenGlobalPathElement_measurable hn α)

theorem ginibreEquilibriumPositivePath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreEquilibriumPositivePath α B) :=
  (ginibreCanonicalPositivePath_measurable hn α).comp
    (((ginibreStationaryFreeInitial_measurable n).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreEquilibriumShiftedPositivePath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) (s : ℝ≥0) :
    Measurable (ginibreEquilibriumShiftedPositivePath α B s) :=
  (ContinuousMap.continuous_precomp _).measurable.comp
    (ginibreEquilibriumPositivePath_measurable hn α B P hB)

theorem ginibreEquilibriumPositivePath_restart_ae {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hiB : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) :
    ginibreEquilibriumShiftedPositivePath α B s =ᵐ[(ginibreMeasure n).prod P]
      (fun p=>ginibreCanonicalPositivePath α (ginibreStationaryCurrentState α B s p,
        ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hiB s).1
  have hF := ginibreEquilibriumShiftedPositivePath_measurable hn α B P hB s
  have hG : Measurable (fun p : Configuration n×Ω=>ginibreCanonicalPositivePath α
      (ginibreStationaryCurrentState α B s p,
        ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) :=
    (ginibreCanonicalPositivePath_measurable hn α).comp
      ((ginibreStationaryCurrentState_measurable hn α B P hB s).prodMk
        ((ginibreBrownianFullContinuousNoise_measurable n _ P hBs α).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).mpr
  apply Filter.Eventually.of_forall
  intro z
  let x := ginibreStationaryFreeInitial n z
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α x.val x.property B P hB hiB,
    ginibreBrownianMaximalProcess_canonical_restart hn α x.val x.property B P hB hiB s]
    with ω hL hr
  have hL' : ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω).val
      (ginibreStationaryCurrentState α B s (z, ω)).val=⊤ := by
    simpa [ginibreStationaryCurrentState, ginibreBrownianStateProcess,
      ginibreCanonicalStateValue, ginibreBrownianMaximalProcess, x] using hr.1
  apply ContinuousMap.ext
  intro t
  change ginibreDrivenGlobalPathElement (α : ℝ) (ginibreStationaryFreeInitial n z,
      ginibreBrownianFullContinuousNoise n B α ω) ((s + t : ℝ≥0) : ℝ) =
    ginibreDrivenGlobalPathElement (α : ℝ) (ginibreStationaryCurrentState α B s (z, ω),
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω) (t : ℝ)
  simp only [ginibreDrivenGlobalPathElement, show ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n B α ω).val (ginibreStationaryFreeInitial n z).val=⊤
          from hL,
    hL', dite_eq_left, ContinuousMap.coe_mk]
  simpa [ginibreStationaryCurrentState, ginibreBrownianStateProcess,
    ginibreCanonicalStateValue, ginibreBrownianMaximalProcess, x] using (hr.2 t).symm

theorem ginibreEquilibriumPositivePath_shift_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hiB : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) :
    ((ginibreMeasure n).prod P).map (ginibreEquilibriumShiftedPositivePath α B s)=
      ((ginibreMeasure n).prod P).map (ginibreEquilibriumPositivePath α B) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hiB s).1
  have hJ := ginibreStationaryCurrentState_future_noise_joint_law hn α B P hB hiB s
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hNs := ginibreBrownianFullContinuousNoise_measurable n (brownianFamilyShift B s) P hBs α
  have hpair : Measurable (fun p : Configuration n×Ω=>(ginibreStationaryCurrentState α B s p,
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) :=
    (ginibreStationaryCurrentState_measurable hn α B P hB s).prodMk (hNs.comp measurable_snd)
  rw [Measure.map_congr (ginibreEquilibriumPositivePath_restart_ae hn α B P hB hiB s)]
  change ((ginibreMeasure n).prod P).map
    (ginibreCanonicalPositivePath α ∘ (fun p=>(ginibreStationaryCurrentState α B s p,
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)))=_
  rw [← Measure.map_map (ginibreCanonicalPositivePath_measurable hn α) hpair, hJ,
    Measure.map_prod_map (ginibreMeasure n) P (ginibreStationaryFreeInitial_measurable n) hN,
    Measure.map_map (ginibreCanonicalPositivePath_measurable hn α)
      ((ginibreStationaryFreeInitial_measurable n).prodMap hN)]
  rfl

theorem ginibreEquilibriumPositivePath_eq_original_ae {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hiB : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ p : Configuration n×Ω ∂(ginibreMeasure n).prod P,∀t : ℝ≥0,
      ginibreEquilibriumPositivePath α B p t=ginibreBrownianMaximalProcess n α p.1 B t p.2 := by
  filter_upwards [ginibre_equilibrium_path_eq_original hn α (ginibreCollisionFreeDefault n).val
    (ginibreCollisionFreeDefault n).property B P hB hiB] with p hp
  intro t
  have h := hp (t : ℝ)
  rw [Real.toNNReal_coe] at h
  exact h

theorem ginibreBrownian_equilibrium_original_finite_dimensional_stationary
    {Ω ι : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) (t : ι → ℝ≥0) :
    ((ginibreMeasure n).prod P).map
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (s+t i) p.2)=
    ((ginibreMeasure n).prod P).map
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (t i) p.2) := by
  have h := ginibreEquilibriumPositivePath_shift_law hn α B P hB hiB s
  have hEval : Measurable (fun X : C(ℝ≥0, Configuration n)=>fun i=>X (t i)) :=
    Measurable.of_eval (fun i=>(continuous_eval_const _).measurable)
  have hmS := ginibreEquilibriumShiftedPositivePath_measurable hn α B P hB s
  have hm := ginibreEquilibriumPositivePath_measurable hn α B P hB
  have hh := congrArg (fun ν : Measure C(ℝ≥0, Configuration n)=>ν.map
    (fun X=>fun i=>X (t i))) h
  rw [Measure.map_map hEval hmS, Measure.map_map hEval hm] at hh
  have heS : (fun p : Configuration n×Ω=>fun i=>ginibreEquilibriumShiftedPositivePath α B s p (t
      i))=ᵐ[(ginibreMeasure n).prod P]
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (s+t i) p.2) := by
    filter_upwards [ginibreEquilibriumPositivePath_eq_original_ae hn α B P hB hiB] with p hp
    funext i
    exact hp (s+t i)
  have he : (fun p : Configuration n×Ω=>fun i=>ginibreEquilibriumPositivePath α B p (t
      i))=ᵐ[(ginibreMeasure n).prod P]
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (t i) p.2) := by
    filter_upwards [ginibreEquilibriumPositivePath_eq_original_ae hn α B P hB hiB] with p hp
    funext i
    exact hp (t i)
  exact (Measure.map_congr heS).symm.trans (hh.trans (Measure.map_congr he))

theorem ginibreBrownian_equilibrium_original_whole_future_stationary
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) :
    ((ginibreMeasure n).prod P).map
      (fun p=>fun t : ℝ≥0=>ginibreBrownianMaximalProcess n α p.1 B (s+t) p.2)=
    ((ginibreMeasure n).prod P).map
      (fun p=>fun t : ℝ≥0=>ginibreBrownianMaximalProcess n α p.1 B t p.2) :=
  ginibreBrownian_equilibrium_original_finite_dimensional_stationary hn α B P hB hiB s id

end
end GinibrePoincare
