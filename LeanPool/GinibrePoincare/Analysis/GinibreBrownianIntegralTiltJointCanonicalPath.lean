/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltJointCanonicalPath.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltKilledOriginalLaw
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathElement
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianStateTransitionKernel

/-!
# Ginibre Brownian integral tilt joint canonical path

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreCanonicalJointHorizonPath_collisionFree`,
`ginibreBrownian_original_joint_killed_compact_path_law_all_initial`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance jointCanonicalPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance jointCanonicalPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance jointCanonicalFullPathMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) :=
    borel _
local instance jointCanonicalFullPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

/-- Joint compact restriction of the actual globally normalized canonical
original solution, including its specified constant fallback on nonglobal inputs. -/
def ginibreCanonicalJointHorizonPath {n : ℕ} (α : ℝ) (T : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ⟨fun t => ginibreDrivenGlobalPathElement α p t.val,
    (ginibreDrivenGlobalPathElement α p).continuous.comp continuous_subtype_val⟩

theorem ginibreCanonicalJointHorizonPath_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) (T : ℝ≥0) :
    Measurable (ginibreCanonicalJointHorizonPath (n := n) α T) := by
  let : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  exact (continuous_eval_const t.val).measurable.comp (ginibreDrivenGlobalPathElement_measurable hn
      α)

theorem ginibreCanonicalJointHorizonPath_apply_of_global {n : ℕ} (α : ℝ) (T : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n)
    (hTop : ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    ginibreCanonicalJointHorizonPath α T p t=
      ginibreDrivenMaximalValue n α p.2.val p.1.val t.val.toNNReal := by
  change ginibreDrivenGlobalPathElement α p t.val=_
  rw [ginibreDrivenGlobalPathElement, dite_eq_left hTop]
  rfl

@[simp] theorem ginibreCanonicalJointHorizonPath_initial {n : ℕ} (α : ℝ) (T : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    ginibreCanonicalJointHorizonPath α T p ⟨0, ⟨le_rfl, T.property⟩⟩=p.1.val := by
  classical
  by_cases hTop : ginibreDrivenMaximalLifetime n α p.2.val p.1.val=⊤
  · rw [ginibreCanonicalJointHorizonPath_apply_of_global α T p hTop]
    have hAlive : (0 : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α p.2.val p.1.val := by rw [hTop]; simp
    simpa [ginibreDrivenMaximalPath] using (ginibreDrivenMaximalPath_segment 0 hAlive).2.1
  · change ginibreDrivenGlobalPathElement α p 0=p.1.val
    rw [ginibreDrivenGlobalPathElement, dite_eq_right hTop]
    rfl

theorem ginibreCanonicalJointHorizonPath_collisionFree {n : ℕ} (α : ℝ) (T : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n)
    (t : Icc (0 : ℝ) (T : ℝ)) : CollisionFree (ginibreCanonicalJointHorizonPath α T p t) := by
  classical
  by_cases hTop : ginibreDrivenMaximalLifetime n α p.2.val p.1.val=⊤
  · rw [ginibreCanonicalJointHorizonPath_apply_of_global α T p hTop]
    exact ginibreDrivenMaximalValue_collisionFree α p.2 p.1 t.val.toNNReal
  · change CollisionFree (ginibreDrivenGlobalPathElement α p t.val)
    rw [ginibreDrivenGlobalPathElement, dite_eq_right hTop]
    exact p.1.property

theorem ginibreCanonicalJointHorizonPath_ae_eq_compact {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (fun ω => ginibreCanonicalJointHorizonPath α T (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B
        α ω))=ᵐ[P]
      ginibreCanonicalCompactPath n α z T (fun ω => (ginibreBrownianFullContinuousNoise n B α
          ω).val) := by
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
  have htop : ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z=⊤
      := hω
  have hAlive : (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B
      α ω).val z := by
    rw [htop]
    exact ENNReal.coe_lt_top
  apply ContinuousMap.ext
  intro t
  exact (ginibreCanonicalJointHorizonPath_apply_of_global α T
    (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω) htop t).trans
      (ginibreCanonicalCompactPath_apply_of_alive n α z T
        (fun ω => (ginibreBrownianFullContinuousNoise n B α ω).val) ω hAlive t).symm

theorem ginibreBrownian_original_joint_killed_compact_path_law {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    (P.map (fun ω => ginibreCanonicalJointHorizonPath α T
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω))).restrict
        (ginibreHamiltonianCompactSurvival n T R)=
    (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
      ginibreHamiltonianKilledOUActionWeight n α T R T.property
        (ginibreHamiltonianOUReferenceHorizon n α z B T ω)))).map
          (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
  rw [Measure.map_congr (ginibreCanonicalJointHorizonPath_ae_eq_compact hn α z hz B P hB hind T)]
  exact ginibreBrownian_original_killed_compact_path_law hn B P hB hind α z hz R hR T hT

theorem ginibreBrownian_original_joint_killed_compact_path_law_all_initial {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (T : ℝ≥0) (hT : 0 < T) :
    (P.map (fun ω => ginibreCanonicalJointHorizonPath α T
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω))).restrict
        (ginibreHamiltonianCompactSurvival n T R)=
    (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
      ginibreHamiltonianKilledOUActionWeight n α T R T.property
        (ginibreHamiltonianOUReferenceHorizon n α z B T ω)))).map
          (ginibreHamiltonianOUReferenceHorizon n α z B T) := by
  classical
  by_cases hR : ginibreHamiltonian n z<R
  · exact ginibreBrownian_original_joint_killed_compact_path_law hn B P hB hind α z hz R hR T hT
  · have hznot : z∉ginibreHamiltonianOUSublevelDomain n R := by
      intro h
      change Real.exp (-R)<ginibreWeight n z at h
      rw [← ginibreHamiltonian_exp_neg z hz] at h
      exact hR (neg_lt_neg_iff.mp (Real.exp_lt_exp.mp h))
    let G := ginibreHamiltonianCompactSurvival n (T : ℝ) R
    let X := fun ω => ginibreCanonicalJointHorizonPath α T (⟨z, hz⟩,
        ginibreBrownianFullContinuousNoise n B α ω)
    let O := ginibreHamiltonianOUReferenceHorizon n α z B T
    have hG : MeasurableSet G := ginibreHamiltonianCompactSurvival_measurableSet n T R
    have hXm : Measurable X := (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
      (measurable_const.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
    have hXnot (ω : Ω) : X ω∉G := by
      intro h
      have hh := h ⟨0, ⟨le_rfl, T.property⟩⟩
      rw [ginibreCanonicalJointHorizonPath_initial] at hh
      exact hznot hh
    have hOnot (ω : Ω) : O ω∉G := by
      intro h
      have hh := h ⟨0, ⟨le_rfl, T.property⟩⟩
      change ginibreHamiltonianOUReferenceProcess n α z B (0 : ℝ).toNNReal
          ω∈ginibreHamiltonianOUSublevelDomain n R at hh
      simp only [Real.toNNReal_zero] at hh
      rw [ginibreHamiltonianOUReferenceProcess_zero] at hh
      exact hznot hh
    have hOrigZero : (P.map X).restrict G=0 := by
      have hpre : X ⁻¹' G=∅ := by
        ext ω
        exact iff_false_intro (hXnot ω)
      rw [Measure.restrict_map hXm hG, hpre, Measure.restrict_empty, Measure.map_zero]
    have hDensityZero : (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n z)*
      ginibreHamiltonianKilledOUActionWeight n α T R T.property (O ω)))=0 := by
      funext ω
      have hm : O ω∉ginibreHamiltonianCompactSurvival n T R := hOnot ω
      simp only [ginibreHamiltonianKilledOUActionWeight, indicator_of_notMem hm, mul_zero,
          ENNReal.ofReal_zero, Pi.zero_apply]
    rw [hOrigZero, hDensityZero, withDensity_zero, Measure.map_zero]

end
end GinibrePoincare
