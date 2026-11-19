/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOriginalEquilibriumMarginals.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOriginalEquilibriumReversal

/-!
# Ginibre Hamiltonian original equilibrium marginals

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalEquilibriumPathLaw_joint_endpoint_swap`,
`ginibreOriginalEquilibriumPathLaw_isProbability`,
`ginibreOriginalEquilibriumPathLaw_initial_preserving`,
`ginibreOriginalEquilibriumPathLaw_terminal_preserving`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreOriginalMarginalsPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreOriginalMarginals_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

theorem ginibreOriginalEquilibriumPathLaw_initial {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => x ⟨0, ⟨le_rfl, T.property⟩⟩) = ginibreMeasure n := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let w := fun x : (((Fin n × Fin 2) → ℝ) × Ω) => vandermondeDensity
      (ginibreHamiltonianOUCoordinateAssembly n x.1)
  let C := ginibreGaussianInitialOriginalPath n α T B
  let A := fun x : (((Fin n × Fin 2) → ℝ) × Ω) => ginibreHamiltonianOUCoordinateAssembly n x.1
  have hC := ginibreGaussianInitialOriginalPath_measurable hn α T B P hB
  have hA : Measurable A := (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp
      measurable_fst
  have hw : Measurable w := measurable_vandermondeDensity.comp hA
  have hCFν : ∀ᵐ x ∂ν, CollisionFree (A x) :=
    (measurePreserving_fst (μ := γ) (ν := P)).quasiMeasurePreserving.ae
      (ginibreGaussian_coordinates_collisionFree_ae hn)
  have hAC : ν.withDensity w ≪ ν := withDensity_absolutelyContinuous ν w
  have hCFρ : ∀ᵐ x ∂ν.withDensity w, CollisionFree (A x) :=
    hAC.ae_le hCFν
  have hEq : (fun x => (C x) ⟨0, ⟨le_rfl, T.property⟩⟩) =ᵐ[ν.withDensity w] A := by
    filter_upwards [hCFρ] with x hx
    change (ginibreCanonicalJointHorizonPath α T
      (ginibreInitialCollisionNormalize n (A x), ginibreBrownianFullContinuousNoise n B α x.2)) ⟨0,
          ⟨le_rfl, T.property⟩⟩ = A x
    rw [ginibreCanonicalJointHorizonPath_initial, ginibreInitialCollisionNormalize_of_free _ hx]
  have hInit := ginibre_completed_initial_noise_initial_law hn P
  dsimp only at hInit
  change ((ginibreNormalizingMass n)⁻¹ • ν.completion.withDensity
    (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν => w x)).map
      (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν => A x) = ginibreMeasure n at hInit
  rw [Measure.map_smul, ginibre_completion_weighted_map ν A hA w hw] at hInit
  swap
  · exact hA.nullMeasurable.measurable'.aemeasurable
  unfold ginibreOriginalEquilibriumPathLaw
  rw [Measure.map_smul _ (continuous_eval_const _).measurable.aemeasurable,
    Measure.map_map (continuous_eval_const _).measurable hC]
  change (ginibreNormalizingMass n)⁻¹ • (ν.withDensity w).map (fun x => (C x) ⟨0, ⟨le_rfl,
      T.property⟩⟩) = _
  rw [Measure.map_congr hEq]
  exact hInit

/-- Full actual original equilibrium path reversal, including the zero horizon. -/
theorem ginibreOriginalEquilibriumPathLaw_reverse_all_horizons {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      ginibreOriginalEquilibriumPathLaw n α T P B := by
  by_cases ht : T = 0
  · subst T
    let : MeasurableSpace C(Icc (0 : ℝ) (0 : ℝ), Configuration n) := borel _
    let : BorelSpace C(Icc (0 : ℝ) (0 : ℝ), Configuration n) := ⟨rfl⟩
    have he : (fun x : C(Icc (0 : ℝ) (0 : ℝ), Configuration n) =>
        x.comp (ginibreHamiltonianCompactReverseTime 0 (le_rfl : (0 : ℝ) ≤ 0))) = id := by
      funext x
      ext t j
      change x ((ginibreHamiltonianCompactReverseTime 0 (le_rfl : (0 : ℝ) ≤ 0)) t) j = x t j
      have hh : (ginibreHamiltonianCompactReverseTime 0 (le_rfl : (0 : ℝ) ≤ 0)) t = t := by
        apply Subtype.ext
        change 0-t.val=t.val
        have hz : t.val = 0 := le_antisymm t.property.2 t.property.1
        simp [hz]
      rw [hh]
    change (ginibreOriginalEquilibriumPathLaw n α 0 P B).map
      (fun x : C(Icc (0 : ℝ) (0 : ℝ), Configuration n) => x.comp
        (ginibreHamiltonianCompactReverseTime 0 (le_rfl : (0 : ℝ) ≤ 0))) = _
    rw [he]
    exact Measure.map_id
  · exact ginibreOriginalEquilibriumPathLaw_reverse hn α P B hB hiB T (lt_of_le_of_ne (zero_le : (0
      : ℝ≥0) ≤ T) (Ne.symm ht))

/-- Actual invariance of the existing Ginibre measure under the genuine
original Brownian-driven Ginibre process, with the paper's speed. -/
theorem ginibreOriginalEquilibriumPathLaw_terminal {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => x ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩) = ginibreMeasure n := by
  rw [ginibreHamiltonian_reversal_endpoint_marginal n (T : ℝ) T.property _
    (ginibreOriginalEquilibriumPathLaw_reverse_all_horizons hn α P B hB hiB T)]
  exact ginibreOriginalEquilibriumPathLaw_initial hn α P B hB T

theorem ginibreOriginalEquilibriumPathLaw_joint_endpoint_swap {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => (x ⟨0, ⟨le_rfl, T.property⟩⟩, x ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩)) =
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => (x ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩, x ⟨0, ⟨le_rfl, T.property⟩⟩)) :=
  ginibreHamiltonian_reversal_joint_endpoint n (T : ℝ) T.property _
    (ginibreOriginalEquilibriumPathLaw_reverse_all_horizons hn α P B hB hiB T)

theorem ginibreOriginalEquilibriumPathLaw_isProbability {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (T : ℝ≥0) : IsProbabilityMeasure (ginibreOriginalEquilibriumPathLaw n α T P B) := by
  constructor
  have h := congrArg (fun μ : Measure (Configuration n) => μ Set.univ)
    (ginibreOriginalEquilibriumPathLaw_initial hn α P B hB T)
  rw [Measure.map_apply (continuous_eval_const _).measurable MeasurableSet.univ,
    Set.preimage_univ, ginibreMeasureIsProbability n hn] at h
  exact h

theorem ginibreOriginalEquilibriumPathLaw_initial_preserving {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (T : ℝ≥0) : MeasurePreserving (fun x => x ⟨0, ⟨le_rfl, T.property⟩⟩)
      (ginibreOriginalEquilibriumPathLaw n α T P B) (ginibreMeasure n) :=
  ⟨(continuous_eval_const _).measurable, ginibreOriginalEquilibriumPathLaw_initial hn α P B hB T⟩

theorem ginibreOriginalEquilibriumPathLaw_terminal_preserving {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    MeasurePreserving (fun x => x ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩)
      (ginibreOriginalEquilibriumPathLaw n α T P B) (ginibreMeasure n) :=
  ⟨(continuous_eval_const _).measurable, ginibreOriginalEquilibriumPathLaw_terminal hn α P B hB hiB
      T⟩

end
end GinibrePoincare
