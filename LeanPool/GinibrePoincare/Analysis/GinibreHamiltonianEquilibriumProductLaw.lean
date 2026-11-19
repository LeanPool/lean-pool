/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianEquilibriumProductLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOriginalEquilibriumMarginals
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumOriginal

/-! # Equilibrium paths with independent initial state and noise

The first identity rewrites the normalized Vandermonde-weighted Gaussian
initial coordinates, together with an independent noise sample, as
`ginibreMeasure n × P`. It uses the Gaussian coordinate assembly law and
transport of the density under the assembly map.

The path-law identity then expresses the original equilibrium law as the
pushforward of that product by the canonical solution map. Collision
normalization does not affect it because the Ginibre initial state is
collision-free almost everywhere. Evaluation at the terminal time gives
the original process marginal; the final invariant-law theorem chooses a
fixed collision-free default state to discharge the auxiliary path-version
parameter. No independence assumption on initial state remains to be proved:
it is built into the product measure. -/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreEquilibriumProductPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreEquilibriumProduct_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance ginibreEquilibriumProductGlobalMeasurable (n : ℕ) :
    MeasurableSpace C(ℝ, Configuration n) := borel _
local instance ginibreEquilibriumProduct_globalBorel (n : ℕ) :
    BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

theorem ginibreGaussian_weighted_initial_noise_product {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (P : Measure Ω) [IsProbabilityMeasure P] :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    ((ginibreNormalizingMass n)⁻¹ • (γ.prod P).withDensity
      (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map
      (Prod.map (ginibreHamiltonianOUCoordinateAssembly n) id) = (ginibreMeasure n).prod P := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let A := Prod.map (ginibreHamiltonianOUCoordinateAssembly n) (id : Ω → Ω)
  have hA : Measurable A := (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.prodMap
      measurable_id
  have hw : Measurable (fun x : Configuration n × Ω => vandermondeDensity x.1) :=
    (ENNReal.measurable_ofReal.comp (contDiff_vandermondeWeight n).continuous.measurable).comp
        measurable_fst
  change ((ginibreNormalizingMass n)⁻¹ • (γ.prod P).withDensity
    ((fun x : Configuration n × Ω => vandermondeDensity x.1) ∘ A)).map A = _
  rw [Measure.map_smul _ hA.aemeasurable, ginibre_map_density_composition _ A hA _ hw]
  have hm : (γ.prod P).map A = (complexGaussianMeasure n).prod P := by
    rw [← Measure.map_prod_map γ P (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
        measurable_id,
      Measure.map_id, ginibreGaussian_coordinate_assembly_law hn]
  rw [hm]
  have hd : ((complexGaussianMeasure n).prod P).withDensity
      (fun x : Configuration n × Ω => vandermondeDensity x.1) = (rawGinibreMeasure n).prod P := by
    have hwv : Measurable (@vandermondeDensity n) :=
      ENNReal.measurable_ofReal.comp (contDiff_vandermondeWeight n).continuous.measurable
    exact (prod_withDensity_left (μ := complexGaussianMeasure n) (ν := P) hwv).symm
  rw [hd, ← Measure.prod_smul_left]
  rfl

theorem ginibreOriginalEquilibriumPathLaw_product {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (T : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    ginibreOriginalEquilibriumPathLaw n α T P B =
    ((ginibreMeasure n).prod P).map (fun p =>
      (ginibreEquilibriumPath α z₀ hz₀ B p).comp
        ⟨Subtype.val, continuous_subtype_val⟩) := by
  let F := fun p : Configuration n × Ω => ginibreCanonicalJointHorizonPath α T
    (ginibreInitialCollisionNormalize n p.1, ginibreBrownianFullContinuousNoise n B α p.2)
  have hF : Measurable F := (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
    (((ginibreInitialCollisionNormalize_measurable n).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))
  have hA : Measurable (Prod.map (ginibreHamiltonianOUCoordinateAssembly n) (id : Ω → Ω)) :=
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.prodMap measurable_id
  have he : ginibreOriginalEquilibriumPathLaw n α T P B = ((ginibreMeasure n).prod P).map F := by
    rw [← ginibreGaussian_weighted_initial_noise_product hn P, Measure.map_map hF hA]
    rw [Measure.map_smul _ (hF.comp hA).aemeasurable]
    rfl
  rw [he]
  apply Measure.map_congr
  let := ginibreMeasure_isProbabilityMeasure hn
  have hCF : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage
        measurable_fst)).mpr
    exact (ginibre_ae_collisionFree n hn).mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hCF] with p hp
  have hN := ginibreInitialCollisionNormalize_of_free p.1 hp
  have hFree : ginibreFreeInitialVersion z₀ hz₀ p.1 = ⟨p.1, hp⟩ := by
    simp [ginibreFreeInitialVersion, hp]
  simp only [F, hN, ginibreEquilibriumPath, hFree, ginibreCanonicalJointHorizonPath]
  rfl

theorem ginibreBrownian_equilibrium_original_marginal {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    ((ginibreMeasure n).prod P).map (fun p => ginibreBrownianMaximalProcess n α p.1 B T p.2) =
      ginibreMeasure n := by
  have h := ginibreOriginalEquilibriumPathLaw_terminal hn α P B hB hiB T
  rw [ginibreOriginalEquilibriumPathLaw_product hn α P B hB T z₀ hz₀] at h
  have hPath : Measurable (fun p : Configuration n × Ω =>
      (ginibreEquilibriumPath α z₀ hz₀ B p).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Icc (0 : ℝ) (T : ℝ), ℝ))) :=
    (ContinuousMap.continuous_precomp _).measurable.comp
      (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  rw [Measure.map_map (continuous_eval_const _).measurable hPath] at h
  have he : (fun p : Configuration n × Ω =>
      ((ginibreEquilibriumPath α z₀ hz₀ B p).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Icc (0 : ℝ) (T : ℝ), ℝ)))
          ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩) =ᵐ[(ginibreMeasure n).prod P]
      (fun p => ginibreBrownianMaximalProcess n α p.1 B T p.2) := by
    filter_upwards [ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hiB] with p hp
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Real.toNNReal_coe] using hp (T : ℝ)
  exact (Measure.map_congr he).symm.trans h

theorem ginibreBrownian_equilibrium_original_invariant {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ((ginibreMeasure n).prod P).map (fun p => ginibreBrownianMaximalProcess n α p.1 B T p.2) =
      ginibreMeasure n :=
  ginibreBrownian_equilibrium_original_marginal hn α P B hB hiB T
    (ginibreCollisionFreeDefault n).val (ginibreCollisionFreeDefault n).property

end
end GinibrePoincare
