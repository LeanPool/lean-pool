/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionL2ProductPairing.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Operator
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianEquilibriumProductLaw

/-!
# Ginibre stochastic transition L 2 product pairing

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2Operator_bounded_measurable_pairing`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance (n : ℕ) (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel
    _
local instance (n : ℕ) (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance instBorelGinibreStochasticTransitionL2ProductPairing60 (n : ℕ) :
    MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

/-- Exact pairing on the literal Ginibre-initial-law times Brownian product. -/
theorem ginibreOriginalStochasticL2Operator_product_pairing {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (f g : Lp ℝ 2 (ginibreMeasure n)) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      ∫ p : Configuration n × Ω, f p.1 * g (ginibreBrownianMaximalProcess n α p.1 B T p.2)
        ∂(ginibreMeasure n).prod P := by
  let z₀ := (ginibreCollisionFreeDefault n).val
  have hz₀ := (ginibreCollisionFreeDefault n).property
  rw [ginibreOriginalStochasticL2Operator_pairing,
    ginibreOriginalEquilibriumPathLaw_product hn α P B hB T z₀ hz₀]
  have hm : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) =>
      f (x ⟨0, ⟨le_rfl, T.property⟩⟩)*g (x ⟨T, ⟨T.property, le_rfl⟩⟩)) :=
    ((Lp.stronglyMeasurable f).measurable.comp (continuous_eval_const _).measurable).mul
      ((Lp.stronglyMeasurable g).measurable.comp (continuous_eval_const _).measurable)
  have hp : Measurable (fun p : Configuration n × Ω =>
    (ginibreEquilibriumPath α z₀ hz₀ B p).comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Icc (0 : ℝ) (T : ℝ), ℝ))) :=
    (ContinuousMap.continuous_precomp _).measurable.comp
      (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  rw [integral_map hp.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  have hCF : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage
        measurable_fst)).mpr
    exact (ginibre_ae_collisionFree n hn).mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hCF, ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hiB] with p hCF hE
  have h0 : ginibreEquilibriumPath α z₀ hz₀ B p 0=p.1 := by
    have h := ginibreCanonicalJointHorizonPath_initial (α : ℝ) T
      (ginibreFreeInitialVersion z₀ hz₀ p.1, ginibreBrownianFullContinuousNoise n B α p.2)
    simpa [ginibreCanonicalJointHorizonPath, ginibreEquilibriumPath, ginibreFreeInitialVersion, hCF]
        using h
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [h0, hE (T : ℝ), Real.toNNReal_coe]

theorem ginibreBrownian_original_joint_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    AEMeasurable (fun p : Configuration n × Ω => ginibreBrownianMaximalProcess n α p.1 B T p.2)
      ((ginibreMeasure n).prod P) := by
  have hm := (ginibreDrivenMaximalValue_joint_measurable hn α T).comp
    (((ginibreInitialCollisionNormalize_measurable n).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))
  apply hm.aemeasurable.congr
  have hCF : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage
        measurable_fst)).mpr
    exact (ginibre_ae_collisionFree n hn).mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hCF] with p hp
  simp only [Function.comp_apply, ginibreInitialCollisionNormalize_of_free p.1 hp,
    ginibreBrownianMaximalProcess]

theorem ginibreOriginalStochasticL2Operator_representative_pairing {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hg : (g : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      ∫ p : Configuration n × Ω, f p.1 * v (ginibreBrownianMaximalProcess n α p.1 B T p.2)
        ∂(ginibreMeasure n).prod P := by
  rw [ginibreOriginalStochasticL2Operator_product_pairing]
  apply integral_congr_ae
  have he : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P,
      g (ginibreBrownianMaximalProcess n α p.1 B T p.2)=
        v (ginibreBrownianMaximalProcess n α p.1 B T p.2) := by
    apply ae_of_ae_map (p := fun z => g z=v z) (ginibreBrownian_original_joint_aemeasurable hn α P B
        hB T)
    rw [ginibreBrownian_equilibrium_original_invariant hn α P B hB hiB T]
    exact hg
  exact he.mono fun p hp => congrArg (fun x => f p.1*x) hp

theorem ginibreOriginalStochasticL2Operator_bounded_measurable_pairing {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hg : (g : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      ∫ z, f z * (∫ ω, v (ginibreBrownianMaximalProcess n α z B T ω) ∂P) ∂ginibreMeasure n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hfi : Integrable (f : Configuration n → ℝ) (ginibreMeasure n) :=
    (Lp.memLp f).integrable (by norm_num)
  have hs : AEStronglyMeasurable (fun p : Configuration n × Ω =>
      f p.1*v (ginibreBrownianMaximalProcess n α p.1 B T p.2)) ((ginibreMeasure n).prod P) :=
    (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).aestronglyMeasurable).mul
      (hv.comp_aemeasurable
        (ginibreBrownian_original_joint_aemeasurable hn α P B hB T)).aestronglyMeasurable
  have hi : Integrable (fun p : Configuration n × Ω =>
      f p.1*v (ginibreBrownianMaximalProcess n α p.1 B T p.2)) ((ginibreMeasure n).prod P) := by
    apply ((hfi.norm.comp_fst P).mul_const C).mono' hs
    exact ae_of_all _ fun p => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  rw [ginibreOriginalStochasticL2Operator_representative_pairing hn α P B hB hiB T f g v hg,
    integral_prod _ hi]
  congr 1
  funext z
  exact integral_const_mul (f z) (fun ω => v (ginibreBrownianMaximalProcess n α z B T ω))

end
end GinibrePoincare
