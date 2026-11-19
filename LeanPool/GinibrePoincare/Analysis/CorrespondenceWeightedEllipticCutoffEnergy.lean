/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticCutoffEnergy.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticCutoffForm
/-!
# Correspondence weighted elliptic cutoff energy

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_annihilator_cutoff_energy`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The exact genuine cutoff energy identity for every weighted L² harmonic
annihilator. All local H¹ and Sobolev testing inputs are proved internally. -/
theorem correspondenceWeightedElliptic_annihilator_cutoff_energy
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (f : E → ℝ) (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hAnn : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, f x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure
          ρ)=0)
    (η : E→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃g : ι→E→ℝ,
      (∀i, MemLp (g i) 2 (correspondenceWeightedEllipticMeasure ρ)) ∧
      (∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*g i x)= -(∫x, fderiv ℝ θ x (b i)*(η x*f x))) ∧
      (∑i,∫x, (g i x)^2∂correspondenceWeightedEllipticMeasure ρ)=
        ∑i,∫x, f x^2*(fderiv ℝ η x (b i))^2∂correspondenceWeightedEllipticMeasure ρ := by
  classical
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff (tsupport η) hc
  have hχval := correspondenceWeightedElliptic_compact_value_memLp ρ hρ.continuous hp f χ hf
      hχ.continuous hχc
  let u := hχval.toLp (fun x=>χ x*f x)
  obtain ⟨J, hJraw⟩ := correspondenceWeightedElliptic_annihilator_local_H1 b ρ hρ hp f hf hAnn χ hχ
      hχc
  have hJ (i) (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
      (∫x, θ x*J i x)= -(∫x, fderiv ℝ θ x (b i)*u x) := by
    rw [hJraw i θ hθ hθc]
    congr 1
    apply integral_congr_ae
    filter_upwards [hχval.coeFn_toLp] with x hx
    rw [hx]
  have hχ' (x) (hx : x∈tsupport η) : χ x=1 := by simpa using (hχone x hx).eq_of_nhds
  let d := fun i x=>fderiv ℝ η x (b i)
  let g := fun i x=>η x*J i x+d i x*f x
  have hGrad := correspondenceWeightedElliptic_cutoff_gradient (fun i=>b i) f χ η hη hc hχ' u
      hχval.coeFn_toLp J hJ
  obtain ⟨hEnergy, hDiff⟩ := correspondenceWeightedElliptic_cutoff_form_identity b ρ hρ hp f hf hAnn
      χ η hη hc hχ'
    u hχval.coeFn_toLp J hJ
  have hf2 : Integrable (fun x=>f x^2) (correspondenceWeightedEllipticMeasure ρ) := by
    simpa [Real.norm_eq_abs, sq_abs] using (memLp_two_iff_integrable_sq_norm
        hf.aestronglyMeasurable).mp hf
  have hρf2 := (correspondenceWeightedElliptic_integrable_density ρ (fun x=>f x^2) hρ.continuous
      hp).mp hf2
  have hd (i) : Continuous (d i) := (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (i) : HasCompactSupport (d i) := hc.fderiv_apply ℝ (b i)
  have hRight (i) : Integrable (fun x=>ρ x*(f x^2*(d i x)^2)) volume := by
    have hi := hρf2.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      ((hd i).mul (hd i)) ((hdc i).mul_right)
    apply hi.congr
    exact ae_of_all volume fun x=>by simp only [Pi.mul_apply, smul_eq_mul]; ring
  have hLeft (i) : Integrable (fun x=>ρ x*(g i x)^2) volume := by
    have hi := (hDiff i).add (hRight i)
    apply hi.congr
    exact ae_of_all volume fun x=>by dsimp [g, d]; ring
  have hμg (i) : MemLp (g i) 2 (correspondenceWeightedEllipticMeasure ρ) := by
    have hac : correspondenceWeightedEllipticMeasure ρ≪(volume : Measure E) :=
        withDensity_absolutelyContinuous _ _
    have hm := (hGrad i).1.aestronglyMeasurable.mono_ac hac
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    have hi := (correspondenceWeightedElliptic_integrable_density ρ (fun x=>(g i x)^2) hρ.continuous
        hp).mpr (hLeft i)
    simpa [Real.norm_eq_abs, sq_abs] using hi
  refine ⟨g, hμg, (fun i=>(hGrad i).2.2),?_⟩
  have ht (i) : (∫x, ρ x*((g i x)^2-f x^2*(d i x)^2))=
      (∫x, ρ x*(g i x)^2)-(∫x, ρ x*(f x^2*(d i x)^2)) := by
    rw [← integral_sub (hLeft i) (hRight i)]
    apply integral_congr_ae
    exact ae_of_all volume fun x=>by ring
  change (∑i,∫x, ρ x*((g i x)^2-f x^2*(d i x)^2))=0 at hEnergy
  simp_rw [ht] at hEnergy
  rw [Finset.sum_sub_distrib] at hEnergy
  simp_rw [correspondenceWeightedElliptic_integral_density ρ _ hρ.continuous hp]
  linarith
end
end GinibrePoincare
