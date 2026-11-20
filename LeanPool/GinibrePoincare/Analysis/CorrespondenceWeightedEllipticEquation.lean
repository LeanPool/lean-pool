/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticEquation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticReal
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityTestIntegrability
/-!
# Correspondence weighted elliptic equation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_annihilator_equation`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The weighted generator `∑ i, (∂_{b i} ∂_{b i} θ + ρ⁻¹ * ∂_{b i} ρ * ∂_{b i} θ)` along the
orthonormal basis `b`. -/
def correspondenceWeightedEllipticGenerator {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (ρ θ : E → ℝ) (x : E) : ℝ :=
  ∑i, (fderiv ℝ (fun y=>fderiv ℝ θ y (b i)) x (b i)+
    (ρ x)⁻¹*fderiv ℝ ρ x (b i)*fderiv ℝ θ x (b i))

/-- A literal weighted-generator annihilator satisfies the actual local
constant-principal-part elliptic divergence equation. -/
theorem correspondenceWeightedElliptic_annihilator_equation
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (u : E → ℝ) (hu : MemLp u 2 (correspondenceWeightedEllipticMeasure ρ))
    (hA : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, u x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure
          ρ)=0)
    (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫x, (ρ x*u x)*(∑i, fderiv ℝ (fun y=>fderiv ℝ θ y (b i)) x (b i)))=
      -(∑i,∫x, (u x*fderiv ℝ ρ x (b i))*fderiv ℝ θ x (b i)) := by
  classical
  have hul := correspondenceWeightedElliptic_locallyIntegrable ρ hρ.continuous hp u hu
  let D := fun i x=>fderiv ℝ θ x (b i)
  let DD := fun i x=>fderiv ℝ (D i) x (b i)
  have hD (i) : ContDiff ℝ ∞ (D i) := (hθ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDDs (i) : ContDiff ℝ ∞ (DD i) := ((hD i).fderiv_right (by simp)).clm_apply contDiff_const
  have hDD (i) : Continuous (DD i) := (hDDs i).continuous
  have hDi (i) : Continuous (fun x=>fderiv ℝ ρ x (b i)) :=
    (hρ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 (i) : Integrable (fun x=>u x*(ρ x*DD i x)) volume :=
    hul.integrable_smul_right_of_hasCompactSupport (hρ.continuous.mul (hDD i))
      (((hc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)).mul_left)
  have hi2 (i) : Integrable (fun x=>u x*(fderiv ℝ ρ x (b i)*D i x)) volume :=
    hul.integrable_smul_right_of_hasCompactSupport ((hDi i).mul (hD i).continuous)
      ((hc.fderiv_apply ℝ (b i)).mul_left)
  have hs1 := integrable_finsetSum Finset.univ (fun i _=>hi1 i)
  have hs2 := integrable_finsetSum Finset.univ (fun i _=>hi2 i)
  have he := hA θ hθ hc
  rw [correspondenceWeightedElliptic_integral_density ρ _ hρ.continuous hp] at he
  have hpt (x) : ρ x*(u x*correspondenceWeightedEllipticGenerator b ρ θ x)=
      (∑i, u x*(ρ x*DD i x))+(∑i, u x*(fderiv ℝ ρ x (b i)*D i x)) := by
    unfold correspondenceWeightedEllipticGenerator
    rw [Finset.mul_sum, Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [DD, D]
    field_simp [(hp x).ne']
  simp_rw [hpt] at he
  rw [integral_add hs1 hs2, integral_finsetSum _ (fun i _=>hi1 i),
    integral_finsetSum _ (fun i _=>hi2 i)] at he
  have hleft : (∫x, (ρ x*u x)*(∑i, DD i x))=∑i,∫x, u x*(ρ x*DD i x) := by
    rw [← integral_finsetSum _ (fun i _=>hi1 i)]
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hright : (∑i,∫x, (u x*fderiv ℝ ρ x (b i))*D i x)=
      ∑i,∫x, u x*(fderiv ℝ ρ x (b i)*D i x) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    exact ae_of_all volume fun x=>mul_assoc _ _ _
  change (∫x, (ρ x*u x)*(∑i, DD i x))= -(∑i,∫x, (u x*fderiv ℝ ρ x (b i))*D i x)
  rw [hleft, hright]
  linarith
end
end GinibrePoincare
