/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticGreen.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticLocalSobolev
/-!
# Correspondence weighted elliptic Green

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_annihilator_local_green`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_annihilator_local_green
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (f : E → ℝ) (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hA : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, f x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure
          ρ)=0)
    (χ : E→ℝ) (u : Lp ℝ 2 (volume : Measure E))
    (hu : (u : E→ℝ)=ᵐ[volume](fun x=>χ x*f x))
    (J : ι→Lp ℝ 2 (volume : Measure E))
    (hJ : ∀i (ψ : E→ℝ), ContDiff ℝ ∞ ψ→HasCompactSupport ψ→
      (∫x, ψ x*J i x)= -(∫x, fderiv ℝ ψ x (b i)*u x))
    (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hχ : ∀x∈tsupport θ, χ x=1) :
    (∑i,∫x, ρ x*J i x*fderiv ℝ θ x (b i))=0 := by
  classical
  let D := fun i x=>fderiv ℝ θ x (b i)
  let ψ := fun i=>ρ*(D i)
  have hD (i) : ContDiff ℝ ∞ (D i) := (hθ.fderiv_right (by simp)).clm_apply contDiff_const
  have hcD (i) : HasCompactSupport (D i) := hc.fderiv_apply ℝ (b i)
  have hψ (i) : ContDiff ℝ 1 (ψ i) := hρ.mul ((hD i).of_le (by norm_num))
  have hcψ (i) : HasCompactSupport (ψ i) := (hcD i).mul_left
  have hsψ (i) : tsupport (ψ i)⊆tsupport θ := tsupport_mul_subset_right.trans
      (tsupport_fderiv_apply_subset ℝ _)
  have hder (i) (x) : fderiv ℝ (ψ i) x (b i)=
      fderiv ℝ ρ x (b i)*D i x+ρ x*fderiv ℝ (D i) x (b i) := by
    rw [fderiv_mul (hρ.differentiable (by norm_num) x) ((hD i).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hul := correspondenceWeightedElliptic_locallyIntegrable ρ hρ.continuous hp f hf
  have hInt (i) : Integrable (fun x=>f x*fderiv ℝ (ψ i) x (b i)) volume :=
    hul.integrable_smul_right_of_hasCompactSupport
      (((hψ i).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ((hcψ i).fderiv_apply ℝ (b i))
  have hterm (i) : (∫x, ρ x*J i x*D i x)= -(∫x, f x*fderiv ℝ (ψ i) x (b i)) := by
    have he := correspondenceWeightedElliptic_weak_test_C1 u (J i) (b i) (hJ i) (ψ i) (hψ i) (hcψ i)
    have hl : (∫x, (ψ i) x*J i x)=∫x, ρ x*J i x*D i x := by
      apply integral_congr_ae
      exact ae_of_all volume fun x=>by dsimp [ψ, Pi.mul_apply]; ring
    have hr : (∫x, fderiv ℝ (ψ i) x (b i)*u x)=∫x, f x*fderiv ℝ (ψ i) x (b i) := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
      by_cases hs : x∈tsupport θ
      · rw [hχ x hs]
        ring
      · have hz : fderiv ℝ (ψ i) x (b i)=0 := by
          rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) (fun ht=>hs (hsψ i ht))]
          rfl
        simp [hz]
    rw [hl, hr] at he
    exact he
  change (∑i,∫x, ρ x*J i x*D i x)=0
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun i _=>hInt i)]
  have he := hA θ hθ hc
  rw [correspondenceWeightedElliptic_integral_density ρ _ hρ.continuous hp] at he
  have hpt (x) : (∑i, f x*fderiv ℝ (ψ i) x (b i))=
      ρ x*(f x*correspondenceWeightedEllipticGenerator b ρ θ x) := by
    simp_rw [hder]
    unfold correspondenceWeightedEllipticGenerator
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [D]
    field_simp [(hp x).ne']; ring
  simp_rw [hpt, he]
  simp
end
end GinibrePoincare
