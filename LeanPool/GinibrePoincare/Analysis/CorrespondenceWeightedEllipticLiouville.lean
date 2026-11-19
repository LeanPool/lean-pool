/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticLiouville.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticZeroGradient
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCutoffs
/-!
# Correspondence weighted elliptic liouville

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_annihilator_constant`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_annihilator_constant
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hp : ∀ x, 0 < ρ x)
    [IsFiniteMeasure (correspondenceWeightedEllipticMeasure ρ)]
    (f : E → ℝ) (hf : MemLp f 2 (correspondenceWeightedEllipticMeasure ρ))
    (hAnn : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, f x*correspondenceWeightedEllipticGenerator b ρ θ x∂correspondenceWeightedEllipticMeasure
          ρ)=0) :
    ∃c : ℝ, f=ᵐ[correspondenceWeightedEllipticMeasure ρ](fun _=>c) := by
  classical
  let μ := correspondenceWeightedEllipticMeasure ρ
  let η := correspondenceBrascampLiebCutoff (E:=E)
  have hcut := fun k=>correspondenceWeightedElliptic_annihilator_cutoff_energy b ρ hρ hp f hf hAnn
    (η k) (correspondenceBrascampLieb_cutoff_smooth k) (correspondenceBrascampLieb_cutoff_compact k)
  choose g hg hw he using hcut
  let G := fun k i=>(hg k i).toLp (g k i)
  have hsq (k i) : ‖G k i‖^2=∫x, (g k i x)^2∂μ := by
    rw [←real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg k i).coeFn_toLp] with x hx
    simp [G, hx, pow_two]
  have hf2 : Integrable (fun x=>f x^2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using (memLp_two_iff_integrable_sq_norm
        hf.aestronglyMeasurable).mp hf
  obtain ⟨M, hM, hbound⟩ := correspondenceBrascampLieb_cutoff_directional_bound b
  let C := (Fintype.card ι : ℝ)*(∫x, f x^2∂μ)
  have hC : 0≤C := mul_nonneg (by positivity) (integral_nonneg fun x=>sq_nonneg _)
  have hnorm (k i) : ‖G k i‖≤Real.sqrt C*(M/((k : ℝ)+1)) := by
    have hsum : ‖G k i‖^2≤∑j, ‖G k j‖^2 := Finset.single_le_sum (fun j _=>sq_nonneg ‖G k j‖)
        (Finset.mem_univ i)
    simp_rw [hsq] at hsum
    rw [he k] at hsum
    have hb (j) : (∫x, f x^2*(fderiv ℝ (η k) x (b j))^2∂μ)≤
        (M/((k : ℝ)+1))^2*(∫x, f x^2∂μ) := by
      have hD : Continuous (fun x=>fderiv ℝ (η k) x (b j)) :=
        ((correspondenceBrascampLieb_cutoff_smooth k).continuous_fderiv (by simp)).clm_apply
            continuous_const
      have hcD := (correspondenceBrascampLieb_cutoff_compact (E:=E) k).fderiv_apply ℝ (b j)
      have hi := hf2.locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hD.mul hD)
          (hcD.mul_right)
      have hi' : Integrable (fun x=>f x^2*(fderiv ℝ (η k) x (b j))^2) μ := by
        simpa [smul_eq_mul, Pi.mul_apply, pow_two] using hi
      rw [←integral_const_mul]
      apply integral_mono hi' (hf2.const_mul _)
      intro x
      dsimp only
      rw [mul_comm ((M/((k : ℝ)+1))^2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hh := hbound k x j
      have hh' := (sq_le_sq₀ (abs_nonneg _) (show 0≤M/((k : ℝ)+1) by positivity)).mpr hh
      simpa only [sq_abs, bakryEmeryGibbsDirectional, η] using hh'
    have hh := hsum.trans (Finset.sum_le_sum fun j _=>hb j)
    have heq : (∑j : ι, (M/((k : ℝ)+1))^2*(∫x, f x^2∂μ))=C*(M/((k : ℝ)+1))^2 := by simp [C];ring
    rw [heq] at hh
    rw [←hsq k i] at hh
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    simpa [mul_pow, Real.sq_sqrt hC] using hh
  have hG (i) : Tendsto (fun k=>G k i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hinv : Tendsto (fun k : ℕ=>((k : ℝ)+1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1
          tendsto_natCast_atTop_atTop)
    have ht := (hinv.const_mul M).const_mul (Real.sqrt C)
    simp only [mul_zero] at ht
    exact squeeze_zero (fun _=>norm_nonneg _) (fun k=>by simpa [div_eq_mul_inv] using hnorm k i) ht
  have hzero (i) (θ : E→ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
      (∫x, f x*fderiv ℝ θ x (b i))=0 := by
    let q := fun x=>θ x/ρ x
    have hq : Continuous q := hθ.continuous.div hρ.continuous (fun x=>(hp x).ne')
    have hqc : HasCompactSupport q := hc.mul_right
    have hqLp : MemLp q 2 μ := hq.memLp_of_hasCompactSupport hqc
    let Q := hqLp.toLp q
    have hpair (k) : inner ℝ Q (G k i)=∫x, θ x*g k i x := by
      rw [L2.inner_def]
      trans ∫x, q x*g k i x∂μ
      · apply integral_congr_ae
        filter_upwards [hqLp.coeFn_toLp, (hg k i).coeFn_toLp] with x hqx hgx
        simp [Q, G, hqx, hgx, RCLike.inner_apply, mul_comm]
      · rw [correspondenceWeightedElliptic_integral_density ρ _ hρ.continuous hp]
        apply integral_congr_ae
        exact ae_of_all volume fun x=>by dsimp [q];field_simp [(hp x).ne']
    have hlim : Tendsto (fun k=>∫x, θ x*g k i x) atTop (𝓝 0) := by
      have ht : Tendsto (fun k=>inner ℝ Q (G k i)) atTop (𝓝 (inner ℝ Q 0)) :=
        tendsto_const_nhds.inner (hG i)
      simpa only [hpair, inner_zero_right] using ht
    have hevent : ∀ᶠ k in atTop, (∫x, θ x*g k i x)= -(∫x, f x*fderiv ℝ θ x (b i)) := by
      filter_upwards [correspondenceBrascampLieb_cutoff_eventually_one (tsupport θ) hc] with k hk
      rw [hw k i θ hθ hc]
      congr 1
      apply integral_congr_ae
      exact ae_of_all volume fun x=>by
        dsimp only
        by_cases hx : x∈tsupport θ
        · change fderiv ℝ θ x (b i)*(correspondenceBrascampLiebCutoff k x*f x)=_
          rw [hk x hx];ring
        · rw [fderiv_of_notMem_tsupport ℝ hx];simp
    have hh := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hevent.mono fun k hk=>hk.symm))
    linarith
  obtain ⟨c, hc⟩ := correspondenceWeightedElliptic_zero_gradient_constant b f
    (correspondenceWeightedElliptic_locallyIntegrable ρ hρ.continuous hp f hf) hzero
  have hac : μ≪(volume : Measure E) := withDensity_absolutelyContinuous _ _
  exact ⟨c, hac.ae_le hc⟩
end
end GinibrePoincare
