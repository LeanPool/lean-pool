/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakAffine.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakDegreeElimination
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakConjugateModes
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityFirstQuotient
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakLinear

/-! # Affine equality on the ordinary symmetric weak domain

Equality removes the higher conjugate Hermite modes. Holomorphic reconstruction
then places the remaining holomorphic part in the first quotient span, whose
representatives are multiples of the coordinate sum. Combining that part with
its conjugate yields the real affine representative almost everywhere.

For the converse, the real and imaginary center-of-mass witnesses and constants
belong to the weak equality subspace. Its linear closure gives every affine
combination; uniqueness of the distributional gradient identifies the supplied
gradient with this constructed pair. The final iff joins these two directions.
-/


@[expose] public section


noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped ComplexConjugate

/-- Every sharp equality attainer in the entire actual symmetric weak domain
is affine in the complex coordinate sum, with no smoothness or polynomial assumption. -/
theorem ginibreEquality_full_weak_affine {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u) :
    ∃ a : ℝ,∃ c : ℂ, (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => a+2*(c*coordinateSum z).re := by
  obtain ⟨hrec, hpos⟩ := ginibreEquality_weak_holomorphic_reconstruction hn u g hu hs heq
  have hfirst := ginibreEquality_positive_conjugate_low_modes_mem_first hn
    (ginibreFullHolomorphicPart n hn u) hpos (by
      intro d hd
      simpa only [Nat.sub_add_cancel (by omega : 1≤d)] using
        ginibreEquality_weak_conjugate_higher_modes_zero hn u g hu hs heq (d-1) (by omega))
  obtain ⟨c, hc⟩ := ginibreEquality_first_quotient_closedSpan_ae_coordinateSum hn
    (ginibreFullHolomorphicPart n hn u) hfirst
  refine ⟨ginibreL2Mean n u, c,?_⟩
  have hv := ginibreFullComplexOfReal_ae n (ginibreFullCenter n hn u)
  rw [hrec] at hv
  have hcenter : (ginibreFullCenter n hn u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => u z-ginibreL2Mean n u := by
    rw [ginibreFullCenter_apply]
    filter_upwards [Lp.coeFn_sub u (ginibreRealConstantL2 n hn (ginibreL2Mean n u)),
      ginibreRealConstantL2_ae n hn (ginibreL2Mean n u)] with z hs hc
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hc]
  filter_upwards [hv, hcenter, hc, Lp.coeFn_add (ginibreFullHolomorphicPart n hn u)
    (star (ginibreFullHolomorphicPart n hn u)), Lp.coeFn_star (ginibreFullHolomorphicPart n hn u)]
    with z hv hcenter hc hadd hstar
  rw [hadd] at hv
  simp only [Pi.add_apply] at hv
  rw [hstar] at hv
  simp only [Pi.star_apply] at hv
  rw [hc, hcenter] at hv
  have hr := congrArg Complex.re hv
  change (c*coordinateSum z).re+(conj (c*coordinateSum z)).re=u z-ginibreL2Mean n u at hr
  simp only [Complex.conj_re] at hr
  linarith

/-- Every actual weak representative of an affine coordinate-sum function
attains the sharp Poincaré constant. -/
theorem ginibreEquality_full_weak_of_affine {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (a : ℝ) (c : ℂ)
    (hrep : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => a + 2 * (c * coordinateSum z).re) :
    ginibreWeakEnergy n g=2*ginibreL2Variance n hn u := by
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨ur, gr, hur, hsr, hfr, her⟩ := centerOfMassReal_attains_symmetric_weak_poincare n hn
  obtain ⟨ui, gi, hui, hsi, hfi, hei⟩ := centerOfMassImag_attains_symmetric_weak_poincare n hn
  let pr : ginibreFullWeakSpace n hn := ⟨(ur, gr), hur, hsr⟩
  let pi : ginibreFullWeakSpace n hn := ⟨(ui, gi), hui, hsi⟩
  let p0 : ginibreFullWeakSpace n hn := ⟨(ginibreRealConstantL2 n hn a, 0),
    ginibreRealConstantL2_weak n hn a, ginibreRealConstantL2_symmetric_pair n hn a⟩
  let q : ginibreFullWeakSpace n hn := p0+(2*c.re)•pr+(-2*c.im)•pi
  have hm : ginibreL2Mean n (ginibreRealConstantL2 n hn a)=a := by
    unfold ginibreL2Mean
    rw [integral_congr_ae (ginibreRealConstantL2_ae n hn a)]
    simp
  have hcenter : ginibreFullCenter n hn (ginibreRealConstantL2 n hn a)=0 := by
    rw [ginibreFullCenter_apply, hm, sub_self]
  have hp0 : p0 ∈ ginibreFullWeakEqualitySpace n hn := by
    intro p
    change (1 / (n : ℝ))*inner ℝ 0 p.val.2=
      2*inner ℝ (ginibreFullCenter n hn (ginibreRealConstantL2 n hn a)) (ginibreFullCenter n hn
        p.val.1)
    simp [hcenter]
  have hpr : pr ∈ ginibreFullWeakEqualitySpace n hn :=
    (ginibreFullWeakEqualitySpace_mem_iff n hn pr).mpr (by
      change ginibreWeakEnergy n gr = 2 * ginibreL2Variance n hn ur
      linarith)
  have hpi : pi ∈ ginibreFullWeakEqualitySpace n hn :=
    (ginibreFullWeakEqualitySpace_mem_iff n hn pi).mpr (by
      change ginibreWeakEnergy n gi = 2 * ginibreL2Variance n hn ui
      linarith)
  have hq : q ∈ ginibreFullWeakEqualitySpace n hn :=
    (ginibreFullWeakEqualitySpace n hn).add_mem
      ((ginibreFullWeakEqualitySpace n hn).add_mem hp0
        ((ginibreFullWeakEqualitySpace n hn).smul_mem _ hpr))
      ((ginibreFullWeakEqualitySpace n hn).smul_mem _ hpi)
  have hqr : (q.val.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => a+2*(c*coordinateSum z).re := by
    have hqval : q.val.1=(ginibreRealConstantL2 n hn a+(2*c.re)•ur)+(-2*c.im)•ui := rfl
    rw [hqval]
    filter_upwards [Lp.coeFn_add (ginibreRealConstantL2 n hn a+(2*c.re)•ur) ((-2*c.im)•ui),
      Lp.coeFn_add (ginibreRealConstantL2 n hn a) ((2*c.re)•ur),
      Lp.coeFn_smul (2*c.re) ur, Lp.coeFn_smul (-2*c.im) ui,
      ginibreRealConstantL2_ae n hn a, hfr, hfi] with z ha hb hr hi hc hf hg
    rw [ha]
    simp only [Pi.add_apply]
    rw [hb]
    simp only [Pi.add_apply]
    rw [hr, hi]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hc, hf, hg]
    simp only [centerOfMassReal, centerOfMassImag, Complex.mul_re]
    ring
  have huq : u=q.val.1 := Lp.ext (hrep.trans hqr.symm)
  have hgq : g=q.val.2 := ginibre_distributional_gradient_unique n hn u g q.val.2 hu
    (by simpa only [huq] using q.property.1)
  rw [huq, hgq]
  exact (ginibreFullWeakEqualitySpace_mem_iff n hn q).mp hq

/-- Exhaustive affine equality classification on the full symmetric ordinary weak domain. -/
theorem ginibreEquality_full_weak_affine_iff {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreWeakEnergy n g=2*ginibreL2Variance n hn u ↔
      ∃ a : ℝ,∃ c : ℂ, (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        fun z => a+2*(c*coordinateSum z).re := by
  constructor
  · exact ginibreEquality_full_weak_affine hn u g hu hs
  · rintro ⟨a, c, hrep⟩
    exact ginibreEquality_full_weak_of_affine hn u g hu a c hrep

end GinibrePoincare
