/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupChainRule.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.L2BoundedCoefficientConvergence
public import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Smooth Lipschitz functional calculus on the full weak Dirichlet domain -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- Exact ordinary gradient chain rule for a smooth scalar composition. -/
theorem ginibreFullSmoothChain_gradient (n : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (fun w => φ (f w)) z = deriv φ (f z) • ginibreEuclideanGradient f z :=
        by
  have hd := ((hφ.differentiable (by simp) (f z)).hasDerivAt).comp_hasFDerivAt z
    ((hf.differentiable (by simp) z).hasFDerivAt)
  ext k
  simp only [ginibreEuclideanGradient, PiLp.smul_apply]
  have hd' : fderiv ℝ (fun w => φ (f w)) z = deriv φ (f z) • fderiv ℝ f z := hd.fderiv
  rw [hd']
  by_cases hk : k.2 = 0 <;> simp [hk]

/-- Scalar composition preserves the actual collision-free symmetric core. -/
theorem ginibreFullSmoothChain_core {n : ℕ} (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hzero : φ 0 = 0) (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    IsTheoremOneNineCore (fun z => φ (f z)) := by
  refine ⟨hφ.comp hf.1, hf.2.1.comp_left hzero, ?_, ?_⟩
  · exact (tsupport_comp_subset hzero f).trans hf.2.2.1
  · intro σ z
    exact congrArg φ (hf.2.2.2 σ z)

/-- The literal proposed chain gradient is an actual weighted L² vector. -/
def ginibreFullChainGradient (n : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (K : ℝ≥0) (hLip : LipschitzWith K φ) (u : GinibreFullValueL2 n)
    (g : GinibreFullGradientL2 n) : GinibreFullGradientL2 n :=
  (L2_boundedCoefficient_memLp (ginibreMeasure n) (fun z => deriv φ (u z))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
    K K.coe_nonneg (fun _ => norm_deriv_le_of_lipschitz hLip) g).toLp
      (fun z => deriv φ (u z) • g z)

theorem ginibreFullChainGradient_ae (n : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (K : ℝ≥0) (hLip : LipschitzWith K φ) (u : GinibreFullValueL2 n)
    (g : GinibreFullGradientL2 n) :
    (ginibreFullChainGradient n φ hφ K hLip u g : Configuration n → EuclideanSpace ℝ (Fin n × Fin
        2))
      =ᵐ[ginibreMeasure n] fun z => deriv φ (u z) • g z :=
  MemLp.coeFn_toLp _

/-- The smooth Lipschitz chain rule on the entire actual symmetric weak domain. -/
theorem ginibreFullWeakSpace_smoothChain (n : ℕ) (hn : 0 < n)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hzero : φ 0 = 0)
    (K : ℝ≥0) (hLip : LipschitzWith K φ) (u : GinibreFullValueL2 n)
    (g : GinibreFullGradientL2 n) (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    (hLip.compLp hzero u, ginibreFullChainGradient n φ hφ K hLip u g) ∈ ginibreFullWeakSpace n hn :=
        by
  obtain ⟨p, hp, hpt⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  choose f hf hv hw using hp
  have htval : Tendsto (fun j => (p j).1) atTop (𝓝 u) :=
    (continuous_fst.tendsto (u, g)).comp hpt
  have htgrad : Tendsto (fun j => (p j).2) atTop (𝓝 g) :=
    (continuous_snd.tendsto (u, g)).comp hpt
  obtain ⟨ns, hns, hnae⟩ := (tendstoInMeasure_of_tendsto_Lp htval).exists_seq_tendsto_ae
  let a j z := deriv φ ((p (ns j)).1 z)
  let c z := deriv φ (u z)
  have ha (j : ℕ) : AEStronglyMeasurable (a j) (ginibreMeasure n) :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (p (ns j)).1)
  have hc : AEStronglyMeasurable c (ginibreMeasure n) :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  have htchain : Tendsto (fun j => ginibreFullChainGradient n φ hφ K hLip
      (p (ns j)).1 (p (ns j)).2) atTop (𝓝 (ginibreFullChainGradient n φ hφ K hLip u g)) := by
    apply L2_boundedCoefficient_tendsto (ginibreMeasure n) a c ha hc K K.coe_nonneg
      (fun _ _ => norm_deriv_le_of_lipschitz hLip) (fun _ => norm_deriv_le_of_lipschitz hLip)
    · filter_upwards [hnae] with z hz
      exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp hz
    · exact htgrad.comp hns.tendsto_atTop
  have htvalue : Tendsto (fun j => hLip.compLp hzero (p (ns j)).1) atTop (𝓝 (hLip.compLp hzero u))
      :=
    (hLip.continuous_compLp hzero).continuousAt.tendsto.comp (htval.comp hns.tendsto_atTop)
  apply (ginibreFullWeakSpace_isClosed n hn).mem_of_tendsto (htvalue.prodMk_nhds htchain)
  apply Eventually.of_forall
  intro j
  have hcomp := ginibreFullSmoothChain_core φ hφ hzero (f (ns j)) (hf (ns j))
  have he : (hLip.compLp hzero (p (ns j)).1,
      ginibreFullChainGradient n φ hφ K hLip (p (ns j)).1 (p (ns j)).2) =
      (ginibreFullCorePair hn (fun z => φ (f (ns j) z)) hcomp).val := by
    apply Prod.ext
    · apply Lp.ext
      exact ((hLip.coeFn_compLp hzero (p (ns j)).1).trans ((hv (ns j)).fun_comp φ)).trans
        (ginibreFullCoreValue_ae hn _ hcomp).symm
    · apply Lp.ext
      filter_upwards [ginibreFullChainGradient_ae n φ hφ K hLip (p (ns j)).1 (p (ns j)).2,
        hv (ns j), hw (ns j), ginibreFullCoreGradient_ae hn _ hcomp] with z hchain hval hgrad hcore
      change ginibreFullChainGradient n φ hφ K hLip (p (ns j)).1 (p (ns j)).2 z =
        ginibreFullCoreGradient hn _ hcomp z
      rw [hchain, hval, hgrad, hcore, ginibreFullSmoothChain_gradient n φ hφ _ (hf (ns j)).1]
  rw [he]
  exact (ginibreFullCorePair hn _ hcomp).property

end
end GinibrePoincare
