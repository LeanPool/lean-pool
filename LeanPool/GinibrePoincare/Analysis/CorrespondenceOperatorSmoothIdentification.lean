/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorSmoothIdentification.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorComplex
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorCoreGreen
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorGreen
public import LeanPool.GinibrePoincare.Analysis.GinibreArbitraryWeakPairClosure
/-!
# Correspondence operator smooth identification

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorGenerator_real_graph_iff_exists_gradient`,
`correspondenceOperatorGenerator_smooth_graph`, `correspondenceOperator_friedrichs_form_closure`,
`correspondenceOperatorGenerator_graph_iff_real_imag`.
-/

@[expose] public section
noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter
open scoped Topology ContDiff

/-- Exact ordinary weak-form characterization of unrestricted operator membership. -/
theorem correspondenceOperatorGenerator_ofReal_variational_iff {n : ℕ} (hn : 0 < n)
    (u v : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) :
    (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
      (correspondenceOperatorGenerator n hn).graph ↔
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h →
        (1/(n : ℝ))*inner ℝ g h = -inner ℝ v w := by
  rw [correspondenceOperatorGenerator_graph_iff,← map_sub,
      correspondenceOperatorComplexResolvent_ofReal]
  have hinj : Function.Injective (ginibreFullComplexOfReal n) := by
    intro a b hab
    have hh := congrArg (ginibreFullComplexRe n) hab
    simpa using hh
  rw [hinj.eq_iff]
  constructor
  · intro heq w h hw
    let r := correspondenceOperatorFormResolvent n hn (u-v)
    have hv : correspondenceOperatorFormValue n hn r=u := heq
    have hrweak := correspondenceOperatorFormSpace_weak n hn r
    have hg : correspondenceOperatorFormGradient n hn r=g :=
      (ginibre_distributional_gradient_unique n hn u g _ hu
        (by simpa only [hv] using hrweak)).symm
    let q : correspondenceOperatorWeakSpace n hn := ⟨(w, h), hw⟩
    have hr := correspondenceOperatorFormResolvent_riesz n hn (u-v)
      (correspondenceOperatorFormOfWeak n hn q)
    rw [correspondenceOperatorFormSpace_inner, correspondenceOperatorFormOfWeak_value,
      correspondenceOperatorFormOfWeak_gradient, hv, hg, inner_sub_left] at hr
    linarith
  · intro heq
    have hh := correspondenceOperatorGenerator_resolvent_unique n hn (u-v) u g hu
      (by intro w h hw; rw [inner_sub_left]; have hh := heq w h hw; linarith)
    exact hh.1.symm

/-- The full unrestricted real operator domain consists exactly of ordinary
weak-H¹ values admitting their actual weighted weak divergence in L². -/
theorem correspondenceOperatorGenerator_real_graph_iff_exists_gradient {n : ℕ} (hn : 0 < n)
    (u v : GinibreFullValueL2 n) :
    (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
      (correspondenceOperatorGenerator n hn).graph ↔
    ∃ g : GinibreFullGradientL2 n, IsGinibreDistributionalGradient n u g ∧
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h →
        (1/(n : ℝ))*inner ℝ g h = -inner ℝ v w := by
  constructor
  · intro hgraph
    have heq := (correspondenceOperatorGenerator_graph_iff n hn _ _).mp hgraph
    rw [← map_sub, correspondenceOperatorComplexResolvent_ofReal] at heq
    have heqr : correspondenceOperatorValueResolvent n hn (u-v)=u := by
      have h := congrArg (ginibreFullComplexRe n) heq
      simpa using h
    let r := correspondenceOperatorFormResolvent n hn (u-v)
    have hv : correspondenceOperatorFormValue n hn r=u := heqr
    have hr := correspondenceOperatorFormSpace_weak n hn r
    have hu : IsGinibreDistributionalGradient n u (correspondenceOperatorFormGradient n hn r) := by
      simpa only [hv] using hr
    exact ⟨_, hu, (correspondenceOperatorGenerator_ofReal_variational_iff hn u v _ hu).mp hgraph⟩
  · rintro ⟨g, hu, heq⟩
    exact (correspondenceOperatorGenerator_ofReal_variational_iff hn u v g hu).mpr heq

theorem correspondenceOperatorGenerator_smooth_graph {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (u v : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (huf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hvf : (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n] ginibrePregenerator n f) :
    (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
      (correspondenceOperatorGenerator n hn).graph := by
  rw [correspondenceOperatorGenerator_ofReal_variational_iff hn u v g hu]
  intro w h hw
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp (ginibreWeakPair_mem_closure_interiorSmooth
      hn w h hw)
  have heq (m : ℕ) : (1 / (n : ℝ)) * inner ℝ g (q m).2 = -inner ℝ v (q m).1 := by
    obtain ⟨φ, hφs, hφc, hφsup, hvalue, hgradient⟩ := hq m
    have hφ := And.intro hφs (And.intro hφc hφsup)
    have hgq : (q m).2 = correspondenceOperatorGinibreFullCoreGradient hn φ hφ := by
      apply Lp.ext
      exact hgradient.trans (correspondenceOperator_ginibreFullCoreGradient_ae hn φ hφ).symm
    have hvq : (q m).1 = correspondenceOperatorGinibreFullCoreValue hn φ hφ := by
      apply Lp.ext
      exact hvalue.trans (correspondenceOperator_ginibreFullCoreValue_ae hn φ hφ).symm
    rw [hgq, hvq]
    have hgreen := correspondenceOperator_ginibreFullGenerator_weak_core_green hn u g hu φ hφ
    have hmix : inner ℝ u (correspondenceOperatorGinibreFullCorePregenerator hn φ hφ) =
        inner ℝ v (correspondenceOperatorGinibreFullCoreValue hn φ hφ) := by
      rw [L2.inner_def, L2.inner_def]
      calc
        (∫ z, (correspondenceOperatorGinibreFullCorePregenerator hn φ hφ) z * u z ∂ginibreMeasure
            n) =
            ∫ z, f z * ginibrePregenerator n φ z ∂ginibreMeasure n := by
          apply integral_congr_ae
          filter_upwards [huf, correspondenceOperator_ginibreFullCorePregenerator_ae hn φ hφ] with z
              hz ha
          rw [hz, ha, mul_comm]
        _ = ∫ z, φ z * ginibrePregenerator n f z ∂ginibreMeasure n :=
          (correspondenceOperator_ginibre_mixed_green_identity hn hφ hf).symm
        _ = ∫ z, (correspondenceOperatorGinibreFullCoreValue hn φ hφ) z * v z ∂ginibreMeasure n :=
            by
          apply integral_congr_ae
          filter_upwards [hvf, correspondenceOperator_ginibreFullCoreValue_ae hn φ hφ] with z hz ha
          rw [hz, ha]
    rw [hmix] at hgreen
    exact hgreen
  have hl : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
      (1 / (n : ℝ)) * inner ℝ g p.2) (𝓝 (w, h))
      (𝓝 ((1 / (n : ℝ)) * inner ℝ g h)) :=
    (continuous_const.mul (continuous_const.inner continuous_snd)).tendsto (w, h)
  have hr : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
      -inner ℝ v p.1) (𝓝 (w, h)) (𝓝 (-inner ℝ v w)) :=
    (continuous_const.inner continuous_fst).neg.tendsto (w, h)
  exact tendsto_nhds_unique (hl.comp hlim) ((hr.comp hlim).congr (fun m => (heq m).symm))

/-- The unrestricted ordinary weak-H¹ graph is exactly the closure of the
literal smooth compact collision-free differential core. This identifies the
closed form used by the unrestricted generator with the Friedrichs form. -/
theorem correspondenceOperator_friedrichs_form_closure (n : ℕ) (hn : 0 < n) :
    (correspondenceOperatorWeakSpace n hn : Set (GinibreFullValueL2 n × GinibreFullGradientL2 n)) =
      closure (ginibreInteriorSmoothPair n) := by
  apply Set.Subset.antisymm
  · intro p hp
    exact ginibreWeakPair_mem_closure_interiorSmooth hn p.1 p.2 hp
  · apply closure_minimal _ (correspondenceOperatorWeakSpace_isClosed n hn)
    intro p hp
    obtain ⟨f, hf, hc, hs, hv, hg⟩ := hp
    exact ginibre_smooth_distributional_gradient n hn p.1 p.2 f hf hv hg

/-- Exact real and imaginary decomposition of the unrestricted complex operator graph. -/
theorem correspondenceOperatorGenerator_graph_iff_real_imag (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n) :
    (u, v) ∈ (correspondenceOperatorGenerator n hn).graph ↔
      correspondenceOperatorValueResolvent n hn (ginibreFullComplexRe n u-ginibreFullComplexRe n v)=
        ginibreFullComplexRe n u ∧
      correspondenceOperatorValueResolvent n hn (ginibreFullComplexIm n u-ginibreFullComplexIm n v)=
        ginibreFullComplexIm n u := by
  rw [correspondenceOperatorGenerator_graph_iff]
  constructor
  · intro hh
    constructor
    · have h := congrArg (ginibreFullComplexRe n) hh
      simpa only [correspondenceOperatorComplexResolvent_re, map_sub] using h
    · have h := congrArg (ginibreFullComplexIm n) hh
      simpa only [correspondenceOperatorComplexResolvent_im, map_sub] using h
  · rintro ⟨hr, hi⟩
    have hd := ginibreFullComplex_decomposition n (correspondenceOperatorComplexResolvent n hn
        (u-v))
    have hdu := ginibreFullComplex_decomposition n u
    have hr' : ginibreFullComplexRe n (correspondenceOperatorComplexResolvent n hn (u-v)) =
        ginibreFullComplexRe n u := by
      rw [correspondenceOperatorComplexResolvent_re, (ginibreFullComplexRe n).map_sub]
      exact hr
    have hi' : ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn (u-v)) =
        ginibreFullComplexIm n u := by
      rw [correspondenceOperatorComplexResolvent_im, (ginibreFullComplexIm n).map_sub]
      exact hi
    rw [hr', hi'] at hd
    exact hd.symm.trans hdu

end GinibrePoincare
