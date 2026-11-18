/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorGraph

/-! # Variational characterization of the full Ginibre generator -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory

/-- The full generator equation is exactly the weak Dirichlet equation on the
whole symmetric distributional-gradient domain. -/
theorem ginibreFullGenerator_real_variational_iff {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g)) :
    ginibreFullSymmetricResolvent n hn (u - v) = u ↔
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h → IsGinibreSymmetricWeakPair (w, h) →
        (1 / (n : ℝ)) * inner ℝ g h = -inner ℝ v.val w := by
  constructor
  · intro heq w h hw hsw
    let r := ginibreFullFormResolvent n hn (u.val - v.val)
    have hv : ginibreFullFormValue n hn r = u.val := congrArg Subtype.val heq
    have hrweak := ginibreFullFormSpace_weak n hn r
    have hg : ginibreFullFormGradient n hn r = g := by
      exact (ginibre_distributional_gradient_unique n hn u.val g _ hu
        (by simpa only [hv] using hrweak.1)).symm
    let q : ginibreFullWeakSpace n hn := ⟨(w, h), hw, hsw⟩
    have hr := ginibreFullFormResolvent_riesz n hn (u.val - v.val)
      (ginibreFullFormOfWeak n hn q)
    rw [ginibreFullFormSpace_inner, ginibreFullFormOfWeak_value,
      ginibreFullFormOfWeak_gradient, hv, hg, inner_sub_left] at hr
    linarith
  · intro heq
    apply Subtype.ext
    have h := ginibreFullGenerator_resolvent_unique n hn (u.val - v.val) u.val g hu hs
      (by intro w h hw hsw; rw [inner_sub_left]; have hh := heq w h hw hsw; linarith)
    exact h.1.symm

/-- Exact complex full-generator membership for embedded real weak-domain
functions, expressed without any auxiliary regularity hypothesis. -/
theorem ginibreFullGenerator_ofReal_variational_iff {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g)) :
    (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
        (ginibreFullGenerator n hn).graph ↔
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h → IsGinibreSymmetricWeakPair (w, h) →
        (1 / (n : ℝ)) * inner ℝ g h = -inner ℝ v.val w := by
  rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal]
  have hi : Function.Injective (ginibreFullSymmetricOfReal n) := by
    intro a b hab
    have h := congrArg (ginibreFullSymmetricRe n) hab
    simpa using h
  rw [hi.eq_iff]
  exact ginibreFullGenerator_real_variational_iff hn u v g hu hs

/-- Exact full real generator domain: both the distributional gradient and the
weak operator equation are obtained from graph membership. -/
theorem ginibreFullGenerator_real_graph_iff_exists_gradient {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) :
    (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
        (ginibreFullGenerator n hn).graph ↔
      ∃ g : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n u.val g ∧
        IsGinibreSymmetricWeakPair (u.val, g) ∧
        ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
          IsGinibreDistributionalGradient n w h → IsGinibreSymmetricWeakPair (w, h) →
          (1 / (n : ℝ)) * inner ℝ g h = -inner ℝ v.val w := by
  constructor
  · intro hgraph
    have heq := (ginibreFullGenerator_graph_iff n hn _ _).mp hgraph
    rw [← map_sub, ginibreFullComplexResolvent_ofReal] at heq
    have heqr : ginibreFullSymmetricResolvent n hn (u - v) = u := by
      have h := congrArg (ginibreFullSymmetricRe n) heq
      simpa using h
    let r := ginibreFullFormResolvent n hn (u.val - v.val)
    have hv : ginibreFullFormValue n hn r = u.val := congrArg Subtype.val heqr
    have hr := ginibreFullFormSpace_weak n hn r
    have hu : IsGinibreDistributionalGradient n u.val (ginibreFullFormGradient n hn r) := by
      simpa only [hv] using hr.1
    have hs : IsGinibreSymmetricWeakPair (u.val, ginibreFullFormGradient n hn r) := by
      simpa only [hv] using hr.2
    exact ⟨_, hu, hs, (ginibreFullGenerator_real_variational_iff hn u v _ hu hs).mp heqr⟩
  · rintro ⟨g, hu, hs, heq⟩
    exact (ginibreFullGenerator_ofReal_variational_iff hn u v g hu hs).mpr heq

/-- Complex full graph membership is exactly simultaneous membership of the
real and imaginary parts in the genuine real weak generator graph. -/
theorem ginibreFullGenerator_graph_iff_real_imag {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) :
    (u, v) ∈ (ginibreFullGenerator n hn).graph ↔
      ginibreFullSymmetricResolvent n hn
        (ginibreFullSymmetricRe n u - ginibreFullSymmetricRe n v) = ginibreFullSymmetricRe n u ∧
      ginibreFullSymmetricResolvent n hn
        (ginibreFullSymmetricIm n u - ginibreFullSymmetricIm n v) = ginibreFullSymmetricIm n u := by
  rw [ginibreFullGenerator_graph_iff]
  constructor
  · intro heq
    constructor
    · have h := congrArg (ginibreFullSymmetricRe n) heq
      simpa only [ginibreFullComplexResolvent_re, map_sub] using h
    · have h := congrArg (ginibreFullSymmetricIm n) heq
      simpa only [ginibreFullComplexResolvent_im, map_sub] using h
  · rintro ⟨hr, hi⟩
    have hre : ginibreFullComplexRe n (ginibreFullComplexResolvent n hn (u - v)).val =
        ginibreFullComplexRe n u.val := by
      have h := ginibreFullComplexResolvent_re n hn (u - v)
      rw [(ginibreFullSymmetricRe n).map_sub] at h
      exact congrArg Subtype.val (h.trans hr)
    have him : ginibreFullComplexIm n (ginibreFullComplexResolvent n hn (u - v)).val =
        ginibreFullComplexIm n u.val := by
      have h := ginibreFullComplexResolvent_im n hn (u - v)
      rw [(ginibreFullSymmetricIm n).map_sub] at h
      exact congrArg Subtype.val (h.trans hi)
    apply Subtype.ext
    rw [← ginibreFullComplex_decomposition n (ginibreFullComplexResolvent n hn (u - v)).val,
      ← ginibreFullComplex_decomposition n u.val, hre, him]

/-- The actual generator quadratic form is the full distributional-gradient
energy, for every real graph element. -/
theorem ginibreFullGenerator_real_energy_identity {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧ IsGinibreSymmetricWeakPair (u.val, g) ∧
      ginibreWeakEnergy n g = -inner ℝ v.val u.val := by
  obtain ⟨g, hu, hs, heq⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp hgraph
  refine ⟨g, hu, hs, ?_⟩
  have h := heq u.val g hu hs
  simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using h

/-- Full graph dissipation is the actual weak Dirichlet energy. -/
theorem ginibreFullGenerator_dissipation_eq_energy {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) := by
  obtain ⟨g, hug, hsg, hvar⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp
    hgraph
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u.val g hug hsg
  refine ⟨g, hug, hsg, ?_⟩
  simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using
    hvar (ginibreFullCenter n hn u.val) g huc hsc

end GinibrePoincare
