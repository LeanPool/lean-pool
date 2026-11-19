/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticResolventSemigroupComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceOrbit
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticRealGraphOrbit

/-!
# Ginibre transition analytic resolvent semigroup comparison

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreSymmetricContractionSemigroup_eq_paper_evolution`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreFullRealEvolution_continuous_orbit {n : ℕ} (hn : 0 < n)
    (u : ginibreFullSymmetricValues n) : Continuous (fun t => ginibreFullRealEvolution n hn t u) :=
  (ginibreFullSymmetricRe n).continuous.comp (continuous_ginibreFullEvolution n hn
      (ginibreFullSymmetricOfReal n u))

theorem ginibreFullRealEvolution_zero_apply {n : ℕ} (hn : 0 < n)
    (u : ginibreFullSymmetricValues n) : ginibreFullRealEvolution n hn 0 u=u := by
  change ginibreFullSymmetricRe n (ginibreFullEvolution n hn 0 (ginibreFullSymmetricOfReal n u))=u
  rw [ginibreFullEvolution_zero]
  exact ginibreFullSymmetricRe_ofReal n u

theorem ginibreFullRealEvolution_scaled_graph_derivative {n : ℕ} (hn : 0 < n)
    (c : ℝ≥0) (hc : 0 < c) (u v : ginibreFullSymmetricValues n)
    (hg : ginibreFullSymmetricResolvent n hn (u - v) = u)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ginibreFullRealEvolution n hn (c*s.toNNReal) u)
      ((c : ℝ) • ginibreFullRealEvolution n hn (c*t.toNNReal) v) t := by
  have hcp : 0 < (c : ℝ) := hc
  have hd := ginibreFullRealEvolution_graph_derivative hn u v hg ((c : ℝ)*t) (mul_pos hcp ht)
  have hlin : HasDerivAt (fun s : ℝ => (c : ℝ)*s) (c : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (c : ℝ)
  have hh := hd.scomp t hlin
  have hmul (s : ℝ) : ((c : ℝ)*s).toNNReal=c*s.toNNReal := by
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_mul (p := (c : ℝ)) (q := s) (show 0 ≤ (c : ℝ) from c.property))
  simp only [Function.comp_def] at hh
  simp_rw [hmul] at hh
  exact hh

/-- A genuine strongly continuous contraction semigroup is uniquely determined
by its actual normalized Bochner resolvent on the symmetric Ginibre L² space. -/
theorem ginibreSymmetricContractionSemigroup_eq_from_actual_laplace {n : ℕ} (hn : 0 < n)
    (A : ℝ≥0 → ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖)
    (hadd : ∀ s t u, A (s + t) u = A s (A t u))
    (hzero : ∀ u, A 0 u = u)
    (c : ℝ≥0) (hc : 0 < c)
    (hLap : ∀ u, (∫ s in Ioi (0 : ℝ), ((c : ℝ) * Real.exp (-(c : ℝ) * s)) • A s.toNNReal u) =
      ginibreFullSymmetricResolvent n hn u) (T : ℝ≥0) :
    A T=ginibreFullRealEvolution n hn (c*T) := by
  have hcp : 0 < (c : ℝ) := hc
  have hComm (u : ginibreFullSymmetricValues n) (t : ℝ≥0) :
      ginibreFullSymmetricResolvent n hn (A t u)=A t (ginibreFullSymmetricResolvent n hn u) := by
    have hh := actualContractionLaplace_commutes A hcont hbound hadd (c : ℝ) hcp u t
    rw [hLap u, hLap (A t u)] at hh
    exact hh.symm
  apply ginibreFullSymmetric_operators_eq_on_resolvent_range hn
  intro u
  let R := ginibreFullSymmetricResolvent n hn
  let x := fun s : ℝ => A s.toNNReal (R u)
  let y := fun s : ℝ => ginibreFullRealEvolution n hn (c*s.toNNReal) (R u)
  let ax := fun s : ℝ => A s.toNNReal (R u)-A s.toNNReal u
  let ay := fun s : ℝ => ginibreFullRealEvolution n hn (c*s.toNNReal) (R u-u)
  have hinit : R (R u-(R u-u))=R u := by
    congr 1
    abel
  have hh := ginibreFullGenerator_real_scaled_orbit_unique hn x y ax ay (c : ℝ) (T : ℝ)
    c.property T.property
    ((hcont (R u)).comp continuous_real_toNNReal).continuousOn
    (((ginibreFullRealEvolution_continuous_orbit hn (R u)).comp
      (continuous_const.mul continuous_real_toNNReal)).continuousOn)
    (fun s hs => by
      have hd := actualContractionLaplace_orbit_derivative A hcont hbound hadd (c : ℝ) hcp u s hs.1
      dsimp only at hd
      rw [hLap u] at hd
      exact hd)
    (fun s hs => ginibreFullRealEvolution_scaled_graph_derivative hn c hc (R u) (R u-u) hinit s
        hs.1)
    (fun s hs => by
      change R (A s.toNNReal (R u)-(A s.toNNReal (R u)-A s.toNNReal u))=A s.toNNReal (R u)
      have he : A s.toNNReal (R u)-(A s.toNNReal (R u)-A s.toNNReal u)=A s.toNNReal u := by abel
      rw [he]
      exact hComm u s.toNNReal)
    (fun s hs => ginibreFullRealEvolution_preserves_graph hn (R u) (R u-u) hinit (c*s.toNNReal))
    (by
      change A (Real.toNNReal 0) (R u)=ginibreFullRealEvolution n hn (c*Real.toNNReal 0) (R u)
      simp only [Real.toNNReal_zero, mul_zero, hzero, ginibreFullRealEvolution_zero_apply hn])
  have he := hh (T : ℝ) ⟨T.property, le_rfl⟩
  simpa only [x, y, Real.toNNReal_coe] using he

theorem ginibreSymmetricContractionSemigroup_eq_paper_evolution {n : ℕ} (hn : 0 < n)
    (A : ℝ≥0 → ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖)
    (hadd : ∀ s t u, A (s + t) u = A s (A t u)) (hzero : ∀ u, A 0 u = u)
    (α : ℝ≥0) (hα : 0 < α)
    (hLap : ∀ u, (∫ s in Ioi (0 : ℝ),
      (((α : ℝ) / (n : ℝ)) * Real.exp (-((α : ℝ) / (n : ℝ)) * s)) • A s.toNNReal u) =
      ginibreFullSymmetricResolvent n hn u) (T : ℝ≥0) :
    A T=ginibreFullRealPaperEvolution n hn α T := by
  have hc : 0 < ginibrePaperSpeedFactor n α := by
    dsimp [ginibrePaperSpeedFactor]
    exact div_pos hα (by exact_mod_cast hn)
  apply ginibreSymmetricContractionSemigroup_eq_from_actual_laplace hn A hcont hbound hadd hzero
    (ginibrePaperSpeedFactor n α) hc
  simpa only [ginibrePaperSpeedFactor_coe] using hLap

end
end GinibrePoincare
