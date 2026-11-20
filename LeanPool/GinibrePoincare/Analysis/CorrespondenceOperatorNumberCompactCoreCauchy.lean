/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCompactCoreCauchy.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactCoreCutoff
/-!
# Correspondence operator number compact core Cauchy

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceNumber_compact_number_cauchy`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff BigOperators Topology
namespace GinibrePoincare
noncomputable section

/-- The difference `f - g` of two compact test functions. -/
def correspondenceNumberTestSub {n : ℕ} (f g : BKCompactTest n) : BKCompactTest n :=
  ⟨fun z=>f z-g z, f.smooth.sub g.smooth, f.compact.sub g.compact⟩

theorem correspondenceNumber_dbar_sub {n : ℕ} (f g : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : Fin n) :
    dbarComponent (fun z=>f z-g z) j=fun z=>dbarComponent f j z-dbarComponent g j z := by
  funext z
  unfold dbarComponent
  rw [fderiv_fun_sub ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z)]
  simp only [sub_apply]
  ring

theorem correspondenceNumberTestSub_l2 {n : ℕ} (f g : BKCompactTest n) :
    (correspondenceNumberTestSub f g).l2=f.l2-g.l2 := by
  apply Lp.ext
  filter_upwards [(correspondenceNumberTestSub f g).l2_coe, Lp.coeFn_sub f.l2 g.l2, f.l2_coe,
      g.l2_coe] with z h0 h1 h2 h3
  rw [h0, h1, Pi.sub_apply, h2, h3]
  rfl

theorem correspondenceNumberTestSub_dbar {n : ℕ} (f g : BKCompactTest n) (j : Fin n) :
    (correspondenceNumberTestSub f g).dbar j=correspondenceNumberTestSub (f.dbar j) (g.dbar j) := by
  have he:=correspondenceNumber_dbar_sub f g f.smooth g.smooth j
  cases f
  cases g
  unfold correspondenceNumberTestSub BKCompactTest.dbar at *
  congr 1

theorem correspondenceNumberTestSub_number {n : ℕ} (hn : 0 < n) (f g : BKCompactTest n) :
    bkCompactNumberL2 (correspondenceNumberTestSub f g)=bkCompactNumberL2 f-bkCompactNumberL2 g :=
        by
  apply (correspondenceOperatorNumber n hn).mem_graph_snd_inj
    (correspondenceOperatorNumber_compact_graph hn (correspondenceNumberTestSub f g))
    ((correspondenceOperatorNumber n hn).graph.sub_mem
      (correspondenceOperatorNumber_compact_graph hn f) (correspondenceOperatorNumber_compact_graph
          hn g))
  exact correspondenceNumberTestSub_l2 f g

/-- Convergence of actual first and second compact jets forces the number
operator values to be Cauchy, through the literal compact identity (6.8). -/
theorem correspondenceNumber_compact_number_cauchy {n : ℕ} (hn : 0 < n)
    (F : ℕ → BKCompactTest n)
    (D : Fin n → BKGaussianL2 n) (Q : Fin n → Fin n → BKGaussianL2 n)
    (hD : ∀ j, Tendsto (fun m => (F m |>.dbar j).l2) atTop (𝓝 (D j)))
    (hQ : ∀ j k, Tendsto (fun m => ((F m |>.dbar j).dbar k).l2) atTop (𝓝 (Q j k))) :
    CauchySeq (fun m=>bkCompactNumberL2 (F m)) := by
  have he (a b : ℕ) : ‖bkCompactNumberL2 (F a)-bkCompactNumberL2 (F b)‖^2=
      (∑j : Fin n,∑k : Fin n, ‖((F a|>.dbar j).dbar k).l2-((F b|>.dbar j).dbar k).l2‖^2)+
        (n : ℝ)*∑j : Fin n, ‖(F a|>.dbar j).l2-(F b|>.dbar j).l2‖^2 := by
    have h := bkCompact_integrated_identity hn (correspondenceNumberTestSub (F a) (F b))
    simpa only [correspondenceNumberTestSub_number hn, correspondenceNumberTestSub_dbar,
      correspondenceNumberTestSub_l2] using h
  have hfst : Tendsto (Prod.fst : ℕ×ℕ→ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ×ℕ→ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_snd
  have hDt j : Tendsto (fun p : ℕ×ℕ=>‖(F p.1|>.dbar j).l2-(F p.2|>.dbar j).l2‖^2) atTop (𝓝 0) := by
    simpa using ((((hD j).comp hfst).sub ((hD j).comp hsnd)).norm).pow 2
  have hQt j k : Tendsto (fun p : ℕ×ℕ=>‖((F p.1|>.dbar j).dbar k).l2-((F p.2|>.dbar j).dbar
      k).l2‖^2) atTop (𝓝 0) := by
    simpa using ((((hQ j k).comp hfst).sub ((hQ j k).comp hsnd)).norm).pow 2
  have ht := (tendsto_finsetSum Finset.univ (fun j _=>tendsto_finsetSum Finset.univ (fun k _=>hQt j
      k))).add
    ((tendsto_finsetSum Finset.univ (fun j _=>hDt j)).const_mul (n : ℝ))
  have htN : Tendsto (fun p : ℕ×ℕ=>‖bkCompactNumberL2 (F p.1)-bkCompactNumberL2 (F p.2)‖^2) atTop (𝓝
      0) := by
    simpa only [he, Finset.sum_const_zero, mul_zero, add_zero] using ht
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have hnorm := htN.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero, dist_eq_norm]
      using hnorm

end
end GinibrePoincare
