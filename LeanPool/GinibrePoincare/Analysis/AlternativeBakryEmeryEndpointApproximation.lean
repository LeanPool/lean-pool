/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryEndpointApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPolygonalApproximation
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryFiniteEndpoint
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobalContinuity
/-!
# Alternative Bakry Emery endpoint approximation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryFiniteEndpoint_sampled_tendsto`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace GinibrePoincare
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual compact-path endpoint coincides with the constructed finite
Gaussian-coordinate endpoint whenever the compact noise is its literal polygon. -/
theorem bakryEmeryLangevinEndpoint_eq_finiteEndpoint
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 ≤ T)
    (P : C(Icc 0 T, EuclideanSpace ℝ ι)) (m : ℕ) (h : ℝ) (hh : 0 < h)
    (hTime : T = (m : ℝ) * h) (x : EuclideanSpace ℝ (Fin m × ι))
    (hP : ∀ t : Icc 0 T, P t = Real.sqrt 2 • bakryEmeryPolygonalNoise m h x.ofLp t.val) :
    bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT P =
      bakryEmeryFiniteEndpoint W κ hκ hW hc z m h hh x := by
  classical
  subst T
  let N := fun s => Real.sqrt 2 • bakryEmeryPolygonalNoise m h x.ofLp s
  have hNM : EqOn (bkWeightedExtension ((m : ℝ)*h) hT P) N (Icc 0 ((m : ℝ)*h)) := by
    intro t ht
    rw [bkWeightedExtension, projIcc_of_mem hT ht]
    exact hP ⟨t, ht⟩
  have he := bakryEmeryLangevinCorrectionOn_noise_congr W κ hκ hW hc
    (bkWeightedExtension ((m : ℝ)*h) hT P) N
    (bkWeightedExtension_continuous _ hT P)
    ((bakryEmeryPolygonalNoise_continuous m h x.ofLp).const_smul (Real.sqrt 2))
    z ((m : ℝ)*h) hT hNM
  unfold bakryEmeryLangevinEndpoint bakryEmeryLangevinStateOn bakryEmeryFiniteEndpoint
  rw [he ⟨hT, le_rfl⟩, hNM ⟨hT, le_rfl⟩]

omit [DecidableEq ι] in
/-- Actual deterministic finite Gaussian-coordinate solutions converge to the
actual Langevin state driven by every continuous zero-initial noise path. -/
theorem bakryEmeryFiniteEndpoint_sampled_tendsto
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (z : EuclideanSpace ℝ ι) (T : ℝ) (hT : 0 < T)
    (N : ℝ → EuclideanSpace ℝ ι) (hN : ContinuousOn N (Icc 0 T)) (hN0 : N 0 = 0) :
    Tendsto (fun n : ℕ => bakryEmeryFiniteEndpoint W κ hκ hW hc z (n+1)
      (T/(n+1 : ℝ)) (by positivity)
      (WithLp.toLp 2 (fun p : Fin (n+1) × ι =>
        (N (((p.1.val+1 : ℕ) : ℝ)*(T/(n+1 : ℝ))) p.2-
         N ((p.1.val : ℝ)*(T/(n+1 : ℝ))) p.2)/Real.sqrt (T/(n+1 : ℝ))))) atTop
      (nhds (bakryEmeryLangevinEndpoint W κ hκ hW hc z T hT.le
        (Real.sqrt 2 • (⟨fun t : Icc 0 T => N t.val,
          continuousOn_iff_continuous_domRestrict.mp hN⟩ : C(Icc 0 T, EuclideanSpace ℝ ι))))) := by
  classical
  have hp := (bakryEmeryPolygonalSamplePath_tendsto T hT N hN).const_smul (Real.sqrt 2)
  have he := (bakryEmeryLangevinEndpoint_continuous W κ hκ hW hc T hT.le).continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := z)).prodMk_nhds hp)
  apply he.congr' (Eventually.of_forall (fun n => ?_))
  have hh : 0 < T/(n+1 : ℝ) := by positivity
  apply bakryEmeryLangevinEndpoint_eq_finiteEndpoint W κ hκ hW hc z T hT.le
    (Real.sqrt 2 • bakryEmeryPolygonalSamplePath T N n) (n+1) (T/(n+1 : ℝ)) hh
  · push_cast
    field_simp
  · intro t
    change Real.sqrt 2 • (bakryEmeryPolygonalNoise (n+1) (T/(n+1 : ℝ))
      (fun p : Fin (n+1) × ι =>
        (N (((p.1.val+1 : ℕ) : ℝ)*(T/(n+1 : ℝ))) p.2-
         N ((p.1.val : ℝ)*(T/(n+1 : ℝ))) p.2)/Real.sqrt (T/(n+1 : ℝ))) t.val+N 0) = _
    rw [hN0, add_zero]

end
end GinibrePoincare
