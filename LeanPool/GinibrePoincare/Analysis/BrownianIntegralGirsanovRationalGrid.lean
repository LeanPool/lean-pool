/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovRationalGrid.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltEndpoint
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovFiniteProductLaw

/-!
# Brownian integral Girsanov rational grid

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUniformNNTime_rational_endpoint`, `brownianRationalPrefix_drift_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal
namespace GinibrePoincare
noncomputable section

/-- Uniform refinement index with exactly `q * (n+1)` cells. -/
def brownianRationalRefinementIndex (q n : ℕ) := q*(n+1)-1

theorem brownianRationalRefinementIndex_succ (q n : ℕ) (hq : 0 < q) :
    brownianRationalRefinementIndex q n+1=q*(n+1) := by
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hq (Nat.succ_pos n)))

theorem brownianRationalRefinementIndex_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (brownianRationalRefinementIndex q) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_id
  have h := Nat.mul_le_mul_right (n+1) (Nat.succ_le_of_lt hq)
  change n ≤ q*(n+1)-1
  omega

/-- Exact alignment of a rational prefix with its own refined uniform mesh. -/
theorem brownianUniformNNTime_rational_prefix (T : ℝ≥0) (p q m k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) :
    itoUniformNNTime T (q*m) k = itoUniformNNTime (T*(p : ℝ≥0)/(q : ℝ≥0)) (p*m) k := by
  apply NNReal.coe_injective
  simp only [itoUniformNNTime_coe, itoUniformTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, Nat.cast_mul]
  have hp' : (p : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hq' : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hm' : (m : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

theorem brownianUniformNNTime_rational_endpoint (T : ℝ≥0) (p q m : ℕ)
    (hq : 0 < q) (hm : 0 < m) :
    itoUniformNNTime T (q*m) (p*m)=T*(p : ℝ≥0)/(q : ℝ≥0) := by
  apply NNReal.coe_injective
  simp only [itoUniformNNTime_coe, itoUniformTime, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, Nat.cast_mul]
  have hq' : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hm' : (m : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

/-- Actual partial drift Riemann sums converge at every rational subdivision
of the fixed terminal horizon. -/
theorem brownianRationalPrefix_drift_tendsto (T : ℝ≥0) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (F : ℝ≥0 → ℝ)
    (hc : ContinuousOn F (Set.Icc 0 (T * (p : ℝ≥0) / (q : ℝ≥0)))) :
    Tendsto (fun n => ∑ k ∈ Finset.range (p*(n+1)),
      F (itoUniformNNTime T (q*(n+1)) k)*((T : ℝ)/(q*(n+1) : ℕ))) atTop
      (𝓝 (∫ s in (0 : ℝ)..(T*(p : ℝ≥0)/(q : ℝ≥0) : ℝ≥0), F (Real.toNNReal s))) := by
  let t := T*(p : ℝ≥0)/(q : ℝ≥0)
  have hfc : ContinuousOn (fun s : ℝ => F (Real.toNNReal s)) (Set.Icc 0 (t : ℝ)) :=
    hc.comp continuous_real_toNNReal.continuousOn (by
      intro s hs
      exact ⟨by positivity, by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2⟩)
  have ht := (itoContinuousScalarRiemann_fin_tendsto (fun s : ℝ => F (Real.toNNReal s)) t hfc).comp
    (brownianRationalRefinementIndex_tendsto p hp)
  have heq (n : ℕ) :
      (∑ k : Fin (brownianRationalRefinementIndex p n+1),
        F (Real.toNNReal (ginibreUniformBrownianTime t (brownianRationalRefinementIndex p n) k))*
        ((t : ℝ)/((brownianRationalRefinementIndex p n : ℝ)+1))) =
      ∑ k ∈ Finset.range (p*(n+1)), F (itoUniformNNTime T (q*(n+1)) k)*((T : ℝ)/(q*(n+1) : ℕ)) := by
    simp only [Real.toNNReal_coe]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => F (ginibreUniformBrownianTime t
      (brownianRationalRefinementIndex p n) k)*((t : ℝ)/((brownianRationalRefinementIndex p n :
          ℝ)+1)))
      (brownianRationalRefinementIndex p n+1)]
    simp_rw [← itoUniformNNTime_eq_ginibreUniformBrownianTime,
      brownianRationalRefinementIndex_succ p n hp]
    apply Finset.sum_congr rfl
    intro k hk
    rw [brownianUniformNNTime_rational_prefix T p q (n+1) k hp hq (Nat.succ_pos n)]
    congr 1
    have hi := congrArg (fun m : ℕ => (m : ℝ)) (brownianRationalRefinementIndex_succ p n hp)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at hi
    rw [hi]
    dsimp only [t]
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
    have hp' : (p : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
    have hq' : (q : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
    have hn' : (n : ℝ)+1≠0 := by positivity
    field_simp
  simpa only [Function.comp_def, heq] using ht

end
end GinibrePoincare
