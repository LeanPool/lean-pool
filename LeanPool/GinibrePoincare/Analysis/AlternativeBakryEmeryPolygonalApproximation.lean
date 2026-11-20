/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryPolygonalApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGrid
public import Mathlib.Topology.ContinuousMap.Compact
/-!
# Alternative Bakry Emery polygonal approximation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryPolygonalSamplePath_tendsto`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
omit [DecidableEq ι] in
omit [Fintype ι] in
theorem bakryEmeryPolygonalNoise_sampled_grid
    (m k : ℕ) (hk : k ≤ m) (h : ℝ) (hh : 0 < h)
    (u : ℕ → EuclideanSpace ℝ ι) :
    bakryEmeryPolygonalNoise m h
      (fun p : Fin m × ι => (u (p.1.val+1) p.2-u p.1.val p.2)/Real.sqrt h)
      ((k : ℝ)*h) = u k-u 0 := by
  classical
  have hr (j : Fin m) : bakryEmeryPolygonalRamp h j.val ((k : ℝ)*h) =
      if j.val < k then Real.sqrt h else 0 := by
    by_cases hj : j.val < k
    · rw [ite_eq_left hj]
      apply bakryEmeryPolygonalRamp_after h hh
      have hj' : ((j.val+1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
      exact mul_le_mul_of_nonneg_right hj' hh.le
    · rw [ite_eq_right hj]
      apply bakryEmeryPolygonalRamp_before h hh.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_not_gt hj) hh.le
  have hs : Real.sqrt h ≠ 0 := Real.sqrt_ne_zero'.mpr hh
  have hf (a : ℝ) : Real.sqrt h*(a/Real.sqrt h)=a := by field_simp
  apply PiLp.ext
  intro i
  change (∑ j : Fin m, bakryEmeryPolygonalRamp h j.val ((k : ℝ)*h) *
      ((u (j.val+1) i-u j.val i)/Real.sqrt h)) = u k i-u 0 i
  simp_rw [hr, ite_mul, hf, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then u (j+1) i-u j i else 0),
    ← Finset.sum_filter]
  have he : (Finset.range m).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  exact Finset.sum_range_sub (fun j => u j i) k

omit [Fintype ι] [DecidableEq ι] in
/-- The sampled polygon is the literal affine interpolation on every grid cell. -/
theorem bakryEmeryPolygonalNoise_sampled_interpolation [Finite ι]
    (m k : ℕ) (hk : k < m) (h : ℝ) (hh : 0 < h)
    (u : ℕ → EuclideanSpace ℝ ι) (t : ℝ)
    (ht : t ∈ Icc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h)) :
    bakryEmeryPolygonalNoise m h
      (fun p : Fin m × ι => (u (p.1.val + 1) p.2 - u p.1.val p.2) / Real.sqrt h) t =
      u k - u 0 + ((t - (k : ℝ) * h) / h) • (u (k + 1) - u k) := by
  classical
  have := Fintype.ofFinite ι
  let x : (Fin m × ι) → ℝ :=
    fun p => (u (p.1.val+1) p.2-u p.1.val p.2)/Real.sqrt h
  let P := bakryEmeryPolygonalNoise m h x
  let D := (1/h) • (u (k+1)-u k)
  have hD : (WithLp.toLp 2 (fun i => x (⟨k, hk⟩, i)/Real.sqrt h) : EuclideanSpace ℝ ι) = D := by
    apply PiLp.ext
    intro i
    change (u (k+1) i-u k i)/Real.sqrt h/Real.sqrt h = (1/h)*(u (k+1) i-u k i)
    rw [div_div, Real.mul_self_sqrt hh.le]
    ring
  have hd (r : ℝ) (hr : r ∈ Ioo ((k : ℝ)*h) t) : HasDerivAt P D r := by
    rw [← hD]
    exact bakryEmeryPolygonalNoise_hasDerivAt m h hh x ⟨k, hk⟩ r ⟨hr.1, hr.2.trans_le ht.2⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (bakryEmeryPolygonalNoise_continuous m h x).continuousOn hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume ((k : ℝ)*h) t)
  rw [intervalIntegral.integral_const] at he
  have hPa : P ((k : ℝ)*h) = u k-u 0 :=
    bakryEmeryPolygonalNoise_sampled_grid m k hk.le h hh u
  change (t-(k : ℝ)*h) • D = P t-P ((k : ℝ)*h) at he
  rw [hPa] at he
  have he' : P t = u k-u 0+(t-(k : ℝ)*h) • D := by
    rw [he]
    abel
  simpa only [P, D, x, smul_smul, one_div, div_eq_mul_inv, one_mul] using he'

omit [DecidableEq ι] in
/-- Affine interpolation stays within the endpoint oscillation bound. -/
theorem bakryEmeryPolygonalNoise_sampled_error
    (m k : ℕ) (hk : k < m) (h : ℝ) (hh : 0 < h)
    (u : ℕ → EuclideanSpace ℝ ι) (t : ℝ)
    (ht : t ∈ Icc ((k : ℝ) * h) (((k + 1 : ℕ) : ℝ) * h))
    (v : EuclideanSpace ℝ ι) (ε : ℝ)
    (h0 : ‖u k - v‖ ≤ ε) (h1 : ‖u (k + 1) - v‖ ≤ ε) :
    ‖bakryEmeryPolygonalNoise m h
      (fun p : Fin m × ι => (u (p.1.val+1) p.2-u p.1.val p.2)/Real.sqrt h) t-
      (v-u 0)‖ ≤ ε := by
  classical
  let a := (t-(k : ℝ)*h)/h
  have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr ht.1) hh.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hh).mpr
    push_cast at ht
    linarith [ht.2]
  have hc0 : u k ∈ Metric.closedBall v ε := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h0
  have hc1 : u (k+1) ∈ Metric.closedBall v ε := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h1
  have hc := (convex_closedBall v ε) hc0 hc1 (show 0 ≤ 1-a by linarith) ha0
    (show (1-a)+a=1 by ring)
  rw [Metric.mem_closedBall, dist_eq_norm] at hc
  rw [bakryEmeryPolygonalNoise_sampled_interpolation m k hk h hh u t ht]
  have he : u k-u 0+a • (u (k+1)-u k)-(v-u 0) =
      ((1-a) • u k+a • u (k+1))-v := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  change ‖u k-u 0+a • (u (k+1)-u k)-(v-u 0)‖ ≤ ε
  rw [he]
  exact hc

private theorem grid_cover (m : ℕ) (hm : 0 < m) (h : ℝ) (_ : 0 < h)
    (t : ℝ) (ht : t ∈ Icc 0 ((m : ℝ) * h)) :
    ∃ k < m, t ∈ Icc ((k : ℝ)*h) (((k+1 : ℕ) : ℝ)*h) := by
  induction m generalizing t with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      refine ⟨0, by omega, ?_⟩
      simpa using ht
    · by_cases htm : t ≤ (m : ℝ)*h
      · obtain ⟨k, hk, hcell⟩ := ih (Nat.pos_of_ne_zero hm0) t ⟨ht.1, htm⟩
        exact ⟨k, Nat.lt_succ_of_lt hk, hcell⟩
      · exact ⟨m, Nat.lt_succ_self m, ⟨(lt_of_not_ge htm).le, ht.2⟩⟩

omit [DecidableEq ι] in
/-- Continuous paths are approximated uniformly by the literal Gaussian-grid
polygon encoding of their sampled increments. -/
theorem bakryEmeryPolygonalNoise_sampled_uniform_error
    (T : ℝ) (N : ℝ → EuclideanSpace ℝ ι) (hN : ContinuousOn N (Icc 0 T))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (m : ℕ) (_ : 0 < m) (h : ℝ), 0 < h → (m : ℝ)*h=T → h < δ →
      ∀ t ∈ Icc 0 T,
      ‖bakryEmeryPolygonalNoise m h
        (fun p : Fin m × ι => (N ((p.1.val+1 : ℕ)*h) p.2-N ((p.1.val : ℝ)*h) p.2)/Real.sqrt h) t-
        (N t-N 0)‖ ≤ ε := by
  classical
  have hu := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).uniformContinuousOn_of_continuous hN
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ,?_⟩
  intro m hm h hh hT hhd t ht
  obtain ⟨k, hk, hcell⟩ := grid_cover m hm h hh t (hT ▸ ht)
  have hend : (((k+1 : ℕ) : ℝ)*h) ≤ T := by
    rw [← hT]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
  have hk0 : 0 ≤ (k : ℝ)*h := by positivity
  have hk1 : 0 ≤ (((k+1 : ℕ) : ℝ)*h) := by positivity
  have hkmem : (k : ℝ)*h ∈ Icc 0 T := ⟨hk0, hcell.1.trans ht.2⟩
  have hk1mem : (((k+1 : ℕ) : ℝ)*h) ∈ Icc 0 T := ⟨hk1, hend⟩
  have hd0 : dist ((k : ℝ)*h) t ≤ h := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hcell.1)]
    push_cast at hcell
    linarith [hcell.2]
  have hd1 : dist (((k+1 : ℕ) : ℝ)*h) t ≤ h := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hcell.2)]
    push_cast at hcell ⊢
    linarith [hcell.1]
  have he0 : ‖N ((k : ℝ)*h)-N t‖ ≤ ε := by
    rw [← dist_eq_norm]
    exact (hclose _ hkmem _ ht (hd0.trans_lt hhd)).le
  have he1 : ‖N (((k+1 : ℕ) : ℝ)*h)-N t‖ ≤ ε := by
    rw [← dist_eq_norm]
    exact (hclose _ hk1mem _ ht (hd1.trans_lt hhd)).le
  simpa using bakryEmeryPolygonalNoise_sampled_error m k hk h hh
    (fun j => N ((j : ℝ)*h)) t hcell (N t) ε he0 he1

/-- The actual sampled polygon as a compact-time continuous path. -/
def bakryEmeryPolygonalSamplePath (T : ℝ) (N : ℝ → EuclideanSpace ℝ ι) (n : ℕ) :
    C(Icc 0 T, EuclideanSpace ℝ ι) :=
  let h := T/(n+1 : ℝ)
  let x : (Fin (n+1) × ι) → ℝ := fun p =>
    (N (((p.1.val+1 : ℕ) : ℝ)*h) p.2-N ((p.1.val : ℝ)*h) p.2)/Real.sqrt h
  ⟨fun t => bakryEmeryPolygonalNoise (n+1) h x t.val+N 0,
    ((bakryEmeryPolygonalNoise_continuous (n+1) h x).comp continuous_subtype_val).add
        continuous_const⟩

omit [DecidableEq ι] in
/-- The exact compact-path convergence needed by the actual continuous Langevin
endpoint map; no Brownian approximation or solution convergence is assumed. -/
theorem bakryEmeryPolygonalSamplePath_tendsto
    (T : ℝ) (hT : 0 < T) (N : ℝ → EuclideanSpace ℝ ι)
    (hN : ContinuousOn N (Icc 0 T)) :
    Filter.Tendsto (bakryEmeryPolygonalSamplePath T N) Filter.atTop
      (nhds (⟨fun t : Icc 0 T => N t.val,
        continuousOn_iff_continuous_domRestrict.mp hN⟩ : C(Icc 0 T, EuclideanSpace ℝ ι))) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, herror⟩ := bakryEmeryPolygonalNoise_sampled_uniform_error T N hN (ε/2) (by
      positivity)
  have hs : Filter.Tendsto (fun n : ℕ => T/(n+1 : ℝ)) Filter.atTop (nhds 0) :=
    by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  filter_upwards [hs.eventually (gt_mem_nhds hδ)] with n hn
  have hh : 0 < T/(n+1 : ℝ) := by positivity
  have heq : ((n+1 : ℕ) : ℝ)*(T/(n+1 : ℝ))=T := by push_cast; field_simp
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr
  intro t
  change ‖bakryEmeryPolygonalNoise (n+1) (T/(n+1 : ℝ))
      (fun p : Fin (n+1) × ι =>
        (N (((p.1.val+1 : ℕ) : ℝ)*(T/(n+1 : ℝ))) p.2-
         N ((p.1.val : ℝ)*(T/(n+1 : ℝ))) p.2)/Real.sqrt (T/(n+1 : ℝ))) t.val+N 0-N t.val‖ ≤ ε/2
  have he := herror (n+1) (by omega) (T/(n+1 : ℝ)) hh heq hn t.val t.property
  convert he using 1
  congr 1
  abel

end
end GinibrePoincare
