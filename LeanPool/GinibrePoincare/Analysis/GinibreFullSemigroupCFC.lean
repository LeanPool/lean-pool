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

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupMultiplier

/-! # Resolvent construction of a strongly continuous contraction semigroup

This is a reusable complex-Hilbert-space construction. Instantiation for the
concrete full Ginibre weak resolvent is a separate theorem.
-/

@[expose] public section

open Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous spectral calculus of a resolvent, at nonnegative time. -/
def resolventCfcEvolution (R : H →L[ℂ] H) (t : ℝ≥0) : H →L[ℂ] H :=
  cfc (resolventEvolutionMultiplier (t : ℝ)) R

@[simp] theorem resolventCfcEvolution_zero (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    resolventCfcEvolution R 0 = 1 := by
  unfold resolventCfcEvolution
  have he : resolventEvolutionMultiplier (0 : ℝ≥0) = (1 : ℝ → ℝ) := by
    funext r; exact resolventEvolutionMultiplier_zero r
  rw [he]
  exact cfc_one ℝ R hR

/-- Exact semigroup law, obtained by the proved scalar multiplier law. -/
theorem resolventCfcEvolution_add (R : H →L[ℂ] H) (s t : ℝ≥0) :
    resolventCfcEvolution R (s + t) = resolventCfcEvolution R s * resolventCfcEvolution R t := by
  unfold resolventCfcEvolution
  have he : resolventEvolutionMultiplier ((s + t : ℝ≥0) : ℝ) =
      fun r => resolventEvolutionMultiplier (s : ℝ) r * resolventEvolutionMultiplier (t : ℝ) r := by
    funext r
    exact resolventEvolutionMultiplier_add s.coe_nonneg t.coe_nonneg r
  rw [he]
  exact cfc_mul _ _ R (resolventEvolutionMultiplier_continuous _).continuousOn
    (resolventEvolutionMultiplier_continuous _).continuousOn

/-- Norm contraction on the entire Hilbert space. -/
theorem resolventCfcEvolution_norm_le (R : H →L[ℂ] H)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖resolventCfcEvolution R t‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro r hr
  have h := resolventEvolutionMultiplier_mem_unit_interval t.coe_nonneg (hSpec r hr)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem resolventCfcEvolution_contracts (R : H →L[ℂ] H)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) (x : H) :
    ‖resolventCfcEvolution R t x‖ ≤ ‖x‖ := by
  have h := (resolventCfcEvolution R t).le_opNorm x
  have hn := resolventCfcEvolution_norm_le R hSpec t
  nlinarith [norm_nonneg x]

/-- Uniform error on the resolvent range, including spectral accumulation at zero. -/
theorem resolventCfcEvolution_range_error_norm_le (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖(resolventCfcEvolution R t - 1) * R‖ ≤ (t : ℝ) := by
  let f := resolventEvolutionMultiplier (t : ℝ)
  have hf : ContinuousOn f (spectrum ℝ R) := (resolventEvolutionMultiplier_continuous
    _).continuousOn
  have he : cfc (fun r : ℝ => (f r - 1) * r) R = (resolventCfcEvolution R t - 1) * R := by
    calc
      _ = cfc (fun r => f r - 1) R * cfc (fun r : ℝ => r) R :=
        cfc_mul _ _ R (hf.sub continuousOn_const) continuousOn_id
      _ = (cfc f R - cfc (fun _ : ℝ => 1) R) * R := by
        rw [cfc_sub f (fun _ : ℝ => 1) R hf continuousOn_const, cfc_id' ℝ R hR]
      _ = _ := by rw [cfc_const_one (R := ℝ) (a := R)]; rfl
  rw [← he]
  apply norm_cfc_le t.coe_nonneg
  intro r hr
  exact resolventEvolutionMultiplier_range_error t.coe_nonneg (hSpec r hr)

/-- Pointwise range estimate in the actual Hilbert norm. -/
theorem resolventCfcEvolution_range_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) (x : H) :
    dist (resolventCfcEvolution R t (R x)) (R x) ≤ (t : ℝ) * ‖x‖ := by
  rw [dist_eq_norm]
  have he : resolventCfcEvolution R t (R x) - R x =
      ((resolventCfcEvolution R t - 1) * R) x := by
    simp only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self]
  rw [he]
  exact ((resolventCfcEvolution R t - 1) * R).le_opNorm x |>.trans
    (mul_le_mul_of_nonneg_right (resolventCfcEvolution_range_error_norm_le R hR hSpec t)
      (norm_nonneg x))

/-- Uniform continuity estimate on the dense resolvent range. -/
theorem resolventCfcEvolution_range_dist (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (s t : ℝ≥0) (x : H) :
    dist (resolventCfcEvolution R s (R x)) (resolventCfcEvolution R t (R x)) ≤
      dist s t * ‖x‖ := by
  suffices h : ∀ s t : ℝ≥0, t ≤ s →
      dist (resolventCfcEvolution R s (R x)) (resolventCfcEvolution R t (R x)) ≤
        dist s t * ‖x‖ by
    rcases le_total t s with hts | hst
    · exact h s t hts
    · simpa only [dist_comm] using h t s hst
  intro s t hts
  have he : s = t + (s - t) := (add_tsub_cancel_of_le hts).symm
  have hbound := resolventCfcEvolution_contracts R hSpec t
    (resolventCfcEvolution R (s - t) (R x) - R x)
  have hrange := resolventCfcEvolution_range_error R hR hSpec (s - t) x
  have hd : dist s t = ((s - t : ℝ≥0) : ℝ) := by
    change dist (s : ℝ) (t : ℝ) = _
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from hts)),
      NNReal.coe_sub hts]
  rw [← hd] at hrange
  rw [dist_eq_norm] at hrange ⊢
  calc
    _ = ‖resolventCfcEvolution R t (resolventCfcEvolution R (s - t) (R x) - R x)‖ := by
      conv_lhs => rw [he, resolventCfcEvolution_add, mul_apply_eq_comp, ← map_sub]
    _ ≤ _ := hbound
    _ ≤ _ := hrange

/-- Strong continuity on the complete Hilbert space, proved by dense-range approximation. -/
theorem continuous_resolventCfcEvolution (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) :
    Continuous (fun t : ℝ≥0 => resolventCfcEvolution R t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨y, hy⟩ := hDense.exists_dist_lt x (show 0 < ε / 3 by positivity)
  refine ⟨ε / (3 * (‖y‖ + 1)), by positivity, ?_⟩
  intro s hs
  have hnear : dist s t * ‖y‖ < ε / 3 := by
    have he := (lt_div_iff₀ (show 0 < 3 * (‖y‖ + 1) by positivity)).mp hs
    nlinarith [dist_nonneg (x := s) (y := t), norm_nonneg y]
  have hfirst : dist (resolventCfcEvolution R s x) (resolventCfcEvolution R s (R y)) ≤ dist x (R
    y) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact resolventCfcEvolution_contracts R hSpec s (x - R y)
  have hlast : dist (resolventCfcEvolution R t (R y)) (resolventCfcEvolution R t x) ≤ dist x (R
    y) := by
    rw [dist_comm, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact resolventCfcEvolution_contracts R hSpec t (x - R y)
  have hmid := resolventCfcEvolution_range_dist R hR hSpec s t y
  have htri := dist_triangle (resolventCfcEvolution R s x)
    (resolventCfcEvolution R s (R y)) (resolventCfcEvolution R t x)
  have htri' := dist_triangle (resolventCfcEvolution R s (R y))
    (resolventCfcEvolution R t (R y)) (resolventCfcEvolution R t x)
  linarith

/-- Strong continuity at zero follows from dense resolvent range, without a spectral gap. -/
theorem resolventCfcEvolution_continuousAt_zero (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) :
    ContinuousAt (fun t : ℝ≥0 => resolventCfcEvolution R t x) 0 :=
  (continuous_resolventCfcEvolution R hR hSpec hDense x).continuousAt

/-- Self-adjointness of every spectral evolution operator. -/
theorem resolventCfcEvolution_selfAdjoint (R : H →L[ℂ] H) (t : ℝ≥0) :
    IsSelfAdjoint (resolventCfcEvolution R t) :=
  cfc_predicate (resolventEvolutionMultiplier (t : ℝ)) R

/-- Positivity in the Hilbert operator order. -/
theorem resolventCfcEvolution_isPositive (R : H →L[ℂ] H)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    (resolventCfcEvolution R t).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  apply cfc_nonneg
  intro r hr
  exact (resolventEvolutionMultiplier_mem_unit_interval t.coe_nonneg (hSpec r hr)).1

/-- Joint strong continuity in time and vector. -/
theorem resolventCfcEvolution_tendsto_apply {ι : Type*} {l : Filter ι}
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (a : ι → ℝ≥0) (b : ι → H) (t : ℝ≥0) (x : H)
    (ha : Filter.Tendsto a l (nhds t)) (hb : Filter.Tendsto b l (nhds x)) :
    Filter.Tendsto (fun i => resolventCfcEvolution R (a i) (b i)) l
      (nhds (resolventCfcEvolution R t x)) := by
  have hfixed := (continuous_resolventCfcEvolution R hR hSpec hDense x).continuousAt.tendsto.comp ha
  have hdist : Filter.Tendsto (fun i => dist (b i) x +
      dist (resolventCfcEvolution R (a i) x) (resolventCfcEvolution R t x)) l (nhds 0) := by
    simpa only [dist_self, zero_add, Function.comp_apply] using
      (hb.dist (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (nhds x))).add
      (hfixed.dist (tendsto_const_nhds : Tendsto (fun _ : ι => resolventCfcEvolution R t x) l
        (nhds (resolventCfcEvolution R t x))))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) ?_ hdist
  intro i
  have he : dist (resolventCfcEvolution R (a i) (b i)) (resolventCfcEvolution R (a i) x) ≤ dist
    (b i) x := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact resolventCfcEvolution_contracts R hSpec (a i) (b i - x)
  exact (dist_triangle (resolventCfcEvolution R (a i) (b i))
    (resolventCfcEvolution R (a i) x) (resolventCfcEvolution R t x)).trans (add_le_add he le_rfl)

end
end GinibrePoincare
