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

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupCFC
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupGenerator

/-! # Exact infinitesimal identification of the resolvent semigroup -/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform second-order expansion on the twice-resolved range. -/
theorem resolventCfcEvolution_second_error_norm (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖(resolventCfcEvolution R t - 1) * R ^ 2 - (t : ℝ) • (R ^ 2 - R)‖ ≤ (t : ℝ) ^ 2 := by
  let f := resolventEvolutionMultiplier (t : ℝ)
  have hf : ContinuousOn f (spectrum ℝ R) := (resolventEvolutionMultiplier_continuous
    _).continuousOn
  have hpow : ContinuousOn (fun r : ℝ => r ^ 2) (spectrum ℝ R) := continuousOn_id.pow 2
  have hg : ContinuousOn (fun r : ℝ => r ^ 2 - r) (spectrum ℝ R) := hpow.sub continuousOn_id
  have he : cfc (fun r : ℝ => (f r - 1) * r ^ 2 - (t : ℝ) * (r ^ 2 - r)) R =
      (resolventCfcEvolution R t - 1) * R ^ 2 - (t : ℝ) • (R ^ 2 - R) := by
    rw [cfc_sub (fun r : ℝ => (f r - 1) * r ^ 2)
      (fun r : ℝ => (t : ℝ) * (r ^ 2 - r)) R
      ((hf.sub continuousOn_const).mul hpow) (hg.const_mul _),
      cfc_mul (fun r : ℝ => f r - 1) (fun r : ℝ => r ^ 2) R
        (hf.sub continuousOn_const) hpow,
      cfc_sub f (fun _ : ℝ => 1) R hf continuousOn_const,
      cfc_const_one (R := ℝ) (a := R), cfc_pow_id R 2 hR,
      cfc_const_mul (t : ℝ) (fun r : ℝ => r ^ 2 - r) R hg,
      cfc_sub (fun r : ℝ => r ^ 2) (fun r : ℝ => r) R hpow continuousOn_id,
      cfc_pow_id R 2 hR, cfc_id' ℝ R hR]
    rfl
  rw [← he]
  apply norm_cfc_le (sq_nonneg (t : ℝ))
  intro r hr
  simpa only [Real.norm_eq_abs] using resolventEvolutionMultiplier_second_error t.coe_nonneg
    (hSpec r hr)

/-- The actual nonnegative-time orbit, extended constantly for negative real times. -/
def resolventCfcOrbit (R : H →L[ℂ] H) (x : H) (t : ℝ) : H :=
  resolventCfcEvolution R (Real.toNNReal t) x

theorem resolventCfcOrbit_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) : Continuous (resolventCfcOrbit R x) :=
  (continuous_resolventCfcEvolution R hR hSpec hDense x).comp continuous_real_toNNReal

/-- Uniform second-order orbit error on actual twice-resolved vectors. -/
theorem resolventCfcEvolution_second_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) (x : H) :
    ‖resolventCfcEvolution R t (R (R x)) - R (R x) -
      (t : ℝ) • (R (R x) - R x)‖ ≤ (t : ℝ) ^ 2 * ‖x‖ := by
  have he : resolventCfcEvolution R t (R (R x)) - R (R x) -
      (t : ℝ) • (R (R x) - R x) =
      (((resolventCfcEvolution R t - 1) * R ^ 2 - (t : ℝ) • (R ^ 2 - R)) : H →L[ℂ] H) x := by
    simp only [pow_two, mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply]
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (resolventCfcEvolution_second_error_norm R hR hSpec t)
      (norm_nonneg x))

/-- Difference quotient after one application of the resolvent. -/
def resolventCfcDifferenceQuotient (R : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  t⁻¹ • ((resolventCfcEvolution R (Real.toNNReal t) - 1) * R)

theorem resolventCfcDifferenceQuotient_norm_le (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ‖resolventCfcDifferenceQuotient R t‖ ≤ 1 := by
  unfold resolventCfcDifferenceQuotient
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have he := resolventCfcEvolution_range_error_norm_le R hR hSpec (Real.toNNReal t)
  rw [Real.coe_toNNReal t ht.le] at he
  calc
    _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.le)
    _ = 1 := inv_mul_cancel₀ ht.ne'

theorem resolventCfcDifferenceQuotient_range_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) (x : H) :
    ‖resolventCfcDifferenceQuotient R t (R x) - (R - 1) (R x)‖ ≤ t * ‖x‖ := by
  have he : resolventCfcDifferenceQuotient R t (R x) - (R - 1) (R x) =
      t⁻¹ • (resolventCfcEvolution R (Real.toNNReal t) (R (R x)) - R (R x) -
        t • (R (R x) - R x)) := by
    simp only [resolventCfcDifferenceQuotient, smul_apply, mul_apply_eq_comp,
      sub_apply, one_apply_eq_self, smul_sub, inv_smul_smul₀ ht.ne']
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have hb := resolventCfcEvolution_second_error R hR hSpec (Real.toNNReal t) x
  rw [Real.coe_toNNReal t ht.le] at hb
  calc
    _ ≤ t⁻¹ * (t ^ 2 * ‖x‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.le)
    _ = t * ‖x‖ := by field_simp

/-- Convergence of the difference quotient on every vector, including outside the operator
  domain. -/
theorem resolventCfcDifferenceQuotient_tendsto (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) :
    Tendsto (fun t : ℝ => resolventCfcDifferenceQuotient R t x)
      (𝓝[Set.Ioi 0] 0) (𝓝 ((R - 1) x)) := by
  let quotient (t : ℝ) : H →L[ℂ] H :=
    if 0 < t then resolventCfcDifferenceQuotient R t else 0
  have hbound (t : ℝ) : ‖quotient t‖ ≤ 1 := by
    unfold quotient
    split_ifs with ht
    · exact resolventCfcDifferenceQuotient_norm_le R hR hSpec ht
    · simp
  have hEq := equicontinuous_of_opNorm_le_one quotient hbound
  have hClosed := hEq.isClosed_setOfPred_tendsto (l := 𝓝[Set.Ioi 0] 0) (R - 1).continuous
  have hRange : Set.range R ⊆ {y | Tendsto (fun t => quotient t y)
      (𝓝[Set.Ioi 0] 0) (𝓝 ((R - 1) y))} := by
    rintro _ ⟨y, rfl⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t < ε / (‖y‖ + 1) :=
      (eventually_lt_nhds (show (0 : ℝ) < ε / (‖y‖ + 1) by positivity)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hnear
    have hpos : 0 < t := ht
    change dist (quotient t (R y)) ((R - 1) (R y)) < ε
    have heq : quotient t = resolventCfcDifferenceQuotient R t := ite_eq_left hpos
    rw [heq, dist_eq_norm]
    calc
      _ ≤ t * ‖y‖ := resolventCfcDifferenceQuotient_range_error R hR hSpec hpos y
      _ ≤ t * (‖y‖ + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hpos.le
      _ < ε := (lt_div_iff₀ (by positivity : 0 < ‖y‖ + 1)).mp hnear
  have hlim := (closure_minimal hRange hClosed) (hDense x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [quotient, show 0 < t from ht]

/-- The exact derivative on the entire resolvent domain. -/
theorem resolventCfcOrbit_hasDerivWithinAt_range (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (x : H) :
    HasDerivWithinAt (resolventCfcOrbit R (R x)) (R x - x) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t; simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨ht, hn⟩; exact lt_of_le_of_ne ht (Ne.symm hn)
    · intro ht; exact ⟨ht.le, ht.ne'⟩
  rw [hset]
  have he : (R - 1) x = R x - x := by simp only [sub_apply, one_apply_eq_self]
  rw [← he]
  apply (resolventCfcDifferenceQuotient_tendsto R hR hSpec hDense x).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_module, sub_zero, resolventCfcOrbit, Real.toNNReal_zero,
    resolventCfcEvolution_zero R hR, one_apply_eq_self, resolventCfcDifferenceQuotient,
    smul_apply, mul_apply_eq_comp, sub_apply]

/-- Generator graph membership gives the actual semigroup right derivative. -/
theorem resolventGenerator_hasDerivWithinAt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (u v : H) (hp : (u, v) ∈ (resolventGenerator R hInj).graph) :
    HasDerivWithinAt (resolventCfcOrbit R u) v (Set.Ici 0) 0 := by
  rw [resolventGenerator_graph R hInj] at hp
  change R (u - v) = u at hp
  have hd := resolventCfcOrbit_hasDerivWithinAt_range R hR hSpec hDense (u - v)
  rw [hp] at hd
  convert hd using 1
  abel

/-- Resolvent commutation follows from the continuous functional calculus. -/
theorem resolventCfcEvolution_commutes (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (t : ℝ≥0) :
    Commute R (resolventCfcEvolution R t) := by
  have he := cfc_commute_cfc (id : ℝ → ℝ) (resolventEvolutionMultiplier (t : ℝ)) R
  rw [cfc_id ℝ R hR] at he
  exact he

/-- An actual right derivative necessarily belongs to the exact generator graph. -/
theorem resolventGenerator_graph_of_hasDerivWithinAt (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (u v : H)
    (hd : HasDerivWithinAt (resolventCfcOrbit R u) v (Set.Ici 0) 0) :
    (u, v) ∈ (resolventGenerator R hInj).graph := by
  have hcomp : HasDerivWithinAt (fun t : ℝ => R (resolventCfcOrbit R u t))
      (R v) (Set.Ici 0) 0 := (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  have he : (fun t : ℝ => R (resolventCfcOrbit R u t)) = resolventCfcOrbit R (R u) := by
    funext t
    exact congrArg (fun L : H →L[ℂ] H => L u)
      (resolventCfcEvolution_commutes R hR (Real.toNNReal t)).eq
  rw [he] at hcomp
  have hder := resolventCfcOrbit_hasDerivWithinAt_range R hR hSpec hDense u
  have hv := UniqueDiffWithinAt.eq_deriv (Set.Ici (0 : ℝ))
    (uniqueDiffWithinAt_Ici 0) hcomp hder
  rw [resolventGenerator_graph R hInj]
  change R (u - v) = u
  rw [map_sub, hv]
  abel

/-- Exact infinitesimal generator of the strongly continuous CFC semigroup. -/
theorem resolventGenerator_graph_iff_right_derivative (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (hDense : DenseRange R) (u v : H) :
    (u, v) ∈ (resolventGenerator R hInj).graph ↔
      HasDerivWithinAt (resolventCfcOrbit R u) v (Set.Ici 0) 0 :=
  ⟨resolventGenerator_hasDerivWithinAt R hR hInj hSpec hDense u v,
    resolventGenerator_graph_of_hasDerivWithinAt R hR hInj hSpec hDense u v⟩

/-- Every semigroup operator preserves the full generator domain and commutes with it. -/
theorem resolventCfcEvolution_preserves_generator_graph (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hInj : Function.Injective R) (t : ℝ≥0) (u v : H)
    (hp : (u, v) ∈ (resolventGenerator R hInj).graph) :
    (resolventCfcEvolution R t u, resolventCfcEvolution R t v) ∈
      (resolventGenerator R hInj).graph := by
  rw [resolventGenerator_graph R hInj] at hp ⊢
  change R (u - v) = u at hp
  change R (resolventCfcEvolution R t u - resolventCfcEvolution R t v) = resolventCfcEvolution R t u
  rw [← map_sub]
  have he := congrArg (fun L : H →L[ℂ] H => L (u - v))
    (resolventCfcEvolution_commutes R hR t).eq
  change R (resolventCfcEvolution R t (u - v)) = resolventCfcEvolution R t (R (u - v)) at he
  rw [he, hp]

end
end GinibrePoincare
