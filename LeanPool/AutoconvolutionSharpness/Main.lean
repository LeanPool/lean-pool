/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Witness
public import LeanPool.AutoconvolutionSharpness.Coefficients
public import LeanPool.AutoconvolutionSharpness.GoodBlocks
public import LeanPool.AutoconvolutionSharpness.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The quantitative construction and sharpness

At this point both the coefficients and the analytic norms refer to the same
polynomial. We apply the estimate to its full coefficient vector, including
zeros, with its actual natural degree. Two limits control the factorial and
geometric factors as the parameters increase.
-/

@[expose] public section

open Filter Finset Polynomial
open scoped BigOperators Topology

namespace Autoconvolutions.Construction

/-- Equation (lower), for the actual step function of the constructed polynomial. -/
theorem witness_ratio_lower {m n K D : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4 * n < D)
    (hJ : 8 * n ^ 3 ≤ J.card) (hIJ : J.card ≤ I.card) :
    let F := witness D n K I J
    (1 - 1 / (n : ℝ)) * Parameters.factorialRatio (2 * n) (2 * K) *
      Parameters.geomRatio ((J.card : ℝ) / I.card) K ≤
      ratio (step F.natDegree (Polynomial.toFn (F.natDegree + 1) F)) := by
  classical
  let F := witness D n K I J
  let p := Polynomial.toFn (F.natDegree + 1) F
  have hn : 0 < n := by omega
  have hj : 0 < J.card := lt_of_lt_of_le (by positivity) hJ
  have hi := hj.trans_le hIJ
  have hp (i : Fin (F.natDegree + 1)) : 0 ≤ p i := witness_nonneg I J i.val
  have hne : ∃ i, 0 < p i := exists_pos_coeff_of_eval_pos F (eval_witness_pos I J hK.le hi hj)
  have cap (k : ℤ) : convCoeff F.natDegree p k ≤ Estimate.height n (2 * K) := by
    by_cases hk : k < 0
    · rw [convCoeff_of_neg _ _ hk]
      exact (Estimate.height_pos _ _).le
    · lift k to ℕ using (by omega : 0 ≤ k)
      rw [show convCoeff F.natDegree p (k : ℤ) = (F ^ 2).coeff k from convCoeff_eq_poly_sq F k]
      exact Blocks.coeff_cap I J hd hK hD k
  have hplateau (x : Blocks.Peak m) (hx : x ∈ Blocks.peakSet I J n K) (h : ℕ) (hh : h ≤ x.1) :
      convCoeff F.natDegree p ((D * Blocks.peakCode D x + h : ℕ) : ℤ) = Estimate.height n x.1 := by
    obtain ⟨hs,ha,hb⟩ := Blocks.peak_mem hx
    rw [show convCoeff F.natDegree p _ = (F ^ 2).coeff _ from convCoeff_eq_poly_sq F _]
    simpa only [F, witness, Blocks.key, Blocks.peakCode, Nat.add_comm h] using
      Blocks.coeff_eq_good I J hd hK hD hs ha hb h hh
  have bound := ratio_ge_blocks F.natDegree p hp hne (Estimate.height n (2 * K))
    (Estimate.height_pos _ _) cap D (Blocks.peakSet I J n K) (Blocks.peakCode D)
    Sigma.fst (fun x => Estimate.height n x.1)
    (Blocks.peakCode_injOn (by omega) hd hK.le hD)
    (fun x hx => by have hs := (Blocks.peak_mem hx).1; omega) hplateau
  rw [Blocks.peak_sum, show (∑ j, p j) = F.eval 1 from poly_sum_eq_eval_one F] at bound
  exact (Estimate.lower_le_block_fraction hn hK.le hJ hIJ (eval_witness I J hK.le hi)).trans bound

end Autoconvolutions.Construction

namespace Autoconvolutions.Parameters

/-- For fixed K, the ratio of factorial heights A₀ / A₂ₖ tends to one as n grows. -/
theorem tendsto_factorialRatio (K : ℕ) :
    Tendsto (fun n : ℕ => factorialRatio (2 * n) (2 * K)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => 1 - ((2 * (K : ℝ)) ^ 2 / 2) / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((2 * (K : ℝ)) ^ 2 / 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (K + 1)] with n hn
    have h := factorialRatio_lower (N := 2 * n) (j := 2 * K) (by omega) (by omega)
    simpa [Nat.cast_mul, div_div] using h
  · filter_upwards [eventually_ge_atTop K] with n hn
    have h := Estimate.height_mono (n := n) (i := 0) (j := 2 * K) (Nat.zero_le _) (by omega)
    have hrat : factorialRatio (2 * n) (2 * K) = Estimate.height n 0 / Estimate.height n (2 * K)
        := by
      simp [factorialRatio, Estimate.height, pow_two]
    rw [hrat]
    exact (div_le_one (Estimate.height_pos n (2 * K))).2 h

/-- With a fixed ratio of alphabet sizes, the quotient of the two truncated
geometric sums tends to that ratio. Mathlib's geometric and weighted
geometric series give the limits of the two partial sums. -/
theorem tendsto_geomRatio {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (geomRatio q) atTop (𝓝 q) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hq₀]
  have hnum := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).tendsto_sum_nat
  have hden := (hasSum_geometric_of_lt_one hq₀.le hq₁).tendsto_sum_nat
  have hq : 1 - q ≠ 0 := (sub_pos.mpr hq₁).ne'
  have h := (hnum.div (hden.pow 2) (pow_ne_zero 2 (inv_ne_zero hq))).comp
    (tendsto_add_atTop_nat 1)
  have he : (q / (1 - q) ^ 2) / ((1 - q)⁻¹) ^ 2 = q := by field_simp
  rw [he] at h
  exact h

end Autoconvolutions.Parameters
