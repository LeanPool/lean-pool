/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.Main

/-!
# Sharpness of the Martin–O’Bryant autoconvolution inequality
-/

public section

namespace Autoconvolutions

open Construction Filter Finset
open scoped Topology

/-- Theorem 1 of Crmarić, Kovač and Rupčić. Section 2 chooses a rational
alphabet ratio close to one, then a truncation level, then the polynomial
exponent. Scaling the two alphabets preserves their selected ratio. -/
theorem sharpness (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (p : Fin (d + 1) → ℝ),
      (∀ j, 0 ≤ p j) ∧ (∃ j, 0 < p j) ∧
      1 - ε < ratio (step d p) := by
  have hε₁ : 1 - ε < 1 := by linarith
  obtain ⟨m, hm, hmε⟩ :=
    ((eventually_gt_atTop 0).and ((tendsto_natCast_div_add_atTop (1 : ℝ)).eventually_const_lt
        hε₁)).exists
  let q : ℝ := m / ((m : ℝ) + 1)
  have hq₀ : 0 < q := by dsimp [q]; positivity
  have hq₁ : q < 1 := by
    dsimp [q]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hqε : 1 - ε < q := hmε
  obtain ⟨K, _, hKε⟩ := ((eventually_gt_atTop 0).and
    ((Parameters.tendsto_geomRatio hq₀ hq₁).eventually_const_lt hqε)).exists
  have h₁ : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) *
      Parameters.factorialRatio (2 * n) (2 * K) * Parameters.geomRatio q K)
      atTop (𝓝 (Parameters.geomRatio q K)) := by
    simpa using ((h₁.mul (Parameters.tendsto_factorialRatio K)).mul_const (Parameters.geomRatio q
        K))
  obtain ⟨n, hKn, hnε⟩ := ((eventually_gt_atTop K).and (hlim.eventually_const_lt hKε)).exists
  let scale := 8 * n ^ 3
  let b := m * scale
  let r := (m + 1) * scale
  have hn : 0 < n := by omega
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hb : 8 * n ^ 3 ≤ b := Nat.le_mul_of_pos_left scale hm
  have hbr : b < r := by dsimp [b, r]; rw [Nat.add_one_mul]; omega
  have hratio : (b : ℝ) / r = q := by
    dsimp [q, b, r]
    push_cast
    exact mul_div_mul_right _ _ (by exact_mod_cast hscale.ne' : (scale : ℝ) ≠ 0)
  let I := oddAlphabet r
  let J := evenAlphabet r b hbr.le
  have hi : I.card = r := card_oddAlphabet r
  have hj : J.card = b := card_evenAlphabet r b hbr.le
  have hJpos : 0 < J.card := by rw [hj]; exact hscale.trans_le hb
  let F := witness (4 * n + 1) n K I J
  have hF : 0 < F.eval 1 := eval_witness_pos I J hKn.le (by omega) hJpos
  refine ⟨F.natDegree, Polynomial.toFn (F.natDegree + 1) F,
    fun j => witness_nonneg I J j.val, exists_pos_coeff_of_eval_pos F hF, ?_⟩
  have hlower := witness_ratio_lower I J (disjoint_alphabets r b hbr.le) hKn
    (Nat.lt_succ_self (4 * n)) (hj ▸ hb) (by omega)
  dsimp only at hlower
  rw [hj, hi, hratio] at hlower
  exact hnε.trans_le hlower

end Autoconvolutions
