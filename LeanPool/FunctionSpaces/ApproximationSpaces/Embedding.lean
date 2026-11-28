/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Embeddings between approximation spaces

For a fixed scheme, the approximation spaces are ordered as follows (Pietsch, DeVore–Lorentz
§7.9):

* `A^s_q ↪ A^s_r` for `q ≤ r`: the fine index may be increased
  (`approxNormDyadic_mono_exponent`);
* `A^s_q ↪ A^t_r` for `t < s` and any `q, r`: a loss in smoothness absorbs any change of the
  fine index (`approxNormDyadic_le_of_lt`), with the constant `(1 - 2^(-(s-t)))⁻¹`.

In the dyadic form both are elementary: the first is the monotonicity of `ℓ_q` norms in `q`,
the second the bound `2^(kt) E_{2^k} ≤ 2^(-k(s-t)) · sup_j 2^(js) E_{2^j}` and the `ℓ_r` norm of
a geometric sequence.  Both are transported to Pietsch's quasi-norm, and combined in
`MemApprox.mono`.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {A : ApproximationScheme X} {s t : ℝ} {q r : ℝ≥0∞}

/-- **Increasing the fine index**: `‖f‖_{A^s_r} ≤ ‖f‖_{A^s_q}` in the dyadic form, for
`0 < q ≤ r`. -/
theorem approxNormDyadic_mono_exponent (hq0 : q ≠ 0) (hqr : q ≤ r) (f : X) :
    A.approxNormDyadic s r f ≤ A.approxNormDyadic s q f := by
  unfold approxNormDyadic
  gcongr
  exact ENNReal.lqNorm_le_lqNorm_of_le hq0 hqr _

/-- Changing the smoothness index multiplies the dyadic terms by `2^(k(t-s))`. -/
theorem approxSeqDyadic_eq_mul (s t : ℝ) (f : X) (k : ℕ) :
    A.approxSeqDyadic t f k = dyadicWeight (t - s) k * A.approxSeqDyadic s f k := by
  rw [approxSeqDyadic, approxSeqDyadic, ← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel]

/-- **Trading smoothness for the fine index**: for `t < s` and `1 ≤ q, r ≤ ∞`,
`‖f‖_{A^t_r} ≤ (1 - 2^(-(s-t)))⁻¹ ‖f‖_{A^s_q}` in the dyadic form. -/
theorem approxNormDyadic_le_of_lt (hq : 1 ≤ q) (hr : 1 ≤ r) (f : X) :
    A.approxNormDyadic t r f ≤ (1 - (2 : ℝ≥0∞) ^ (-(s - t)))⁻¹ * A.approxNormDyadic s q f := by
  set C := (1 - (2 : ℝ≥0∞) ^ (-(s - t)))⁻¹
  set D := lqNorm q (A.approxSeqDyadic s f)
  have hC : 1 ≤ C := ENNReal.one_le_one_sub_two_rpow_neg_inv _
  have hD : lqNorm r (A.approxSeqDyadic t f) ≤ C * D := by
    calc lqNorm r (A.approxSeqDyadic t f)
        ≤ lqNorm r (fun k => D * dyadicWeight (-(s - t)) k) := ENNReal.lqNorm_mono fun k => by
          rw [approxSeqDyadic_eq_mul s t, show t - s = -(s - t) by ring, mul_comm D]
          gcongr
          exact approxSeqDyadic_le_lqNorm (zero_lt_one.trans_le hq).ne' f k
      _ = D * lqNorm r (dyadicWeight (-(s - t))) := ENNReal.lqNorm_const_mul _ _
      _ ≤ D * C := by gcongr; exact ENNReal.lqNorm_dyadicWeight_neg_le hr _
      _ = C * D := mul_comm _ _
  calc A.approxNormDyadic t r f = ‖f‖ₑ + lqNorm r (A.approxSeqDyadic t f) := rfl
    _ ≤ C * ‖f‖ₑ + C * D := add_le_add (le_mul_of_one_le_left' hC) hD
    _ = C * A.approxNormDyadic s q f := by rw [approxNormDyadic, mul_add]

/-- **Increasing the fine index** for Pietsch's quasi-norm, `s ≥ 0`, `1 ≤ q ≤ r`. -/
theorem approxNorm_le_of_exponent_le (hq : 1 ≤ q) (hqr : q ≤ r) (hs : 0 ≤ s) (f : X) :
    A.approxNorm s r f ≤ 2 ^ s * (4 * 2 ^ s) * A.approxNorm s q f := by
  calc A.approxNorm s r f ≤ 2 ^ s * A.approxNormDyadic s r f :=
        approxNorm_le_approxNormDyadic (hq.trans hqr) hs f
    _ ≤ 2 ^ s * A.approxNormDyadic s q f := by
        gcongr; exact approxNormDyadic_mono_exponent (zero_lt_one.trans_le hq).ne' hqr f
    _ ≤ 2 ^ s * (4 * 2 ^ s * A.approxNorm s q f) := by
        gcongr; exact approxNormDyadic_le_approxNorm hq hs f
    _ = _ := by ring

/-- **Trading smoothness for the fine index** for Pietsch's quasi-norm, `0 ≤ t < s`. -/
theorem approxNorm_le_of_lt (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 0 ≤ t) (hts : t < s) (f : X) :
    A.approxNorm t r f ≤
      2 ^ t * (1 - (2 : ℝ≥0∞) ^ (-(s - t)))⁻¹ * (4 * 2 ^ s) * A.approxNorm s q f := by
  calc A.approxNorm t r f ≤ 2 ^ t * A.approxNormDyadic t r f :=
        approxNorm_le_approxNormDyadic hr ht f
    _ ≤ 2 ^ t * ((1 - (2 : ℝ≥0∞) ^ (-(s - t)))⁻¹ * A.approxNormDyadic s q f) := by
        gcongr; exact approxNormDyadic_le_of_lt hq hr f
    _ ≤ 2 ^ t * ((1 - (2 : ℝ≥0∞) ^ (-(s - t)))⁻¹ * (4 * 2 ^ s * A.approxNorm s q f)) := by
        gcongr; exact approxNormDyadic_le_approxNorm hq (ht.trans hts.le) f
    _ = _ := by ring

/-- `A^s_q ⊆ A^s_r` for `1 ≤ q ≤ r` and `s ≥ 0`. -/
theorem MemApprox.mono_exponent (hq : 1 ≤ q) (hqr : q ≤ r) (hs : 0 ≤ s) {f : X}
    (hf : A.MemApprox s q f) : A.MemApprox s r f := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs] at hf
  rw [memApprox_iff_approxNormDyadic_lt_top (hq.trans hqr) hs]
  exact (approxNormDyadic_mono_exponent (zero_lt_one.trans_le hq).ne' hqr f).trans_lt hf

/-- `A^s_q ⊆ A^t_r` for `0 ≤ t < s` and all `1 ≤ q, r ≤ ∞`. -/
theorem MemApprox.of_lt (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 0 ≤ t) (hts : t < s) {f : X}
    (hf : A.MemApprox s q f) : A.MemApprox t r f := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq (ht.trans hts.le)] at hf
  rw [memApprox_iff_approxNormDyadic_lt_top hr ht]
  exact (approxNormDyadic_le_of_lt hq hr f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hts)).lt_top hf)

/-- **The embeddings `A^s_q ↪ A^t_r`**: for `0 ≤ t` and either `t < s`, or `t = s` and
`q ≤ r`, every element of `A^s_q` belongs to `A^t_r`. -/
theorem MemApprox.mono (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 0 ≤ t)
    (h : t < s ∨ (t = s ∧ q ≤ r)) {f : X} (hf : A.MemApprox s q f) : A.MemApprox t r f := by
  rcases h with h | ⟨rfl, hqr⟩
  · exact hf.of_lt hq hr ht h
  · exact hf.mono_exponent hq hqr ht

/-- The approximation spaces decrease in `s` and increase in `q`, as submodules. -/
theorem approxSpace_mono (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h : t < s ∨ (t = s ∧ q ≤ r)) : A.approxSpace s q hs hq ≤ A.approxSpace t r ht hr :=
  fun _ hf => MemApprox.mono hq hr ht h hf

/-- For `0 ≤ t < s`, the dyadic series `∑ₖ 2^(kt) E_{2^k}(f)` converges for `f ∈ A^s_q`.  This
is the form in which telescoping arguments use membership. -/
theorem MemApprox.lqNorm_one_lt_top (hq : 1 ≤ q) (ht : 0 ≤ t) (hts : t < s) {f : X}
    (hf : A.MemApprox s q f) : lqNorm 1 (A.approxSeqDyadic t f) < ∞ :=
  (memApprox_iff_lqNorm_dyadic_lt_top le_rfl ht).1 (hf.of_lt hq le_rfl ht hts)

end ApproximationScheme
