/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Norm
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Dyadic
public import Mathlib.Analysis.MeanInequalitiesPow

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The dyadic quasi-norm of `A^s_q`

Since `E_n(f)` decreases in `n`, only the errors at the dyadic points `n = 2^k` matter:
for `s ≥ 0` and `1 ≤ q ≤ ∞`,

`‖f‖_{A^s_q} ≍ ‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}`,

with the explicit constants `approxNorm ≤ 2^s · approxNormDyadic` and
`approxNormDyadic ≤ 4 · 2^s · approxNorm` (`approxNorm_le_approxNormDyadic`,
`approxNormDyadic_le_approxNorm`).  The term `‖f‖` is needed because the dyadic sequence
starts with `E_1(f)`, which vanishes on `A 1`, while Pietsch's sequence starts with
`E_0(f) = ‖f‖`.

The equivalence holds for every `q ∈ (0, ∞]`, also below `1`, with the constants
`C_q 2^s` and `4 C_q² 2^s`, where `C_q = LpAddConst q` is Mathlib's constant of the
quasi-triangle inequality, `2^(1/q - 1)` for `0 < q < 1` and `1` otherwise
(`approxNorm_le_approxNormDyadic'`, `approxNormDyadic_le_approxNorm'`,
`memApprox_iff_approxNormDyadic_lt_top'`, `memApprox_iff_lqNorm_dyadic_lt_top'`); the statements
for `q ≥ 1` are their cases `C_q = 1`. The primed statements assume `q ≠ 0`, the range `(0, ∞]`
of Pietsch's definition; the bound of the dyadic quasi-norm by Pietsch's needs it, since
`lqNorm 0 = 0`.

**Why the dyadic form is the working norm.** Its weights `2^(ks)` do not depend on `q`, so
comparing different `q` is monotonicity of `ℓ_q` norms, and a shift `k ↦ k + 1` multiplies the
weights by the constant `2^s`.  Every later theorem is proved for `approxNormDyadic` and
transported through this equivalence; no later proof unfolds Pietsch's weights `n^(s - 1/q)`.

For an approximant `a ∈ A_{2^k}` the quasi-norm of `A^s_∞` is at most a finite sum
(`approxNormDyadic_top_le_of_mem`).  The file ends with the consequence that the errors of an
element of `A^s_q`, `s > 0`, tend to zero, so that `A^s_q` lies in the closure of `⋃ A n`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight LpAddConst LpAddConst_of_one_le)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (A : ApproximationScheme X)

/-- The **dyadic sequence** `(2^(ks) E_{2^k}(f))_k`. -/
noncomputable def approxSeqDyadic (s : ℝ) (f : X) (k : ℕ) : ℝ≥0∞ :=
  dyadicWeight s k * A.approxError f (2 ^ k)

/-- The **dyadic quasi-norm** `‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}`, equivalent to Pietsch's
quasi-norm for `s ≥ 0`. -/
noncomputable def approxNormDyadic (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f)

variable {A} {s : ℝ} {q : ℝ≥0∞}

/-- Each term `2^(ks) E_{2^k}(f)` is at most the `ℓ_q` norm of the dyadic sequence, for every
`q ≠ 0`. -/
theorem approxSeqDyadic_le_lqNorm (hq0 : q ≠ 0) (f : X) (k : ℕ) :
    A.approxSeqDyadic s f k ≤ lqNorm q (A.approxSeqDyadic s f) :=
  ENNReal.le_lqNorm hq0 _ k

/-- `‖f‖ ≤ ‖f‖^dyadic_{A^s_q}`. -/
theorem enorm_le_approxNormDyadic (f : X) : ‖f‖ₑ ≤ A.approxNormDyadic s q f := le_self_add

/-- The `ℓ_q` part of the dyadic quasi-norm is at most the quasi-norm. -/
theorem lqNorm_le_approxNormDyadic (f : X) :
    lqNorm q (A.approxSeqDyadic s f) ≤ A.approxNormDyadic s q f := le_add_self

/-- Powers of the dyadic terms: `(2^(ks) E_{2^k}(f))^p = 2^(ksp) E_{2^k}(f)^p` for `p ≥ 0`. -/
theorem approxSeqDyadic_rpow {p : ℝ} (hp : 0 ≤ p) (f : X) (k : ℕ) :
    A.approxSeqDyadic s f k ^ p = dyadicWeight (s * p) k * A.approxError f (2 ^ k) ^ p := by
  rw [approxSeqDyadic, ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.dyadicWeight_rpow]

/-- The first dyadic term is `E_1(f)`. -/
theorem approxSeqDyadic_zero (f : X) : A.approxSeqDyadic s f 0 = A.approxError f 1 := by
  simp [approxSeqDyadic]

/-- The dyadic quasi-norm of `0` is `0`. -/
@[simp]
theorem approxNormDyadic_zero (s : ℝ) (q : ℝ≥0∞) : A.approxNormDyadic s q 0 = 0 := by
  have : A.approxSeqDyadic s 0 = fun _ => 0 := by funext k; simp [approxSeqDyadic]
  simp [approxNormDyadic, this]

/-- The dyadic terms are homogeneous: `2^(ks) E_{2^k}(c f) = |c| 2^(ks) E_{2^k}(f)`. -/
theorem approxSeqDyadic_smul (c : ℝ) (f : X) :
    A.approxSeqDyadic s (c • f) = fun k => ‖c‖ₑ * A.approxSeqDyadic s f k := by
  funext k; rw [approxSeqDyadic, approxSeqDyadic, approxError_smul, mul_left_comm]

/-- The dyadic quasi-norm is homogeneous: `‖c f‖^dyadic = |c| ‖f‖^dyadic`. -/
theorem approxNormDyadic_smul (c : ℝ) (f : X) :
    A.approxNormDyadic s q (c • f) = ‖c‖ₑ * A.approxNormDyadic s q f := by
  rw [approxNormDyadic, approxNormDyadic, approxSeqDyadic_smul, ENNReal.lqNorm_const_mul,
    eNorm_smul, mul_add]

/-- The dyadic quasi-norm is even: `‖-f‖_{A^s_q} = ‖f‖_{A^s_q}`. -/
theorem approxNormDyadic_neg (f : X) : A.approxNormDyadic s q (-f) = A.approxNormDyadic s q f := by
  have h : A.approxSeqDyadic s (-f) = A.approxSeqDyadic s f := by
    funext k
    rw [approxSeqDyadic, approxSeqDyadic, approxError_neg]
  rw [approxNormDyadic, approxNormDyadic, h, eNorm_neg]

/-- **Pietsch's quasi-norm is dominated by the dyadic one**, for every `q ≠ 0`: for `s ≥ 0`,
`‖f‖_{A^s_q} ≤ C_q 2^s (‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q)` with Mathlib's constant
`C_q = LpAddConst q` of the quasi-triangle inequality (`1` for `q ≥ 1`). Cauchy condensation
compares the `q`-th powers, and `(x^q + y^q)^(1/q) ≤ C_q (x + y)`
(`ENNReal.rpow_add_rpow_le_LpAddConst_mul`). -/
theorem approxNorm_le_approxNormDyadic' (hq0 : q ≠ 0) (hs : 0 ≤ s) (f : X) :
    A.approxNorm s q f ≤ LpAddConst q * 2 ^ s * A.approxNormDyadic s q f := by
  have h2s := ENNReal.one_le_two_rpow hs
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [LpAddConst_of_one_le le_top, one_mul, approxNorm_top, approxNormDyadic,
      ENNReal.lqNorm_top]
    calc ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxError f n
        ≤ A.approxError f 0 + 2 ^ s * ⨆ k, dyadicWeight s k * A.approxError f (2 ^ k) :=
          ENNReal.iSup_pow_mul_le_dyadic (approxError_anti f) hs
      _ ≤ 2 ^ s * ‖f‖ₑ + 2 ^ s * ⨆ k, A.approxSeqDyadic s f k := by
          rw [approxError_zero_right]
          exact add_le_add (le_mul_of_one_le_left' h2s) le_rfl
      _ = 2 ^ s * (‖f‖ₑ + ⨆ k, A.approxSeqDyadic s f k) := by rw [mul_add]
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
  have hD : lqNorm q (A.approxSeqDyadic s f) ^ q.toReal =
      ∑' k, dyadicWeight (s * q.toReal) k * A.approxError f (2 ^ k) ^ q.toReal := by
    rw [ENNReal.lqNorm_rpow hq0 hq']
    simp_rw [approxSeqDyadic_rpow hp.le]
  set p := q.toReal
  have hb : Antitone fun n => A.approxError f n ^ p := fun m n h =>
    ENNReal.rpow_le_rpow (approxError_anti f h) hp.le
  set D := lqNorm q (A.approxSeqDyadic s f)
  have hpow : A.approxNorm s q f ^ p ≤ (2 ^ s) ^ p * (‖f‖ₑ ^ p + D ^ p) := by
    rw [approxNorm_rpow hq0 hq']
    calc ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) * A.approxError f n ^ p
        ≤ A.approxError f 0 ^ p + 2 ^ max (s * p - 1) 0 *
            ∑' k, dyadicWeight (s * p - 1 + 1) k * A.approxError f (2 ^ k) ^ p :=
          ENNReal.tsum_pow_mul_le_dyadic hb (s * p - 1)
      _ = ‖f‖ₑ ^ p + 2 ^ max (s * p - 1) 0 * D ^ p := by
          rw [sub_add_cancel, hD, approxError_zero_right]
      _ ≤ (2 ^ s) ^ p * ‖f‖ₑ ^ p + (2 ^ s) ^ p * D ^ p := by
          gcongr
          · exact le_mul_of_one_le_left' (ENNReal.one_le_rpow h2s hp |>.trans_eq' rfl)
          · rw [← ENNReal.rpow_mul]
            exact ENNReal.rpow_le_rpow_of_exponent_le one_le_two
              (max_le (by linarith) (by positivity))
      _ = (2 ^ s) ^ p * (‖f‖ₑ ^ p + D ^ p) := by rw [mul_add]
  calc A.approxNorm s q f = (A.approxNorm s q f ^ p) ^ (1 / p) := by
        rw [one_div, ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ ((2 ^ s) ^ p * (‖f‖ₑ ^ p + D ^ p)) ^ (1 / p) := by gcongr
    _ = 2 ^ s * (‖f‖ₑ ^ p + D ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div, ENNReal.rpow_rpow_inv hp.ne']
    _ ≤ 2 ^ s * (LpAddConst q * (‖f‖ₑ + D)) := by
        gcongr; exact ENNReal.rpow_add_rpow_le_LpAddConst_mul hq0 hq' _ _
    _ = LpAddConst q * 2 ^ s * A.approxNormDyadic s q f := by rw [approxNormDyadic]; ring

/-- **Pietsch's quasi-norm is dominated by the dyadic one**: for `s ≥ 0` and `1 ≤ q ≤ ∞`,
`‖f‖_{A^s_q} ≤ 2^s (‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q)`, the case `LpAddConst q = 1` of
`ApproximationScheme.approxNorm_le_approxNormDyadic'`. -/
theorem approxNorm_le_approxNormDyadic (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    A.approxNorm s q f ≤ 2 ^ s * A.approxNormDyadic s q f := by
  simpa [LpAddConst_of_one_le hq] using
    approxNorm_le_approxNormDyadic' (zero_lt_one.trans_le hq).ne' hs f

/-- **The shifted dyadic sequence**, for every `q ≠ 0`: `(2^(ks) E_{2^(k+1)}(f))_k` has `ℓ_q` norm
at most `2 C_q ‖f‖_{A^s_q}` for `s ≥ 0`, with Mathlib's constant `C_q = LpAddConst q`. Cauchy
condensation bounds the `q`-th power by `2^(max(1 - sq, 0)) ≤ 2 ≤ (2 C_q)^q` times
`‖f‖_{A^s_q}^q` (`ENNReal.two_rpow_one_div_le_two_mul_LpAddConst`). -/
theorem lqNorm_dyadic_succ_le' (hq0 : q ≠ 0) (hs : 0 ≤ s) (f : X) :
    lqNorm q (fun k => dyadicWeight s k * A.approxError f (2 ^ (k + 1))) ≤
      2 * LpAddConst q * A.approxNorm s q f := by
  rcases eq_or_ne q ∞ with rfl | hq'
  · rw [ENNReal.lqNorm_top, LpAddConst_of_one_le le_top, mul_one]
    calc ⨆ k, dyadicWeight s k * A.approxError f (2 ^ (k + 1))
        ≤ ⨆ k, dyadicWeight s k * A.approxError f (2 ^ k) := iSup_mono fun k => by
          gcongr
          exact approxError_anti f (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
      _ ≤ ⨆ n, ((n + 1 : ℕ) : ℝ≥0∞) ^ s * A.approxError f n := ENNReal.dyadic_le_iSup_pow_mul hs
      _ = A.approxNorm s ∞ f := (approxNorm_top s f).symm
      _ ≤ 2 * A.approxNorm s ∞ f := le_mul_of_one_le_left' one_le_two
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq'
  set p := q.toReal
  have hb : Antitone fun n => A.approxError f n ^ p := fun m n h =>
    ENNReal.rpow_le_rpow (approxError_anti f h) hp.le
  have h2 : (2 : ℝ≥0∞) ≤ (2 * LpAddConst q) ^ p := by
    calc (2 : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
      _ ≤ (2 * LpAddConst q) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.two_rpow_one_div_le_two_mul_LpAddConst q) hp.le
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.lqNorm_rpow hq0 hq']
  calc ∑' k, (dyadicWeight s k * A.approxError f (2 ^ (k + 1))) ^ p
      = ∑' k, dyadicWeight (s * p - 1 + 1) k * A.approxError f (2 ^ (k + 1)) ^ p := by
        congr 1; funext k
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.dyadicWeight_rpow, sub_add_cancel]
    _ ≤ 2 ^ max (-(s * p - 1)) 0 * ∑' n, ((n + 1 : ℕ) : ℝ≥0∞) ^ (s * p - 1) *
          A.approxError f n ^ p := ENNReal.dyadic_le_tsum_pow_mul hb _
    _ = 2 ^ max (-(s * p - 1)) 0 * A.approxNorm s q f ^ p := by rw [approxNorm_rpow hq0 hq']
    _ ≤ (2 * LpAddConst q) ^ p * A.approxNorm s q f ^ p := by
        have hsp : 0 ≤ s * p := mul_nonneg hs hp.le
        gcongr ?_ * _
        refine le_trans ?_ h2
        calc (2 : ℝ≥0∞) ^ max (-(s * p - 1)) 0 ≤ 2 ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le one_le_two (max_le (by linarith) zero_le_one)
          _ = 2 := ENNReal.rpow_one 2
    _ = (2 * LpAddConst q * A.approxNorm s q f) ^ p := (ENNReal.mul_rpow_of_nonneg _ _ hp.le).symm

/-- The shifted dyadic sequence `(2^(ks) E_{2^(k+1)}(f))_k` is dominated by twice Pietsch's
quasi-norm for `1 ≤ q ≤ ∞`, the case `LpAddConst q = 1` of
`ApproximationScheme.lqNorm_dyadic_succ_le'`. -/
theorem lqNorm_dyadic_succ_le (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    lqNorm q (fun k => dyadicWeight s k * A.approxError f (2 ^ (k + 1))) ≤
      2 * A.approxNorm s q f := by
  simpa [LpAddConst_of_one_le hq] using lqNorm_dyadic_succ_le' (zero_lt_one.trans_le hq).ne' hs f

/-- **The dyadic quasi-norm is dominated by Pietsch's**, for every `q ≠ 0`: for `s ≥ 0`,
`‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q ≤ 4 C_q² 2^s ‖f‖_{A^s_q}` with Mathlib's constant
`C_q = LpAddConst q` of the quasi-triangle inequality (`1` for `q ≥ 1`). The first dyadic term is
`E_1(f) ≤ ‖f‖`, and the shifted ones are bounded by `ApproximationScheme.lqNorm_dyadic_succ_le'`;
splitting off the first term costs `C_q` (`ENNReal.lqNorm_le_head_add_shift'`). -/
theorem approxNormDyadic_le_approxNorm' (hq0 : q ≠ 0) (hs : 0 ≤ s) (f : X) :
    A.approxNormDyadic s q f ≤ LpAddConst q ^ 2 * 4 * 2 ^ s * A.approxNorm s q f := by
  set P := A.approxNorm s q f
  set C := LpAddConst q
  have h2s := ENNReal.one_le_two_rpow hs
  have hC : 1 ≤ C := ENNReal.one_le_LpAddConst q
  have h1 : 1 ≤ C ^ 2 * 2 ^ s :=
    (one_mul (1 : ℝ≥0∞)).symm.le.trans (mul_le_mul' (one_le_pow₀ hC) h2s)
  have hC2 : C ≤ C ^ 2 * 2 ^ s :=
    calc C = C * 1 * 1 := by ring
      _ ≤ C * C * 2 ^ s := by gcongr
      _ = C ^ 2 * 2 ^ s := by ring
  have hfP : ‖f‖ₑ ≤ P := enorm_le_approxNorm hq0 f
  have hhead : A.approxSeqDyadic s f 0 ≤ P := by
    rw [approxSeqDyadic_zero]; exact (approxError_le_enorm f 1).trans hfP
  have hshift : lqNorm q (fun k => A.approxSeqDyadic s f (k + 1)) ≤ 2 ^ s * (2 * C * P) := by
    have : (fun k => A.approxSeqDyadic s f (k + 1)) =
        fun k => 2 ^ s * (dyadicWeight s k * A.approxError f (2 ^ (k + 1))) := by
      funext k; rw [approxSeqDyadic, ENNReal.dyadicWeight_succ, mul_assoc]
    rw [this, ENNReal.lqNorm_const_mul]
    gcongr
    exact lqNorm_dyadic_succ_le' hq0 hs f
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ P + C * (P + 2 ^ s * (2 * C * P)) := by
        gcongr
        exact (ENNReal.lqNorm_le_head_add_shift' q _).trans (by gcongr)
    _ = (1 + C + 2 * C ^ 2 * 2 ^ s) * P := by ring
    _ ≤ (C ^ 2 * 2 ^ s + C ^ 2 * 2 ^ s + 2 * C ^ 2 * 2 ^ s) * P := by gcongr
    _ = C ^ 2 * 4 * 2 ^ s * P := by ring

/-- **The dyadic quasi-norm is dominated by Pietsch's**: for `s ≥ 0` and `1 ≤ q ≤ ∞`,
`‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_q ≤ 4 · 2^s ‖f‖_{A^s_q}`, the case `LpAddConst q = 1` of
`ApproximationScheme.approxNormDyadic_le_approxNorm'`. -/
theorem approxNormDyadic_le_approxNorm (hq : 1 ≤ q) (hs : 0 ≤ s) (f : X) :
    A.approxNormDyadic s q f ≤ 4 * 2 ^ s * A.approxNorm s q f := by
  simpa [LpAddConst_of_one_le hq] using
    approxNormDyadic_le_approxNorm' (zero_lt_one.trans_le hq).ne' hs f

/-- For `s ≥ 0` and every `q ≠ 0`, `f ∈ A^s_q` iff its dyadic quasi-norm is finite. -/
theorem memApprox_iff_approxNormDyadic_lt_top' (hq0 : q ≠ 0) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ A.approxNormDyadic s q f < ∞ := by
  have hC := ENNReal.LpAddConst_lt_top q
  constructor
  · intro hf
    refine (approxNormDyadic_le_approxNorm' hq0 hs f).trans_lt (ENNReal.mul_lt_top ?_ hf)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_ne_top hC.ne).lt_top (by norm_num))
      (ENNReal.two_rpow_ne_top s).lt_top
  · intro hf
    exact (approxNorm_le_approxNormDyadic' hq0 hs f).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC (ENNReal.two_rpow_ne_top s).lt_top) hf)

/-- For `s ≥ 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff its dyadic quasi-norm is finite. -/
theorem memApprox_iff_approxNormDyadic_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ A.approxNormDyadic s q f < ∞ :=
  memApprox_iff_approxNormDyadic_lt_top' (zero_lt_one.trans_le hq).ne' hs

/-- For `s ≥ 0` and every `q ≠ 0`, `f ∈ A^s_q` iff `(2^(ks) E_{2^k}(f))_k ∈ ℓ_q`. -/
theorem memApprox_iff_lqNorm_dyadic_lt_top' (hq0 : q ≠ 0) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ lqNorm q (A.approxSeqDyadic s f) < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top' hq0 hs, approxNormDyadic, ENNReal.add_lt_top]
  exact and_iff_right eNorm_lt_top

/-- For `s ≥ 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `(2^(ks) E_{2^k}(f))_k ∈ ℓ_q`. -/
theorem memApprox_iff_lqNorm_dyadic_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) {f : X} :
    A.MemApprox s q f ↔ lqNorm q (A.approxSeqDyadic s f) < ∞ :=
  memApprox_iff_lqNorm_dyadic_lt_top' (zero_lt_one.trans_le hq).ne' hs

/-- A bound on the dyadic quasi-norm gives the decay `E_{2^k}(f) ≤ 2^(-ks) ‖f‖^dyadic`, for every
`q ≠ 0`. -/
theorem approxError_pow_le (hq0 : q ≠ 0) (f : X) (k : ℕ) :
    A.approxError f (2 ^ k) ≤ dyadicWeight (-s) k * lqNorm q (A.approxSeqDyadic s f) := by
  calc A.approxError f (2 ^ k) = dyadicWeight (-s) k * A.approxSeqDyadic s f k := by
        rw [approxSeqDyadic, ← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
    _ ≤ _ := by gcongr; exact approxSeqDyadic_le_lqNorm hq0 f k

/-- **The quasi-norm of `A^s_∞` of an approximant**: for `a ∈ A_{2^k}`, `E_{2^j}(a) = 0` for
`j ≥ k`, hence `‖a‖_{A^s_∞} ≤ ‖a‖ + ∑_{j<k} 2^(js) E_{2^j}(a)`. -/
theorem approxNormDyadic_top_le_of_mem {k : ℕ} {a : X} (ha : a ∈ A (2 ^ k)) :
    A.approxNormDyadic s ∞ a ≤ ‖a‖ₑ + ∑ j ∈ Finset.range k, A.approxSeqDyadic s a j := by
  rw [approxNormDyadic, ENNReal.lqNorm_top]
  gcongr
  refine iSup_le fun j => ?_
  rcases lt_or_ge j k with hj | hj
  · exact Finset.single_le_sum (f := A.approxSeqDyadic s a) (fun _ _ => zero_le)
      (Finset.mem_range.2 hj)
  · rw [approxSeqDyadic,
      approxError_eq_zero_of_mem (mem_of_le (Nat.pow_le_pow_right two_pos hj) ha), mul_zero]
    exact zero_le

/-- For `f ∈ A^s_q` with `s > 0`, the dyadic errors `E_{2^k}(f)` tend to zero. -/
theorem tendsto_approxError_pow_zero_of_memApprox (hq : 1 ≤ q) (hs : 0 < s) {f : X}
    (hf : A.MemApprox s q f) : Tendsto (fun k => A.approxError f (2 ^ k)) atTop (𝓝 0) := by
  have hD := (memApprox_iff_lqNorm_dyadic_lt_top hq hs.le).1 hf
  set D := lqNorm q (A.approxSeqDyadic s f)
  have hgeom : Tendsto (fun k => D * ((2 : ℝ≥0∞) ^ (-s)) ^ k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.two_rpow_neg_lt_one hs))
      (Or.inr hD.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom (fun _ => bot_le)
    fun k => by
      rw [mul_comm, ← ENNReal.dyadicWeight_eq_pow]
      exact approxError_pow_le (zero_lt_one.trans_le hq).ne' f k

/-- **`A^s_q` lies in the closure of `⋃ A n`** for `s > 0`. -/
theorem mem_closure_iUnion_of_memApprox (hq : 1 ≤ q) (hs : 0 < s) {f : X}
    (hf : A.MemApprox s q f) : f ∈ closure (⋃ n, A n) :=
  (tendsto_approxError_zero_iff f).1
    (tendsto_approxError_zero_of_pow (tendsto_approxError_pow_zero_of_memApprox hq hs hf))

end ApproximationScheme
