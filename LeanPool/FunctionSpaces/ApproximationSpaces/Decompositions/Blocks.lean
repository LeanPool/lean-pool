/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Lift
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Block decompositions

For `s > 0`, `1 ≤ q ≤ ∞` and a Banach space `X`, an element `f` lies in `A^s_q` if and only if
it has a **block decomposition**

`f = ∑_{k ≥ 0} g_k`,   `g_k ∈ A (2^k)`,   `(2^(ks) ‖g_k‖)_k ∈ ℓ_q`

(`memApprox_iff_blockDecompNorm_lt_top`), and the infimum of `‖(2^(ks) ‖g_k‖)_k‖_q` over all
block decompositions (`blockDecompNorm`) is an equivalent quasi-norm
(`approxNormDyadic_le_blockDecompNorm`, `blockDecompNorm_le_approxNormDyadic`).  Each block
`g_k` is a whole level, an approximant of complexity `2^k`.  Atomic decompositions refine every
block into localised atoms with coefficients; wavelet decompositions expand it in a basis.

* Given a decomposition, `∑_{j < k} g_j ∈ A (2^k)`, so `E_{2^k}(f) ≤ ∑_{i ≥ 0} ‖g_{k+i}‖`, and
  Hardy's inequality for tails gives the bound on `‖f‖_{A^s_q}`.
* Conversely, the differences of near-best approximants form a decomposition
  (`g_{k+2} = a_{k+1} - a_k ∈ A (2^(k+2))`), whose norms are controlled by the errors.
* For concrete blocks such as Littlewood–Paley blocks, a finite weighted `ℓ_q` norm makes the
  series converge absolutely (`HasSum.of_tendsto_of_lqNorm_dyadicWeight_lt_top`), and blocks
  bounded by the errors have weighted `ℓ_q` norm at most a multiple of `‖f‖_{A^s_q}`
  (`lqNorm_dyadicWeight_mul_enorm_le_approxNormDyadic`).
* A series moved up by `γ` levels (`shiftSeq`) keeps its sum, and blocks `a_j ∈ A (2^(j+γ))`
  become blocks `g_i ∈ A (2^i)` with the same weighted `ℓ_q` norm (`shiftSeq_mem`,
  `lqNorm_shiftSeq_le`).
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

/-- **A weighted `ℓ_q` bound gives the sum**: for `s > 0` and `1 ≤ q ≤ ∞`, a sequence `b_j` in a
complete normed group with `‖(2^(js) ‖b_j‖)_j‖_{ℓ_q} < ∞` is absolutely summable
(`ENNReal.tsum_le_lqNorm_dyadicWeight`), so its sum is the limit `f` of its partial sums. -/
theorem HasSum.of_tendsto_of_lqNorm_dyadicWeight_lt_top {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {s : ℝ} {q : ℝ≥0∞} (hs : 0 < s) (hq : 1 ≤ q) {b : ℕ → E} {f : E}
    (hb : Tendsto (fun n => ∑ j ∈ range n, b j) atTop (𝓝 f))
    (hL : ENNReal.lqNorm q (fun j => ENNReal.dyadicWeight s j * ‖b j‖ₑ) < ∞) : HasSum b f :=
  (Summable.of_eNorm (ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs) hL.ne)
    (ENNReal.tsum_le_lqNorm_dyadicWeight hq s _))).hasSum_iff_tendsto_nat.2 hb

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

variable (A) in
/-- The **block decomposition quasi-norm**: the infimum of `‖(2^(ks) ‖g_k‖)_k‖_q` over all
block decompositions `f = ∑ g_k` with `g_k ∈ A (2^k)`. -/
noncomputable def blockDecompNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ⨅ (g : ℕ → X) (_ : ∀ k, g k ∈ A (2 ^ k)) (_ : HasSum g f),
    lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ)

/-- Every block decomposition `f = ∑ g_k` with `g_k ∈ A_{2^k}` bounds the block decomposition
quasi-norm. -/
theorem blockDecompNorm_le {f : X} {g : ℕ → X} (hg : ∀ k, g k ∈ A (2 ^ k)) (hf : HasSum g f) :
    A.blockDecompNorm s q f ≤ lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) :=
  iInf₂_le_of_le g hg (iInf_le_of_le hf le_rfl)

/-- The partial sums of a block decomposition are approximants: `∑_{j<k} g_j ∈ A (2^k)`, since
`∑_{j<k} 2^j < 2^k` (Mathlib's `Nat.geomSum_lt`). -/
theorem sum_range_mem {g : ℕ → X} (hg : ∀ k, g k ∈ A (2 ^ k)) (k : ℕ) :
    ∑ j ∈ range k, g j ∈ A (2 ^ k) :=
  A.mem_of_le (Nat.geomSum_lt le_rfl fun _ hj => mem_range.1 hj).le
    (sum_mem (range k) fun j _ => hg j)

/-- **A block decomposition controls the approximation norm**: for `s > 0`,
`‖f‖^dyadic ≤ 2 (1 - 2^(-s))⁻¹ ‖(2^(ks) ‖g_k‖)_k‖_q`. -/
theorem approxNormDyadic_le_of_hasSum (hq : 1 ≤ q) {f : X} {g : ℕ → X}
    (hg : ∀ k, g k ∈ A (2 ^ k)) (hf : HasSum g f) :
    A.approxNormDyadic s q f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) := by
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹
  set L := lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ)
  have htail : ∀ k, ‖f - ∑ j ∈ range k, g j‖ₑ ≤ ∑' i, ‖g (k + i)‖ₑ := fun k =>
    (hf.enorm_sub_sum_range_le k).trans_eq (by simp_rw [add_comm])
  have hD : lqNorm q (A.approxSeqDyadic s f) ≤ Cs * L := by
    calc lqNorm q (A.approxSeqDyadic s f)
        ≤ lqNorm q (fun k => dyadicWeight s k * ∑' i, ‖g (k + i)‖ₑ) :=
          ENNReal.lqNorm_mono fun k => by
            rw [approxSeqDyadic]; gcongr
            exact (approxError_le_of_mem (sum_range_mem hg k) f).trans (htail k)
      _ ≤ Cs * L := ENNReal.hardy_tail_le hq s (fun m => ‖g m‖ₑ)
  have hf' : ‖f‖ₑ ≤ Cs * L :=
    calc ‖f‖ₑ = ‖f - ∑ j ∈ range 0, g j‖ₑ := by simp
      _ ≤ ∑' i, ‖g (0 + i)‖ₑ := htail 0
      _ ≤ Cs * L := by
          simpa only [zero_add] using ENNReal.tsum_le_lqNorm_dyadicWeight hq s (‖g ·‖ₑ)
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ Cs * L + Cs * L := add_le_add hf' hD
    _ = 2 * Cs * L := by ring

/-- **The block decomposition quasi-norm controls the approximation norm**, `s > 0`. -/
theorem approxNormDyadic_le_blockDecompNorm (hs : 0 < s) (hq : 1 ≤ q) (f : X) :
    A.approxNormDyadic s q f ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * A.blockDecompNorm s q f := by
  have h : 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)
  have h0 : 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ ≠ 0 :=
    mul_ne_zero two_ne_zero (zero_lt_one.trans_le (ENNReal.one_le_one_sub_two_rpow_neg_inv s)).ne'
  rw [blockDecompNorm, ENNReal.mul_iInf_of_ne h0 h]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 h]
  refine le_iInf fun hg => ?_
  rw [ENNReal.mul_iInf_of_ne h0 h]
  exact le_iInf fun hf => approxNormDyadic_le_of_hasSum hq hg hf

/-- The block decomposition built from near-best approximants: `g 0 = 0`, `g 1 = a 0` and
`g (k + 2) = a (k + 1) - a k`. -/
noncomputable def DyadicApprox.blocks {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) : ℕ → X
  | 0 => 0
  | 1 => D.a 0
  | k + 2 => D.a (k + 1) - D.a k

/-- The blocks of a dyadic approximation lie in the right sets: `g_k ∈ A_{2^k}`. -/
theorem DyadicApprox.blocks_mem {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (k : ℕ) :
    D.blocks k ∈ A (2 ^ k) := by
  match k with
  | 0 => exact A.zero_mem _
  | 1 => exact A.mem_of_le (by norm_num) (D.mem 0)
  | k + 2 => exact D.sub_mem k

/-- The partial sums of the blocks are the approximants: `∑_{j < K+2} g_j = a_K`. -/
theorem DyadicApprox.sum_range_blocks {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (K : ℕ) :
    ∑ j ∈ range (K + 2), D.blocks j = D.a K := by
  induction K with
  | zero => simp [Finset.sum_range_succ, DyadicApprox.blocks]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [DyadicApprox.blocks]
    abel

/-- The blocks of near-best approximants are summable in norm: for `f ∈ A^s_q` with `s > 0`
and tolerances with `∑ t_k ≤ 2 ‖f‖`, `∑_k ‖g_k‖ < ∞`. -/
theorem DyadicApprox.tsum_enorm_blocks_ne_top (hs : 0 < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (htsum : ∑' k, t k ≤ 2 * ‖f‖ₑ) : ∑' k, ‖D.blocks k‖ₑ ≠ ∞ := by
  have hg : ∀ k, ‖D.blocks (k + 2)‖ₑ ≤ 2 * (A.approxError f (2 ^ k) + t k) := fun k =>
    D.enorm_sub_succ_le ht k
  have hE1 : lqNorm 1 (A.approxSeqDyadic 0 f) < ∞ := hf.lqNorm_one_lt_top hq le_rfl hs
  have htail : ∑' k, ‖D.blocks (k + 2)‖ₑ ≠ ∞ := by
    have hfin : 2 * (lqNorm 1 (A.approxSeqDyadic 0 f) + 2 * ‖f‖ₑ) ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2
        ⟨hE1.ne, ENNReal.mul_ne_top (by norm_num) eNorm_ne_top⟩)
    refine ne_top_of_le_ne_top hfin ?_
    calc ∑' k, ‖D.blocks (k + 2)‖ₑ ≤ ∑' k, 2 * (A.approxError f (2 ^ k) + t k) :=
          tsum_le_tsum hg
      _ = 2 * (∑' k, A.approxSeqDyadic 0 f k + ∑' k, t k) := by
          rw [ENNReal.tsum_mul_left, tsum_add]; simp [approxSeqDyadic]
      _ ≤ 2 * (lqNorm 1 (A.approxSeqDyadic 0 f) + 2 * ‖f‖ₑ) := by
          rw [ENNReal.lqNorm_one]; gcongr
  rw [← Summable.sum_add_tsum_nat_add' (f := fun k => ‖D.blocks k‖ₑ) (k := 2)
    CompleteLattice.summable]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun j _ => eNorm_ne_top, htail⟩

/-- **The blocks of near-best approximants add up to `f`**: in a Banach space, for
`f ∈ A^s_q` with `s > 0` and tolerances that decrease, tend to `0` and satisfy
`∑ t_k ≤ 2 ‖f‖`. -/
theorem DyadicApprox.hasSum_blocks [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (htend : Tendsto t atTop (𝓝 0)) (htsum : ∑' k, t k ≤ 2 * ‖f‖ₑ) :
    HasSum D.blocks f := by
  have hsum : Summable D.blocks := Summable.of_eNorm (D.tsum_enorm_blocks_ne_top hs hq hf ht htsum)
  have he := tendsto_approxError_pow_zero_of_memApprox hq hs hf
  have h2 : Tendsto (fun K => ∑ j ∈ range (K + 2), D.blocks j) atTop (𝓝 (∑' k, D.blocks k)) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  simp_rw [D.sum_range_blocks] at h2
  have hfeq : f = ∑' k, D.blocks k := tendsto_nhds_unique (D.tendsto he htend) h2
  exact (congrArg (HasSum D.blocks) hfeq).mpr hsum.hasSum

/-- **The weighted blocks of near-best approximants**: for decreasing tolerances with
`t_0 ≤ ‖f‖` and `‖(2^(ks) t_k)_k‖_q ≤ 2 ‖f‖`,
`‖(2^(ks) ‖g_k‖)_k‖_q ≤ 3·2^s ‖f‖ + 2·4^s (‖(2^(ks) E_{2^k}(f))_k‖_q + 2 ‖f‖)`. -/
theorem DyadicApprox.lqNorm_blocks_le (hq : 1 ≤ q) {f : X} {t : ℕ → ℝ≥0∞}
    (D : A.DyadicApprox f t) (ht : Antitone t) (ht0 : t 0 ≤ ‖f‖ₑ)
    (htq : lqNorm q (fun k => dyadicWeight s k * t k) ≤ 2 * ‖f‖ₑ) :
    lqNorm q (fun k => dyadicWeight s k * ‖D.blocks k‖ₑ) ≤ 2 ^ s * (3 * ‖f‖ₑ) +
      2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) := by
  have hg : ∀ k, ‖D.blocks (k + 2)‖ₑ ≤ 2 * (A.approxError f (2 ^ k) + t k) := fun k =>
    D.enorm_sub_succ_le ht k
  have hg1 : ‖D.blocks 1‖ₑ ≤ 3 * ‖f‖ₑ :=
    calc ‖D.blocks 1‖ₑ = ‖D.a 0‖ₑ := rfl
      _ ≤ 2 * ‖f‖ₑ + t 0 := D.enorm_zero_le
      _ ≤ 2 * ‖f‖ₑ + ‖f‖ₑ := by gcongr
      _ = 3 * ‖f‖ₑ := by ring
  refine ((ENNReal.lqNorm_le_head_add_shift hq _).trans (add_le_add le_rfl
    (ENNReal.lqNorm_le_head_add_shift hq _))).trans ?_
  have h0 : dyadicWeight s 0 * ‖D.blocks 0‖ₑ = 0 := by simp [DyadicApprox.blocks]
  have h1 : dyadicWeight s (0 + 1) * ‖D.blocks (0 + 1)‖ₑ ≤ 2 ^ s * (3 * ‖f‖ₑ) := by
    rw [zero_add, ENNReal.dyadicWeight_succ, ENNReal.dyadicWeight_zero_right, mul_one]
    gcongr
  have h2 : lqNorm q (fun k => dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 1 + 1)‖ₑ) ≤
      2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) := by
    calc lqNorm q (fun k => dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 1 + 1)‖ₑ)
        ≤ lqNorm q (fun k => 2 * dyadicWeight s 2 *
            (A.approxSeqDyadic s f k + dyadicWeight s k * t k)) :=
          ENNReal.lqNorm_mono fun k => by
            calc dyadicWeight s (k + 1 + 1) * ‖D.blocks (k + 2)‖ₑ
                ≤ dyadicWeight s (k + 2) * (2 * (A.approxError f (2 ^ k) + t k)) := by
                  gcongr; exact hg k
              _ = _ := by rw [ENNReal.dyadicWeight_add_nat, approxSeqDyadic]; ring
      _ = 2 * dyadicWeight s 2 *
            lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ _ := by
          gcongr
          exact (ENNReal.lqNorm_add_le hq _ _).trans (add_le_add le_rfl htq)
  rw [h0, zero_add]
  exact add_le_add h1 h2

/-- **The block decomposition of near-best approximants**: for tolerances `t` that decrease, tend to
`0`, start at most at `‖f‖` and satisfy `∑ t_k ≤ 2 ‖f‖` and `‖(2^(ks) t_k)_k‖_q ≤ 2 ‖f‖`, the
blocks of a dyadic approximation of `f ∈ A^s_q` form a block decomposition of `f` with
`‖(2^(ks) ‖g_k‖)_k‖_q ≤ 3·2^s ‖f‖ + 2·4^s (‖(2^(ks) E_{2^k}(f))_k‖_q + 2 ‖f‖)`. -/
theorem DyadicApprox.blockDecompNorm_le [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (ht0 : t 0 ≤ ‖f‖ₑ) (htend : Tendsto t atTop (𝓝 0)) (htsum : ∑' k, t k ≤ 2 * ‖f‖ₑ)
    (htq : lqNorm q (fun k => dyadicWeight s k * t k) ≤ 2 * ‖f‖ₑ) :
    A.blockDecompNorm s q f ≤ 2 ^ s * (3 * ‖f‖ₑ) +
      2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ) :=
  (ApproximationScheme.blockDecompNorm_le D.blocks_mem
    (D.hasSum_blocks hs hq hf ht htend htsum)).trans (D.lqNorm_blocks_le hq ht ht0 htq)

/-- **Existence of a block decomposition with bounds**: in a Banach space, for `s > 0` and
`f ∈ A^s_q`, there are blocks `g_k ∈ A (2^k)` with `f = ∑ g_k`, `∑_k ‖g_k‖ < ∞` and
`‖(2^(ks) ‖g_k‖)_k‖_q ≤ (3·2^s + 4·4^s) ‖f‖^dyadic`. -/
theorem exists_blocks [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) :
    ∃ g : ℕ → X, (∀ k, g k ∈ A (2 ^ k)) ∧ HasSum g f ∧ ∑' k, ‖g k‖ₑ ≠ ∞ ∧
      lqNorm q (fun k => dyadicWeight s k * ‖g k‖ₑ) ≤
        (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨fun _ => 0, fun k => A.zero_mem _, hasSum_zero, by simp, by simp⟩
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s)
  have ht := tolerance_anti f hs.le
  have htsum := tsum_tolerance_le f hs.le
  refine ⟨D.blocks, D.blocks_mem, D.hasSum_blocks hs hq hf ht (tendsto_tolerance f (by linarith))
    htsum, D.tsum_enorm_blocks_ne_top hs hq hf ht htsum, ?_⟩
  refine (D.lqNorm_blocks_le hq ht (tolerance_zero f s).le
    (lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl)).trans ?_
  have hfN : ‖f‖ₑ ≤ A.approxNormDyadic s q f := enorm_le_approxNormDyadic f
  have hDN : lqNorm q (A.approxSeqDyadic s f) + ‖f‖ₑ = A.approxNormDyadic s q f := by
    rw [approxNormDyadic, add_comm]
  calc 2 ^ s * (3 * ‖f‖ₑ) + 2 * dyadicWeight s 2 * (lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ)
      = 2 ^ s * (3 * ‖f‖ₑ) + 2 * dyadicWeight s 2 *
          ((lqNorm q (A.approxSeqDyadic s f) + ‖f‖ₑ) + ‖f‖ₑ) := by ring
    _ ≤ 2 ^ s * (3 * A.approxNormDyadic s q f) + 2 * dyadicWeight s 2 *
          (A.approxNormDyadic s q f + A.approxNormDyadic s q f) := by
        rw [hDN]; gcongr
    _ = (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by ring

/-- **The approximation norm controls the block decomposition quasi-norm**: in a Banach space
and for `s > 0`, `inf ‖(2^(ks) ‖g_k‖)_k‖_q ≤ (3·2^s + 4·4^s) ‖f‖^dyadic`. -/
theorem blockDecompNorm_le_approxNormDyadic [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) (f : X) :
    A.blockDecompNorm s q f ≤ (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by
  by_cases hf : A.MemApprox s q f
  · obtain ⟨g, hg, hgf, -, hle⟩ := exists_blocks hs hq hf
    exact (blockDecompNorm_le hg hgf).trans hle
  · rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le, not_lt, top_le_iff] at hf
    rw [hf, ENNReal.mul_top (by positivity)]; exact le_top

/-! ### Weighted sequences of blocks -/

/-- **Blocks controlled by the errors**: for `s ≥ 0`, `1 ≤ q ≤ ∞`, `M ≥ 1` and a sequence `b_j`
in a normed group with `‖b_j‖ ≤ C ‖f‖` for `j < M` and `‖b_{n+M}‖ ≤ C E_{2^n}(f)` for every `n`,
`‖(2^(js) ‖b_j‖)_j‖_{ℓ_q} ≤ M 2^(Ms) C ‖f‖^dyadic`.  For Littlewood–Paley blocks `b_j = Δ_j f`
this is the bound of the Littlewood–Paley quasi-norm by the approximation norm. -/
theorem lqNorm_dyadicWeight_mul_enorm_le_approxNormDyadic {E : Type*} [NormedAddCommGroup E]
    (hs : 0 ≤ s) (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M) {C : ℝ≥0∞} {f : X} {b : ℕ → E}
    (hhead : ∀ j < M, ‖b j‖ₑ ≤ C * ‖f‖ₑ)
    (htail : ∀ n, ‖b (n + M)‖ₑ ≤ C * A.approxError f (2 ^ n)) :
    lqNorm q (fun j => dyadicWeight s j * ‖b j‖ₑ) ≤
      M * dyadicWeight s M * C * A.approxNormDyadic s q f := by
  set w := dyadicWeight s M
  set a : ℕ → ℝ≥0∞ := fun j => dyadicWeight s j * ‖b j‖ₑ
  have hhead' : ∀ j < M, a j ≤ w * C * ‖f‖ₑ := fun j hj => by
    rw [mul_assoc]
    exact mul_le_mul' (ENNReal.dyadicWeight_mono hs hj.le) (hhead j hj)
  have htail' : ∀ n, a (n + M) ≤ w * C * A.approxSeqDyadic s f n := fun n => by
    calc a (n + M) = w * dyadicWeight s n * ‖b (n + M)‖ₑ := by
          simp only [a]; rw [add_comm n M, ENNReal.dyadicWeight_add_nat, add_comm M n]
      _ ≤ w * dyadicWeight s n * (C * A.approxError f (2 ^ n)) := by gcongr; exact htail n
      _ = w * C * A.approxSeqDyadic s f n := by rw [approxSeqDyadic]; ring
  calc lqNorm q a ≤ ∑ j ∈ range M, a j + lqNorm q (fun n => a (n + M)) :=
        ENNReal.lqNorm_le_sum_range_add_shift hq a M
    _ ≤ ∑ _j ∈ range M, w * C * ‖f‖ₑ + lqNorm q (fun n => w * C * A.approxSeqDyadic s f n) := by
        gcongr with j hj
        · exact hhead' j (mem_range.1 hj)
        · exact ENNReal.lqNorm_mono htail'
    _ = (M : ℝ≥0∞) * (w * C * ‖f‖ₑ) + w * C * lqNorm q (A.approxSeqDyadic s f) := by
        rw [sum_const, card_range, nsmul_eq_mul, ENNReal.lqNorm_const_mul]
    _ ≤ (M : ℝ≥0∞) * (w * C * ‖f‖ₑ) + (M : ℝ≥0∞) * (w * C * lqNorm q (A.approxSeqDyadic s f)) :=
        add_le_add le_rfl (le_mul_of_one_le_left zero_le (by exact_mod_cast hM))
    _ = M * w * C * A.approxNormDyadic s q f := by rw [approxNormDyadic]; ring

/-- **The characterisation of `A^s_q` by block decompositions**: in a Banach space, for
`s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `f = ∑ g_k` with `g_k ∈ A (2^k)` and
`(2^(ks) ‖g_k‖)_k ∈ ℓ_q`. -/
theorem memApprox_iff_blockDecompNorm_lt_top [CompleteSpace X] (hs : 0 < s) (hq : 1 ≤ q) {f : X} :
    A.MemApprox s q f ↔ A.blockDecompNorm s q f < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    exact (blockDecompNorm_le_approxNormDyadic hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
        (ENNReal.two_rpow_ne_top _).lt_top,
        ENNReal.mul_lt_top (by norm_num) (ENNReal.dyadicWeight_lt_top s 2)⟩) h)
  · intro h
    exact (approxNormDyadic_le_blockDecompNorm hs hq f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs).lt_top) h)

/-! ### Series moved up by a number of levels -/

/-- The sequence `a` moved up by `γ` levels: `a_{i-γ}` at the levels `i ≥ γ`, and `0` below. -/
def shiftSeq (γ : ℕ) (a : ℕ → X) (i : ℕ) : X := if γ ≤ i then a (i - γ) else 0

omit [NormedSpace ℝ X] in
/-- `(shiftSeq γ a)_{n+γ} = a_n`. -/
theorem shiftSeq_add (γ : ℕ) (a : ℕ → X) (n : ℕ) : shiftSeq γ a (n + γ) = a n := by
  simp [shiftSeq]

omit [NormedSpace ℝ X] in
/-- The levels below `γ` of the moved sequence are `0`. -/
theorem shiftSeq_of_lt {γ i : ℕ} (a : ℕ → X) (h : i < γ) : shiftSeq γ a i = 0 := by
  simp [shiftSeq, not_le.2 h]

omit [NormedSpace ℝ X] in
/-- **Moving a series up keeps its sum.** -/
theorem hasSum_shiftSeq {γ : ℕ} {a : ℕ → X} {f : X} (hfa : HasSum a f) :
    HasSum (shiftSeq γ a) f := by
  refine (hasSum_nat_add_iff' γ).1 ?_
  have h1 : (fun n => shiftSeq γ a (n + γ)) = a := funext (shiftSeq_add γ a)
  have h2 : ∑ i ∈ range γ, shiftSeq γ a i = 0 :=
    Finset.sum_eq_zero fun i hi => shiftSeq_of_lt a (Finset.mem_range.1 hi)
  rw [h1, h2, sub_zero]
  exact hfa

/-- **Moving approximants up**: if `a_j ∈ A_{2^(j+γ)}`, then `(shiftSeq γ a)_i ∈ A_{2^i}`. -/
theorem shiftSeq_mem {A : ApproximationScheme X} {γ : ℕ} {a : ℕ → X}
    (ha : ∀ j, a j ∈ A (2 ^ (j + γ))) (i : ℕ) : shiftSeq γ a i ∈ A (2 ^ i) := by
  by_cases h : γ ≤ i
  · simp only [shiftSeq, h, ↓reduceIte]
    have := ha (i - γ)
    rwa [Nat.sub_add_cancel h] at this
  · simp only [shiftSeq, h, ↓reduceIte]
    exact A.zero_mem _

omit [NormedSpace ℝ X] in
/-- **The weighted norm of a moved sequence**:
`‖(2^(iσ) ‖(shiftSeq γ a)_i‖)_i‖_{ℓ_q} ≤ ‖(2^((j+γ)σ) ‖a_j‖)_j‖_{ℓ_q}`. -/
theorem lqNorm_shiftSeq_le (γ : ℕ) (a : ℕ → X) (σ : ℝ) (q : ℝ≥0∞) :
    lqNorm q (fun i => dyadicWeight σ i * ‖shiftSeq γ a i‖ₑ) ≤
      lqNorm q (fun j => dyadicWeight σ (j + γ) * ‖a j‖ₑ) := by
  have : (fun i => dyadicWeight σ i * ‖shiftSeq γ a i‖ₑ) = fun i =>
      if γ ≤ i then (fun j => dyadicWeight σ (j + γ) * ‖a j‖ₑ) (i - γ) else 0 := by
    funext i
    by_cases h : γ ≤ i
    · simp only [shiftSeq, h, ↓reduceIte, Nat.sub_add_cancel h]
    · simp [shiftSeq, h]
  rw [this]
  exact ENNReal.lqNorm_shiftRight_le γ (fun j => dyadicWeight σ (j + γ) * ‖a j‖ₑ)

end ApproximationScheme
