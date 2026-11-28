/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Embedding
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Characterisation by dyadic blocks for projection schemes

Many schemes come with **uniformly bounded projections**: bounded linear maps `P n : X → X`
onto `A n` (fixing `A n`) with `‖P n‖ ≤ M` (`ApproximationScheme.ProjectionScheme`).  Examples:
partial sums of an unconditional or orthonormal basis (Fourier series in `L_2`, wavelets in
`L_p`), conditional expectations onto dyadic σ-algebras (Haar).  Bounded projections onto an
increasing sequence of subspaces `V_k` give a projection scheme for the dyadic scheme of the
`V_k` (`ProjectionScheme.ofMonotone`).  For projection schemes:

* `P n` is a near-best approximation: `E_n(f) ≤ ‖f - P n f‖ ≤ (1 + M) E_n(f)`
  (`enorm_sub_le_approxError`), a **Lebesgue inequality**;
* `A^s_q` is characterised by the **dyadic blocks** `Δ_k f = P (2^(k+1)) f - P (2^k) f`:
  for `s > 0`, and if `P n f → f` for every `f`,

  `‖f‖_{A^s_q} ≍ ‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_{ℓ_q}`

  (`blockNorm_le_approxNormDyadic`, `approxNormDyadic_le_blockNorm`).

For a wavelet basis the block `Δ_k f` is the part of `f` at level `k`, and for an orthonormal
basis `‖Δ_k f‖` is the `ℓ²` norm of the coefficients in the block; this is how coefficient
characterisations of Besov spaces arise.  The direction `≲` uses Hardy's inequality for tails;
the density hypothesis is needed because the blocks see nothing outside the closure of
`⋃ A n`.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A **projection scheme**: bounded linear projections `P n` of `X` onto `A n`, uniformly
bounded by `M`. -/
structure ProjectionScheme (A : ApproximationScheme X) where
  /-- The projection onto the approximants of complexity `n`. -/
  P : ℕ → X →L[ℝ] X
  mem : ∀ n f, P n f ∈ A n
  proj : ∀ n, ∀ a ∈ A n, P n a = a
  /-- The uniform bound on the projections. -/
  bound : ℝ
  norm_le : ∀ n, ‖P n‖ ≤ bound

namespace ProjectionScheme

/-- **The projection scheme of an increasing sequence of subspaces**: bounded linear projections
`Q_k` onto `V_k`, with `Q_k a = a` for `a ∈ V_k` and `‖Q_k‖ ≤ B`, give a projection scheme for the
dyadic scheme `ofMonotoneSubmodules V`, with `P_0 = 0` and `P_n = Q_⌊log₂ n⌋` for `n ≥ 1`. -/
noncomputable def ofMonotone (V : ℕ → Submodule ℝ X) (hV : Monotone V) (Q : ℕ → X →L[ℝ] X)
    (hmem : ∀ k f, Q k f ∈ V k) (hproj : ∀ k, ∀ a ∈ V k, Q k a = a) (B : ℝ)
    (hB : ∀ k, ‖Q k‖ ≤ B) : (ofMonotoneSubmodules V hV).ProjectionScheme where
  P n := if n = 0 then 0 else Q (Nat.log 2 n)
  mem n f := by
    split_ifs with hn
    · rw [hn, zero_apply, mem_ofMonotoneSubmodules_zero]
    · exact (mem_ofMonotoneSubmodules hn).2 (hmem _ f)
  proj n a ha := by
    split_ifs with hn
    · subst hn
      rw [mem_ofMonotoneSubmodules_zero.1 ha, zero_apply]
    · exact hproj _ a ((mem_ofMonotoneSubmodules hn).1 ha)
  bound := B
  norm_le n := by
    split_ifs
    · simpa using (norm_nonneg (Q 0)).trans (hB 0)
    · exact hB _

/-- The projection of complexity `2^k` of `ProjectionScheme.ofMonotone` is `Q_k`. -/
theorem ofMonotone_two_pow {V : ℕ → Submodule ℝ X} {hV : Monotone V} {Q : ℕ → X →L[ℝ] X}
    {hmem : ∀ k f, Q k f ∈ V k} {hproj : ∀ k, ∀ a ∈ V k, Q k a = a} {B : ℝ}
    {hB : ∀ k, ‖Q k‖ ≤ B} (k : ℕ) :
    (ofMonotone V hV Q hmem hproj B hB).P (2 ^ k) = Q k := by
  simp only [ofMonotone, pow_ne_zero k two_ne_zero, ↓reduceIte, Nat.log_pow Nat.one_lt_two]

variable {A : ApproximationScheme X} (PS : ProjectionScheme A)

/-- The bound of a projection scheme is nonnegative. -/
theorem bound_nonneg : 0 ≤ PS.bound := (norm_nonneg _).trans (PS.norm_le 0)

/-- `‖P_n f‖ ≤ M ‖f‖`. -/
theorem enorm_apply_le (n : ℕ) (f : X) : ‖PS.P n f‖ₑ ≤ ENNReal.ofReal PS.bound * ‖f‖ₑ := by
  refine ((PS.P n).le_opENorm f).trans ?_
  gcongr
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (PS.norm_le n)

/-- `P n f` is an approximant, so `E_n(f) ≤ ‖f - P n f‖`. -/
theorem approxError_le_enorm_sub (n : ℕ) (f : X) : A.approxError f n ≤ ‖f - PS.P n f‖ₑ :=
  approxError_le_of_mem (PS.mem n f) f

/-- **The Lebesgue inequality**: `‖f - P n f‖ ≤ (1 + M) E_n(f)`. -/
theorem enorm_sub_le_approxError (n : ℕ) (f : X) :
    ‖f - PS.P n f‖ₑ ≤ (1 + ENNReal.ofReal PS.bound) * A.approxError f n :=
  le_mul_approxError_of_forall_mem
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)
    fun a ha => enorm_sub_apply_le_of_apply_eq (PS.enorm_apply_le n) (PS.proj n a ha) f

/-- The **dyadic block** `Δ_k f = P (2^(k+1)) f - P (2^k) f`. -/
noncomputable def block (k : ℕ) (f : X) : X := PS.P (2 ^ (k + 1)) f - PS.P (2 ^ k) f

/-- A block is controlled by the error: `‖Δ_k f‖ ≤ 2 (1 + M) E_{2^k}(f)`. -/
theorem enorm_block_le (k : ℕ) (f : X) :
    ‖PS.block k f‖ₑ ≤ 2 * (1 + ENNReal.ofReal PS.bound) * A.approxError f (2 ^ k) := by
  calc ‖PS.block k f‖ₑ = ‖(f - PS.P (2 ^ k) f) - (f - PS.P (2 ^ (k + 1)) f)‖ₑ := by
        rw [block]; congr 1; abel
    _ ≤ ‖f - PS.P (2 ^ k) f‖ₑ + ‖f - PS.P (2 ^ (k + 1)) f‖ₑ := eNorm_sub_le
    _ ≤ (1 + ENNReal.ofReal PS.bound) * A.approxError f (2 ^ k) +
          (1 + ENNReal.ofReal PS.bound) * A.approxError f (2 ^ k) := by
        gcongr
        · exact PS.enorm_sub_le_approxError _ f
        · exact (PS.enorm_sub_le_approxError _ f).trans (by
            gcongr; exact approxError_anti f (Nat.pow_le_pow_right two_pos (Nat.le_succ k)))
    _ = _ := by ring

/-- The **block quasi-norm** `‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_{ℓ_q}`. -/
noncomputable def blockNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖PS.P 1 f‖ₑ + lqNorm q (fun k => dyadicWeight s k * ‖PS.block k f‖ₑ)

variable {s : ℝ} {q : ℝ≥0∞}

/-- **The blocks are controlled by the approximation norm**:
`‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_q ≤ (M + 2 (1 + M)) ‖f‖^dyadic`. -/
theorem blockNorm_le_approxNormDyadic (f : X) :
    PS.blockNorm s q f ≤
      (ENNReal.ofReal PS.bound + 2 * (1 + ENNReal.ofReal PS.bound)) * A.approxNormDyadic s q f := by
  set c := 2 * (1 + ENNReal.ofReal PS.bound)
  have hlq : lqNorm q (fun k => dyadicWeight s k * ‖PS.block k f‖ₑ) ≤
      c * lqNorm q (A.approxSeqDyadic s f) := by
    rw [← ENNReal.lqNorm_const_mul]
    refine ENNReal.lqNorm_mono fun k => ?_
    rw [approxSeqDyadic, mul_left_comm]
    gcongr
    exact PS.enorm_block_le k f
  calc PS.blockNorm s q f ≤ ENNReal.ofReal PS.bound * ‖f‖ₑ + c * lqNorm q (A.approxSeqDyadic s f) :=
        add_le_add (PS.enorm_apply_le 1 f) hlq
    _ ≤ (ENNReal.ofReal PS.bound + c) * ‖f‖ₑ + (ENNReal.ofReal PS.bound + c) *
          lqNorm q (A.approxSeqDyadic s f) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = _ := by rw [approxNormDyadic, mul_add]

/-- The blocks telescope: `∑_{i < N} Δ_{k+i} f = P (2^(k+N)) f - P (2^k) f`. -/
theorem sum_block (k N : ℕ) (f : X) :
    ∑ i ∈ range N, PS.block (k + i) f = PS.P (2 ^ (k + N)) f - PS.P (2 ^ k) f := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, block, show k + N + 1 = k + (N + 1) by ring]
    abel

/-- If `P n f → f`, the error of `P (2^k)` is the norm of the tail of the blocks:
`‖f - P (2^k) f‖ ≤ ∑_{i ≥ 0} ‖Δ_{k+i} f‖`. -/
theorem enorm_sub_le_tsum_block {f : X} (hf : Tendsto (fun n => PS.P n f) atTop (𝓝 f)) (k : ℕ) :
    ‖f - PS.P (2 ^ k) f‖ₑ ≤ ∑' i, ‖PS.block (k + i) f‖ₑ := by
  have hlim : Tendsto (fun N => PS.P (2 ^ (k + N)) f - PS.P (2 ^ k) f) atTop
      (𝓝 (f - PS.P (2 ^ k) f)) := by
    refine (hf.comp ?_).sub_const _
    exact (tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) fun b => ⟨b, by omega⟩)
  refine le_of_tendsto' ((continuous_eNorm.tendsto _).comp hlim) fun N => ?_
  rw [Function.comp_apply, ← PS.sum_block k N f]
  exact (eNorm_sum_le _ _).trans (sum_le_tsum _)

/-- **The approximation norm is controlled by the blocks**: for `s > 0`, `1 ≤ q ≤ ∞` and
`P n f → f`, `‖f‖^dyadic ≤ (1 + 2 C_s) (‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_q)` with
`C_s = (1 - 2^(-s))⁻¹`. -/
theorem approxNormDyadic_le_blockNorm (hq : 1 ≤ q) {f : X}
    (hf : Tendsto (fun n => PS.P n f) atTop (𝓝 f)) :
    A.approxNormDyadic s q f ≤ (1 + 2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹) * PS.blockNorm s q f := by
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹
  set L := lqNorm q (fun k => dyadicWeight s k * ‖PS.block k f‖ₑ)
  have hD : lqNorm q (A.approxSeqDyadic s f) ≤ Cs * L := by
    calc lqNorm q (A.approxSeqDyadic s f)
        ≤ lqNorm q (fun k => dyadicWeight s k * ∑' i, ‖PS.block (k + i) f‖ₑ) :=
          ENNReal.lqNorm_mono fun k => by
            rw [approxSeqDyadic]; gcongr
            exact (PS.approxError_le_enorm_sub _ f).trans (PS.enorm_sub_le_tsum_block hf k)
      _ ≤ Cs * L := ENNReal.hardy_tail_le hq s (fun m => ‖PS.block m f‖ₑ)
  have hsum : ∑' i, ‖PS.block i f‖ₑ ≤ Cs * L :=
    ENNReal.tsum_le_lqNorm_dyadicWeight hq s (‖PS.block · f‖ₑ)
  have h0 := PS.enorm_sub_le_tsum_block hf 0
  simp only [pow_zero, zero_add] at h0
  have hf' : ‖f‖ₑ ≤ ‖PS.P 1 f‖ₑ + Cs * L := by
    calc ‖f‖ₑ = ‖PS.P 1 f + (f - PS.P 1 f)‖ₑ := by congr 1; abel
      _ ≤ ‖PS.P 1 f‖ₑ + ‖f - PS.P 1 f‖ₑ := eNorm_add_le _ _
      _ ≤ ‖PS.P 1 f‖ₑ + Cs * L := by gcongr; exact h0.trans hsum
  have hC1 : 1 ≤ Cs := ENNReal.one_le_one_sub_two_rpow_neg_inv s
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ (‖PS.P 1 f‖ₑ + Cs * L) + Cs * L := add_le_add hf' hD
    _ ≤ (1 + 2 * Cs) * ‖PS.P 1 f‖ₑ + (1 + 2 * Cs) * L := by
        have : ‖PS.P 1 f‖ₑ ≤ (1 + 2 * Cs) * ‖PS.P 1 f‖ₑ := le_mul_of_one_le_left' le_self_add
        calc (‖PS.P 1 f‖ₑ + Cs * L) + Cs * L = ‖PS.P 1 f‖ₑ + 2 * Cs * L := by ring
          _ ≤ (1 + 2 * Cs) * ‖PS.P 1 f‖ₑ + (1 + 2 * Cs) * L := by
              gcongr; exact le_add_self
    _ = _ := by rw [blockNorm, mul_add]

/-- If `⋃ A n` is dense, the projections converge: `P n f → f` for every `f`. -/
theorem tendsto_of_dense (hd : closure (⋃ n, A n) = Set.univ) (f : X) :
    Tendsto (fun n => PS.P n f) atTop (𝓝 f) := by
  have hE' := (tendsto_approxError_zero_iff (A := A) f).2 (by rw [hd]; trivial)
  have hbound :
      Tendsto (fun n => (1 + ENNReal.ofReal PS.bound) * A.approxError f n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hE' (Or.inr (ENNReal.add_ne_top.2
      ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩))
  have h0 : Tendsto (fun n => ‖f - PS.P n f‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => bot_le)
      (PS.enorm_sub_le_approxError · f)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simpa [Function.comp_def, norm_sub_rev] using this

/-- **Characterisation of `A^s_q` by dyadic blocks**: for a projection scheme with dense
`⋃ A n`, `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff
`‖P 1 f‖ + ‖(2^(ks) ‖Δ_k f‖)_k‖_q < ∞`. -/
theorem memApprox_iff_blockNorm_lt_top (hd : closure (⋃ n, A n) = Set.univ) (hs : 0 < s)
    (hq : 1 ≤ q) {f : X} : A.MemApprox s q f ↔ PS.blockNorm s q f < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs.le]
  constructor
  · intro h
    exact (PS.blockNorm_le_approxNormDyadic f).trans_lt (ENNReal.mul_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩)⟩) h)
  · intro h
    exact (PS.approxNormDyadic_le_blockNorm hq (PS.tendsto_of_dense hd f)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top
        (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs).lt_top⟩) h)

end ProjectionScheme

end ApproximationScheme
