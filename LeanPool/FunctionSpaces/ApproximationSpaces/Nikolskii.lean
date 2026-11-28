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
# The Nikolskii transfer theorem

Let `ι : Y → X` be an injective bounded linear map between Banach spaces, `A` a scheme in
`X` whose approximants lie in `ι(Y)`, and suppose the **Nikolskii inequality**

`a ∈ A n, n ≥ 1  ⟹  a = ι y  with  ‖y‖_Y ≤ C n^α ‖a‖_X`

(`LiftBound ι A α C`).  Pull the scheme back to `Y`, `B n = ι⁻¹(A n)`.  Then for `0 ≤ α < s`
and `1 ≤ q ≤ ∞`, every `f ∈ A^s_q(X)` is `f = ι y` for some `y ∈ B^{s-α}_q(Y)`, with

`‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}`,   `K = nikolskiiConst C α s`

in the dyadic quasi-norms (`exists_preimage_of_nikolskii`).  The typical case is
`X = L_p ⊇ Y = L_r` with `p < r` and `α = d (1/p - 1/r)`: a function in the Besov space
`B^s_{p,q}` with `s > d(1/p - 1/r)` is in `L_r` and belongs to `B^{s - d(1/p-1/r)}_{r,q}`.
`ι` is the inclusion `L_r → L_p`, which is not surjective, so `f` is *a priori* only an
element of `L_p`; the theorem constructs its `L_r` version.

**Proof.** The telescoping lift of `ApproximationSpaces.Lift` gives `y = y_0 + ∑_k d_k` in `Y`
whose partial sums `z_k` lie in `B (2^k)`.  So `E^B_{2^k}(y) ≤ ‖y - z_k‖ ≤ ∑_{i ≥ k} ‖d_i‖` and
`‖d_i‖ ≲ 2^(iα) E_{2^i}(f)`; Hardy's inequality for tails with exponent `s - α > 0`
(`ENNReal.hardy_tail_le`) converts this into the bound on `‖(2^(k(s-α)) E^B_{2^k}(y))_k‖_q`
(`approxNormDyadic_le_of_tail`, which the trace transfer theorem uses as well).
The strict inequality `α < s` is needed for Hardy's inequality and for the convergence of the
series; the limiting case `α = s` is false in general.
-/

@[expose] public section

open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {α C s : ℝ} {q : ℝ≥0∞}

/-- The constant of the Nikolskii transfer theorem,
`3 C + 3 K (1 - 2^(-(s-α)))⁻¹ + 2 K` with `K = liftConst C α`. -/
noncomputable def nikolskiiConst (C α s : ℝ) : ℝ≥0∞ :=
  3 * ENNReal.ofReal C + 3 * liftConst C α * (1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹ + 2 * liftConst C α

/-- The constant of the Nikolskii transfer theorem is finite for `α < s`. -/
theorem nikolskiiConst_ne_top (C : ℝ) (h : α < s) : nikolskiiConst C α s ≠ ∞ := by
  have h1 : liftConst C α ≠ ∞ := liftConst_ne_top C α
  have h2 := ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 h)
  unfold nikolskiiConst
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h1) h2⟩,
    ENNReal.mul_ne_top (by norm_num) h1⟩

/-- **The transfer estimate.**  Let `1 ≤ q ≤ ∞`, `α ≤ s`, `t_k = tolerance f s k` and
`g_k = 2^(kα) (E_{2^k}(f) + t_k)`.  If an element `y` of `Y` and a scheme `B` in `Y` satisfy
`‖y‖ ≤ c (2 ‖f‖ + ‖f‖) + K ∑_k g_k` and `E^B_{2^k}(y) ≤ K ∑_{i ≥ 0} g_{k+i}` for every `k`, then
`‖y‖_{B^{s-α}_q} ≤ (3 c + 3 K (1 - 2^(-(s-α)))⁻¹ + 2 K) ‖f‖_{A^s_q}` in the dyadic
quasi-norms.  The constant is finite for `α < s` (`ENNReal.one_sub_two_rpow_neg_inv_ne_top`),
the case of both transfer theorems.  Hardy's inequality for tails (`ENNReal.hardy_tail_le`)
turns the tail bound into the bound of the `ℓ_q` part.  The Nikolskii transfer theorem and the
trace transfer theorem (`TraceBound.approxNormDyadic_ext_le`) both end with this estimate. -/
theorem approxNormDyadic_le_of_tail {B : ApproximationScheme Y} {c K : ℝ≥0∞} (hαs : α ≤ s)
    (hq : 1 ≤ q) (f : X) {y : Y}
    (hy : ‖y‖ₑ ≤ c * (2 * ‖f‖ₑ + ‖f‖ₑ) +
      K * ∑' k, dyadicWeight α k * (A.approxError f (2 ^ k) + tolerance f s k))
    (herr : ∀ k, B.approxError y (2 ^ k) ≤ K * ∑' i, dyadicWeight α (k + i) *
      (A.approxError f (2 ^ (k + i)) + tolerance f s (k + i))) :
    B.approxNormDyadic (s - α) q y ≤
      (3 * c + 3 * K * (1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹ + 2 * K) * A.approxNormDyadic s q f := by
  set N := A.approxNormDyadic s q f
  set Cs := (1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹
  set g : ℕ → ℝ≥0∞ := fun m => dyadicWeight α m * (A.approxError f (2 ^ m) + tolerance f s m)
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  have hL : lqNorm 1 (A.approxSeqDyadic α f) ≤ Cs * N :=
    (lqNorm_le_approxNormDyadic f).trans (approxNormDyadic_le_of_lt hq le_rfl f)
  have hg : ∀ k, dyadicWeight (s - α) k * g k =
      A.approxSeqDyadic s f k + dyadicWeight s k * tolerance f s k := fun k => by
    simp only [g, approxSeqDyadic, ← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel,
      mul_add]
  have hlq : lqNorm q (B.approxSeqDyadic (s - α) y) ≤ K * (Cs * (2 * N)) := by
    calc lqNorm q (B.approxSeqDyadic (s - α) y)
        ≤ lqNorm q (fun k => K * (dyadicWeight (s - α) k * ∑' i, g (k + i))) :=
          ENNReal.lqNorm_mono fun k =>
            (mul_le_mul' le_rfl (herr k)).trans_eq (mul_left_comm _ _ _)
      _ = K * lqNorm q (fun k => dyadicWeight (s - α) k * ∑' i, g (k + i)) :=
          ENNReal.lqNorm_const_mul _ _
      _ ≤ K * (Cs * lqNorm q (fun k => dyadicWeight (s - α) k * g k)) := by
          gcongr; exact ENNReal.hardy_tail_le hq (s - α) g
      _ ≤ K * (Cs * (2 * N)) := by
          gcongr
          simp_rw [hg]
          refine (lqNorm_approxSeqDyadic_add_tolerance_le hq f s).trans ?_
          calc lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ
              ≤ 2 * lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ := by
                gcongr; exact le_mul_of_one_le_left' one_le_two
            _ = 2 * N := by rw [show N = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) from rfl]; ring
  have hnorm : ‖y‖ₑ ≤ (3 * c + K * Cs + 2 * K) * N := by
    calc ‖y‖ₑ ≤ c * (2 * ‖f‖ₑ + ‖f‖ₑ) + K * ∑' k, g k := hy
      _ ≤ c * (3 * N) + K * (Cs * N + 2 * N) := by
          gcongr
          · calc 2 * ‖f‖ₑ + ‖f‖ₑ = 3 * ‖f‖ₑ := by ring
              _ ≤ 3 * N := by gcongr
          · exact (tsum_dyadicWeight_mul_add_tolerance_le (A := A) f hαs).trans
              (add_le_add hL (by gcongr))
      _ = (3 * c + K * Cs + 2 * K) * N := by ring
  calc B.approxNormDyadic (s - α) q y = ‖y‖ₑ + lqNorm q (B.approxSeqDyadic (s - α) y) := rfl
    _ ≤ (3 * c + K * Cs + 2 * K) * N + K * (Cs * (2 * N)) := add_le_add hnorm hlq
    _ = (3 * c + 3 * K * Cs + 2 * K) * N := by ring

/-- **The Nikolskii transfer theorem.**  For an injective `ι : Y → X` with a Nikolskii
inequality of exponent `α` for `A`, `0 ≤ α < s` and `1 ≤ q ≤ ∞`, every `f ∈ A^s_q(X)` is
`ι y` for some `y ∈ Y` with `‖y‖_{B^{s-α}_q} ≤ K ‖f‖_{A^s_q}` (dyadic quasi-norms), where `B`
is the scheme `ι⁻¹(A n)` in `Y`. -/
theorem exists_preimage_of_nikolskii [CompleteSpace Y] (hι : Function.Injective ι)
    (hN : LiftBound ι A α C) (hC : 0 ≤ C) (hα : 0 ≤ α) (hαs : α < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) :
    ∃ y : Y, ι y = f ∧ (A.comap ι.toLinearMap hι).approxNormDyadic (s - α) q y ≤
      nikolskiiConst C α s * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero ι, by simp⟩
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s)
  obtain ⟨y, hy, hyle, htail⟩ := D.exists_preimage (tolerance_anti f (hα.trans hαs.le)) hN hC
    hα (tsum_dyadicWeight_mul_add_tolerance_ne_top hαs.le (hf.lqNorm_one_lt_top hq hα hαs).ne)
  rw [tolerance_zero] at hyle
  refine ⟨y, hy, approxNormDyadic_le_of_tail hαs.le hq f hyle fun k => ?_⟩
  obtain ⟨z, hz, hzle⟩ := htail k
  exact (approxError_le_of_mem (A.mem_comap.2 hz) y).trans hzle

/-- **The Nikolskii transfer theorem**, membership form: `f ∈ A^s_q(X)` gives `f = ι y` with
`y ∈ B^{s-α}_q(Y)`. -/
theorem MemApprox.exists_preimage_of_nikolskii [CompleteSpace Y] (hι : Function.Injective ι)
    (hN : LiftBound ι A α C) (hC : 0 ≤ C) (hα : 0 ≤ α) (hαs : α < s) (hq : 1 ≤ q) {f : X}
    (hf : A.MemApprox s q f) :
    ∃ y : Y, ι y = f ∧ (A.comap ι.toLinearMap hι).MemApprox (s - α) q y := by
  obtain ⟨y, hy, hle⟩ := ApproximationScheme.exists_preimage_of_nikolskii hι hN hC hα hαs hq hf
  refine ⟨y, hy, (memApprox_iff_approxNormDyadic_lt_top hq (sub_nonneg.2 hαs.le)).2 ?_⟩
  exact hle.trans_lt (ENNReal.mul_lt_top (nikolskiiConst_ne_top C hαs).lt_top
    ((memApprox_iff_approxNormDyadic_lt_top hq (hα.trans hαs.le)).1 hf))

end ApproximationScheme
