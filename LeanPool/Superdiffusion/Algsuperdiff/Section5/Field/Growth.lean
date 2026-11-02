/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Continuity

/-!
# Growth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Linear growth of the stream matrix

On a cube of scale `ℓ` the normalized field splits as
`k = (k_ℓ - k_ℓ(0)) + Σ_{n > ℓ} (j_n - j_n(0))`.  The first summand is bounded by
twice the descending value sum on `□_ℓ`, the second by the diameter `3^{ℓ}` of
the cube times the ascending gradient sum on `□_ℓ`.  The quantitative condition
of the carrier bounds the first by `C 3^{ℓ}` and the second by `C`, so the size
of the field on `□_ℓ` is at most a dimensional multiple of `C 3^{ℓ}`.

Choosing the smallest cube containing the ball of radius `R` turns this into the
linear bound `‖k‖_{L^∞(B_R)} ≤ C_k (1 + R)` for `R ≥ 1`, with the sample constant
`C_k` displayed explicitly.  The true growth of the source field is `R^{γ}`;
the linear statement is the one the process theory consumes.

## Main definitions

* `streamTailConst ω` — the sample constant supplied by the carrier.
* `streamFieldGrowthConst ω` — the explicit linear-growth constant.

## Main results

* `matrixOperatorNorm_streamField_le_on_cube` — the cube form.
* `matrixOperatorNorm_streamField_le` — the linear growth on balls.

## References

* ABK26, the stream matrix; the almost sure bound `‖k‖_{L^∞(U_m)} ≲ 3^{γ m}`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport HCPolySupport.Book.Ch02
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## 1. The matrix norm through the entries -/

private theorem matrixOperatorNorm_le_sum_abs_entries (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ i, ∑ k, |A i k| := by
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A (0 : Mat d)
  simpa only [matrixOperatorNorm_zero, Matrix.zero_apply, sub_zero, zero_add] using h

private theorem sum_abs_entries_le_of_forall (A : Mat d) {b : ℝ}
    (h : ∀ i k, |A i k| ≤ b) : (∑ i, ∑ k, |A i k|) ≤ (d : ℝ) ^ 2 * b := by
  calc (∑ i, ∑ k, |A i k|) ≤ ∑ _i : Fin d, ∑ _k : Fin d, b := by
        gcongr with i _ k _
        exact h i k
    _ = (d : ℝ) ^ 2 * b := by
        simp [pow_two]
        ring

/-! ## 2. The sample constant -/

/-- The sample constant of the quantitative two-leg condition. -/
def streamTailConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℕ :=
  Classical.choose (fullTailGood_growth M omega)

theorem streamTailConst_spec (M : ABKModel d) (omega : FullSample d M.gamma) :
    StreamGrowthBounded (streamTailConst M omega) omega.1 :=
  Classical.choose_spec (fullTailGood_growth M omega)

/-! ## 3. The two legs on one cube -/

private theorem abs_cutoff_entry_le_on_cube (M : ABKModel d) (omega : FullSample d M.gamma) {C : ℕ}
    (hC : StreamGrowthBounded C omega.1) (ell : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (ell : ℤ))) (i k : Fin d) :
    |cutoff (ell : ℤ) omega.1 x i k| ≤ (C : ℝ) * (3 : ℝ) ^ ell := by
  have habs : ∀ r : ℕ, |omega.1.1 ((ell : ℤ) - (r : ℤ)) x i k| ≤
      localCubeControl (ell : ℤ) (omega.1.1 ((ell : ℤ) - (r : ℤ))) :=
    fun r => abs_entry_le_localCubeControl (ell : ℤ) _ hx i k
  have hsummable := summable_localCubeControl_descending omega.1 (ell : ℤ) (ell : ℤ)
  have hsummable_abs : Summable fun r : ℕ => |omega.1.1 ((ell : ℤ) - (r : ℤ)) x i k| :=
    Summable.of_nonneg_of_le (fun r => abs_nonneg _) habs hsummable
  have hnorm : Summable fun r : ℕ => ‖omega.1.1 ((ell : ℤ) - (r : ℤ)) x i k‖ := by
    simpa only [Real.norm_eq_abs] using hsummable_abs
  calc |cutoff (ell : ℤ) omega.1 x i k| =
      |∑' r : ℕ, omega.1.1 ((ell : ℤ) - (r : ℤ)) x i k| := by rw [cutoff_apply_entry]
    _ ≤ ∑' r : ℕ, |omega.1.1 ((ell : ℤ) - (r : ℤ)) x i k| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ, localCubeControl (ell : ℤ) (omega.1.1 ((ell : ℤ) - (r : ℤ))) :=
        hsummable_abs.tsum_le_tsum habs hsummable
    _ ≤ (C : ℝ) * (3 : ℝ) ^ ell := tsum_lowerValue_le_of_streamGrowthBounded hC ell

/-- Dropping the first term of a convergent series of nonnegative reals keeps
any upper bound on its sum. -/
private theorem tsum_succ_le_of_nonneg {f : ℕ → ℝ} (hf : Summable f)
    (hf0 : ∀ n : ℕ, 0 ≤ f n) {C : ℝ} (h : (∑' n : ℕ, f n) ≤ C) :
    (∑' n : ℕ, f (n + 1)) ≤ C := by
  have hsplit := hf.tsum_eq_zero_add
  linarith only [hsplit, h, hf0 0]

private theorem tsum_localCubeDerivNorm_succ_le (M : ABKModel d) (omega : FullSample d M.gamma) {C
  : ℕ}
    (hC : StreamGrowthBounded C omega.1) (ell : ℕ) :
    (∑' r : ℕ,
        localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)))) ≤ (C : ℝ) := by
  have hstep := tsum_succ_le_of_nonneg
    (f := fun s : ℕ => localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + (s : ℤ))))
    (summable_localCubeDerivNorm_ascending_base omega.1 hC ell)
    (fun _ => localCubeDerivNorm_nonneg _ _)
    (tsum_localCubeDerivNorm_ascending_le omega.1 hC ell)
  refine le_trans (le_of_eq (tsum_congr fun r => ?_)) hstep
  have hidx : (ell : ℤ) + 1 + (r : ℤ) = (ell : ℤ) + ((r + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [hidx]

private theorem abs_upperTail_entry_le_on_cube (M : ABKModel d) (omega : FullSample d M.gamma) {C
  : ℕ}
    (hC : StreamGrowthBounded C omega.1) (ell : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (ell : ℤ))) (i k : Fin d) :
    |∑' r : ℕ, (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
        omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k)| ≤
      (d : ℝ) * (C : ℝ) * ‖x‖ := by
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hmaj : Summable fun r : ℕ =>
      (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) * ‖x‖ :=
    ((summable_localCubeDerivNorm_ascending omega ell ((ell : ℤ) + 1)).mul_left
      (d : ℝ)).mul_right _
  have habs : ∀ r : ℕ,
      |omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
          omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k| ≤
        (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) *
          ‖x‖ :=
    fun r => abs_entry_sub_le_of_mem_openOriginCube (ell : ℤ) _ hx i k
  have hsummable_abs : Summable fun r : ℕ =>
      |omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
        omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k| :=
    Summable.of_nonneg_of_le (fun r => abs_nonneg _) habs hmaj
  have hnorm : Summable fun r : ℕ =>
      ‖omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
        omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k‖ := by
    simpa only [Real.norm_eq_abs] using hsummable_abs
  have htail : (∑' r : ℕ,
      localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)))) ≤ (C : ℝ) :=
    tsum_localCubeDerivNorm_succ_le M omega hC ell
  calc |∑' r : ℕ, (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
        omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k)| ≤
      ∑' r : ℕ, |omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
        omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ, (d : ℝ) *
          localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ))) * ‖x‖ :=
        hsummable_abs.tsum_le_tsum habs hmaj
    _ = (d : ℝ) *
          (∑' r : ℕ,
            localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)))) * ‖x‖ := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ (d : ℝ) * (C : ℝ) * ‖x‖ := by
        have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        have := mul_le_mul_of_nonneg_left htail hd
        exact mul_le_mul_of_nonneg_right this hxnn

/-! ## 4. The bound on a cube -/

/-- **The size of the field on the origin cube of scale `ℓ`.** -/
theorem matrixOperatorNorm_streamField_le_on_cube (M : ABKModel d) (omega : FullSample d M.gamma)
  (ell : ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (ell : ℤ))) :
    matrixOperatorNorm (streamField omega x) ≤
      ((d : ℝ) ^ 2 * ((streamTailConst M omega : ℝ) * (2 + (d : ℝ) / 2))) * (3 : ℝ) ^ ell := by
  have hC := streamTailConst_spec M omega
  set C : ℕ := streamTailConst M omega with hC_def
  have hzpow : (3 : ℝ) ^ ((ell : ℕ) : ℤ) = (3 : ℝ) ^ ell := by simp
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ ell := by
    have h := norm_le_of_mem_openOriginCube hx
    rwa [hzpow] at h
  have hentry : ∀ i k : Fin d, |streamField omega x i k| ≤
      ((C : ℝ) * (2 + (d : ℝ) / 2)) * (3 : ℝ) ^ ell := by
    intro i k
    have hsplit := streamField_eq_cutoff_add_upperTail omega (ell : ℤ) x i k
    have h1 := abs_cutoff_entry_le_on_cube M omega hC ell hx i k
    have h2 := abs_cutoff_entry_le_on_cube M omega hC ell
      (zero_mem_openOriginCube d (ell : ℤ)) i k
    have h3 := abs_upperTail_entry_le_on_cube M omega hC ell hx i k
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
    have h4 : (d : ℝ) * (C : ℝ) * ‖x‖ ≤
        (d : ℝ) * (C : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ ell) :=
      mul_le_mul_of_nonneg_left hxnorm (mul_nonneg hd hCnn)
    rw [hsplit]
    calc |cutoff (ell : ℤ) omega.1 x i k - cutoff (ell : ℤ) omega.1 0 i k +
          ∑' r : ℕ, (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
            omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k)| ≤
        |cutoff (ell : ℤ) omega.1 x i k - cutoff (ell : ℤ) omega.1 0 i k| +
          |∑' r : ℕ, (omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) x i k -
            omega.1.1 ((ell : ℤ) + 1 + (r : ℤ)) 0 i k)| := abs_add_le _ _
      _ ≤ (|cutoff (ell : ℤ) omega.1 x i k| + |cutoff (ell : ℤ) omega.1 0 i k|) +
            (d : ℝ) * (C : ℝ) * ‖x‖ := by
          exact add_le_add (abs_sub _ _) h3
      _ ≤ ((C : ℝ) * (2 + (d : ℝ) / 2)) * (3 : ℝ) ^ ell := by
          linarith only [h1, h2, h4]
  calc matrixOperatorNorm (streamField omega x) ≤
      ∑ i, ∑ k, |streamField omega x i k| :=
        matrixOperatorNorm_le_sum_abs_entries _
    _ ≤ (d : ℝ) ^ 2 * (((C : ℝ) * (2 + (d : ℝ) / 2)) * (3 : ℝ) ^ ell) :=
        sum_abs_entries_le_of_forall _ hentry
    _ = ((d : ℝ) ^ 2 * ((C : ℝ) * (2 + (d : ℝ) / 2))) * (3 : ℝ) ^ ell := by ring

/-! ## 5. Linear growth on balls -/

/-- **The explicit linear-growth constant** of the normalized field: a
dimensional factor times the sample constant of the carrier. -/
def streamFieldGrowthConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  6 * ((d : ℝ) ^ 2 * ((streamTailConst M omega : ℝ) * (2 + (d : ℝ) / 2)))

theorem streamFieldGrowthConst_nonneg (M : ABKModel d) (omega : FullSample d M.gamma) :
    0 ≤ streamFieldGrowthConst M omega := by
  unfold streamFieldGrowthConst
  positivity

/-- **Linear growth**: `‖k‖_{L^∞(B_R)} ≤ C_k (1 + R)` for every `R ≥ 1`, with the
sample constant `C_k` of `streamFieldGrowthConst`. -/
theorem matrixOperatorNorm_streamField_le (M : ABKModel d) (omega : FullSample d M.gamma) {R : ℝ}
  (hR : 1 ≤ R)
    {x : Vec d} (hx : ‖x‖ ≤ R) :
    matrixOperatorNorm (streamField omega x) ≤ streamFieldGrowthConst M omega * (1 + R) := by
  classical
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hex : ∃ n : ℕ, 2 * R < (3 : ℝ) ^ n :=
    ((tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop (2 * R)).exists
  obtain ⟨ell, hell_spec, hupper⟩ :
      ∃ ell : ℕ, 2 * R < (3 : ℝ) ^ ell ∧ (3 : ℝ) ^ ell ≤ 6 * R := by
    have hfind : 2 * R < (3 : ℝ) ^ Nat.find hex := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h
      · exfalso
        rw [h0, pow_zero] at hfind
        linarith only [hfind, hR]
      · exact h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hprev : ¬ (2 * R < (3 : ℝ) ^ m) := Nat.find_min hex (by omega)
    have hprev' : (3 : ℝ) ^ m ≤ 2 * R := not_lt.1 hprev
    refine ⟨Nat.find hex, hfind, ?_⟩
    rw [hm, pow_succ]
    linarith only [hprev']
  have hmem : x ∈ openCubeSet (originCube d (ell : ℤ)) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hzpow : (3 : ℝ) ^ ((ell : ℕ) : ℤ) = (3 : ℝ) ^ ell := by simp
    have hnorm_i : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hxi : |x i| ≤ R := hnorm_i.trans hx
    have hhalf : R < (1 / 2 : ℝ) * (3 : ℝ) ^ ell := by linarith only [hell_spec]
    rw [hzpow]
    constructor
    · linarith only [hxi, hhalf, neg_abs_le (x i)]
    · linarith only [hxi, hhalf, le_abs_self (x i)]
  have hcube := matrixOperatorNorm_streamField_le_on_cube M omega ell hmem
  have hKnn : (0 : ℝ) ≤ (d : ℝ) ^ 2 * ((streamTailConst M omega : ℝ) * (2 + (d : ℝ) / 2)) := by
    positivity
  calc matrixOperatorNorm (streamField omega x) ≤
      ((d : ℝ) ^ 2 * ((streamTailConst M omega : ℝ) * (2 + (d : ℝ) / 2))) * (3 : ℝ) ^ ell :=
        hcube
    _ ≤ ((d : ℝ) ^ 2 * ((streamTailConst M omega : ℝ) * (2 + (d : ℝ) / 2))) * (6 * R) :=
        mul_le_mul_of_nonneg_left hupper hKnn
    _ = streamFieldGrowthConst M omega * R := by
        unfold streamFieldGrowthConst
        ring
    _ ≤ streamFieldGrowthConst M omega * (1 + R) := by
        have := streamFieldGrowthConst_nonneg M omega
        nlinarith only [this, hRpos]

/-- The ambient supremum norm is dominated by the Euclidean norm. -/
private theorem norm_le_sqrt_vecNormSq (x : Vec d) : ‖x‖ ≤ Real.sqrt (vecNormSq x) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (HCPolySupport.sq_apply_le_vecNormSq x i)

/-- **Linear growth on Euclidean balls**, the form of the source's
`‖k‖_{L^∞(B_R)} ≤ C_k (1 + R)`: the ambient supremum norm of `Vec d` is
dominated by the Euclidean norm, so the ball statement follows from the cube
statement with the same constant. -/
theorem matrixOperatorNorm_streamField_le_of_euclidean (M : ABKModel d) (omega : FullSample d
  M.gamma) {R : ℝ}
    (hR : 1 ≤ R) {x : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R) :
    matrixOperatorNorm (streamField omega x) ≤ streamFieldGrowthConst M omega * (1 + R) :=
  matrixOperatorNorm_streamField_le M omega hR ((norm_le_sqrt_vecNormSq x).trans hx)

end

end Algsuperdiff.Section5.Field
