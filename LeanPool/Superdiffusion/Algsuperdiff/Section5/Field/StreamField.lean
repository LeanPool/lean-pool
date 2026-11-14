/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Carrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ShellPerturbation

/-!
# StreamField

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The full stream matrix

ABK26's stream matrix is the formal sum `k(x) = Σ_{n ∈ ℤ} j_n(x)`, which does
not converge; the paper records that it is the differences `k(x) - k(y)` that
converge, and that only `∇ · k` enters the generator, so the field is defined
modulo constants.  This module builds the normalized representative

`k(x) = Σ_{n ∈ ℤ} (j_n(x) - j_n(0))` ,

as an honest `tsum` over `ℤ`, on the carrier `FullSample` where both halves
converge locally uniformly: the descending half from the value gauges of the
cutoff carrier, the ascending half from the gradient gauges through the mean
value inequality.

## Main definitions

* `streamField ω` — the normalized field `k`, matrix valued.

## Main results

* `streamField_skew`, `streamField_zero` — antisymmetry and the normalization.
* `streamField_eq_cutoff_add_upperTail` — the identification with the cutoffs:
  `k(x) - k_m(x) + k_m(0) = Σ_{n > m} (j_n(x) - j_n(0))`.
* `streamField_sub_cutoff_sub_eq` — the same identity in subtractive form.

## References

* ABK26, the stream matrix and the remark that only differences converge.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-! ## 1. Origin cubes of nonnegative scale exhaust the space -/

theorem exists_nat_mem_openOriginCube (x : Vec d) :
    ∃ ell : ℕ, x ∈ openCubeSet (originCube d (ell : ℤ)) := by
  have hpow : ∀ᶠ n : ℕ in Filter.atTop, 2 * ‖x‖ + 1 < (3 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop _
  obtain ⟨n, hn⟩ := hpow.exists
  refine ⟨n, ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hpow_int : (3 : ℝ) ^ ((n : ℕ) : ℤ) = (3 : ℝ) ^ n := by simp
  have hlt : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    have hnorm : 0 ≤ ‖x‖ := norm_nonneg x
    linarith only [hxi, hn, hnorm]
  rw [hpow_int]
  constructor
  · linarith only [hlt, neg_abs_le (x i)]
  · linarith only [hlt, le_abs_self (x i)]

theorem norm_le_of_mem_openOriginCube {ell : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) :
    ‖x‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ ell := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ell := zpow_pos (by norm_num) ell
  refine (pi_norm_le_iff_of_nonneg (by linarith only [hpos])).2 fun i => ?_
  obtain ⟨h1, h2⟩ := mem_openCubeSet_originCube_iff.1 hx i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [h1, h2]

theorem zero_mem_openOriginCube (d : ℕ) (ell : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d ell) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ell := zpow_pos (by norm_num) ell
  constructor <;> simp <;> linarith only [hpos]

/-! ## 2. The mean value bound on a cube -/

/-- **The mean value inequality for one shell on an origin cube**, in the
ambient norms, with the dimensional cost `d` of the conversion between the
ambient norm of the stored derivative and its exact Euclidean induced norm. -/
theorem norm_sub_zero_le_of_mem_openOriginCube (ell : ℤ) (j : ShellField d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    ‖j x - j 0‖ ≤ (d : ℝ) * localCubeDerivNorm ell j * ‖x‖ := by
  have hbound := Section5.Support.holderSeminormBoundOn_one_of_hasFDerivAt
    (U := openCubeSet (originCube d ell)) (convex_openCubeSet _)
    (F := fun z : Vec d => j z) (F' := fun z : Vec d => ShellField.deriv j z)
    (fun z _ => j.hasFDerivAt z)
    (L := (d : ℝ) * localCubeDerivNorm ell j)
    (fun z hz => (Section5.Support.norm_le_dim_mul_matrixDerivativeNorm
        (ShellField.deriv j z)).trans
      (mul_le_mul_of_nonneg_left
        (matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell j hz)
        (Nat.cast_nonneg d)))
  have h := hbound x hx 0 (zero_mem_openOriginCube d ell)
  rwa [sub_zero, Real.rpow_one] at h

/-- The entrywise form of the mean value bound. -/
theorem abs_entry_sub_le_of_mem_openOriginCube (ell : ℤ) (j : ShellField d)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |j x i k - j 0 i k| ≤ (d : ℝ) * localCubeDerivNorm ell j * ‖x‖ := by
  refine le_trans ?_ (norm_sub_zero_le_of_mem_openOriginCube ell j hx)
  have h := Matrix.norm_entry_le_entrywise_sup_norm (j x - j 0) (i := i) (j := k)
  simpa only [Matrix.sub_apply, Real.norm_eq_abs] using h

/-! ## 3. Summability of the two halves on the carrier -/

/-- The ascending gradient series on the origin cube of scale `ℓ` is summable
with sum at most the carrier's constant, uniformly in the starting index. -/
theorem summable_localCubeDerivNorm_ascending_base (omega : CutoffSample d) {C : ℕ}
    (hC : StreamGrowthBounded C omega) (ell : ℕ) :
    Summable fun r : ℕ => localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ))) :=
  summable_of_sum_range_le (c := (C : ℝ)) (fun _ => localCubeDerivNorm_nonneg _ _)
    fun q => sum_range_localCubeDerivNorm_le hC ell q

/-- The ascending gradient series on `□_ℓ` sums to at most the sample
constant. -/
theorem tsum_localCubeDerivNorm_ascending_le (omega : CutoffSample d) {C : ℕ}
    (hC : StreamGrowthBounded C omega) (ell : ℕ) :
    (∑' r : ℕ, localCubeDerivNorm (ell : ℤ) (omega.1 ((ell : ℤ) + (r : ℤ)))) ≤ (C : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => localCubeDerivNorm_nonneg _ _)
    fun q => sum_range_localCubeDerivNorm_le hC ell q

/-- The ascending gradient series on the origin cube of scale `ℓ` is summable
from any starting index: shifting the starting index changes the family by
finitely many terms. -/
theorem summable_localCubeDerivNorm_ascending (omega : FullSample d gamma) (ell : ℕ)
    (N : ℤ) :
    Summable fun r : ℕ => localCubeDerivNorm (ell : ℤ) (omega.1.1 (N + (r : ℤ))) := by
  have hupper : UpperGradBounded (ell : ℤ) 0 omega.1 := by
    rw [← ratPoint_zero]
    exact fullTailGood_upperGrad omega.2 (ell : ℤ) (0 : Fin d → ℚ)
  have hshell : Summable fun r : ℕ =>
      Section4.Support.shellW1InfGradNorm (ell : ℤ)
        (omega.1.1 ((ell : ℤ) + (r : ℤ))) := by
    simpa only [ShellField.translate_zero] using summable_of_upperGradBounded hupper
  have hbase : Summable fun r : ℕ =>
      localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + (r : ℤ))) := by
    refine Summable.of_nonneg_of_le (fun r => localCubeDerivNorm_nonneg _ _) (fun r => ?_)
      (hshell.mul_left ((3 : ℝ) ^ ell))
    have h := Section4.Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm
      (ell : ℤ) (omega.1.1 ((ell : ℤ) + (r : ℤ)))
    have hpow : (0 : ℝ) < (3 : ℝ) ^ ell := by positivity
    have hz : ((3 : ℝ) ^ ((ell : ℕ) : ℤ))⁻¹ = ((3 : ℝ) ^ ell)⁻¹ := by simp
    rw [zpow_neg, hz] at h
    calc
      localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + (r : ℤ))) =
          (3 : ℝ) ^ ell * (((3 : ℝ) ^ ell)⁻¹ *
            localCubeDerivNorm (ell : ℤ) (omega.1.1 ((ell : ℤ) + (r : ℤ)))) := by
        field_simp
      _ ≤ (3 : ℝ) ^ ell * Section4.Support.shellW1InfGradNorm (ell : ℤ)
            (omega.1.1 ((ell : ℤ) + (r : ℤ))) :=
        mul_le_mul_of_nonneg_left h hpow.le
  set K : ℕ := ((ell : ℤ) - N).toNat with hK_def
  set S : ℕ := (N + (K : ℤ) - (ell : ℤ)).toNat with hS_def
  refine (summable_nat_add_iff K).1 ?_
  have hshift := (summable_nat_add_iff S).2 hbase
  refine hshift.congr fun r => ?_
  have hidx : (ell : ℤ) + ((r + S : ℕ) : ℤ) = N + ((r + K : ℕ) : ℤ) := by
    have hKz : (K : ℤ) = max ((ell : ℤ) - N) 0 := by omega
    have hSz : (S : ℤ) = max (N + (K : ℤ) - (ell : ℤ)) 0 := by omega
    push_cast
    omega
  rw [hidx]

/-- The descending value series on any origin cube is summable, by the
lower-tail condition already carried by the ambient carrier. -/
theorem summable_localCubeControl_descending (omega : CutoffSample d) (ell m : ℤ) :
    Summable fun r : ℕ => localCubeControl ell (omega.1 (m - (r : ℤ))) :=
  lowerTailGood_summable omega.2 ell m

/-! ## 4. Summability of the normalized increments -/

/-- The ascending half, from any starting index, is summable. -/
theorem summable_streamIncrement_ascending (omega : FullSample d gamma) (N : ℤ)
    (x : Vec d) (i k : Fin d) :
    Summable fun r : ℕ =>
      omega.1.1 (N + (r : ℤ)) x i k - omega.1.1 (N + (r : ℤ)) 0 i k := by
  obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
  refine Summable.of_norm_bounded
    (g := fun r : ℕ =>
      (d : ℝ) * localCubeDerivNorm (ell : ℤ) (omega.1.1 (N + (r : ℤ))) * ‖x‖)
    (((summable_localCubeDerivNorm_ascending omega ell N).mul_left (d : ℝ)).mul_right ‖x‖)
    fun r => ?_
  rw [Real.norm_eq_abs]
  exact abs_entry_sub_le_of_mem_openOriginCube (ell : ℤ) (omega.1.1 (N + (r : ℤ))) hx i k

/-- The descending half is summable entrywise. -/
theorem summable_streamIncrement_descending (omega : CutoffSample d) (m : ℤ)
    (x : Vec d) (i k : Fin d) :
    Summable fun r : ℕ =>
      omega.1 (m - (r : ℤ)) x i k - omega.1 (m - (r : ℤ)) 0 i k := by
  obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
  refine Summable.of_norm_bounded
    (g := fun r : ℕ => 2 * localCubeControl (ell : ℤ) (omega.1 (m - (r : ℤ))))
    ((summable_localCubeControl_descending omega (ell : ℤ) m).mul_left 2) fun r => ?_
  rw [Real.norm_eq_abs]
  have h1 := abs_entry_le_localCubeControl (ell : ℤ) (omega.1 (m - (r : ℤ))) hx i k
  have h2 := abs_entry_le_localCubeControl (ell : ℤ) (omega.1 (m - (r : ℤ)))
    (zero_mem_openOriginCube d (ell : ℤ)) i k
  calc |omega.1 (m - (r : ℤ)) x i k - omega.1 (m - (r : ℤ)) 0 i k| ≤
      |omega.1 (m - (r : ℤ)) x i k| + |omega.1 (m - (r : ℤ)) 0 i k| := abs_sub _ _
    _ ≤ 2 * localCubeControl (ell : ℤ) (omega.1 (m - (r : ℤ))) := by
      linarith only [h1, h2]

/-! ## 5. The field -/

/-- **The normalized stream matrix** `k(x) = Σ_{n ∈ ℤ} (j_n(x) - j_n(0))`.
The sum is over all of `ℤ` and is genuinely convergent on the carrier; the
normalization at the origin is the additive constant the source leaves free. -/
def streamField (omega : FullSample d gamma) (x : Vec d) : Mat d :=
  fun i k => ∑' n : ℤ, (omega.1.1 n x i k - omega.1.1 n 0 i k)

@[simp]
theorem streamField_apply_entry (omega : FullSample d gamma) (x : Vec d) (i k : Fin d) :
    streamField omega x i k = ∑' n : ℤ, (omega.1.1 n x i k - omega.1.1 n 0 i k) :=
  rfl

/-- **The normalization**: the field vanishes at the origin. -/
@[simp]
theorem streamField_zero (omega : FullSample d gamma) : streamField omega 0 = 0 := by
  ext i k
  simp only [streamField_apply_entry, sub_self, tsum_zero, Matrix.zero_apply]

/-- **Antisymmetry**: every shell is antisymmetric, hence so is the sum. -/
theorem streamField_skew (omega : FullSample d gamma) (x : Vec d) :
    (streamField omega x).transpose = -streamField omega x := by
  ext i k
  rw [Matrix.transpose_apply, Matrix.neg_apply, streamField_apply_entry,
    streamField_apply_entry]
  calc (∑' n : ℤ, (omega.1.1 n x k i - omega.1.1 n 0 k i)) =
      ∑' n : ℤ, -(omega.1.1 n x i k - omega.1.1 n 0 i k) := by
        refine tsum_congr fun n => ?_
        rw [ShellField.skew_entry (omega.1.1 n) x k i,
          ShellField.skew_entry (omega.1.1 n) 0 k i]
        ring
    _ = -∑' n : ℤ, (omega.1.1 n x i k - omega.1.1 n 0 i k) := tsum_neg

/-! ## 6. The identification with the cutoffs -/

/-- **The cutoff identification.**  For every scale `m`, the normalized field is
the normalized `m`-th cutoff plus the tail of the ascending half:
`k(x) = (k_m(x) - k_m(0)) + Σ_{n > m} (j_n(x) - j_n(0))`. -/
theorem streamField_eq_cutoff_add_upperTail (omega : FullSample d gamma) (m : ℤ)
    (x : Vec d) (i k : Fin d) :
    streamField omega x i k =
      (cutoff m omega.1 x i k - cutoff m omega.1 0 i k) +
        ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) 0 i k) := by
  set f : ℤ → ℝ := fun n => omega.1.1 n x i k - omega.1.1 n 0 i k with hf_def
  have hshift : (∑' n : ℤ, f n) = ∑' n : ℤ, f (n + (m + 1)) :=
    (Equiv.tsum_eq (Equiv.addRight (m + 1)) f).symm
  have hasc : Summable fun r : ℕ => f ((r : ℤ) + (m + 1)) := by
    have h := summable_streamIncrement_ascending omega (m + 1) x i k
    refine h.congr fun r => ?_
    have hidx : m + 1 + (r : ℤ) = (r : ℤ) + (m + 1) := by ring
    rw [hf_def, hidx]
  have hdesc : Summable fun r : ℕ => f (-((r : ℤ) + 1) + (m + 1)) := by
    have h := summable_streamIncrement_descending omega.1 m x i k
    refine h.congr fun r => ?_
    have hidx : m - (r : ℤ) = -((r : ℤ) + 1) + (m + 1) := by ring
    rw [hf_def, hidx]
  have hsplit : (∑' n : ℤ, f (n + (m + 1))) =
      (∑' r : ℕ, f ((r : ℤ) + (m + 1))) + ∑' r : ℕ, f (-((r : ℤ) + 1) + (m + 1)) :=
    tsum_of_nat_of_neg_add_one hasc hdesc
  have hdesc_eq : (∑' r : ℕ, f (-((r : ℤ) + 1) + (m + 1))) =
      cutoff m omega.1 x i k - cutoff m omega.1 0 i k := by
    have hsx : Summable fun r : ℕ => omega.1.1 (m - (r : ℤ)) x i k := by
      obtain ⟨ell, hx⟩ := exists_nat_mem_openOriginCube x
      exact (summable_localCubeControl_descending omega.1 (ell : ℤ) m).of_norm_bounded fun r => by
        simpa only [Real.norm_eq_abs] using
          abs_entry_le_localCubeControl (ell : ℤ) (omega.1.1 (m - (r : ℤ))) hx i k
    have hs0 : Summable fun r : ℕ => omega.1.1 (m - (r : ℤ)) 0 i k := by
      exact (summable_localCubeControl_descending omega.1 0 m).of_norm_bounded fun r => by
        simpa only [Real.norm_eq_abs] using
          abs_entry_le_localCubeControl (0 : ℤ) (omega.1.1 (m - (r : ℤ)))
            (zero_mem_openOriginCube d 0) i k
    calc (∑' r : ℕ, f (-((r : ℤ) + 1) + (m + 1))) =
        ∑' r : ℕ, (omega.1.1 (m - (r : ℤ)) x i k - omega.1.1 (m - (r : ℤ)) 0 i k) := by
          refine tsum_congr fun r => ?_
          have hidx : -((r : ℤ) + 1) + (m + 1) = m - (r : ℤ) := by ring
          rw [hf_def, hidx]
      _ = (∑' r : ℕ, omega.1.1 (m - (r : ℤ)) x i k) -
            ∑' r : ℕ, omega.1.1 (m - (r : ℤ)) 0 i k := hsx.tsum_sub hs0
      _ = cutoff m omega.1 x i k - cutoff m omega.1 0 i k := by
          rw [cutoff_apply_entry, cutoff_apply_entry]
  have hasc_eq : (∑' r : ℕ, f ((r : ℤ) + (m + 1))) =
      ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) 0 i k) := by
    refine tsum_congr fun r => ?_
    have hidx : (r : ℤ) + (m + 1) = m + 1 + (r : ℤ) := by ring
    rw [hf_def, hidx]
  rw [streamField_apply_entry, hshift, hsplit, hdesc_eq, hasc_eq, add_comm]

/-- The identification in the subtractive form of the source: the difference
between the field and its `m`-th cutoff, both normalized at the origin, is the
tail `Σ_{n > m} (j_n(x) - j_n(0))`. -/
theorem streamField_sub_cutoff_sub_eq (omega : FullSample d gamma) (m : ℤ) (x : Vec d)
    (i k : Fin d) :
    streamField omega x i k - cutoff m omega.1 x i k + cutoff m omega.1 0 i k =
      ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) 0 i k) := by
  rw [streamField_eq_cutoff_add_upperTail omega m x i k]
  ring

end

end Algsuperdiff.Section5.Field
