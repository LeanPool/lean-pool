/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GeometricSums

/-!
# WindowAmplitudes

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `√`-growing window amplitudes of the Step-3 layer variables

ABK26, `l.minimal.scale.sep` Step 3.  Step 3 applies the `Γ_σ` triangle
inequality to two finite layer sums, and the resulting scales are geometrically
weighted sums of the **`√`-growing** per-cube amplitude `Cv √(k + 1 − i)`
supplied by `e.maxy.bound`.  This module closes both of those deterministic
amplitude sums, and the weighted `tsum` that recombines the below-window
channel.

The two closures are exactly the tex's `Cs^{−3/2}` and `Cs^{−5/2}`, i.e.
`geomSqrtConst α` and `geomTailConst α · geomSqrtConst α`.  They are the point
of the sharp Cauchy--Schwarz closure
`Algsuperdiff.Probability.sum_threePow_neg_sqrt_le`: the crude `√(r+1) ≤ r+1`
would give `geomTailConst α ^ 2` and `geomTailConst α ^ 3`, half a power of the
parameter worse in each channel, and the printed envelope would not close.

Everything here is deterministic real arithmetic in the amplitudes `Cv`, `α` and
the scale indices; no sample space, no measure and no coefficient field appears.
The corresponding `O_{Γ₂}` statements about the layer variables themselves are
left to the consumer, which owns the carrier.

## Main results

* `Algsuperdiff.Probability.sum_windowAmp_le` — the in-window closure.
* `Algsuperdiff.Probability.sum_headAmp_le` — the below-window closure at depth
  `j`, with its `√(j+1)` growth.
* `Algsuperdiff.Probability.tsum_weight_step3HeadAmp_le` — the weighted
  recombination of the below-window channel.

## References

* ABK26, `l.minimal.scale.sep`, Step 3.
-/

namespace Algsuperdiff.Probability

open HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-! ## The explicit amplitudes -/

/-- The uniform `Γ₂` amplitude of the in-window layer variable: `gammaTriangleConst
2 · Cv · (1−3^{−α})^{−3/2}` — the tex's `Cs^{−3/2}`. -/
def step3WindowAmp (Cv α : ℝ) : ℝ := gammaTriangleConst 2 * (Cv * geomSqrtConst α)

/-- The per-`j` `Γ₂` amplitude of the below-window layer variable:
`gammaTriangleConst 2 · Cv · ((1−3^{−α})^{−3/2} + √(j+1)(1−3^{−α})⁻¹)`. It grows
like `√j`, which is exactly why the below-window channel needs a **per-layer**
tail closure and not a uniform one. -/
def step3HeadAmp (Cv α : ℝ) (j : ℕ) : ℝ :=
  gammaTriangleConst 2 *
    (Cv * (geomSqrtConst α + Real.sqrt ((j : ℝ) + 1) * geomTailConst α))

/-- The `Γ₂` amplitude of the below-window weighted sum `∑'_j 3^{−αj} H_j`:
`(gammaTriangleConst 2)² · 2 Cv (1−3^{−α})^{−5/2}` — the tex's `Cs^{−5/2}`. -/
def step3TailAmp (Cv α : ℝ) : ℝ :=
  gammaTriangleConst 2 *
    (gammaTriangleConst 2 * (2 * Cv * (geomTailConst α * geomSqrtConst α)))

theorem step3WindowAmp_pos {Cv α : ℝ} (hα : 0 < α) (hCv : 0 < Cv) :
    0 < step3WindowAmp Cv α := by
  simp only [step3WindowAmp]
  exact mul_pos gammaTriangleConst_pos (mul_pos hCv (geomSqrtConst_pos hα))

theorem step3HeadAmp_nonneg {Cv α : ℝ} (hα : 0 < α) (hCv : 0 ≤ Cv) (j : ℕ) :
    0 ≤ step3HeadAmp Cv α j := by
  have hCg : 0 < geomTailConst α := geomTailConst_pos hα
  have h1 : (0 : ℝ) ≤ geomSqrtConst α := (geomSqrtConst_pos hα).le
  have h2 : (0 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) * geomTailConst α :=
    mul_nonneg (Real.sqrt_nonneg _) hCg.le
  simp only [step3HeadAmp]
  exact mul_nonneg gammaTriangleConst_pos.le
    (mul_nonneg hCv (by linarith only [h1, h2]))

theorem step3HeadAmp_pos {Cv α : ℝ} (hα : 0 < α) (hCv : 0 < Cv) (j : ℕ) :
    0 < step3HeadAmp Cv α j := by
  have hCg : 0 < geomTailConst α := geomTailConst_pos hα
  have h1 : (0 : ℝ) < geomSqrtConst α := geomSqrtConst_pos hα
  have h2 : (0 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) * geomTailConst α :=
    mul_nonneg (Real.sqrt_nonneg _) hCg.le
  simp only [step3HeadAmp]
  exact mul_pos gammaTriangleConst_pos (mul_pos hCv (by linarith only [h1, h2]))

theorem step3TailAmp_nonneg {Cv α : ℝ} (hα : 0 < α) (hCv : 0 ≤ Cv) :
    0 ≤ step3TailAmp Cv α := by
  have hCg : 0 < geomTailConst α := geomTailConst_pos hα
  have h3 : (0 : ℝ) ≤ geomTailConst α * geomSqrtConst α :=
    mul_nonneg hCg.le (geomSqrtConst_pos hα).le
  simp only [step3TailAmp]
  exact mul_nonneg gammaTriangleConst_pos.le
    (mul_nonneg gammaTriangleConst_pos.le
      (mul_nonneg (mul_nonneg (by norm_num) hCv) h3))

/-! ## The two deterministic amplitude sums -/

/-- **The in-window amplitude sum, uniformly in `i` and `m`**.  The `Γ_σ` triangle
applied to `∑_{k=i}^m 3^{−α(k−i)} V i k` produces the scale `∑_{k=i}^m
3^{−α(k−i)} Cv √(k+1−i)`; that sum is `≤ Cv(1−3^{−α})^{−3/2}` for every `i` and
every `m`. -/
theorem sum_windowAmp_le {Cv α : ℝ} (hα : 0 < α) (hCv : 0 ≤ Cv) (i m : ℤ) :
    ∑ k ∈ Finset.Icc i m,
        (3 : ℝ) ^ (-(α * ((k - i : ℤ) : ℝ))) * (Cv * Real.sqrt (((k + 1 - i : ℤ) : ℝ)))
      ≤ Cv * geomSqrtConst α := by
  classical
  have hre := sum_Icc_eq_sum_range_offset i m
    (fun k => (3 : ℝ) ^ (-(α * ((k - i : ℤ) : ℝ)))
      * (Cv * Real.sqrt (((k + 1 - i : ℤ) : ℝ))))
  refine hre.trans_le ?_
  have hterm : ∀ r ∈ Finset.range ((m - i + 1).toNat),
      (3 : ℝ) ^ (-(α * (((i + (r : ℤ)) - i : ℤ) : ℝ)))
          * (Cv * Real.sqrt ((((i + (r : ℤ)) + 1 - i : ℤ) : ℝ)))
        ≤ (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) * Cv := by
    intro r _
    have h1 : ((i + (r : ℤ)) - i : ℤ) = (r : ℤ) := by ring
    have h2 : ((i + (r : ℤ)) + 1 - i : ℤ) = (r : ℤ) + 1 := by ring
    rw [h1, h2]
    push_cast
    exact le_of_eq (by ring)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hmul : ∑ r ∈ Finset.range ((m - i + 1).toNat),
        (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) * Cv
      = (∑ r ∈ Finset.range ((m - i + 1).toNat),
          (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)) * Cv := by
    rw [Finset.sum_mul]
  rw [hmul]
  have hmm := mul_le_mul_of_nonneg_right
    (sum_threePow_neg_sqrt_le (α := α) hα (Finset.range ((m - i + 1).toNat))) hCv
  have hcomm : geomSqrtConst α * Cv = Cv * geomSqrtConst α := by ring
  linarith only [hmm, hcomm.le, hcomm.ge]

/-- **The below-window amplitude sum, at layer depth `j`**.  For `i = n−1−j` and `k
∈ [n, m]` we have `k+1−i = (k−n+1) + (j+1)`, so `√(k+1−i) ≤ √(k−n+1) + √(j+1)`,
and the geometric closures give the per-`j` amplitude `Cv((1−3^{−α})^{−3/2} +
√(j+1)(1−3^{−α})⁻¹)`. -/
theorem sum_headAmp_le {Cv α : ℝ} (hα : 0 < α) (hCv : 0 ≤ Cv) (n m : ℤ) (j : ℕ) :
    ∑ k ∈ Finset.Icc n m,
        (3 : ℝ) ^ (-(α * ((k - n : ℤ) : ℝ)))
          * (Cv * Real.sqrt (((k + 1 - (n - 1 - (j : ℤ)) : ℤ) : ℝ)))
      ≤ Cv * (geomSqrtConst α + Real.sqrt ((j : ℝ) + 1) * geomTailConst α) := by
  classical
  have hre := sum_Icc_eq_sum_range_offset n m
    (fun k => (3 : ℝ) ^ (-(α * ((k - n : ℤ) : ℝ)))
      * (Cv * Real.sqrt (((k + 1 - (n - 1 - (j : ℤ)) : ℤ) : ℝ))))
  refine hre.trans_le ?_
  have hterm : ∀ r ∈ Finset.range ((m - n + 1).toNat),
      (3 : ℝ) ^ (-(α * (((n + (r : ℤ)) - n : ℤ) : ℝ)))
          * (Cv * Real.sqrt ((((n + (r : ℤ)) + 1 - (n - 1 - (j : ℤ)) : ℤ) : ℝ)))
        ≤ (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) * Cv
          + (3 : ℝ) ^ (-(α * (r : ℝ))) * (Cv * Real.sqrt ((j : ℝ) + 1)) := by
    intro r _
    have h1 : ((n + (r : ℤ)) - n : ℤ) = (r : ℤ) := by ring
    have h2 : ((n + (r : ℤ)) + 1 - (n - 1 - (j : ℤ)) : ℤ)
        = ((r : ℤ) + 1) + ((j : ℤ) + 1) := by ring
    rw [h1, h2]
    push_cast
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hkey : Real.sqrt (((r : ℝ) + 1) + ((j : ℝ) + 1))
        ≤ Real.sqrt ((r : ℝ) + 1) + Real.sqrt ((j : ℝ) + 1) :=
      sqrt_add_le_add_sqrt (by linarith only [hr0]) (by linarith only [hj0])
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(α * (r : ℝ))) := Real.rpow_nonneg (by norm_num) _
    have h4 : (3 : ℝ) ^ (-(α * (r : ℝ)))
          * (Cv * Real.sqrt (((r : ℝ) + 1) + ((j : ℝ) + 1)))
        ≤ (3 : ℝ) ^ (-(α * (r : ℝ)))
          * (Cv * (Real.sqrt ((r : ℝ) + 1) + Real.sqrt ((j : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hCv) hw
    have h5 : (3 : ℝ) ^ (-(α * (r : ℝ)))
          * (Cv * (Real.sqrt ((r : ℝ) + 1) + Real.sqrt ((j : ℝ) + 1)))
        = (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) * Cv
          + (3 : ℝ) ^ (-(α * (r : ℝ))) * (Cv * Real.sqrt ((j : ℝ) + 1)) := by ring
    linarith only [h4, h5.le, h5.ge]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsplit : ∑ r ∈ Finset.range ((m - n + 1).toNat),
        ((3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) * Cv
          + (3 : ℝ) ^ (-(α * (r : ℝ))) * (Cv * Real.sqrt ((j : ℝ) + 1)))
      = (∑ r ∈ Finset.range ((m - n + 1).toNat),
            (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)) * Cv
        + (∑ r ∈ Finset.range ((m - n + 1).toNat), (3 : ℝ) ^ (-(α * (r : ℝ))))
            * (Cv * Real.sqrt ((j : ℝ) + 1)) := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  rw [hsplit]
  have hA := mul_le_mul_of_nonneg_right
    (sum_threePow_neg_sqrt_le (α := α) hα (Finset.range ((m - n + 1).toNat))) hCv
  have hB := mul_le_mul_of_nonneg_right
    (sum_threePow_neg_le (α := α) hα (Finset.range ((m - n + 1).toNat)))
    (mul_nonneg hCv (Real.sqrt_nonneg ((j : ℝ) + 1)))
  have hcomm : geomSqrtConst α * Cv
        + geomTailConst α * (Cv * Real.sqrt ((j : ℝ) + 1))
      = Cv * (geomSqrtConst α + Real.sqrt ((j : ℝ) + 1) * geomTailConst α) := by ring
  linarith only [hA, hB, hcomm.le, hcomm.ge]

/-! ## The weighted amplitude tsum of the below-window channel -/

/-- The below-window weighted amplitude splits into a pure geometric channel and
a `√`-weighted geometric channel. -/
theorem weight_step3HeadAmp_eq (Cv α : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(α * (j : ℝ))) * step3HeadAmp Cv α j
      = gammaTriangleConst 2 * (Cv * geomSqrtConst α) * (3 : ℝ) ^ (-(α * (j : ℝ)))
        + gammaTriangleConst 2 * (Cv * geomTailConst α)
            * ((3 : ℝ) ^ (-(α * (j : ℝ))) * Real.sqrt ((j : ℝ) + 1)) := by
  simp only [step3HeadAmp]
  ring

/-- The below-window amplitudes are geometrically summable (they grow like
`√j`). -/
theorem summable_weight_step3HeadAmp {Cv α : ℝ} (hα : 0 < α) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-(α * (j : ℝ))) * step3HeadAmp Cv α j) := by
  have h := ((hasSum_threePow_neg hα).summable.mul_left
      (gammaTriangleConst 2 * (Cv * geomSqrtConst α))).add
    ((summable_threePow_neg_sqrt hα).mul_left
      (gammaTriangleConst 2 * (Cv * geomTailConst α)))
  exact h.congr fun j => (weight_step3HeadAmp_eq Cv α j).symm

/-- **The below-window weighted amplitude tsum, closed.** `∑'_j
3^{−αj}·step3HeadAmp ≤ gammaTriangleConst 2 · 2Cv(1−3^{−α})^{−5/2}` — the tex's
`Cs^{−5/2}`. -/
theorem tsum_weight_step3HeadAmp_le {Cv α : ℝ} (hα : 0 < α) (hCv : 0 ≤ Cv) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(α * (j : ℝ))) * step3HeadAmp Cv α j
      ≤ gammaTriangleConst 2 * (2 * Cv * (geomTailConst α * geomSqrtConst α)) := by
  have hs1 : Summable (fun j : ℕ => (3 : ℝ) ^ (-(α * (j : ℝ)))) :=
    (hasSum_threePow_neg hα).summable
  have hs2 : Summable
      (fun j : ℕ => (3 : ℝ) ^ (-(α * (j : ℝ))) * Real.sqrt ((j : ℝ) + 1)) :=
    summable_threePow_neg_sqrt hα
  have heq : (fun j : ℕ => (3 : ℝ) ^ (-(α * (j : ℝ))) * step3HeadAmp Cv α j)
      = fun j : ℕ =>
        gammaTriangleConst 2 * (Cv * geomSqrtConst α) * (3 : ℝ) ^ (-(α * (j : ℝ)))
          + gammaTriangleConst 2 * (Cv * geomTailConst α)
              * ((3 : ℝ) ^ (-(α * (j : ℝ))) * Real.sqrt ((j : ℝ) + 1)) :=
    funext fun j => weight_step3HeadAmp_eq Cv α j
  rw [heq,
    Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _),
    tsum_mul_left, tsum_mul_left, (hasSum_threePow_neg hα).tsum_eq]
  have hB0 : (0 : ℝ) ≤ gammaTriangleConst 2 * (Cv * geomTailConst α) :=
    mul_nonneg gammaTriangleConst_pos.le
      (mul_nonneg hCv (geomTailConst_pos hα).le)
  have hbnd := mul_le_mul_of_nonneg_left (tsum_threePow_neg_sqrt_le hα) hB0
  have hfin : gammaTriangleConst 2 * (Cv * geomSqrtConst α) * geomTailConst α
        + gammaTriangleConst 2 * (Cv * geomTailConst α) * geomSqrtConst α
      = gammaTriangleConst 2 * (2 * Cv * (geomTailConst α * geomSqrtConst α)) := by
    ring
  linarith only [hbnd, hfin.le, hfin.ge]

end

end Algsuperdiff.Probability
