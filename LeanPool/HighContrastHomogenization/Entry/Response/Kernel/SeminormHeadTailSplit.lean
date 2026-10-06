/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointRecentHeadEstimate
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# High-contrast homogenization: Entry.Response.Kernel.SeminormHeadTailSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The head/tail split of the scale-average seminorm

The scale-average (Besov) seminorm
`besovSeminorm t avg = ∑' n, 3 ^ ((t - n) / 2) √(card⁻¹ ∑_w |avg n w|²)` is split at a window
depth `H` into a finite head and an older-scale tail, resting on the fact that the flat average of
the depth-`n` subcell averages recovers the parent cell average. On the good branch, each
discarded scale `n` beyond `H` carries the factor `1 + 3 ^ (ρn/2)`, and the resulting
`3 ^ (-n/2)`-weighted tail is controlled by `6/(1-ρ)`. This file converts that per-scale analytic
bound into the two branch bounds of Proposition `p.response.transfer`, the diagonal weak-norm
estimate of the response transfer, and proves the good branch's majorant is summable.
-/

section
/-!
## The parent cell average of a doubled field is the flat average of its subcell averages

For an invertible grid `q`, a generation `t` and a depth `n`, the `3^{nd}` aligned depth-`n`
subcells `adaptedCellAtCenter q (t - n) w` are pairwise disjoint open sets of equal volume,
contained
in the parent cell `HighContrast.adaptedCell q t`, and covering it up to the Lebesgue-null grid
seams.  Consequently, for a doubled field `X` whose components are integrable on the parent
cell, the flat average over the index box of the subcell averages of each component equals the
parent cell average of that component.

This is the vector-valued counterpart of the scalar parent energy partition: each component of
`cellAverage` is a scalar `volumeAverage`, and the whole statement is `2 d` instances of the
almost-everywhere partition identity `average_over_aePartition`.  The equal volume of the
subcells is what makes the unweighted flat mean correct; a weighted sum would be needed without
it.  Measurability, disjointness, containment and the null seam are all supplied by `IsUnit q`
through the cell lemmas, while the integrability of each component is an explicit hypothesis.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The parent cell average is the flat average of the subcell averages.**  For an invertible
grid `q`, generation `t` and depth `n`, each component of the parent cell average of a doubled
field `X` over `HighContrast.adaptedCell q t` equals the flat average over the `3^{nd}` aligned
depth-`n` subcells of that component's subcell averages.  Every geometric hypothesis is
discharged from `IsUnit q`; only the integrability of the two components on the parent cell
remains as a hypothesis. -/
theorem cellAverage_parent_eq_avg_subcells (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (X : Vec d → BlockVec d)
    (h1 : ∀ j : Fin d, IntegrableOn (fun x => (X x).1 j) (HighContrast.adaptedCell q t))
    (h2 : ∀ j : Fin d, IntegrableOn (fun x => (X x).2 j) (HighContrast.adaptedCell q t)) :
    (∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).1 i
      = (cellAverage (HighContrast.adaptedCell q t) X).1 i) ∧
    (∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).2 i
      = (cellAverage (HighContrast.adaptedCell q t) X).2 i) := by
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hdisj : ∀ w ∈ triadicIndexBox d n, ∀ w' ∈ triadicIndexBox d n, w ≠ w' →
      Disjoint (adaptedCellAtCenter q (t - (n : ℤ)) w) (adaptedCellAtCenter q (t - (n : ℤ)) w') :=
    fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww'
  have hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hnull : volume (HighContrast.adaptedCell q t \
      ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0 :=
    adaptedCell_diff_biUnion_null q hq t n
  have hvolw : ∀ w ∈ triadicIndexBox d n,
      ((triadicIndexBox d n).card : ℝ)
          * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
        = (volume (HighContrast.adaptedCell q t)).toReal :=
    fun w _ => volume_adaptedCellAtCenter_card_eq q hq t n w
  constructor
  · intro i
    have hi := average_over_aePartition (Z := triadicIndexBox d n)
      (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
      (U := HighContrast.adaptedCell q t) (g := fun x => (X x).1 i)
      hmeas hdisj hsub hnull hvolw (h1 i) hUpos hUfin hZne
    simpa only [cellAverage] using hi
  · intro i
    have hi := average_over_aePartition (Z := triadicIndexBox d n)
      (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
      (U := HighContrast.adaptedCell q t) (g := fun x => (X x).2 i)
      hmeas hdisj hsub hnull hvolw (h2 i) hUpos hUfin hZne
    simpa only [cellAverage] using hi

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The head/tail split of a scale-average sum, generic

The cell-average argument splits the scale-average seminorm at the window depth `H`. The tree
proves that split only privately, tied to the cell-average family, so no consumer above can reuse
it.  This module proves the two series facts the split rests on, for an arbitrary summable real
family: the split itself, and the geometric bound on the shifted tail.  Nothing here mentions a
cell, a coefficient field, or a seminorm, so the module sits below every carrier and can be used
on either side of the estimate.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- Splitting a summable real series at an index `H + 1`: the full sum is the finite head over
`range (H + 1)` plus the tail whose indices are shifted by `H + 1`. -/
theorem tsum_split_range {f : ℕ → ℝ} (hf : Summable f) (H : ℕ) :
    ∑' n : ℕ, f n = (∑ n ∈ Finset.range (H + 1), f n) + ∑' n : ℕ, f (n + (H + 1)) :=
  (hf.sum_add_tsum_nat_add (H + 1)).symm

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The scale-average seminorm: head window plus per-scale tail

The scale-average seminorm
`besovSeminorm t avg = ∑' n, 3 ^ ((t - n) / 2) * √(card⁻¹ ∑_w |avg n w|²)`
splits at the window edge `H`: the first `H + 1` terms are the head, the older-scale terms are the
tail.  The split landed here keeps every tail term intact, in the per-scale shape the energy bound
reads, rather than collapsing the tail through Jensen.  Both statements are series identities
about the seminorm itself; nothing here mentions a cell, a coefficient field, or a maximizer.

`besovTerm` is defined in a module above this one and is deliberately not imported, so the `n`-th
term is spelled out here.  The tail index follows `tsum_split_range`, namely `j + (H + 1)`.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- Normalizing by the factor `3 ^ (-(t/2))` moves the weight of the `n`-th scale-average term
from the paper's `3 ^ ((t - n)/2)` to `3 ^ (-(n/2))`. -/
theorem normalized_besovTerm (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) (n : ℕ) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        ((3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
          Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      = (3 : ℝ) ^ (-((n : ℝ) / 2)) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
  rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hexp : -((t : ℝ) / 2) + (((t : ℝ) - (n : ℝ)) / 2) = -((n : ℝ) / 2) := by ring
  rw [hexp]

/-- The normalized scale-average seminorm is the finite head over `range (H + 1)` plus the
per-scale tail of every older term, each term kept as an individual weighted scale average. -/
theorem besovSeminorm_window_tail_eq (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
    (H : ℕ) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
      = (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
        + ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
            Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d (j + (H + 1)),
                blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)) := by
  classical
  have hbes : besovSeminorm t avg =
      ∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := rfl
  rw [hbes, ← tsum_mul_left]
  rw [tsum_congr fun n => normalized_besovTerm t avg n]
  have hnorm : Summable fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) :=
    (hsum.mul_left _).congr fun n => normalized_besovTerm t avg n
  rw [tsum_split_range hnorm H]
  have htail : (∑' j : ℕ, (3 : ℝ) ^ (-((((j + (H + 1) : ℕ) : ℝ)) / 2)) *
        Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d (j + (H + 1)),
            blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)))
      = ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d (j + (H + 1)),
            blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)) :=
    tsum_congr fun j => by
      have hcast : (((j + (H + 1) : ℕ) : ℝ)) = (j : ℝ) + ((H : ℝ) + 1) := by
        push_cast; ring
      have hexp : -((((j + (H + 1) : ℕ) : ℝ)) / 2) = -(((H : ℝ) + 1 + (j : ℝ)) / 2) := by
        rw [hcast]; ring
      rw [hexp]
  rw [htail]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Real arithmetic for the discarded old scales on the good branch

Below the response window the cell-average lemma discards the scales above the cutoff `H` and
pays `3 ^ (-((1 - ρ) / 2) * H)` for them.  On the good branch each discarded scale `n` carries
the factor `1 + 3 ^ (ρ n / 2)`, so the `3 ^ (-(n / 2))`-weighted tail
`∑ j, 3 ^ (-(n / 2)) * (1 + 3 ^ (ρ n / 2))`, with `n = H + 1 + j`, is controlled by
`6 / (1 - ρ)` times the window weight.  This leaf module records the three real inequalities
realizing that step for `0 ≤ ρ < 1`.  No cell, matrix or measure appears.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- The sharp geometric coefficient at `a = (1 - ρ) / 2`: the pointwise factor `2` leaves an
extra `3 ^ (-a)` behind the geometric ratio, and the combined bound
`2 * 3 ^ (-a) * (1 - 3 ^ (-a))⁻¹ ≤ 3 / a` holds for every `a > 0`. -/
private theorem oldScale_sharp (a : ℝ) (ha0 : 0 < a) :
    2 * (3 : ℝ) ^ (-a) * (1 - (3 : ℝ) ^ (-a))⁻¹ ≤ 3 / a := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  have hlog_gt_one : 1 < Real.log 3 := by
    have h3 : Real.exp 1 < 3 := by
      have h9 := Real.exp_one_lt_d9
      linarith only [h9]
    have h4 := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h4
  have hlog23 : (2 : ℝ) / 3 ≤ Real.log 3 := by linarith only [hlog_gt_one]
  have hkey : (3 : ℝ) ^ (-a) * (3 + 2 * a) ≤ 3 := by
    have ha' : 0 ≤ a := ha0.le
    have hexp : a * Real.log 3 + 1 ≤ Real.exp (a * Real.log 3) :=
      Real.add_one_le_exp _
    have hrpow : (3 : ℝ) ^ a = Real.exp (a * Real.log 3) := by
      rw [Real.rpow_def_of_pos h3pos a]
      congr 1
      ring
    have hle : 1 + (2 : ℝ) / 3 * a ≤ (3 : ℝ) ^ a := by
      calc 1 + (2 : ℝ) / 3 * a = 1 + a * (2 / 3) := by ring
        _ ≤ 1 + a * Real.log 3 := by
              have hm := mul_le_mul_of_nonneg_left hlog23 ha'
              linarith only [hm]
        _ = a * Real.log 3 + 1 := by ring
        _ ≤ Real.exp (a * Real.log 3) := hexp
        _ = (3 : ℝ) ^ a := hrpow.symm
    have h3a_pos : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos h3pos a
    have h2 : 3 + 2 * a ≤ 3 * (3 : ℝ) ^ a := by
      calc 3 + 2 * a = 3 * (1 + (2 : ℝ) / 3 * a) := by ring
        _ ≤ 3 * (3 : ℝ) ^ a := mul_le_mul_of_nonneg_left hle (by norm_num)
    have hneg : (3 : ℝ) ^ (-a) = ((3 : ℝ) ^ a)⁻¹ := Real.rpow_neg h3nonneg a
    rw [hneg, inv_mul_eq_div]
    exact (div_le_iff₀ h3a_pos).mpr h2
  have hsub : 2 * a * (3 : ℝ) ^ (-a) ≤ 3 * (1 - (3 : ℝ) ^ (-a)) := by
    have h := hkey
    have hexpand : (3 : ℝ) ^ (-a) * (3 + 2 * a)
        = 3 * (3 : ℝ) ^ (-a) + 2 * a * (3 : ℝ) ^ (-a) := by ring
    rw [hexpand] at h
    linarith only [h]
  have hlt1 : (3 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [ha0])
  have hpos1mr : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith only [hlt1]
  have hdiv : 2 * (3 : ℝ) ^ (-a) ≤ (3 / a) * (1 - (3 : ℝ) ^ (-a)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
    linarith only [hsub]
  have hstep : (2 * (3 : ℝ) ^ (-a)) * (1 - (3 : ℝ) ^ (-a))⁻¹
      ≤ ((3 / a) * (1 - (3 : ℝ) ^ (-a))) * (1 - (3 : ℝ) ^ (-a))⁻¹ :=
    mul_le_mul_of_nonneg_right hdiv (inv_nonneg.mpr hpos1mr.le)
  have hrhs : ((3 / a) * (1 - (3 : ℝ) ^ (-a))) * (1 - (3 : ℝ) ^ (-a))⁻¹ = 3 / a := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos1mr), mul_one]
  exact hstep.trans_eq hrhs

/-- The pointwise good-branch decay: for `0 ≤ ρ < 1` and `x ≥ 0`, the weight
`3 ^ (-(x / 2))` applied to `1 + 3 ^ (ρ x / 2)` is bounded by
`2 * 3 ^ (-((1 - ρ) / 2 * x))`. -/
theorem oldScale_pointwise (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (x : ℝ) (hx : 0 ≤ x) :
    (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
      ≤ 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
  have _hρ1 : ρ < 1 := hρ1
  have _hρ0 : 0 ≤ ρ := hρ0
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  have hcoef : (1 - ρ) / 2 ≤ 1 / 2 := by linarith only [hρ0]
  have hle_exp : -(x / 2) ≤ -((1 - ρ) / 2 * x) := by
    have h : (1 - ρ) / 2 * x ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right hcoef hx
    linarith only [h]
  have hA : (3 : ℝ) ^ (-(x / 2)) ≤ (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) :=
    Real.rpow_le_rpow_of_exponent_le h3one hle_exp
  have hB : (3 : ℝ) ^ (-(x / 2)) * (3 : ℝ) ^ (ρ * x / 2)
      = (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
    rw [← Real.rpow_add h3pos]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
      = (3 : ℝ) ^ (-(x / 2))
          + (3 : ℝ) ^ (-(x / 2)) * (3 : ℝ) ^ (ρ * x / 2) := by ring
    _ = (3 : ℝ) ^ (-(x / 2)) + (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by rw [hB]
    _ ≤ (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) + (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by
          linarith only [hA]
    _ = 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := by ring

/-- The good-branch discarded tail: for `0 ≤ ρ < 1`, the `3 ^ (-(n / 2))`-weighted sum of
`1 + 3 ^ (ρ n / 2)` over the scales `n = H + 1, H + 2, …` is bounded by `6 / (1 - ρ)` times
the window weight `3 ^ (-((1 - ρ) / 2) * H)`. -/
theorem oldScale_tail_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (H : ℕ) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))
      ≤ 6 / (1 - ρ) * (3 : ℝ) ^ (-((1 - ρ) / 2 * (H : ℝ))) := by
  set a : ℝ := (1 - ρ) / 2 with ha
  set r : ℝ := (3 : ℝ) ^ (-a) with hr
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have ha_pos : 0 < a := by rw [ha]; linarith only [hρ1]
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact (Real.rpow_pos_of_pos h3pos (-a)).le
  have hr_lt_one : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [ha_pos])
  set c : ℝ := 2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) with hc
  have hc_expand : c = (3 : ℝ) ^ (-(a * (H : ℝ))) * (2 * (3 : ℝ) ^ (-a)) := by
    rw [hc]
    have h : -(a * ((H : ℝ) + 1)) = -(a * (H : ℝ)) + (-a) := by ring
    rw [h, Real.rpow_add h3pos]
    ring
  have hg_summ : Summable (fun j : ℕ => c * r ^ j) :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left c
  have hf_nonneg : ∀ j : ℕ,
      0 ≤ (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) := by
    intro j
    apply mul_nonneg
    · exact (Real.rpow_pos_of_pos h3pos _).le
    · have hpos : 0 < (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2) :=
        Real.rpow_pos_of_pos h3pos _
      linarith only [hpos]
  have hle : ∀ j : ℕ,
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) ≤ c * r ^ j := by
    intro j
    set x : ℝ := (H : ℝ) + 1 + (j : ℝ) with hx
    have hx_nonneg : 0 ≤ x := by rw [hx]; positivity
    have hp := oldScale_pointwise ρ hρ0 hρ1 x hx_nonneg
    have hpow : (3 : ℝ) ^ (-(a * (j : ℝ))) = r ^ j := by
      rw [hr]
      have h1 : -(a * (j : ℝ)) = (-a) * (j : ℝ) := by ring
      rw [h1, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-a) (j : ℝ), Real.rpow_natCast]
    have hsplit : (3 : ℝ) ^ (-((1 - ρ) / 2 * x))
        = (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j := by
      have he : -((1 - ρ) / 2 * x) = -(a * ((H : ℝ) + 1)) + (-(a * (j : ℝ))) := by
        rw [← ha, hx]
        ring
      rw [he, Real.rpow_add h3pos, hpow]
    calc (3 : ℝ) ^ (-(x / 2)) * (1 + (3 : ℝ) ^ (ρ * x / 2))
        ≤ 2 * (3 : ℝ) ^ (-((1 - ρ) / 2 * x)) := hp
      _ = 2 * ((3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j) := by rw [hsplit]
      _ = c * r ^ j := by rw [hc]; ring
  have hf_summ : Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))) :=
    Summable.of_nonneg_of_le hf_nonneg hle hg_summ
  have hmono : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)))
      ≤ ∑' j : ℕ, c * r ^ j :=
    hf_summ.tsum_le_tsum hle hg_summ
  have htsum_g : (∑' j : ℕ, c * r ^ j) = c * (1 - r)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
  have hcoef : (3 : ℝ) / a = 6 / (1 - ρ) := by
    have hne : (1 : ℝ) - ρ ≠ 0 := by linarith only [hρ1]
    rw [ha]
    field_simp [hne]
    ring
  calc (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)))
      ≤ ∑' j : ℕ, c * r ^ j := hmono
    _ = c * (1 - r)⁻¹ := htsum_g
    _ = (3 : ℝ) ^ (-(a * (H : ℝ))) * (2 * (3 : ℝ) ^ (-a) * (1 - r)⁻¹) := by
          rw [hc_expand]; ring
    _ ≤ (3 : ℝ) ^ (-(a * (H : ℝ))) * (3 / a) :=
          mul_le_mul_of_nonneg_left (oldScale_sharp a ha_pos)
            (Real.rpow_pos_of_pos h3pos _).le
    _ = 6 / (1 - ρ) * (3 : ℝ) ^ (-(a * (H : ℝ))) := by rw [hcoef]; ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The older-scale tail of the cell-average estimate, both branches of the cutoff

The per-scale analytic bound of the cell-average estimate is
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ` with `ρ = Quenched.contrastRho γ`.  This module
converts
that pointwise family bound into the two branch bounds carried by the printed tail.

On the good branch `M ≤ 1` the factor `√M` may be dropped and the discarded old scales
`n = H + 1, H + 2, …` are summed with the weight `3 ^ (-(n / 2))`; the sharp geometric
comparison already in the tree leaves the window factor `3 ^ (-(Quenched.contrastAlpha γ · H))`
and the
constant `16 / (1 - Quenched.contrastRho γ)`.

On the bad branch `1 < M` the whole weighted sum over all scales is absorbed; splitting
`1 + √M · 3 ^ (ρ n / 2)` into its two geometric parts and using `1 - Quenched.contrastRho γ = 2 ·
Quenched.contrastAlpha γ` again leaves `16 / (1 - Quenched.contrastRho γ) · K · √M · ℰ`.  Only
real analysis on a
sequence appears; no cell, matrix or measure is involved.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

/-- The good-branch majorant `3 ^ (-(n / 2)) (1 + 3 ^ (ρ n / 2))`, `n = H + 1 + j`, is
summable for `0 ≤ ρ < 1`: the crude comparison `≤ 2 · 3 ^ (-(a n))` with
`a = (1 - ρ) / 2 ∈ (0, 1 / 2]` against a geometric series suffices. -/
private theorem good_majorant_summable (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (H : ℕ) :
    Summable (fun j : ℕ => (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
      (1 + (3 : ℝ) ^ (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2))) := by
  have _hρ0 : 0 ≤ ρ := hρ0
  have _hρ1 : ρ < 1 := hρ1
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3one : (1 : ℝ) ≤ 3 := by norm_num
  set a : ℝ := (1 - ρ) / 2 with ha
  have ha_le : a ≤ 1 / 2 := by rw [ha]; linarith only [hρ0]
  set r : ℝ := (3 : ℝ) ^ (-a) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos h3pos _).le
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by rw [ha]; linarith only [hρ1])
  have hg : Summable (fun j : ℕ => (2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1)))) * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
  · exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le
      (by have h := Real.rpow_pos_of_pos h3pos (ρ * ((H : ℝ) + 1 + (j : ℝ)) / 2)
          linarith only [h])
  · set n : ℝ := (H : ℝ) + 1 + (j : ℝ) with hn
    have hn0 : 0 ≤ n := by rw [hn]; positivity
    have h1 : (3 : ℝ) ^ (-(n / 2)) ≤ (3 : ℝ) ^ (-(a * n)) := by
      apply Real.rpow_le_rpow_of_exponent_le h3one
      have h : a * n ≤ (1 / 2) * n := mul_le_mul_of_nonneg_right ha_le hn0
      linarith only [h]
    have h2 : (3 : ℝ) ^ (-(n / 2)) * (3 : ℝ) ^ (ρ * n / 2)
        = (3 : ℝ) ^ (-(a * n)) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      rw [ha]; ring
    have hsplit : (3 : ℝ) ^ (-(a * n)) = (3 : ℝ) ^ (-(a * ((H : ℝ) + 1))) * r ^ j := by
      rw [hr]
      have he : -(a * n) = -(a * ((H : ℝ) + 1)) + (-(a * (j : ℝ))) := by rw [hn]; ring
      rw [he, Real.rpow_add h3pos]
      rw [show -(a * (j : ℝ)) = (-a) * (j : ℝ) by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-a) (j : ℝ), Real.rpow_natCast]
    calc (3 : ℝ) ^ (-(n / 2)) * (1 + (3 : ℝ) ^ (ρ * n / 2))
        = (3 : ℝ) ^ (-(n / 2)) + (3 : ℝ) ^ (-(n / 2)) * (3 : ℝ) ^ (ρ * n / 2) := by ring
      _ = (3 : ℝ) ^ (-(n / 2)) + (3 : ℝ) ^ (-(a * n)) := by rw [h2]
      _ ≤ (3 : ℝ) ^ (-(a * n)) + (3 : ℝ) ^ (-(a * n)) := by linarith only [h1]
      _ = 2 * (3 : ℝ) ^ (-(a * n)) := by ring
      _ = (2 * (3 : ℝ) ^ (-(a * ((H : ℝ) + 1)))) * r ^ j := by rw [hsplit]; ring

/-- The good branch of the older-scale tail: a nonnegative per-scale family obeying
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ`, with `M ≤ 1`, has its `3 ^ (-(n / 2))`
weighted tail from `H + 1` on bounded by `16 / (1 - Quenched.contrastRho γ) · K ·
3 ^ (-(Quenched.contrastAlpha γ · H)) · ℰ`. -/
theorem tail_good_le {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (H : ℕ) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hM : 0 ≤ M) (hgood : M ≤ 1)
    (T : ℕ → ℝ) (hT0 : ∀ n, 0 ≤ T n)
    (hT : ∀ n, T n ≤ Real.sqrt 2 * K *
      (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * En) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)
      ≤ 16 / (1 - Quenched.contrastRho γ) * K * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * En := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have _hγ := hγ
  have hρ0 : 0 ≤ Quenched.contrastRho γ := by rw [Quenched.contrastRho]; linarith only [hγ.1]
  have hρ1 : Quenched.contrastRho γ < 1 := by rw [Quenched.contrastRho]; linarith only [hγ.2]
  have hαeq : (1 - Quenched.contrastRho γ) / 2 = Quenched.contrastAlpha γ := by rw [Quenched.contrastAlpha, Quenched.contrastRho]; ring
  have h1mρ : 0 < 1 - Quenched.contrastRho γ := by linarith only [hρ1]
  have hsqM : (Real.sqrt M) ^ 2 ≤ 1 := by rw [Real.sq_sqrt hM]; exact hgood
  have hsqrt_le : Real.sqrt M ≤ 1 :=
    le_of_sq_le_sq (by simpa using hsqM) (by norm_num)
  set G : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
      (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * ((H : ℝ) + 1 + (j : ℝ)) / 2)) with hG
  have hG_summ : Summable G := by
    rw [hG]
    exact good_majorant_summable (Quenched.contrastRho γ) hρ0 hρ1 H
  have hf_nonneg : ∀ j : ℕ,
      0 ≤ (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j) := by
    intro j
    exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le (hT0 _)
  have hpoint : ∀ j : ℕ,
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)
        ≤ Real.sqrt 2 * K * En * G j := by
    intro j
    set x : ℝ := (H : ℝ) + 1 + (j : ℝ) with hx
    have hTj := hT (H + 1 + j)
    rw [show ((H + 1 + j : ℕ) : ℝ) = x by rw [hx]; push_cast; ring] at hTj
    have hpowpos : 0 < (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2) := Real.rpow_pos_of_pos h3pos _
    have hsq : Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)
        ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2) := by
      calc Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)
          ≤ 1 * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2) :=
            mul_le_mul_of_nonneg_right hsqrt_le hpowpos.le
        _ = (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2) := by ring
    have hinner : Real.sqrt 2 * K * (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En
        ≤ Real.sqrt 2 * K * (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En := by
      have hs2K : 0 ≤ Real.sqrt 2 * K := mul_nonneg (Real.sqrt_nonneg 2) hK
      have hstep : (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2))
          ≤ (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) := by linarith only [hsq]
      calc Real.sqrt 2 * K * (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En
          = (Real.sqrt 2 * K)
              * ((1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En) := by ring
        _ ≤ (Real.sqrt 2 * K) * ((1 + (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hEn) hs2K
        _ = Real.sqrt 2 * K * (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En := by ring
    have hw : 0 ≤ (3 : ℝ) ^ (-(x / 2)) := (Real.rpow_pos_of_pos h3pos _).le
    calc (3 : ℝ) ^ (-(x / 2)) * T (H + 1 + j)
        ≤ (3 : ℝ) ^ (-(x / 2)) * (Real.sqrt 2 * K *
            (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En) :=
          mul_le_mul_of_nonneg_left hTj hw
      _ ≤ (3 : ℝ) ^ (-(x / 2)) * (Real.sqrt 2 * K *
            (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * x / 2)) * En) :=
          mul_le_mul_of_nonneg_left hinner hw
      _ = Real.sqrt 2 * K * En * G j := by
          simp only [hG]
          rw [← hx]
          ring
  have hf_summ : Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j)) :=
    Summable.of_nonneg_of_le hf_nonneg hpoint (hG_summ.mul_left _)
  have hmono : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j))
      ≤ ∑' j : ℕ, Real.sqrt 2 * K * En * G j :=
    hf_summ.tsum_le_tsum hpoint (hG_summ.mul_left _)
  have hval : (∑' j : ℕ, Real.sqrt 2 * K * En * G j)
      = Real.sqrt 2 * K * En * ∑' j : ℕ, G j := tsum_mul_left
  set θ : ℝ := (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) with hθ
  have hTail : (∑' j : ℕ, G j) ≤ 6 / (1 - Quenched.contrastRho γ) * θ := by
    rw [hG]
    have h := oldScale_tail_le (Quenched.contrastRho γ) hρ0 hρ1 H
    rw [hαeq, ← hθ] at h
    exact h
  have hθ0 : 0 ≤ θ := (Real.rpow_pos_of_pos h3pos _).le
  have hsqrt2_le : Real.sqrt 2 ≤ 2 :=
    le_of_sq_le_sq
      (by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num)
      (by norm_num)
  have h6sqrt : Real.sqrt 2 * 6 ≤ 16 := by linarith only [hsqrt2_le]
  have hfinal : Real.sqrt 2 * K * En * (6 / (1 - Quenched.contrastRho γ) * θ)
      ≤ 16 / (1 - Quenched.contrastRho γ) * K * θ * En := by
    have hX : 0 ≤ K * En * θ / (1 - Quenched.contrastRho γ) :=
      div_nonneg (mul_nonneg (mul_nonneg hK hEn) hθ0) h1mρ.le
    rw [show Real.sqrt 2 * K * En * (6 / (1 - Quenched.contrastRho γ) * θ)
          = (Real.sqrt 2 * 6) * (K * En * θ / (1 - Quenched.contrastRho γ)) by ring,
        show 16 / (1 - Quenched.contrastRho γ) * K * θ * En
          = 16 * (K * En * θ / (1 - Quenched.contrastRho γ)) by ring]
    exact mul_le_mul_of_nonneg_right h6sqrt hX
  calc (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) * T (H + 1 + j))
      ≤ ∑' j : ℕ, Real.sqrt 2 * K * En * G j := hmono
    _ = Real.sqrt 2 * K * En * ∑' j : ℕ, G j := hval
    _ ≤ Real.sqrt 2 * K * En * (6 / (1 - Quenched.contrastRho γ) * θ) :=
          mul_le_mul_of_nonneg_left hTail
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
    _ ≤ 16 / (1 - Quenched.contrastRho γ) * K * θ * En := hfinal

/-- The bad branch of the older-scale tail: a nonnegative per-scale family obeying
`T n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · ℰ`, with `1 < M`, has its `3 ^ (-(n / 2))`
weighted sum over all scales bounded by `16 / (1 - Quenched.contrastRho γ) · K · √M · ℰ`. -/
theorem tail_bad_le {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hbad : 1 < M)
    (T : ℕ → ℝ) (hT0 : ∀ n, 0 ≤ T n)
    (hT : ∀ n, T n ≤ Real.sqrt 2 * K *
      (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * En) :
    ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n
      ≤ 16 / (1 - Quenched.contrastRho γ) * K * Real.sqrt M * En := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have _hγ := hγ
  have hαpos : 0 < Quenched.contrastAlpha γ := by rw [Quenched.contrastAlpha]; linarith only [hγ.2]
  have hαle1 : Quenched.contrastAlpha γ ≤ 1 := by rw [Quenched.contrastAlpha]; linarith only [hγ.1]
  have hαle_half : Quenched.contrastAlpha γ ≤ 1 / 2 := by rw [Quenched.contrastAlpha]; linarith only [hγ.1]
  have hαle_quarter : Quenched.contrastAlpha γ ≤ 1 / 4 := by rw [Quenched.contrastAlpha]; linarith only [hγ.1]
  have hs1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr (le_of_lt hbad)
  have hs0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hrα0 : 0 ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ)) := (Real.rpow_pos_of_pos h3pos _).le
  have hrα1 : (3 : ℝ) ^ (-(Quenched.contrastAlpha γ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hαpos])
  set A : ℝ := (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ with hAdef
  set B : ℝ := (1 - (3 : ℝ) ^ (-(Quenched.contrastAlpha γ)))⁻¹ with hBdef
  have hterm1 : ∀ n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))
      = ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    intro n
    rw [show -((n : ℝ) / 2) = (-(1 / 2 : ℝ)) * (n : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have htermα : ∀ n : ℕ, (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))
      = ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := by
    intro n
    rw [show -(Quenched.contrastAlpha γ * (n : ℝ)) = (-(Quenched.contrastAlpha γ)) * (n : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have hg1_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2))) := by
    rw [show (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)))
          = (fun n : ℕ => ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) by funext n; exact hterm1 n]
    exact summable_geometric_of_lt_one
      ((Real.rpow_pos_of_pos h3pos _).le)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hgα_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))) := by
    rw [show (fun n : ℕ => (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ))))
          = (fun n : ℕ => ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n) by funext n; exact htermα n]
    exact summable_geometric_of_lt_one hrα0 hrα1
  have hg2_summ : Summable (fun n : ℕ =>
      Real.sqrt M * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))) := hgα_summ.mul_left _
  have hg1_eq : (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))) = A := by
    rw [hAdef]
    have h := geom_sum_rpow (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [show ∀ n : ℕ, -((n : ℝ) / 2) = -((1 / 2 : ℝ) * (n : ℝ)) by
      intro n; ring] using h
  have hgα_eq : (∑' n : ℕ, (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))) = B := by
    rw [hBdef]
    exact geom_sum_rpow (Quenched.contrastAlpha γ) hαpos
  set G : ℕ → ℝ := fun n => Real.sqrt 2 * K * En *
      ((3 : ℝ) ^ (-((n : ℝ) / 2))
        + Real.sqrt M * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))) with hG
  have hG_summ : Summable G := by
    rw [hG]
    have hgeom : Summable (fun n : ℕ =>
        (Real.sqrt 2 * K * En * (1 + Real.sqrt M)) * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n) :=
      (summable_geometric_of_lt_one hrα0 hrα1).mul_left _
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
    · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
        (add_nonneg (Real.rpow_pos_of_pos h3pos _).le
          (mul_nonneg hs0 (Real.rpow_pos_of_pos h3pos _).le))
    · have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have h1 : (3 : ℝ) ^ (-((n : ℝ) / 2)) ≤ ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := by
        rw [← htermα]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        have h : Quenched.contrastAlpha γ * (n : ℝ) ≤ (1 / 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hαle_half hn0
        linarith only [h]
      have hsum : (3 : ℝ) ^ (-((n : ℝ) / 2))
            + Real.sqrt M * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))
          ≤ (1 + Real.sqrt M) * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := by
        rw [htermα]
        calc (3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n
            ≤ ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n
              + Real.sqrt M * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := add_le_add h1 le_rfl
          _ = (1 + Real.sqrt M) * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := by ring
      calc Real.sqrt 2 * K * En *
            ((3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ))))
          ≤ (Real.sqrt 2 * K * En)
              * ((1 + Real.sqrt M) * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n) :=
            mul_le_mul_of_nonneg_left hsum
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hK) hEn)
        _ = (Real.sqrt 2 * K * En * (1 + Real.sqrt M)) * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ))) ^ n := by
            ring
  have hf_nonneg : ∀ n : ℕ, 0 ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n := by
    intro n
    exact mul_nonneg (Real.rpow_pos_of_pos h3pos _).le (hT0 n)
  have hpoint : ∀ n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n ≤ G n := by
    intro n
    have hpow : (3 : ℝ) ^ (-((n : ℝ) / 2)) * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)
        = (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ))) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      rw [Quenched.contrastAlpha, Quenched.contrastRho]
      ring
    have hw : 0 ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := (Real.rpow_pos_of_pos h3pos _).le
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (Real.sqrt 2 * K *
              (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * En) :=
          mul_le_mul_of_nonneg_left (hT n) hw
      _ = Real.sqrt 2 * K * En *
            ((3 : ℝ) ^ (-((n : ℝ) / 2))
              + Real.sqrt M * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (n : ℝ)))) := by
          rw [← hpow]; ring
      _ = G n := by rw [hG]
  have hGval : (∑' n : ℕ, G n)
      = Real.sqrt 2 * K * En * (A + Real.sqrt M * B) := by
    rw [hG]
    rw [tsum_mul_left]
    rw [hg1_summ.tsum_add hg2_summ]
    rw [tsum_mul_left]
    rw [hg1_eq, hgα_eq]
  have hA : A ≤ 3 := by rw [hAdef]; exact inv_one_sub_rpow_half_le
  have hB : B ≤ 3 / Quenched.contrastAlpha γ := by
    rw [hBdef]
    exact inv_one_sub_rpow_le (Quenched.contrastAlpha γ) hαpos hαle1
  have hsumAB : Real.sqrt 2 * (A + Real.sqrt M * B)
      ≤ Real.sqrt 2 * 3 + Real.sqrt 2 * (Real.sqrt M * (3 / Quenched.contrastAlpha γ)) := by
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : Real.sqrt 2 * A ≤ Real.sqrt 2 * 3 := mul_le_mul_of_nonneg_left hA hs2
    have h2 : Real.sqrt M * B ≤ Real.sqrt M * (3 / Quenched.contrastAlpha γ) :=
      mul_le_mul_of_nonneg_left hB hs0
    have h3 : Real.sqrt 2 * (Real.sqrt M * B)
        ≤ Real.sqrt 2 * (Real.sqrt M * (3 / Quenched.contrastAlpha γ)) :=
      mul_le_mul_of_nonneg_left h2 hs2
    rw [mul_add]
    exact add_le_add h1 h3
  have hsqrt2_le : Real.sqrt 2 ≤ 2 :=
    le_of_sq_le_sq
      (by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]; norm_num)
      (by norm_num)
  have hkey : Real.sqrt 2 * 3 * Quenched.contrastAlpha γ ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M := by
    have h1 : Real.sqrt 2 * 3 * Quenched.contrastAlpha γ ≤ Real.sqrt 2 * 3 * (1 / 4) :=
      mul_le_mul_of_nonneg_left hαle_quarter (by positivity)
    have h2 : Real.sqrt 2 * 3 * (1 / 4) ≤ 2 := by linarith only [hsqrt2_le]
    have h4 : (2 : ℝ) ≤ 8 - Real.sqrt 2 * 3 := by linarith only [hsqrt2_le]
    have h3 : (2 : ℝ) ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M := by
      calc (2 : ℝ) = 2 * 1 := by ring
        _ ≤ (8 - Real.sqrt 2 * 3) * Real.sqrt M :=
            mul_le_mul h4 hs1 (by norm_num) (by linarith only [h4])
    linarith only [h1, h2, h3]
  have htarget : Real.sqrt 2 * 3 + Real.sqrt 2 * (Real.sqrt M * (3 / Quenched.contrastAlpha γ))
      ≤ 8 / Quenched.contrastAlpha γ * Real.sqrt M := by
    have hmul : (Real.sqrt 2 * 3
          + Real.sqrt 2 * (Real.sqrt M * (3 / Quenched.contrastAlpha γ))) * Quenched.contrastAlpha γ
        ≤ (8 / Quenched.contrastAlpha γ * Real.sqrt M) * Quenched.contrastAlpha γ := by
      rw [show (Real.sqrt 2 * 3
              + Real.sqrt 2 * (Real.sqrt M * (3 / Quenched.contrastAlpha γ))) * Quenched.contrastAlpha γ
            = Real.sqrt 2 * 3 * Quenched.contrastAlpha γ + Real.sqrt 2 * 3 * Real.sqrt M by
            field_simp [hαpos.ne'],
          show (8 / Quenched.contrastAlpha γ * Real.sqrt M) * Quenched.contrastAlpha γ = 8 * Real.sqrt M by
            field_simp [hαpos.ne']]
      linarith only [hkey]
    exact le_of_mul_le_mul_right hmul hαpos
  have hscalar : Real.sqrt 2 * (A + Real.sqrt M * B)
      ≤ 16 / (1 - Quenched.contrastRho γ) * Real.sqrt M := by
    have h8 : 16 / (1 - Quenched.contrastRho γ) = 8 / Quenched.contrastAlpha γ := by
      rw [show 1 - Quenched.contrastRho γ = 2 * Quenched.contrastAlpha γ by rw [Quenched.contrastAlpha, Quenched.contrastRho]; ring]
      ring_nf
    rw [h8]
    exact hsumAB.trans htarget
  have hfin : Real.sqrt 2 * K * En * (A + Real.sqrt M * B)
      ≤ 16 / (1 - Quenched.contrastRho γ) * K * Real.sqrt M * En := by
    have hKEn : 0 ≤ K * En := mul_nonneg hK hEn
    have h := mul_le_mul_of_nonneg_left hscalar hKEn
    calc Real.sqrt 2 * K * En * (A + Real.sqrt M * B)
        = (K * En) * (Real.sqrt 2 * (A + Real.sqrt M * B)) := by ring
      _ ≤ (K * En) * (16 / (1 - Quenched.contrastRho γ) * Real.sqrt M) := h
      _ = 16 / (1 - Quenched.contrastRho γ) * K * Real.sqrt M * En := by ring
  have hf_summ : Summable (fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n) :=
    Summable.of_nonneg_of_le hf_nonneg hpoint hG_summ
  calc (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) * T n)
      ≤ ∑' n : ℕ, G n := hf_summ.tsum_le_tsum hpoint hG_summ
    _ = Real.sqrt 2 * K * En * (A + Real.sqrt M * B) := hGval
    _ ≤ 16 / (1 - Quenched.contrastRho γ) * K * Real.sqrt M * En := hfin

end

end HCPolySupport.HighContrast.Multiscale
end
