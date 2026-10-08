/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TriadicRefinementIncrement
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellOscillationSplit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars

/-!
# High-contrast homogenization: Entry.Response.Direct.DescendantIndexStationarity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The descendant index decomposition and its stationarity reduction

The triadic index box enumerating the `3^{(m+1)d}` aligned cells of one generation inside a coarser
adapted cell splits every depth-`(H+n)` index into an outer index naming the depth-`H` cell
containing it and an inner index naming its position there, a balanced-ternary grouping with its
own bound and injectivity properties. Because the descendant sum of `p.response.transfer` cuts the
terminal cell into generation-`(s-n)` aligned cells indexed exactly this way, stationarity of the
coefficient law acts on the outer index alone: translating by the generation-`s` cell centre
identifies a descendant cell's annealed coarse block with a fixed translate depending only on the
inner index. A companion pair of lemmas telescopes the same descendant sum's weighted flat cell
averages generation by generation down to depth `H`, the arithmetic the oscillation half of the
cutoff-mean row sums against the source load.
-/

section
/-!
## The descendant telescoping of the cutoff cell weights

Refining the depth-`m` subdivision of the terminal cell into the depth-`(m+1)` subdivision turns
the difference of the two weighted flat cell averages of the cutoff cell weights against the cell
averages of a fixed integrable field into the flat average of the weight increment against the
finer cell averages.  Summing those increments over the generations telescopes the depth-`N`
weighted flat average into the terminal depth-zero term plus the descendant sum that
`p.response.transfer` bounds.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The increment of the weighted flat cell average across one generation.**  Refining the
depth-`m` subdivision into the depth-`(m+1)` subdivision turns the difference of the two weighted
flat averages into the flat average of the weight increment against the finer cell averages. -/
theorem avsum_weighted_volumeAverage_succ_sub {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f
        - ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          (volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
              - volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Transport.gridParent W))
                  (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  have h :
      ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
        = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
            volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Transport.gridParent W))
                (fun x => φ x - 1)
              * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f :=
    avsum_weighted_volumeAverage_succ_eq (q := q) hq t m
      (fun v => volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) (fun x => φ x - 1))
      (f := f) hf
  rw [h, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro W _
  ring

/-- **The weighted flat cell average telescopes over the generations.**  The depth-`N` weighted
flat average of the cutoff cell weights against the cell averages of `f` is the terminal term
plus the sum of the generation increments.  For a cutoff of the class `IsResponseCutoff` the
terminal term vanishes, so the whole quantity is the descendant sum of
`p.response.transfer`. -/
theorem avsum_weighted_volumeAverage_eq_sum_range {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d N).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d N,
          volumeAverage (adaptedCellAtCenter q (t - (N : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (N : ℤ)) W) f
      = volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x - 1)
            * volumeAverage (HighContrast.adaptedCell q t) f
        + ∑ m ∈ Finset.range N,
            ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
              (volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
                  - volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) (Transport.gridParent W))
                      (fun x => φ x - 1))
                * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  induction N with
  | zero =>
      have hbox0 : triadicIndexBox d 0 = {(0 : Fin d → ℤ)} := by
        unfold triadicIndexBox
        have hfun : (fun _ : Fin d => Finset.Icc (-(((3 ^ 0 - 1) / 2 : ℕ) : ℤ))
            (((3 ^ 0 - 1) / 2 : ℕ) : ℤ)) = (fun _ : Fin d => ({(0 : ℤ)} : Finset ℤ)) := by
          funext i
          simp
        rw [hfun]
        exact Fintype.piFinset_singleton (fun _ : Fin d => (0 : ℤ))
      have hcell0 : adaptedCellAtCenter q t (0 : Fin d → ℤ) = HighContrast.adaptedCell q t := by
        have hc : adaptedCellCenter q t (0 : Fin d → ℤ) = 0 := by
          rw [adaptedCellCenter]
          have h0 : (fun i => (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
            funext i
            simp
          rw [h0, matVecMul_zero, smul_zero]
        rw [adaptedCellAtCenter, hc]
        simp only [HighContrast.adaptedCellTranslate, zero_add, Set.image_id']
      rw [Finset.sum_range_zero, add_zero, hbox0]
      simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_mul,
        Finset.sum_singleton, Nat.cast_zero, sub_zero, hcell0]
  | succ N ih =>
      have h := avsum_weighted_volumeAverage_succ_sub (q := q) hq t N φ hf
      simp only [Finset.sum_range_succ]
      rw [← add_assoc, ← ih, ← h]
      ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The oscillation decomposition of the cutoff-mean row

The oscillation half of the cutoff-mean row of `p.response.transfer` compares the
`(φ - 1)`-weighted average of an integrable density `f` over the terminal cell with its depth-`H`
cell part.  Refining the subdivision generation by generation, that difference is the sum of the
generation increments of the descendant sum, carried by the deeper cells, plus the defect of the
farthest cell part.  The telescoping identity at every depth produces both readings once it is
subtracted from itself at the shifted depth.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The shifted descendant telescoping.**  The difference between the depth-`(H+N)` and the
depth-`H` weighted flat cell averages is the sum of the `N` generation increments below the
scale-`s` cells, the depth-`n` increment being carried by the generation `t - (H + n + 1)`. -/
theorem avsum_weighted_volumeAverage_add_sub_eq_sum_range {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (H N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + N),
          volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) f
        - ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) (fun x => φ x - 1)
            * volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) f
      = ∑ n ∈ Finset.range N,
          ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + n + 1),
            (volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
                - volumeAverage (adaptedCellAtCenter q (t - ((H + n : ℕ) : ℤ))
                    (Transport.gridParent W)) (fun x => φ x - 1))
              * volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) f := by
  have hHN := avsum_weighted_volumeAverage_eq_sum_range (q := q) hq t (H + N) φ hf
  have hH := avsum_weighted_volumeAverage_eq_sum_range (q := q) hq t H φ hf
  rw [hHN, hH, Finset.sum_range_add]
  ring

/-- **The oscillation decomposition of the cutoff-mean row at every refinement depth.**  The
`(φ-1)`-weighted average of `f` over the terminal cell is its depth-`H` cell part, plus the first
`N` generation increments of the descendant sum of `p.response.transfer`, plus a remainder which
is the defect of the depth-`(H+N)` cell part. -/
theorem volumeAverage_sub_one_eq_cellPart_add_sum_range_add_rem {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (H N : ℕ) (φ : Vec d → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * f x)
      = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) (fun x => φ x - 1)
              * volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) f
        + (∑ n ∈ Finset.range N,
            ((triadicIndexBox d (H + n + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + n + 1),
              (volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x
                - 1)
                  - volumeAverage (adaptedCellAtCenter q (t - ((H + n : ℕ) : ℤ))
                      (Transport.gridParent W)) (fun x => φ x - 1))
                * volumeAverage (adaptedCellAtCenter q (t - ((H + n + 1 : ℕ) : ℤ)) W) f)
        + (volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * f x)
            - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (H + N),
                volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) (fun x => φ x - 1)
                  * volumeAverage (adaptedCellAtCenter q (t - ((H + N : ℕ) : ℤ)) W) f) := by
  rw [← avsum_weighted_volumeAverage_add_sub_eq_sum_range hq t H N φ hf]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Grouping the triadic index box at `3 ^ n`

`triadicIndexBox d m` indexes the `3 ^ (m * d)` aligned cells of generation `t - m` inside the
adapted cell of generation `t`.  Writing a generation gap as `H + n`, every depth-`(H + n)` index
`W` splits uniquely as `W = 3 ^ n * w + z`, with `w` the outer index of the depth-`H` cell
containing the cell and `z` the inner index of the cell inside it.  This is balanced ternary with
the digits grouped at `3 ^ n`.  It is what lets the descendant sum of `p.response.transfer` read
the annealed head of the source load: the `3 ^ ((H + n) * d)` descendants of the terminal cell at
generation `s - n` are exactly `3 ^ (H * d)` translated copies of the `3 ^ (n * d)` descendants of
one scale-`s` cell.

The proof needs no explicit inverse: the grouped-digit map is injective and the two finsets have
the same cardinality, so its image is everything.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- `triadicIndexBound m = (3 ^ m - 1) / 2` is the radius of the depth-`m` index box
`triadicIndexBox d m`, i.e. the box is the integer interval `[-b m, b m]` in every coordinate. -/
@[expose]
public def triadicIndexBound (m : ℕ) : ℕ := (3 ^ m - 1) / 2

/-- Twice the radius of the depth-`m` index box is `3 ^ m - 1`, since `3 ^ m` is odd. -/
private theorem two_mul_triadicIndexBound (m : ℕ) :
    2 * (triadicIndexBound m : ℤ) = (3 : ℤ) ^ m - 1 := by
  obtain ⟨k, hk⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hb : triadicIndexBound m = k := by
    unfold triadicIndexBound
    omega
  have hkz : (3 : ℤ) ^ m = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  rw [hb, hkz]
  ring

/-- The radius of the depth-`(H + n)` box is the grouped-digit bound `3 ^ n * b H + b n`. -/
private theorem triadicIndexBound_add (H n : ℕ) :
    (triadicIndexBound (H + n) : ℤ)
      = 3 ^ n * (triadicIndexBound H : ℤ) + (triadicIndexBound n : ℤ) := by
  obtain ⟨kH, hkH⟩ : Odd ((3 : ℕ) ^ H) := Odd.pow (by decide)
  obtain ⟨kn, hkn⟩ : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
  have hbH : triadicIndexBound H = kH := by
    unfold triadicIndexBound
    omega
  have hbn : triadicIndexBound n = kn := by
    unfold triadicIndexBound
    omega
  have hmain : triadicIndexBound (H + n) = 3 ^ n * kH + kn := by
    unfold triadicIndexBound
    have hpow : 3 ^ (H + n) = 2 * (3 ^ n * kH + kn) + 1 := by
      rw [pow_add, hkH, hkn]
      ring
    omega
  rw [hbH, hbn, hmain]
  push_cast
  ring

/-- **The grouped-digit index is in the box.**  If the outer index `w` lies in the box of depth
`H` and the inner index `z` in the box of depth `n`, then `3^n w + z` lies in the box of depth
`H + n`. -/
theorem mem_triadicIndexBox_add_of_mem {d H n : ℕ} {w z : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d H) (hz : z ∈ triadicIndexBox d n) :
    (fun i => 3 ^ n * w i + z i) ∈ triadicIndexBox d (H + n) := by
  rw [mem_triadicIndexBox_iff]
  intro i
  have hwi : |w i| ≤ (triadicIndexBound H : ℤ) := by
    simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hw) i
  have hzi : |z i| ≤ (triadicIndexBound n : ℤ) := by
    simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz) i
  have hwnn : (0 : ℤ) ≤ (3 : ℤ) ^ n := pow_nonneg (by norm_num) n
  calc
    |(3 : ℤ) ^ n * w i + z i| ≤ |(3 : ℤ) ^ n * w i| + |z i| := abs_add_le ..
    _ = (3 : ℤ) ^ n * |w i| + |z i| := by rw [abs_mul, abs_of_nonneg hwnn]
    _ ≤ (3 : ℤ) ^ n * (triadicIndexBound H : ℤ) + (triadicIndexBound n : ℤ) :=
          add_le_add (mul_le_mul_of_nonneg_left hwi hwnn) hzi
    _ = (((3 ^ (H + n) - 1) / 2 : ℕ) : ℤ) := by
          rw [← triadicIndexBound_add H n]
          simp only [triadicIndexBound]

/-- **The grouped-digit map is injective.**  Two pairs of an outer and an inner index that give
the same grouped index are equal: the inner digits span less than one outer step. -/
theorem triadicIndexBox_add_injOn {d H n : ℕ} {w z w' z' : Fin d → ℤ}
    (hz : z ∈ triadicIndexBox d n) (hz' : z' ∈ triadicIndexBox d n)
    (h : (fun i => 3 ^ n * w i + z i) = (fun i => 3 ^ n * w' i + z' i)) :
    w = w' ∧ z = z' := by
  have hnpos : (0 : ℤ) < (3 : ℤ) ^ n := pow_pos (by norm_num) n
  have main : w = w' ∧ z = z' := by
    have hw : w = w' := by
      funext i
      have hzi : |z i| ≤ (triadicIndexBound n : ℤ) := by
        simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz) i
      have hz'i : |z' i| ≤ (triadicIndexBound n : ℤ) := by
        simpa only [triadicIndexBound] using (mem_triadicIndexBox_iff.mp hz') i
      have hdiff_le : |z' i - z i| ≤ 2 * (triadicIndexBound n : ℤ) := by
        obtain ⟨h1, h2⟩ := abs_le.mp hzi
        obtain ⟨h1', h2'⟩ := abs_le.mp hz'i
        rw [abs_le]
        constructor <;> omega
      have hdiff_lt : |z' i - z i| < (3 : ℤ) ^ n := by
        have h2b := two_mul_triadicIndexBound n
        rw [h2b] at hdiff_le
        omega
      have hmul : (3 : ℤ) ^ n * (w i - w' i) = z' i - z i := by
        have hi : (3 : ℤ) ^ n * w i + z i = (3 : ℤ) ^ n * w' i + z' i := by
          simpa only [] using congrFun h i
        have hsub : (3 : ℤ) ^ n * w i - (3 : ℤ) ^ n * w' i = z' i - z i := by
          linarith only [hi]
        simpa only [mul_sub] using hsub
      have habs : (3 : ℤ) ^ n * |w i - w' i| = |z' i - z i| := by
        rw [← hmul, abs_mul, abs_of_nonneg (le_of_lt hnpos)]
      by_contra hne
      have hge1 : 1 ≤ |w i - w' i| := Int.one_le_abs (sub_ne_zero.mpr hne)
      have hle : (3 : ℤ) ^ n ≤ (3 : ℤ) ^ n * |w i - w' i| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hge1 (le_of_lt hnpos)
      rw [habs] at hle
      exact (not_le.mpr hdiff_lt) hle
    refine ⟨hw, ?_⟩
    funext i
    have hi : (3 : ℤ) ^ n * w i + z i = (3 : ℤ) ^ n * w' i + z' i := by
      simpa only [] using congrFun h i
    rw [congrFun hw i] at hi
    exact add_left_cancel hi
  have aux : ∀ _k : ℕ, w = w' ∧ z = z' := fun _ => main
  exact aux H

/-- The grouped-digit map `(w, z) ↦ (fun i => 3 ^ n * w i + z i)` on pairs of indices. -/
private abbrev groupedIndex {d : ℕ} (n : ℕ) (p : (Fin d → ℤ) × (Fin d → ℤ)) : Fin d → ℤ :=
  fun i => 3 ^ n * p.1 i + p.2 i

/-- **The index box of depth `H + n` is the grouped product of the boxes of depths `H` and
`n`.**  Summing a function over the depth-`(H+n)` box is summing it over the outer box of the
depth-`H` cells and, inside each, over the inner box of the depth-`n` descendants. -/
theorem sum_triadicIndexBox_add {d : ℕ} (H n : ℕ) (F : (Fin d → ℤ) → ℝ) :
    ∑ W ∈ triadicIndexBox d (H + n), F W
      = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          F (fun i => 3 ^ n * w i + z i) := by
  classical
  have hmem : ∀ p ∈ (triadicIndexBox d H) ×ˢ (triadicIndexBox d n),
      groupedIndex n p ∈ triadicIndexBox d (H + n) := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact mem_triadicIndexBox_add_of_mem hp.1 hp.2
  have hinj : Set.InjOn (groupedIndex n)
      (((triadicIndexBox d H) ×ˢ (triadicIndexBox d n) :
        Finset ((Fin d → ℤ) × (Fin d → ℤ))) : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    intro p hp q hq heq
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have heq' : (fun i => 3 ^ n * p.1 i + p.2 i) = (fun i => 3 ^ n * q.1 i + q.2 i) := heq
    obtain ⟨hw', hz'⟩ := triadicIndexBox_add_injOn (H := H) hp.2 hq.2 heq'
    exact Prod.ext hw' hz'
  have hcard : ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).card
      = (triadicIndexBox d (H + n)).card := by
    rw [Finset.card_product, card_triadicIndexBox_nat H, card_triadicIndexBox_nat n,
      card_triadicIndexBox_nat (H + n), ← mul_pow, ← pow_add]
  have himage : ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).image (groupedIndex n)
      = triadicIndexBox d (H + n) := by
    refine Finset.eq_of_subset_of_card_le (fun W hW => ?_) ?_
    · rw [Finset.mem_image] at hW
      obtain ⟨p, hp, rfl⟩ := hW
      exact hmem p hp
    · rw [Finset.card_image_of_injOn hinj]
      exact hcard.ge
  calc
    ∑ W ∈ triadicIndexBox d (H + n), F W
        = ∑ W ∈ ((triadicIndexBox d H) ×ˢ (triadicIndexBox d n)).image (groupedIndex n),
            F W := by rw [himage]
    _ = ∑ p ∈ (triadicIndexBox d H) ×ˢ (triadicIndexBox d n), F (groupedIndex n p) := by
          rw [Finset.sum_image hinj]
    _ = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            F (groupedIndex n (w, z)) := by
          rw [Finset.sum_product]
    _ = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            F (fun i => 3 ^ n * w i + z i) := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed block of a descendant cell depends only on its inner index

In the descendant sum of `p.response.transfer` the terminal cell is cut into the
`3^{(H+n)d}` aligned cells of generation `s - n`, indexed by `3^n w + z` with `w` the index of
the scale-`s` cell containing the descendant and `z` the index of the descendant inside that
cell.  Stationarity acts on the outer index alone: the generation-`s` translation `3^s q w` is
an integer vector once `s ≥ j_*`, the law is invariant under integer translations, and the
recentring `a_- = a - g`, `a_+ = aᵀ + g` adds a constant matrix field, which commutes with
translation.  Hence the annealed block of the descendant cell does not depend on `w`, only on
the inner index `z`.

This is the descendant form of the landed
`annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq`, whose case `n = 0` recovers that statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter measurable_translateCoeff
  translateCoeff)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- A translated adapted cell is the translate of the centred adapted cell: both are the
image of `⋄_j^q` under `x ↦ y + x`. -/
private theorem adaptedCellTranslate_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y = translateSet y (HighContrast.adaptedCell q j) := by
  ext x
  simp only [HighContrast.adaptedCellTranslate, translateSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [← hwxy, add_comm]⟩
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [hwxy, add_comm]⟩

/-- Translation by a sum is the composite of the two translations. -/
private theorem translateSet_add {d : ℕ} (a b : Vec d) (U : Set (Vec d)) :
    translateSet (a + b) U = translateSet a (translateSet b U) := by
  ext x
  simp only [translateSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨y + b, ⟨y, hy, rfl⟩, ?_⟩
    rw [hx]
    abel
  · rintro ⟨y, ⟨y₀, hy₀, hy⟩, hx⟩
    refine ⟨y₀, hy₀, ?_⟩
    rw [hx, hy]
    abel

/-- The centre of the grouped descendant cell is the outer scale-`j` centre plus the inner
scale-`(j - n)` centre: the scaled index `3^n w + z` distributes over the additive and
homogeneous map `matVecMul q`. -/
private theorem adaptedCellCenter_add_scale {d : ℕ} (q : Mat d) (j : ℤ) (n : ℕ)
    (w z : Fin d → ℤ) :
    adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
      = adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z := by
  have hvec : (fun i => ((3 ^ n * w i + z i : ℤ) : ℝ))
      = (3 : ℝ) ^ n • (fun i => (w i : ℝ)) + (fun i => (z i : ℝ)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  calc
    adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
        = (3 : ℝ) ^ (j - (n : ℤ))
            • matVecMul q (fun i => ((3 ^ n * w i + z i : ℤ) : ℝ)) := rfl
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • matVecMul q ((3 : ℝ) ^ n • (fun i => (w i : ℝ)) + (fun i => (z i : ℝ))) := by
          rw [hvec]
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • (matVecMul q ((3 : ℝ) ^ n • (fun i => (w i : ℝ)))
                + matVecMul q (fun i => (z i : ℝ))) := by
          rw [matVecMul_add]
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • ((3 : ℝ) ^ n • matVecMul q (fun i => (w i : ℝ))
                + matVecMul q (fun i => (z i : ℝ))) := by
          rw [matVecMul_smul]
    _ = ((3 : ℝ) ^ (j - (n : ℤ)) * (3 : ℝ) ^ n)
            • matVecMul q (fun i => (w i : ℝ))
          + (3 : ℝ) ^ (j - (n : ℤ)) • matVecMul q (fun i => (z i : ℝ)) := by
          rw [smul_add, smul_smul]
    _ = (3 : ℝ) ^ j • matVecMul q (fun i => (w i : ℝ))
          + (3 : ℝ) ^ (j - (n : ℤ)) • matVecMul q (fun i => (z i : ℝ)) := by
          have hpow : (3 : ℝ) ^ (j - (n : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ j := by
            rw [← zpow_natCast (3 : ℝ) n, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            congr 1
            omega
          rw [hpow]
    _ = adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z := rfl

/-- The grouped descendant cell is the integer-scale translate of the inner descendant cell by
the outer scale-`j` centre. -/
private theorem adaptedCellAtCenter_descendant_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (n : ℕ)
    (w z : Fin d → ℤ) :
    adaptedCellAtCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
      = translateSet (adaptedCellCenter q j w) (adaptedCellAtCenter q (j - (n : ℤ)) z) := by
  calc
    adaptedCellAtCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
        = adaptedCellTranslate q (j - (n : ℤ))
            (adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)) := rfl
    _ = adaptedCellTranslate q (j - (n : ℤ))
            (adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z) := by
          rw [adaptedCellCenter_add_scale]
    _ = translateSet (adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z)
            (adaptedCell q (j - (n : ℤ))) := by
          rw [adaptedCellTranslate_eq_translateSet]
    _ = translateSet (adaptedCellCenter q j w)
            (translateSet (adaptedCellCenter q (j - (n : ℤ)) z)
              (adaptedCell q (j - (n : ℤ)))) := by
          rw [translateSet_add]
    _ = translateSet (adaptedCellCenter q j w) (adaptedCellAtCenter q (j - (n : ℤ)) z) := by
          unfold adaptedCellAtCenter
          rw [adaptedCellTranslate_eq_translateSet]

/-- The coarse block of the recentred field `a_- = a - g` on the integer translate of a set is
the coarse block of the translated recentred field on the set.  The recentring subtracts the
constant matrix field `g`, which is unaffected by translation, so the covariance is that of the
coarse block matrix itself. -/
private theorem coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus {d : ℕ}
    (zz : Fin d → ℤ) (V : Set (Vec d)) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (translateSet (Source.AKL.intTranslation zz) V) (respCoeffMinus F a)
      = coarseBlockMatrix V (respCoeffMinus F (translateCoeff zz a)) := by
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae zz a.1] with x hxpt
  exact (congrArg (fun M : Mat d => M - respg F) hxpt).symm

/-- The coarse block of the recentred field `a_+ = aᵀ + g` on the integer translate of a set is
the coarse block of the translated recentred field on the set.  The recentring adds the constant
matrix field `g`, which is unaffected by translation, so the covariance is that of the coarse
block matrix itself. -/
private theorem coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus {d : ℕ}
    (zz : Fin d → ℤ) (V : Set (Vec d)) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (translateSet (Source.AKL.intTranslation zz) V) (respCoeffPlus F a)
      = coarseBlockMatrix V (respCoeffPlus F (translateCoeff zz a)) := by
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae zz a.1] with x hxpt
  exact (congrArg (fun M : Mat d => matTranspose M + respg F) hxpt).symm

/-- Stationarity of a scalar functional of the coefficient field: precomposing with an integer
translation leaves the `P`-integral unchanged. -/
private theorem integral_comp_translateCoeff_eq_aux {d : ℕ} (P : Measure (CoeffSpace d))
    (hstat : IsStationaryLaw P) (z : Fin d → ℤ) (f : CoeffSpace d → ℝ)
    (hf : AEStronglyMeasurable f P) :
    (∫ a, f (translateCoeff z a) ∂P) = ∫ a, f a ∂P := by
  have h := integral_map (μ := P) (φ := translateCoeff z)
    (measurable_translateCoeff z).aemeasurable (f := f) (by rw [hstat z]; exact hf)
  rw [hstat z] at h
  exact h.symm

/-- Stationarity of a scalar functional of a descendant cell: the outer centre of a scale-`j ≥
j_*` aligned cell is an integer translation and the law is invariant under integer translations,
so the `P`-integral of the functional of the grouped descendant cell equals that of the inner
cell. -/
private theorem integral_descendantCell_eq_aux {d : ℕ}
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (G : Set (Vec d) → CoeffSpace d → ℝ)
    (hG : ∀ (zz : Fin d → ℤ) (a : CoeffSpace d),
      G (translateSet (Source.AKL.intTranslation zz)
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)) a
        = G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) (translateCoeff
          zz a))
    (hmeas : AEStronglyMeasurable
      (G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)) P) :
    (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) a ∂P)
      = ∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) a ∂P := by
  obtain ⟨zz, hzz⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar m hj w
  have hcongr : (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) a ∂P)
      = ∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
          (translateCoeff zz a) ∂P := by
    apply integral_congr_ae
    filter_upwards with a
    rw [adaptedCellAtCenter_descendant_eq_translateSet, hzz]
    exact hG zz a
  rw [hcongr]
  exact integral_comp_translateCoeff_eq_aux P hstat zz _ hmeas

/-- **The annealed block of a descendant cell is independent of the scale-`j` cell containing
it, minus sign.**  For a stationary law and a scale `j >= j_*`, the annealed block of the
generation-`(j - n)` aligned cell at the grouped index `3^n w + z` is the annealed block of the
generation-`(j - n)` aligned cell at the inner index `z`. -/
theorem annealedBlockOf_descendant_respCoeffMinus_eq {d : ℕ}
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffMinus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffMinus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).upperLeft i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
      ℤ)) z)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
            ℤ)) z)
              (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).lowerRight i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
      ℤ)) z)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
            ℤ)) z)
              (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

/-- **The annealed block of a descendant cell is independent of the scale-`j` cell containing
it, plus sign.**  The adjoint twin of `annealedBlockOf_descendant_respCoeffMinus_eq`, for the
recentred family `a_+ = a^t + g`. -/
theorem annealedBlockOf_descendant_respCoeffPlus_eq {d : ℕ}
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffPlus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffPlus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).upperLeft i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
      ℤ)) z)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
            ℤ)) z)
              (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).lowerRight i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
      ℤ)) z)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n :
            ℤ)) z)
              (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

end

end HCPolySupport.HighContrast.Multiscale
end
