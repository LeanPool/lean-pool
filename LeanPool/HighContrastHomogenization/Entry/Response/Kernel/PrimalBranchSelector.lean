/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.SeminormHeadTailSplit

/-!
# High-contrast homogenization: Entry.Response.Kernel.PrimalBranchSelector

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The branch selector for the normalized scale-average seminorm

Given the per-scale bound `S n ≤ √2 · K · (1 + √M · 3^(ρn/2)) · ℰ`, this file proves the printed
estimate in two branches: on `1 < M` the whole series is absorbed by the recent-scale weight, and
on `M ≤ 1` the head/tail split applies. It records the algebraic spine of that per-scale bound,
composes it with the variance bound and the remaining analytic inputs into the per-scale tail, and
rewrites the estimate's left-hand side as a genuine `besovSeminorm` of a `cellAverageFamily` split
at the window depth. It also proves the summability the split needs for the recentred,
metric-transported cell-average family. The branch selection and the cell-average inputs serve the
diagonal weak-norm estimate of `p.response.transfer`.
-/

section
/-!
## The two branch bounds for the whole normalized scale-average seminorm

The cell-average estimate's left-hand side is the normalized seminorm
`3 ^ (-(t / 2)) * besovSeminorm t avg`, i.e. `∑' n, 3 ^ (-(n / 2)) * S n` with `S` the depth-`n`
scale average.  Given the per-scale bound `S n ≤ √2 · K · (1 + √M · 3 ^ (ρ n / 2)) · En`, the
printed estimate is proved in two branches.  On `1 < M` the whole series is absorbed by the
older-scale term; on `M ≤ 1` only the scales beyond the window `H` are, and the first `H + 1`
scales remain as an explicit head sum.  Nothing here mentions a matrix or a measure: both
statements are real analysis about the family `avg` alone.

The normalization `3 ^ (-(t / 2)) * besovSeminorm t avg = ∑' n, 3 ^ (-(n / 2)) * S n` is the
unsplit form of `normalized_besovTerm`; it is proved inline because the module that once
packaged it is not present, so the bad branch never needs the window split.
-/

namespace HCPolySupport.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- The two branch bounds of the cell-average estimate for the whole normalized seminorm.  The
per-scale input is `S n ≤ √2 · K · (1 + √M · 3 ^ (Quenched.contrastRho γ * n / 2)) · En`; summing it
geometrically gives the bad-branch bound `16 / (1 - Quenched.contrastRho γ) · K · √M · En` on `1 <
M`, and the
good-branch bound `∑_{n ≤ H} 3 ^ (-(n / 2)) S n + 16 / (1 - Quenched.contrastRho γ) · K ·
3 ^ (-(Quenched.contrastAlpha γ * H)) · En` on `M ≤ 1`. -/
theorem primal_branches {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (t : ℤ) (H : ℕ)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d) {K En M : ℝ}
    (hK : 0 ≤ K) (hEn : 0 ≤ En) (hM : 0 ≤ M)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
    (hscale : ∀ n : ℕ,
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
        ≤ Real.sqrt 2 * K *
            (1 + Real.sqrt M * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * En) :
    (1 < M → (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        ≤ 16 / (1 - Quenched.contrastRho γ) * K * Real.sqrt M * En) ∧
    (M ≤ 1 → (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        ≤ (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
              Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
                ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
          + 16 / (1 - Quenched.contrastRho γ) * K * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * En) := by
  constructor
  · intro hbad
    -- The bad branch works on the whole series, normalized termwise.
    have hnorm : (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
        = ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
      change (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          (∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
        = ∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
      rw [← tsum_mul_left]
      exact tsum_congr fun n => normalized_besovTerm t avg n
    rw [hnorm]
    exact tail_bad_le hγ hK hEn hbad
      (fun n : ℕ => Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      (fun n => Real.sqrt_nonneg _) hscale
  · intro hgood
    -- The good branch keeps the head and bounds only the older scales beyond `H`.
    have hsplit := besovSeminorm_window_tail_eq t avg hsum H
    have htail := tail_good_le hγ H hK hEn hM hgood
      (fun n : ℕ => Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      (fun n => Real.sqrt_nonneg _) hscale
    -- The split indexes the tail by `j + (H + 1)`, the good bound by `H + 1 + j`.
    have htail_eq : (∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
          Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d (j + (H + 1)),
              blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)))
        = ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
          Real.sqrt ((((triadicIndexBox d (H + 1 + j)).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d (H + 1 + j),
              blockVecDot (avg (H + 1 + j) w) (avg (H + 1 + j) w)) := by
      apply tsum_congr
      intro j
      rw [Nat.add_comm j (H + 1)]
    rw [hsplit, htail_eq]
    exact add_le_add le_rfl htail

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The per-scale energy bound

The head/tail splitting of the normalized scale-average seminorm leaves a single per-scale
estimate: the normalized `L²` average, over the depth-`n` aligned subcells, of the metric transport
of the recentred cell averages of a doubled field is bounded by `√2 · K · B · ℰ`, where `ℰ` is the
pathwise optimizer energy of the parent adapted cell.

The algebraic content is the real-arithmetic spine `scaleInput_spine_le`, which combines a
per-cell quadratic bound with an averaged energy bound.  This module specializes that spine to the
parent optimizer energy: the averaged energy bound is the partition identity that recombines the
subcell energy averages into the squared parent energy, so the energy factor in the conclusion is
the parent pathwise energy itself.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The per-scale energy bound, from a per-cell bound and an averaged energy bound.**  If every
depth-`n` subcell `adaptedCellAtCenter q (t - n) w` bounds the quadratic metric form of the
transported
cell average `R (X)_w` by `(K B)^2` times a nonnegative energy density `G w`, and if the flat
average of `G` over the subcells is at most `2 En^2`, then the flat `L²` average of the transported
cell averages is at most `√2 · K · B · En`.

This is the spine `scaleInput_spine_le` at load `En` and defect `1`; the factor `√1 = 1` is
discarded. -/
theorem scaleEnergy_of_analytic (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ) (K B En : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hEn : 0 ≤ En)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
        ≤ (K * B) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * En ^ 2) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 * K * B * En := by
  have h := scaleInput_spine_le (triadicIndexBox d n) R
    (fun w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Y w)) G K B En 1
    hK hB hEn zero_le_one hcell (by simpa only [mul_one] using henergy)
  simpa only [Real.sqrt_one, mul_one] using h

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The composed per-scale tail bound

At depth `n` the older-scale tail of the cell-average estimate compares the transported recentred
subcell averages of the doubled optimizer field with the transported parent cell average.  This
module composes the per-scale energy bound `scaleEnergy_of_analytic` with the two remaining
analytic inputs:

* the variance bound `hvar`, which majorizes the recentred flat `L²` average by the uncentred one;
* the per-cell energy bound `hcell` and the parent partition identity `hpart`, which supply the
  averaged energy bound of the spine.

The result is the tail estimate `√(card⁻¹ ∑ |R((X)_w − (X)_U)|²) ≤ √2 · K · B · ℰ`, where `ℰ` is
the pathwise optimizer energy of the parent adapted cell.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The composed per-scale tail bound.**  Suppose the recentred flat `L²` average of the
transported subcell averages is at most the uncentred one, each transported subcell average
satisfies the quadratic bound against `(K B)^2` times twice its subcell energy average, and the flat
average of the subcell energy averages equals the squared parent pathwise energy `ℰ^2`.  Then the
transported recentred tail is at most `√2 · K · B · ℰ`. -/
theorem scaleTail_of_inputs (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hvar : ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (optimizerField b u) -
                cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (optimizerField b u) -
                cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
        ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u)))
              (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u))))
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)))
        ≤ (K * B) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)))
    (hpart : ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u) -
              cellAverage (HighContrast.adaptedCell q t) (optimizerField b u)))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (optimizerField b u) -
              cellAverage (HighContrast.adaptedCell q t) (optimizerField b u))))
      ≤ Real.sqrt 2 * K * B * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u := by
  have henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      ≤ 2 * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
    have heq : ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
        = 2 * (((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)) := by
      rw [← Finset.mul_sum]
      ring
    rw [heq, hpart]
  have hunc : Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        blockVecDot
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (optimizerField b u)))
          (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (optimizerField b u))))
      ≤ Real.sqrt 2 * K * B * weakOptimizerEnergy (HighContrast.adaptedCell q t) b u :=
    scaleEnergy_of_analytic q t n R (fun _ => optimizerField b u)
      (fun w => 2 * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
      K B (weakOptimizerEnergy (HighContrast.adaptedCell q t) b u)
      hK hB (Real.sqrt_nonneg _) hcell henergy
  exact le_trans (Real.sqrt_le_sqrt hvar) hunc

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The left-hand side of the cell-average estimate, public

The cell-average estimate has left-hand side

`3 ^ (-(t / 2)) * besovSeminorm t (fun n w => blockMatVecMul A (cellAverageFamily q t X n w - c))`,

and its argument needs that quantity rewritten as a `besovSeminorm` of a genuine
`cellAverageFamily` and then split at the window depth.  `RecentEnergyMapSupport.lean`
contains both steps, but `private`, so no consumer above that module can reach them.  This module
lands public copies.

The recentring here asks integrability only on the cells the seminorm actually reads,
`w ∈ triadicIndexBox d n`, rather than on every label; that is exactly the hypothesis
`besovSeminorm_congr` needs.

## Main results

* `cellAverage_blockMatVecMul`: the cell average commutes with block transport.
* `cellAverage_sub_const`: the cell average of a recentred field.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem integrableOn_matVecMul_apply {V : Set (Vec d)} (M : Mat d) (Y : Vec d → Vec d)
    (hY : ∀ j, IntegrableOn (fun x => Y x j) V) (i : Fin d) :
    IntegrableOn (fun x => matVecMul M (Y x) i) V := by
  have h : (fun x => matVecMul M (Y x) i) = fun x => ∑ j, M i j * Y x j := rfl
  rw [h]
  exact integrable_finsetSum _ (fun j _ => (hY j).const_mul (M i j))

omit [NeZero d] in
private theorem volumeAverage_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) {f : Vec d → ℝ} (hf : IntegrableOn f V) (k : ℝ) :
    volumeAverage V (fun x => f x - k) = volumeAverage V f - k := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have hc : IntegrableOn (fun _ : Vec d => k) V := integrable_const k
  have h : (fun x => f x - k) = f - (fun _ => k) := rfl
  rw [h, volumeAverage_sub hf hc, volumeAverage_const hvol]

omit [NeZero d] in
/-- The cell average commutes with the block transport: averaging the transported field is the
transport of the averaged field.  Integrability is asked componentwise on `V`. -/
theorem cellAverage_blockMatVecMul {V : Set (Vec d)} (A : BlockMat d)
    (Y : Vec d → BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (Y x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (Y x).2 j) V) :
    cellAverage V (fun x => blockMatVecMul A (Y x)) = blockMatVecMul A (cellAverage V Y) := by
  have key : ∀ (M N : Mat d) (i : Fin d),
      volumeAverage V (fun x => matVecMul M (Y x).1 i + matVecMul N (Y x).2 i)
        = matVecMul M (fun j => volumeAverage V (fun x => (Y x).1 j)) i
          + matVecMul N (fun j => volumeAverage V (fun x => (Y x).2 j)) i := by
    intro M N i
    have hM : IntegrableOn (fun x => matVecMul M (Y x).1 i) V :=
      integrableOn_matVecMul_apply M (fun x => (Y x).1) h1 i
    have hN : IntegrableOn (fun x => matVecMul N (Y x).2 i) V :=
      integrableOn_matVecMul_apply N (fun x => (Y x).2) h2 i
    have hsplit : (fun x => matVecMul M (Y x).1 i + matVecMul N (Y x).2 i)
        = (fun x => matVecMul M (Y x).1 i) + (fun x => matVecMul N (Y x).2 i) := rfl
    rw [hsplit, volumeAverage_add hM hN]
    congr 1
    · exact volumeAverage_vecDot_left (M i) (fun x => (Y x).1) h1
    · exact volumeAverage_vecDot_left (N i) (fun x => (Y x).2) h2
  have hfst : (cellAverage V fun x => blockMatVecMul A (Y x)).1
      = (blockMatVecMul A (cellAverage V Y)).1 := by
    funext i
    exact key A.upperLeft A.upperRight i
  have hsnd : (cellAverage V fun x => blockMatVecMul A (Y x)).2
      = (blockMatVecMul A (cellAverage V Y)).2 := by
    funext i
    exact key A.lowerLeft A.lowerRight i
  exact Prod.ext hfst hsnd

omit [NeZero d] in
/-- The cell average of a recentred field is the recentred cell average, provided the cell has
finite and nonzero volume so that the constant integrates to itself. -/
theorem cellAverage_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hVpos : (volume V).toReal ≠ 0) (Y : Vec d → BlockVec d) (c : BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (Y x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (Y x).2 j) V) :
    cellAverage V (fun x => Y x - c) = cellAverage V Y - c := by
  have hfst : (cellAverage V fun x => Y x - c).1 = (cellAverage V Y - c).1 := by
    funext i
    exact volumeAverage_sub_const hVfin hVpos (h1 i) (c.1 i)
  have hsnd : (cellAverage V fun x => Y x - c).2 = (cellAverage V Y - c).2 := by
    funext i
    exact volumeAverage_sub_const hVfin hVpos (h2 i) (c.2 i)
  exact Prod.ext hfst hsnd

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Summability of the recentred, metric-transported cell-average family

The scale-average seminorm `besovSeminorm` is a real `tsum`, so every identity that splits it
needs its family to be summable.  The tree already proves the needed summability above the
cell-average estimate in `ResponseWeakEstimateBasics.lean`, but that module sits above the
estimate in
public import order, so the estimate cannot reach it.  This module re-lands the same fact below
it, on
the two public cell-average identities of `PrimalBranchSelector.lean`.

The engine is `summable_besov_cellAverageFamily` (`ScaleAverageSeminorm.lean`): for the transported
recentring `x ↦ A (X x - ⟨X⟩_{U_t})` the family of cell averages is summable as soon as the
transported field is in `L²` on `U_t`; the recentred family of the statement is that family,
restricted to the labels `w ∈ triadicIndexBox d n` the seminorm reads.

The second statement is the unsplit normalisation of the seminorm: pulling the factor
`3 ^ (-(t/2))` inside the `tsum` moves the weight of the `n`-th term to `3 ^ (-(n/2))`.  It is a
series identity and needs no summability.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Local helpers

These are the `L²`-to-integrability ingredients of the proof.  They are not imported because the
copies in `ResponseWeakEstimateBasics.lean` are `private` and that module is above this one in
import
order.  The cell-average identities themselves are the public
`cellAverage_blockMatVecMul` and `cellAverage_sub_const`. -/

omit [NeZero d] in
/-- A slot of a vector `L²` field on `U` is integrable on every finite-measure subset `V ⊆ U`. -/
private theorem integrableOn_slot {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hVfin : volume V ≠ ⊤) {g : Vec d → Vec d} (hg : MemVectorL2 U g) (j : Fin d) :
    IntegrableOn (fun x => g x j) V := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have h2 : MemLp (fun x => g x j) 2 (volume.restrict U) :=
    (MeasureTheory.memLp_pi_iff.mp hg) j
  have h2' : MemLp (fun x => g x j) 2 (volume.restrict V) :=
    h2.mono_measure (Measure.restrict_mono hVU le_rfl)
  exact MemLp.integrable (by norm_num) h2'

omit [NeZero d] in
/-- The squared pointwise norm of a block field whose two slots are `L²` is `L¹`. -/
private theorem memLp_one_blockVecDot {U : Set (Vec d)} {X : Vec d → BlockVec d}
    (h1 : MemVectorL2 U (fun x => (X x).1)) (h2 : MemVectorL2 U (fun x => (X x).2)) :
    MemLp (fun x => blockVecDot (X x) (X x)) 1 (volume.restrict U) := by
  have e1 := MeasureTheory.memLp_pi_iff.mp h1
  have e2 := MeasureTheory.memLp_pi_iff.mp h2
  rw [memLp_one_iff_integrable]
  have hA : Integrable (fun x => ∑ i, (X x).1 i * (X x).1 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e1 i).integrable_mul (e1 i)
  have hB : Integrable (fun x => ∑ i, (X x).2 i * (X x).2 i) (volume.restrict U) :=
    integrable_finsetSum _ fun i _ => by
      simpa [Pi.mul_apply] using! (e2 i).integrable_mul (e2 i)
  simpa [blockVecDot, vecDot] using! hA.add hB

/-- **The summability half.**  The recentred, metric-transported cell-average family of an
`L²(U_t)` block field is summable with the scale weights of the seminorm.  The engine
`summable_besov_cellAverageFamily` is applied to the transported recentring
`X' = x ↦ A (X x - ⟨X⟩_{U_t})`; on the read cells the cell average of `X'` is the transported
recentred cell average, by the two public cell-average identities. -/
theorem summable_centred (q : Mat d) (hq : IsUnit q) (t : ℤ) (A : BlockMat d)
    (X : Vec d → BlockVec d)
    (hs1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).1))
    (hs2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).2)) :
    Summable (fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul A (cellAverageFamily q t X n w - cellAverage (HighContrast.adaptedCell q t) X))
            (blockMatVecMul A (cellAverageFamily q t X n w -
              cellAverage (HighContrast.adaptedCell q t) X)))) := by
  classical
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure (volume.restrict (HighContrast.adaptedCell q t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hUfin⟩
  set C : BlockVec d := cellAverage (HighContrast.adaptedCell q t) X with hCdef
  set X' : Vec d → BlockVec d := fun x => blockMatVecMul A (X x - C) with hX'def
  have hd1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).1 - C.1) :=
    hs1.sub (memLp_const C.1)
  have hd2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X x).2 - C.2) :=
    hs2.sub (memLp_const C.2)
  have hX'1 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).1) :=
    (memVectorL2_matVecMul_const A.upperLeft hd1).add
      (memVectorL2_matVecMul_const A.upperRight hd2)
  have hX'2 : MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (X' x).2) :=
    (memVectorL2_matVecMul_const A.lowerLeft hd1).add
      (memVectorL2_matVecMul_const A.lowerRight hd2)
  have hX'mem : MemLp (fun x => blockVecDot (X' x) (X' x)) 1
      (volume.restrict (HighContrast.adaptedCell q t)) :=
    memLp_one_blockVecDot hX'1 hX'2
  have hsum' := summable_besov_cellAverageFamily q hq t X' hX'mem
  refine hsum'.congr fun n => ?_
  have hV : ∀ w ∈ triadicIndexBox d n,
      cellAverageFamily q t X' n w = blockMatVecMul A (cellAverageFamily q t X n w - C) := by
    intro w hw
    have hsub : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
      adaptedCellAtCenter_subset_adaptedCell q t n hw
    have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
      Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
    have : IsFiniteMeasure (volume.restrict (adaptedCellAtCenter q (t - (n : ℤ)) w)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
    have hVpos : (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal ≠ 0 :=
      ne_of_gt (volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w)
    have h1 : ∀ j, IntegrableOn (fun x => (X x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => integrableOn_slot hsub hVfin hs1 j
    have h2 : ∀ j, IntegrableOn (fun x => (X x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => integrableOn_slot hsub hVfin hs2 j
    have hc1 : ∀ j, IntegrableOn (fun x => (X x - C).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => (h1 j).sub (integrable_const (C.1 j))
    have hc2 : ∀ j, IntegrableOn (fun x => (X x - C).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
      fun j => (h2 j).sub (integrable_const (C.2 j))
    unfold cellAverageFamily
    rw [hX'def]
    rw [cellAverage_blockMatVecMul A (fun x => X x - C) hc1 hc2,
      cellAverage_sub_const hVfin hVpos X C h1 h2]
  have hsumeq : ∑ w ∈ triadicIndexBox d n,
        blockVecDot (cellAverageFamily q t X' n w) (cellAverageFamily q t X' n w)
      = ∑ w ∈ triadicIndexBox d n,
        blockVecDot (blockMatVecMul A (cellAverageFamily q t X n w - C))
          (blockMatVecMul A (cellAverageFamily q t X n w - C)) :=
    Finset.sum_congr rfl fun w hw => by rw [hV w hw]
  rw [hsumeq]

end

end HCPolySupport.HighContrast.Multiscale
end
