/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointRecentHeadEstimate
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ParentEnergyMapPort
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.PrimalBranchSelector
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentScaleEnergyRoute
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.SeminormHeadTailSplit

/-!
# High-contrast homogenization: Entry.Response.Kernel.CentredVarianceTailRoute

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centred variance bound and the adjoint tail route

At each depth, the flat average over the depth-`n` subcells of the recentred transported cell
averages is compared with the same average of the uncentred ones, using the identity that the
mean square distance from the mean is the second moment minus the squared mean; since the flat
average of the subcell averages is the parent average, this dominates the centred scale term by
the uncentred one. This file records the resulting per-scale older-scale bound at the estimate's
own carriers, proves the adjoint twin of the two older-scale tail branches of
`e.response.weak.estimate`, and composes the two branches with the finite-window head through the
branch-free selector to obtain the diagonal weak-norm estimate for the transposed recentred
coefficient, the adjoint twin of `l.weaknorms.moreproto`.
-/

section
/-!
## The centred scale term is dominated by the uncentred one

At each depth the flat average over the depth-`n` subcells of the recentred transported cell
averages is compared with the same average of the uncentred ones.  Since the flat average of the
subcell averages is the parent average (an equal-volume partition), this is the elementary
identity "the mean square distance from the mean is the second moment minus the square of the
mean".  This file proves the purely algebraic inequality over an arbitrary finite index set, and
then its instance at the estimate's carriers, where the metric transport `R` is applied first.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Bilinearity helpers -/

omit [NeZero d] in
/-- The doubled pairing against the zero vector vanishes. -/
private theorem blockVecDot_zero_left_variance (m : BlockVec d) :
    blockVecDot (0 : BlockVec d) m = 0 := by
  change blockVecDot ((0 : Vec d), (0 : Vec d)) m = 0
  simp [blockVecDot, vecDot]

omit [NeZero d] in
/-- The doubled pairing is additive in its first argument, hence linear over a finite sum. -/
private theorem blockVecDot_finset_sum_left {ι : Type*} (Z : Finset ι)
    (y : ι → BlockVec d) (m : BlockVec d) :
    blockVecDot (∑ w ∈ Z, y w) m = ∑ w ∈ Z, blockVecDot (y w) m := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, blockVecDot_add_left, ih]

omit [NeZero d] in
/-- The doubled pairing is additive in its first argument, including subtraction. -/
private theorem blockVecDot_sub_left (X Y Z : BlockVec d) :
    blockVecDot (X - Y) Z = blockVecDot X Z - blockVecDot Y Z := by
  rw [sub_eq_add_neg, blockVecDot_add_left]
  have hneg : blockVecDot (-Y) Z = -blockVecDot Y Z := by
    simpa using blockVecDot_smul_left (-1 : ℝ) Y Z
  rw [hneg]
  ring

omit [NeZero d] in
/-- Expanding the squared distance from the mean. -/
private theorem blockVecDot_sub_self_expand (X m : BlockVec d) :
    blockVecDot (X - m) (X - m)
      = blockVecDot X X - 2 * blockVecDot X m + blockVecDot m m := by
  rw [blockVecDot_sub_right, blockVecDot_sub_left, blockVecDot_sub_left,
    blockVecDot_comm m X]
  ring

omit [NeZero d] in
/-- The first component of a finite sum of doubled vectors is the sum of the first components. -/
private theorem fst_finset_sum {ι : Type*} (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, y w).1 = ∑ w ∈ Z, (y w).1 := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp [ih]

omit [NeZero d] in
/-- The second component of a finite sum of doubled vectors is the sum of the second
components. -/
private theorem snd_finset_sum {ι : Type*} (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, y w).2 = ∑ w ∈ Z, (y w).2 := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp [ih]

omit [NeZero d] in
/-- The zero doubled vector is annihilated by a block matrix. -/
private theorem blockMatVecMul_zero (A : BlockMat d) :
    blockMatVecMul A (0 : BlockVec d) = 0 := by
  change blockMatVecMul A ((0 : Vec d), (0 : Vec d)) = ((0 : Vec d), (0 : Vec d))
  simp [blockMatVecMul, matVecMul_zero]

omit [NeZero d] in
/-- A block matrix is additive, hence linear over a finite sum of doubled vectors. -/
private theorem blockMatVecMul_finset_sum {ι : Type*} (A : BlockMat d)
    (Z : Finset ι) (y : ι → BlockVec d) :
    (∑ w ∈ Z, blockMatVecMul A (y w)) = blockMatVecMul A (∑ w ∈ Z, y w) := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp [blockMatVecMul_zero]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, blockMatVecMul_add, ih]

/-! ## The algebraic inequality -/

omit [NeZero d] in
/-- **Variance is at most the second moment.**  For a finite nonempty index set `Z`, a family of
doubled vectors `y` and a doubled vector `m` whose two components are the corresponding flat
averages of the family, the flat average of the squared distance from `m` is at most the flat
average of the squared norm.  This is
`E‖y - m‖² = E‖y‖² - ‖m‖² ≤ E‖y‖²`. -/
theorem avsum_blockVecDot_sub_mean_le {iota : Type*} (Z : Finset iota) (hZ : Z.Nonempty)
    (y : iota → BlockVec d) (m : BlockVec d)
    (hmean1 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i = m.1 i)
    (hmean2 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i = m.2 i) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
      ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) := by
  classical
  have hcard : (Z.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hZ)
  have havg : ∑ w ∈ Z, y w = (Z.card : ℝ) • m := by
    refine Prod.ext ?_ ?_
    · funext i
      have hS : (∑ w ∈ Z, y w).1 i = (Z.card : ℝ) * m.1 i := by
        have hfst : (∑ w ∈ Z, y w).1 i = ∑ w ∈ Z, (y w).1 i := by
          rw [congrFun (fst_finset_sum Z y) i, Finset.sum_apply]
        rw [hfst]
        have hc : (Z.card : ℝ) * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i)
            = ∑ w ∈ Z, (y w).1 i := by
          rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
        rw [← hc, hmean1 i]
      have hrhs : ((Z.card : ℝ) • m).1 i = (Z.card : ℝ) * m.1 i := by
        rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      rw [hrhs]
      exact hS
    · funext i
      have hS : (∑ w ∈ Z, y w).2 i = (Z.card : ℝ) * m.2 i := by
        have hsnd : (∑ w ∈ Z, y w).2 i = ∑ w ∈ Z, (y w).2 i := by
          rw [congrFun (snd_finset_sum Z y) i, Finset.sum_apply]
        rw [hsnd]
        have hc : (Z.card : ℝ) * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i)
            = ∑ w ∈ Z, (y w).2 i := by
          rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
        rw [← hc, hmean2 i]
      have hrhs : ((Z.card : ℝ) • m).2 i = (Z.card : ℝ) * m.2 i := by
        rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [hrhs]
      exact hS
  have hdot : ∑ w ∈ Z, blockVecDot (y w) m = (Z.card : ℝ) * blockVecDot m m := by
    rw [← blockVecDot_finset_sum_left Z y m, havg, blockVecDot_smul_left]
  have hsum_expand :
      ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
        = (∑ w ∈ Z, blockVecDot (y w) (y w)) - (Z.card : ℝ) * blockVecDot m m := by
    calc ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
        = ∑ w ∈ Z, (blockVecDot (y w) (y w) - 2 * blockVecDot (y w) m
            + blockVecDot m m) :=
          Finset.sum_congr rfl fun w _ => blockVecDot_sub_self_expand (y w) m
      _ = (∑ w ∈ Z, blockVecDot (y w) (y w)) - 2 * (∑ w ∈ Z, blockVecDot (y w) m)
            + (Z.card : ℝ) * blockVecDot m m := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
      _ = (∑ w ∈ Z, blockVecDot (y w) (y w)) - (Z.card : ℝ) * blockVecDot m m := by
          rw [hdot]
          ring
  rw [hsum_expand]
  have hP : (0 : ℝ) ≤ blockVecDot m m := blockVecDot_nonneg m
  have hmul : (Z.card : ℝ)⁻¹ * ((Z.card : ℝ) * blockVecDot m m) = blockVecDot m m := by
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  have hrew : (Z.card : ℝ)⁻¹ * ((∑ w ∈ Z, blockVecDot (y w) (y w))
        - (Z.card : ℝ) * blockVecDot m m)
      = (Z.card : ℝ)⁻¹ * (∑ w ∈ Z, blockVecDot (y w) (y w)) - blockVecDot m m := by
    rw [mul_sub, hmul]
  rw [hrew]
  linarith only [hP]

/-! ## The instance at the estimate's carriers -/

omit [NeZero d] in
/-- **The centred transported scale term is dominated by the uncentred one.**  Applying the
algebraic inequality to `y w = blockMatVecMul R ((X)_{V_w})` and
`m = blockMatVecMul R ((X)_U)`, with the parent-mean identity supplied as a hypothesis and the
metric transport `R` distributed over the difference by linearity. -/
theorem scaleTerm_centred_le (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (X : Vec d → BlockVec d)
    (hmean1 : ∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).1 i
      = (cellAverage (HighContrast.adaptedCell q t) X).1 i)
    (hmean2 : ∀ i : Fin d, ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X).2 i
      = (cellAverage (HighContrast.adaptedCell q t) X).2 i) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X -
              cellAverage (HighContrast.adaptedCell q t) X))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X -
              cellAverage (HighContrast.adaptedCell q t) X))
      ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X)) := by
  classical
  let Z : Finset (Fin d → ℤ) := triadicIndexBox d n
  let v : (Fin d → ℤ) → BlockVec d := fun w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X
  let V : BlockVec d := cellAverage (HighContrast.adaptedCell q t) X
  have hZne : Z.Nonempty := by
    change (triadicIndexBox d n).Nonempty
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have havg : (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, v w) = V := by
    refine Prod.ext ?_ ?_
    · funext i
      rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      have hfst : (∑ w ∈ Z, v w).1 i = ∑ w ∈ Z, (v w).1 i := by
        rw [congrFun (fst_finset_sum Z v) i, Finset.sum_apply]
      rw [hfst]
      exact hmean1 i
    · funext i
      rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      have hsnd : (∑ w ∈ Z, v w).2 i = ∑ w ∈ Z, (v w).2 i := by
        rw [congrFun (snd_finset_sum Z v) i, Finset.sum_apply]
      rw [hsnd]
      exact hmean2 i
  let y : (Fin d → ℤ) → BlockVec d := fun w => blockMatVecMul R (v w)
  let m : BlockVec d := blockMatVecMul R V
  have hsumy : ∑ w ∈ Z, y w = blockMatVecMul R (∑ w ∈ Z, v w) :=
    blockMatVecMul_finset_sum R Z v
  have hm : (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w) = m := by
    calc (Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)
        = (Z.card : ℝ)⁻¹ • blockMatVecMul R (∑ w ∈ Z, v w) := by rw [hsumy]
      _ = blockMatVecMul R ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, v w)) :=
            (blockMatVecMul_smul R (Z.card : ℝ)⁻¹ (∑ w ∈ Z, v w)).symm
      _ = blockMatVecMul R V := by rw [havg]
      _ = m := rfl
  have hy1 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i = m.1 i := by
    intro i
    have hcomp : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).1 i = m.1 i :=
      congrArg (fun z : BlockVec d => z.1 i) hm
    have h2 : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).1 i
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).1 i := by
      rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        congrFun (fst_finset_sum Z y) i, Finset.sum_apply]
    rw [h2] at hcomp
    exact hcomp
  have hy2 : ∀ i : Fin d, (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i = m.2 i := by
    intro i
    have hcomp : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).2 i = m.2 i :=
      congrArg (fun z : BlockVec d => z.2 i) hm
    have h2 : ((Z.card : ℝ)⁻¹ • (∑ w ∈ Z, y w)).2 i
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (y w).2 i := by
      rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        congrFun (snd_finset_sum Z y) i, Finset.sum_apply]
    rw [h2] at hcomp
    exact hcomp
  have hbase : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m)
      ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) :=
    avsum_blockVecDot_sub_mean_le Z hZne y m hy1 hy2
  have hsum_eq : (∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w - V))
        (blockMatVecMul R (v w - V)))
      = ∑ w ∈ Z, blockVecDot (y w - m) (y w - m) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [blockMatVecMul_sub_vec]
  calc (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w - V))
          (blockMatVecMul R (v w - V))
      = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w - m) (y w - m) := by rw [hsum_eq]
    _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (y w) (y w) := hbase
    _ = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockVecDot (blockMatVecMul R (v w))
          (blockMatVecMul R (v w)) := rfl

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The per-scale older-scale bound at the estimate's own carriers

The cell-average estimate `e.response.weak.estimate` controls, at each depth `n`, the normalized
`L²` average over the aligned depth-`n` subcells of the recentred transported subcell averages of
the doubled optimizer field, by `√2 · K · B · ℰ`.  Here `K` is the square root of the spectral
bound of the normalized block, `B = 1 + √M · 3^{ρ n / 2}` combines the all-scale maximum `M` with
the geometric window weight, and `ℰ` is the pathwise optimizer energy of the parent adapted cell.

This module specializes the generic composed bound `scaleTail_of_inputs` to the estimate's own
carriers: the selected grid `respGrid`, the parent cell `respCell`, the metric transport
`blockSqrt (respM0 F)`, the coefficient field `respCoeffMinus F a`, and the optimizer field of the
parent.  The three analytic inputs are supplied generically: the variance step
`scaleTerm_centred_le` fed with the parent-mean identity
`cellAverage_parent_eq_avg_subcells`, the per-cell quadratic bound `hcell` (a hypothesis), and
the parent energy partition `parent_energy_partition_cell`.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The per-scale older-scale bound at the estimate's own carriers.**  For an invertible selected
grid, a generation `t`, a depth `n` and a parent harmonic optimizer, if every aligned depth-`n`
subcell bounds the quadratic metric form of its transported cell average by `(K B)^2` times twice
its energy average, then the normalized `L²` average of the recentred transported subcell averages
is at most `√2 · K · B · ℰ`, where `K = √(‖(Ehat_t^-)_+‖)` and `B = 1 + √M · 3^{ρ n / 2}`.  The
parent-mean identity and the parent energy partition are discharged internally from `IsUnit q`; the
integrability and nonnegativity of the parent energy density remain explicit hypotheses. -/
theorem scaleTail_carrier (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
              (optimizerField (respCoeffMinus F a) u x).2)))
    (h1 : ∀ j : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).1 j) (respCell jStar F t))
    (h2 : ∀ j : Fin d, IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) u x).2 j) (respCell jStar F t))
    (hnn : 0 ≤ volumeAverage (respCell jStar F t)
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2))
    (hintE : IntegrableOn
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2) (respCell jStar F t)) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u := by
  have hmean := cellAverage_parent_eq_avg_subcells (respGrid jStar F) hgrid t n
    (optimizerField (respCoeffMinus F a) u) h1 h2
  have hvar := scaleTerm_centred_le (respGrid jStar F) t n (blockSqrt (respM0 F))
    (optimizerField (respCoeffMinus F a) u) hmean.1 hmean.2
  have hpart := parent_energy_partition_cell (respGrid jStar F) hgrid t n
    (respCoeffMinus F a) u hnn hintE
  have hK : 0 ≤
      Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) :=
    Real.sqrt_nonneg _
  have hB : 0 ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) := by
    have hs : 0 ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) := Real.sqrt_nonneg _
    have hp : 0 ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    linarith only [mul_nonneg hs hp]
  exact scaleTail_of_inputs (respGrid jStar F) t n (blockSqrt (respM0 F))
    (respCoeffMinus F a) u
    (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))))
    (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))
    hK hB hvar hcell hpart

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two tail branches of the cell-average estimate, adjoint sign

The cell-average estimate `e.response.weak.estimate` bounds the normalized scale-average seminorm
of the recentred, metric-transported subcell averages of the doubled optimizer field, in two
branches according to the size of the all-scale maximum `M = respAllScaleMax P γ jStar F t a`.
This module is the adjoint twin of `tailBranches_minus`: the parent optimizer is attached to
the transposed recentred response coefficient `respCoeffPlus F a`, and the reference sample is the
adjoint normalised block `respEhatPlus`.

Every input of the older-scale branch is composed here once at the estimate's own carriers: the
per-cell bound `tailCell_of_bridge_plus`, the generic per-scale assembly `scaleTail_of_inputs`
instantiated at the adjoint coefficient, the summability `summable_centred`, and the
integrability and nonnegativity inputs.  The abstract branch splitting `primal_branches` then
turns the per-scale bound into the two printed branch bounds.

The per-scale family is `M_0^{1/2} · ((X)_{z + U_{t-n}} − (X)_{U_t})`, the transported recentring of
the parent optimizer field `X = (∇v, b ∇v)`.  On `1 < M` the whole series is absorbed by the
older-scale term; on `M ≤ 1` only the scales beyond a window `H` are absorbed and the first `H + 1`
scales remain as an explicit head sum.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The two older-scale branches of the cell-average estimate, adjoint sign.**  For an
invertible selected grid, a generation `t`, a parent harmonic optimizer attached to the transposed
recentred response coefficient, and the pointwise elliptic data of the parent and normalized
blocks, the normalized seminorm of the recentred transported optimizer field obeys the bad-branch
bound `16 / (1 - Quenched.contrastRho γ) · K · √M · ℰ` when `1 < M` and the good-branch bound
`∑_{n ≤ H} 3 ^ (-(n / 2)) S n + 16 / (1 - Quenched.contrastRho γ) · K · 3 ^
(-(Quenched.contrastAlpha γ H)) · ℰ` when
`M ≤ 1`, where `K = √(‖(Ehat_t^+)_+‖)`, `ℰ` is the weak optimizer energy, and `S n` is the
depth-`n` scale average. -/
theorem tailBranches_plus (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    (1 < respAllScaleMax P γ jStar F t a →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffPlus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          ≤ 16 / (1 - Quenched.contrastRho γ) *
              Real.sqrt
                (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
              Real.sqrt (respAllScaleMax P γ jStar F t a) *
              weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u) ∧
    (respAllScaleMax P γ jStar F t a ≤ 1 →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffPlus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          ≤ (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
                Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                  ∑ w ∈ triadicIndexBox d n,
                    blockVecDot
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffPlus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffPlus F a) u)))
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffPlus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffPlus F a) u)))))
            + 16 / (1 - Quenched.contrastRho γ) *
                Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
                (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) *
                weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u) := by
  classical
  obtain ⟨hmem1, hmem2⟩ :=
    memVectorL2_optimizerField_respCoeffPlus_cell (respGrid jStar F) hgrid t F a u
  have hK : 0 ≤ Real.sqrt
      (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) :=
    Real.sqrt_nonneg _
  have hEn : 0 ≤ weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u :=
    Real.sqrt_nonneg _
  have hM : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun Hb => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨n, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hsum := summable_centred (respGrid jStar F) hgrid t (blockSqrt (respM0 F))
    (optimizerField (respCoeffPlus F a) u) hmem1 hmem2
  have hscale : ∀ n : ℕ,
      Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u := by
    intro n
    have hcell := tailCell_of_bridge_plus P γ jStar F t hgrid a n u hm hEmean hEhat hM0 hbdd
    have h1 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffPlus F a) u x).1 j) (respCell jStar F t) :=
      fun j => (integrableOn_optimizerField_respCoeffPlus_cell
        (respGrid jStar F) hgrid t F a u j).1
    have h2 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffPlus F a) u x).2 j) (respCell jStar F t) :=
      fun j => (integrableOn_optimizerField_respCoeffPlus_cell
        (respGrid jStar F) hgrid t F a u j).2
    have hnn := energyDensity_average_nonneg_plus (respGrid jStar F) hgrid t F a u
    have hintE := integrableOn_energyDensity_respCoeffPlus (respGrid jStar F) hgrid t F a u
    have hmean := cellAverage_parent_eq_avg_subcells (respGrid jStar F) hgrid t n
      (optimizerField (respCoeffPlus F a) u) h1 h2
    have hvar := scaleTerm_centred_le (respGrid jStar F) t n (blockSqrt (respM0 F))
      (optimizerField (respCoeffPlus F a) u) hmean.1 hmean.2
    have hpart := parent_energy_partition_cell (respGrid jStar F) hgrid t n
      (respCoeffPlus F a) u hnn hintE
    have hKp : 0 ≤ Real.sqrt
        (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) :=
      Real.sqrt_nonneg _
    have hBp : 0 ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
        (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) := by
      have hs : 0 ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) := Real.sqrt_nonneg _
      have hp : 0 ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
        (Real.rpow_pos_of_pos (by norm_num) _).le
      linarith only [mul_nonneg hs hp]
    exact scaleTail_of_inputs (respGrid jStar F) t n (blockSqrt (respM0 F))
      (respCoeffPlus F a) u
      (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))))
      (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
        (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))
      hKp hBp hvar hcell hpart
  exact primal_branches hγ t H
    (fun n w => blockMatVecMul (blockSqrt (respM0 F))
      (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
        cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
    hK hEn hM hsum hscale

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cell-average estimate for the transposed recentred coefficient

The adjoint twin of the cell-average estimate `l.weaknorms.moreproto`: the two older-scale
branches at the estimate's own carriers and the finite-window head compose through the branch-free
selector, exactly as for the recentred coefficient itself.  The statement is the route's, carried
here so that the route file stays short.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The cell-average estimate, adjoint sign.**  The scale-average seminorm of the recentred
doubled optimizer state of the transposed recentred coefficient is bounded by the two finite
recent-scale sums plus the older-scale energy term, with the printed cutoff selector.  See
`e.response.weak.estimate`. -/
theorem diagonalWeakNorm_primal_plus (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n w =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))) ≤
      16 * Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar
              F t)
              (respCoeffPlus F a)) +
        (16 / (1 - Quenched.contrastRho γ) *
            Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u := by
  classical
  have hrho : Quenched.contrastRho γ < 1 := by
    have := _hγ.2
    rw [Quenched.contrastRho]
    linarith only [this]
  have hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    respEhatPlus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    respMean_posDef_of_integrable hgrid t hint
  obtain ⟨hbad, hgood⟩ :=
    tailBranches_plus P γ _hγ jStar H F t hgrid a u hm hEmean hE hM0 hbdd
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) with hKdef
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hLdef
  set Ene : ℝ := weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u with hEnedef
  set Sums : ℝ := 16 * K * L *
    (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) +
      weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
        (respCoeffPlus F a)) with hSumsdef
  set c : ℝ := 16 / (1 - Quenched.contrastRho γ) * K with hcdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hEne0 : 0 ≤ Ene := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - Quenched.contrastRho γ := by linarith only [hrho]
    rw [hcdef]
    positivity
  have hSums0 : 0 ≤ Sums := by
    have h1 : 0 ≤ weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
        (respCoeffPlus F a) := weakCellSum_nonneg _ _ _ _ _
    have h2 : 0 ≤ weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
        (respEhatPlus P jStar F t) (respCoeffPlus F a) := weakAverageSum_nonneg _ _ _ _ _ _
    rw [hSumsdef]
    have : 0 ≤ 16 * K * L := by positivity
    exact mul_nonneg this (by linarith only [h1, h2])
  have hMnn : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun _ => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨m, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hgood' : respAllScaleMax P γ jStar F t a ≤ 1 →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        ≤ Sums + c * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * Ene := by
    intro hMle
    have hhead := recentHead_carrier_plus P γ _hγ jStar H F t e hgrid hint a hbdd u hu hMle
    have hhead' : (∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffPlus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffPlus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u))))) ≤ Sums := hhead
    have := hgood hMle
    linarith only [this, hhead']
  have hbad' : 1 < respAllScaleMax P γ jStar F t a →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        ≤ c * Real.sqrt (respAllScaleMax P γ jStar F t a) * Ene := by
    intro hMgt
    have := hbad hMgt
    linarith only [this]
  have hkey := head_le_add_max_mul_ite _hγ H hMnn
    ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n w =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
            cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
    Sums Ene c c hc0 hc0 hSums0 hEne0 hgood' hbad'
  rwa [max_self] at hkey

end

end HCPolySupport.HighContrast.Multiscale
end
