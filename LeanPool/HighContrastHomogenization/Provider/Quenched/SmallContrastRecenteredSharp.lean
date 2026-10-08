/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenEntries
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewBlock
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastRecenteredSharp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recentered annealed block: Schur data and sharp order

Recentering the coefficient field by the constant skew `g` replaces the
annealed block by its shear congruence, whose Schur coordinate drops by `g`
while the two diagonal Schur data are unchanged.  The sharp order for the
recentered block follows from the pathwise toolkit at the recentered samples
and matrix Jensen — not from a congruence of the original sharp order, which
is false in general.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The Schur representation of a shear congruence: the skew coordinate drops
by the shear while both diagonal coordinates persist. -/
theorem toFullBlockMat_skewBlockCongr_of_schurBlock
    {A : BlockMat d} {S SStar K : Mat d} (g : Mat d)
    (hE : toFullBlockMat A = schurBlock S SStar K) :
    toFullBlockMat (Response.skewBlockCongr g A) =
      schurBlock S SStar (K - g) := by
  rw [Response.toFullBlockMat_skewBlockCongr, hE, schurBlock, schurBlock]
  have hcompose :
      fullBlockShear (-K) * fullBlockShear g = fullBlockShear (-(K - g)) := by
    rw [fullBlockShear_mul]
    congr 1
    abel
  calc
    (fullBlockShear g)ᴴ *
        ((fullBlockShear (-K))ᴴ * Matrix.fromBlocks S 0 0 SStar⁻¹ *
          fullBlockShear (-K)) * fullBlockShear g =
        (fullBlockShear (-K) * fullBlockShear g)ᴴ *
          Matrix.fromBlocks S 0 0 SStar⁻¹ *
            (fullBlockShear (-K) * fullBlockShear g) := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = (fullBlockShear (-(K - g)))ᴴ * Matrix.fromBlocks S 0 0 SStar⁻¹ *
          fullBlockShear (-(K - g)) := by
      rw [hcompose]

/-- **The sharp order for the recentered annealed block.**  The pathwise
positivity and pathwise sharp order hold at every sample, in particular at
the recentered samples; matrix Jensen then gives the annealed sharp order for
the recentered mean.  Both toolkit facts are theorems of the coarse-block
positivity module, so the only hypothesis on the law is integrability. -/
theorem blockSharp_skewBlockCongr_annealedBlock_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) :
    BlockMatLoewnerLE
      (blockSharp (Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d)))))
      (Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d)))) := by
  have hU : IsOpenBoundedConvexDomain (U : Set (Vec d)) := U.isDomain
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    ENNReal.toReal_pos (hU.isOpen.measure_pos volume U.nonempty).ne'
      hU.volume_lt_top.ne
  have hpos := Sharp.blockPosDef_coarseBlock_of_volume_pos hU hvol
  have hsharp := Sharp.blockMatLoewnerLE_blockSharp_coarseBlock hU hvol
  -- the recentered pathwise block
  set A2 : CoeffSpace d → FullBlockMat d := fun a =>
    toFullBlockMat (coarseBlock (U : Set (Vec d)) (a.subSkew g hg))
    with hA2
  have hA2eq : ∀ a, A2 a =
      (fullBlockShear g)ᴴ *
        toFullBlockMat (coarseBlock (U : Set (Vec d)) a) *
          fullBlockShear g := by
    intro a
    change toFullBlockMat (coarseBlock (U : Set (Vec d)) (a.subSkew g hg)) = _
    rw [Response.coarseBlock_subSkew U a g hg, Response.toFullBlockMat_skewBlockCongr]
  have hintF : Integrable
      (fun a => toFullBlockMat (coarseBlock (U : Set (Vec d)) a)) P :=
    integrable_toFullBlockMat hint
  have hint2 : Integrable A2 P := by
    have h := integrable_mul_left_mul_right (μ := P)
      (fullBlockShear g)ᴴ (fullBlockShear g) hintF
    refine h.congr (Filter.Eventually.of_forall fun a => ?_)
    exact (hA2eq a).symm
  -- pathwise data at the recentered samples
  have hpos2 : ∀ a, (A2 a).PosDef := fun a =>
    posDef_toFullBlockMat
      (isSymmetricBlockMat_coarseBlock _ (a.subSkew g hg))
      (hpos (a.subSkew g hg))
  have hsharp2 : ∀ a, fullBlockSharp (A2 a) ≤ A2 a := fun a =>
    fullBlockSharp_le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_coarseBlock _ (a.subSkew g hg))
      (hpos (a.subSkew g hg)) (hsharp (a.subSkew g hg))
  -- integrability of the pathwise sharp
  have hentryF : ∀ p q, AEStronglyMeasurable
      (fun a => toFullBlockMat (coarseBlock (U : Set (Vec d)) a) p q) P := by
    intro p q
    simpa only [toFullBlockMat_eq_blockMatEntry] using
      (hint p q).aestronglyMeasurable
  have hentry2 : ∀ p q, AEStronglyMeasurable (fun a => A2 a p q) P := by
    intro p q
    have hsum : AEStronglyMeasurable
        (∑ j : BlockCoord d, ∑ i : BlockCoord d,
          fun a : CoeffSpace d =>
            (fullBlockShear g)ᴴ p i *
              (toFullBlockMat (coarseBlock (U : Set (Vec d)) a) i j *
                fullBlockShear g j q)) P :=
      Finset.aestronglyMeasurable_sum _ fun j _ =>
        Finset.aestronglyMeasurable_sum _ fun i _ =>
          ((hentryF i j).mul_const _).const_mul _
    refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Finset.sum_apply]
    rw [hA2eq a, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- entrywise integrability of the coarse response and of the recentered
  -- pathwise block, at the scalar level where the ambient matrix norm plays
  -- no role
  have hintEntryF : ∀ p q, Integrable
      (fun a => toFullBlockMat (coarseBlock (U : Set (Vec d)) a) p q) P := by
    intro p q
    simpa only [toFullBlockMat_eq_blockMatEntry] using hint p q
  have hintEntryA2 : ∀ p q, Integrable (fun a => A2 a p q) P := by
    intro p q
    have hsum : Integrable
        (∑ j : BlockCoord d, ∑ i : BlockCoord d,
          fun a : CoeffSpace d =>
            (fullBlockShear g)ᴴ p i *
              (toFullBlockMat (coarseBlock (U : Set (Vec d)) a) i j *
                fullBlockShear g j q)) P :=
      integrable_finsetSum' _ fun j _ =>
        integrable_finsetSum' _ fun i _ =>
          ((hintEntryF i j).mul_const _).const_mul _
    refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Finset.sum_apply]
    rw [hA2eq a, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hintTraceA2 : Integrable (fun a => Matrix.trace (A2 a)) P := by
    have hEq : (fun a => Matrix.trace (A2 a)) = fun a => ∑ i, A2 a i i := by
      funext a
      simp only [Matrix.trace, Matrix.diag_apply]
    rw [hEq]
    exact integrable_finsetSum _ fun i _ => hintEntryA2 i i
  -- per-entry measurability of the pathwise sharp, reusing the entrywise
  -- toolkit for a two-sided constant conjugate of an inverse
  have hmeasRefl : ∀ i j : BlockCoord d, AEStronglyMeasurable
      (fun _ : CoeffSpace d => fullBlockRefl d i j) P :=
    fun _ _ => aestronglyMeasurable_const
  have hmeasInvA2 : ∀ i j, AEStronglyMeasurable (fun a => (A2 a)⁻¹ i j) P :=
    aestronglyMeasurable_inv_of_entries hentry2
  have hmeasLinvA2 : ∀ i j, AEStronglyMeasurable
      (fun a => (fullBlockRefl d * (A2 a)⁻¹) i j) P :=
    aestronglyMeasurable_entry_mul (F := fun _ => fullBlockRefl d)
      (G := fun a => (A2 a)⁻¹) hmeasRefl hmeasInvA2
  have hmeasSharp2 : ∀ p q, AEStronglyMeasurable
      (fun a => fullBlockSharp (A2 a) p q) P := by
    intro p q
    simpa only [fullBlockSharp] using
      aestronglyMeasurable_entry_mul (F := fun a => fullBlockRefl d * (A2 a)⁻¹)
        (G := fun _ => fullBlockRefl d) hmeasLinvA2 hmeasRefl p q
  -- every entry of the pathwise sharp is bounded by the trace of the
  -- recentered pathwise block: the sharp is positive semidefinite with
  -- eigenvalues below its own trace, itself below the trace of the
  -- dominating block
  have hboundSharp2 : ∀ a p q,
      |fullBlockSharp (A2 a) p q| ≤ Matrix.trace (A2 a) := by
    intro a p q
    have hBherm : (fullBlockSharp (A2 a)).IsHermitian :=
      (posDef_fullBlockSharp (hpos2 a)).isHermitian
    have hBnn : ∀ i, 0 ≤ hBherm.eigenvalues i :=
      (posDef_fullBlockSharp (hpos2 a)).posSemidef.eigenvalues_nonneg
    have hBtrace : Matrix.trace (fullBlockSharp (A2 a)) = ∑ i, hBherm.eigenvalues i := by
      simpa using hBherm.trace_eq_sum_eigenvalues
    have hmono : Matrix.trace (fullBlockSharp (A2 a)) ≤ Matrix.trace (A2 a) := by
      have hsub : (A2 a - fullBlockSharp (A2 a)).PosSemidef := Matrix.le_iff.mp (hsharp2 a)
      have htn := hsub.trace_nonneg
      rw [Matrix.trace_sub] at htn
      linarith only [htn]
    have htraceNonneg : (0 : ℝ) ≤ Matrix.trace (A2 a) :=
      le_trans (hBtrace ▸ Finset.sum_nonneg fun i _ => hBnn i) hmono
    refine Recurrence.abs_apply_le_of_abs_eigenvalues_le hBherm htraceNonneg
      (fun i => ?_) p q
    rw [abs_of_nonneg (hBnn i)]
    calc hBherm.eigenvalues i ≤ Matrix.trace (fullBlockSharp (A2 a)) := by
          rw [hBtrace]
          exact Finset.single_le_sum (fun j _ => hBnn j) (Finset.mem_univ i)
      _ ≤ Matrix.trace (A2 a) := hmono
  have hintSharp2 : Integrable (fun a => fullBlockSharp (A2 a)) P := by
    refine integrable_of_entries fun p q => ?_
    refine Integrable.mono' hintTraceA2 (hmeasSharp2 p q)
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs]
    exact hboundSharp2 a p q
  -- the recentered mean and its positivity
  have hmean2 : (∫ a, A2 a ∂P) =
      toFullBlockMat
        (Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d)))) := by
    rw [hA2]
    exact Response.integral_coarseBlock_subSkew U hint g hg
  have hEpos2 :
      (toFullBlockMat
        (Response.skewBlockCongr g (annealedBlock P (U : Set (Vec d))))).PosDef :=
    posDef_toFullBlockMat
      (Response.isSymmetricBlockMat_skewBlockCongr
        (isSymmetricBlockMat_annealedBlock P _))
      (Response.blockPosDef_skewBlockCongr
        (blockPosDef_annealedBlock hint hpos))
  -- matrix Jensen for the recentered mean
  have hkey := fullBlockSharp_integral_le_integral (μ := P)
    (A := A2) hpos2 hsharp2 hint2 hintSharp2
    (by rw [hmean2]; exact hEpos2)
  rw [hmean2] at hkey
  refine blockMatLoewnerLE_of_le ?_
  rwa [toFullBlockMat_blockSharp]

end

end HCPolySupport.HighContrast.Quenched
