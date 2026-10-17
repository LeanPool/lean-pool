/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Moments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperLaw
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Diagonal
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.RealStationaryTransfer
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.AnnealedSubadditivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.MomentFactorBounds.Apex

/-!
# Monotonicity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Loewner monotonicity of the annealed cutoff cube matrices

ABK26: by subadditivity, the matrices `bfAhom_m(cu_n)` are monotone
nonincreasing in `n` in the Loewner (positive semidefinite) order.  The paper
places no sign restriction on `n`, and the consumers instantiate the statement
at every `n ∈ ℤ`, so the monotonicity below is stated for all `n ≤ k` in `ℤ`.

Three inputs go into the proof.

* The deterministic a.e. block subadditivity comparison
  `Ch04.RestrictionLawCarrier.coarseBlockMatrix_le_descendantsAverageBlockMat_ae`
  and the block quadratic-form machinery of
  `Ch04.blockMatLoewnerLE_of_integral_quadratic_mono` are supplied by
  CoarseGraining and are scale-free.
* Entrywise integrability of the coarse block matrix on the parent cube and on each of its
  descendants is discharged from the proved cutoff moment layer:
  `integrable_LambdaSqCoeffField_pow_cutoffLaw` and
  `integrable_lambdaSqCoeffField_inv_pow_cutoffLaw` hold for the unnormalized cutoff law
  on an *arbitrary* triadic cube, so CoarseGraining's factor-moment route
`Ch04.RestrictionLawCarrier.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables`
  applies verbatim.  No `(P4)` record and no structural-law hypothesis is needed.
* The stationary transfer identifying the expectation on a descendant cube with
  the expectation on the origin cube at the descendant scale.  This is the only
  step that is *not* scale-free in CoarseGraining:
  `Ch04.RestrictionLawCarrier.blockMatLoewnerLE_annealedBlockMatrixAtScale`
  routes it through `RestrictionStationaryLaw = IsStationaryR`, which only sees
  integer translations, whereas a descendant offset `3 ^ n * z` is an integer
  vector only for `n ≥ 0`.  The genuine cutoff law is invariant under *every
  real* translation, so this repository reroutes the transfer through
  `Algsuperdiff.Section3.Cutoff.coefficientCutoffLaw_stationary_real` and the
  scale-free geometry of `Provider.Annealed.RealStationaryTransfer`.  That
  removes the sign restriction entirely.

## Main results

* `coefficientCutoffLaw_integrable_coarseFullBlockMatrixAtCube`
* `coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix`
* `coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale`
* `coefficientCutoffLaw_matLoewnerLE_annealedBAtScale`
* `coefficientCutoffLaw_matLoewnerLE_annealedSigmaStarInvAtScale`
-/

namespace Algsuperdiff.Section3.Provider.Annealed

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The full unfolded coarse block observable of the genuine cutoff is integrable
on every triadic cube.  Both factor moments are the proved cutoff moments at
exponent one. -/
theorem coefficientCutoffLaw_integrable_coarseFullBlockMatrixAtCube
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) :
    Integrable (Ch04.coarseFullBlockMatrixAtCube Q) (Cutoff.coefficientCutoffLaw M m) :=
  (Cutoff.coefficientCutoffLaw_lawCarrier M
      m).integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables
    Q (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) (le_refl 1)
    (Cutoff.integrable_LambdaSqCoeffField_pow_cutoffLaw M m Q
      (by norm_num : (0 : ℝ) < 1) 1)
    (Cutoff.integrable_lambdaSqCoeffField_inv_pow_cutoffLaw M m Q
      (by norm_num : (0 : ℝ) < 1) 1)

/-- Every entry of the doubled coarse block matrix of the genuine cutoff is
integrable on every triadic cube. -/
theorem coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) (alpha beta : BlockCoord d) :
    Integrable
      (fun a : RegCoeffField d =>
        blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta)
      (Cutoff.coefficientCutoffLaw M m) :=
  Ch04.RestrictionLawCarrier.integrable_coarseBlockMatrixEntry_of_integrableFullBlock
    (coefficientCutoffLaw_integrable_coarseFullBlockMatrixAtCube M m Q) alpha beta

omit [NeZero d] in
/-- Real-translation invariance of the genuine cutoff law, in the form consumed
by the scale-free transfer layer. -/
theorem coefficientCutoffLaw_isStationaryRealR (M : ABKModel d) (m : ℤ) :
    IsStationaryRealR (Cutoff.coefficientCutoffLaw M m) :=
  Cutoff.coefficientCutoffLaw_stationary_real M m

/-! ## Descendant averages of the coarse block entries -/

omit [NeZero d] in
private theorem descendantsAverage_congr {Q : TriadicCube d} {j : ℕ}
    {F G : TriadicCube d → ℝ} (h : ∀ R ∈ descendantsAtDepth Q j, F R = G R) :
    descendantsAverage Q j F = descendantsAverage Q j G := by
  classical
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum F =
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (descendantsAtDepth Q j).sum G
  rw [Finset.sum_congr rfl h]

omit [NeZero d] in
private theorem descendantsAverage_const (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  classical
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
      (descendantsAtDepth Q j).sum (fun _ => c) = c
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [NeZero d] in
private theorem blockMatEntry_descendantsAverageBlockMat_eq (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) (alpha beta : BlockCoord d) :
    blockMatEntry
        (descendantsAverageBlockMat Q j (fun R => coarseBlockMatrix (cubeSet R) a.toFun))
        alpha beta =
      descendantsAverage Q j
        (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta) := by
  cases alpha <;> cases beta <;> rfl

omit [NeZero d] in
/-- Depth form of the descendant index set below an origin cube. -/
private theorem descendantsAtDepth_originCube_eq_descendantsAtScale {n k : ℤ} (hnk : n ≤ k) :
    descendantsAtDepth (originCube d k) (Int.toNat (k - n)) =
      descendantsAtScale (originCube d k) n :=
  (descendantsAtScale_eq_descendantsAtDepth (originCube d k) (k := n) hnk).symm

/-- Every entry of the descendant-average coarse block matrix is integrable. -/
private theorem coefficientCutoffLaw_integrable_blockMatEntry_descendantsAverageBlockMat
    (M : ABKModel d) (m : ℤ) (k : ℤ) (j : ℕ) (alpha beta : BlockCoord d) :
    Integrable
      (fun a : RegCoeffField d =>
        blockMatEntry
          (descendantsAverageBlockMat (originCube d k) j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta)
      (Cutoff.coefficientCutoffLaw M m) := by
  have hEntryFun :
      (fun a : RegCoeffField d =>
        blockMatEntry
          (descendantsAverageBlockMat (originCube d k) j
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta) =
        fun a : RegCoeffField d =>
          descendantsAverage (originCube d k) j
            (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta) := by
    funext a
    exact blockMatEntry_descendantsAverageBlockMat_eq (originCube d k) j a alpha beta
  rw [hEntryFun]
  exact Ch04.integrable_descendantsAverage
    (fun R _hR =>
      coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix M m R alpha beta)

/-- **The stationary expectation step, without a sign restriction.**  The
expectation of an entry of the descendant-average coarse block matrix at scale
`n` below the origin cube at scale `k` is the annealed origin-cube entry at
scale `n`.  This mirrors CoarseGraining's private
`Ch04.RestrictionLawCarrier.integral_descendantsAverageBlockMat_entry_eq_annealedBlockMatrixAtScale`
with the integer-translation transfer replaced by the real-translation transfer
of `Provider.Annealed.RealStationaryTransfer`. -/
private theorem coefficientCutoffLaw_integral_blockMatEntry_descendantsAverageBlockMat
    (M : ABKModel d) (m : ℤ) {n k : ℤ} (hnk : n ≤ k) (alpha beta : BlockCoord d) :
    ∫ a,
        blockMatEntry
          (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta
        ∂(Cutoff.coefficientCutoffLaw M m) =
      blockMatEntry
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n) alpha beta := by
  classical
  have hEntryFun :
      (fun a : RegCoeffField d =>
        blockMatEntry
          (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta) =
        fun a : RegCoeffField d =>
          descendantsAverage (originCube d k) (Int.toNat (k - n))
            (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta) := by
    funext a
    exact blockMatEntry_descendantsAverageBlockMat_eq (originCube d k) (Int.toNat (k - n))
      a alpha beta
  have htransfer :
      ∀ R ∈ descendantsAtDepth (originCube d k) (Int.toNat (k - n)),
        (∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta
            ∂(Cutoff.coefficientCutoffLaw M m)) =
          ∫ a,
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) alpha beta
            ∂(Cutoff.coefficientCutoffLaw M m) := by
    intro R hR
    refine
      integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale
        (Cutoff.coefficientCutoffLaw_lawCarrier M m)
        (coefficientCutoffLaw_isStationaryRealR M m) hnk ?_ alpha beta
    rwa [descendantsAtDepth_originCube_eq_descendantsAtScale hnk] at hR
  calc
    ∫ a,
        blockMatEntry
          (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta
        ∂(Cutoff.coefficientCutoffLaw M m)
        =
      ∫ a,
        descendantsAverage (originCube d k) (Int.toNat (k - n))
          (fun R => blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta)
        ∂(Cutoff.coefficientCutoffLaw M m) := by
        rw [hEntryFun]
    _ =
      descendantsAverage (originCube d k) (Int.toNat (k - n))
        (fun R =>
          ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet R) a.toFun) alpha beta
            ∂(Cutoff.coefficientCutoffLaw M m)) :=
        Ch04.integral_descendantsAverage_eq_descendantsAverage_integral
          (fun R _hR =>
            coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix M m R alpha beta)
    _ =
      descendantsAverage (originCube d k) (Int.toNat (k - n))
        (fun _ =>
          ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) alpha beta
            ∂(Cutoff.coefficientCutoffLaw M m)) :=
        descendantsAverage_congr htransfer
    _ =
      ∫ a, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d n)) a.toFun) alpha beta
        ∂(Cutoff.coefficientCutoffLaw M m) :=
        descendantsAverage_const (originCube d k) (Int.toNat (k - n)) _
    _ =
      blockMatEntry
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n) alpha beta := by
        cases alpha <;> cases beta <;> rfl

/-- The entrywise expectation of the descendant-average coarse block matrix is
the annealed block matrix at the descendant scale. -/
private theorem coefficientCutoffLaw_integral_descendantsAverageBlockMat_eq
    (M : ABKModel d) (m : ℤ) {n k : ℤ} (hnk : n ≤ k) :
    ({ upperLeft := fun i j =>
          ∫ a,
            (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).upperLeft i j
            ∂(Cutoff.coefficientCutoffLaw M m),
       upperRight := fun i j =>
          ∫ a,
            (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).upperRight i j
            ∂(Cutoff.coefficientCutoffLaw M m),
       lowerLeft := fun i j =>
          ∫ a,
            (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).lowerLeft i j
            ∂(Cutoff.coefficientCutoffLaw M m),
       lowerRight := fun i j =>
          ∫ a,
            (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).lowerRight i j
            ∂(Cutoff.coefficientCutoffLaw M m) } : BlockMat d) =
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> funext i j
  · exact coefficientCutoffLaw_integral_blockMatEntry_descendantsAverageBlockMat M m hnk
      (Sum.inl i) (Sum.inl j)
  · exact coefficientCutoffLaw_integral_blockMatEntry_descendantsAverageBlockMat M m hnk
      (Sum.inl i) (Sum.inr j)
  · exact coefficientCutoffLaw_integral_blockMatEntry_descendantsAverageBlockMat M m hnk
      (Sum.inr i) (Sum.inl j)
  · exact coefficientCutoffLaw_integral_blockMatEntry_descendantsAverageBlockMat M m hnk
      (Sum.inr i) (Sum.inr j)

/-! ## The Loewner monotonicity -/

/-- **ABK26.**  The annealed cutoff block matrices on origin cubes are
nonincreasing in the cube scale in the Loewner order, at every pair of integer
scales `n ≤ k`. -/
theorem coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
    (M : ABKModel d) (m : ℤ) {n k : ℤ} (hnk : n ≤ k) :
    BlockMatLoewnerLE
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) k)
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n) := by
  classical
  have hParentInt :
      ∀ alpha beta : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun) alpha beta)
          (Cutoff.coefficientCutoffLaw M m) := fun alpha beta =>
    coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix M m (originCube d k)
      alpha beta
  have hChildInt :
      ∀ alpha beta : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            blockMatEntry
              (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
                (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) alpha beta)
          (Cutoff.coefficientCutoffLaw M m) := fun alpha beta =>
    coefficientCutoffLaw_integrable_blockMatEntry_descendantsAverageBlockMat M m k
      (Int.toNat (k - n)) alpha beta
  refine
    Ch04.blockMatLoewnerLE_of_integral_quadratic_mono
      (P := Cutoff.coefficientCutoffLaw M m)
      (A := Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) k)
      (B := Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n)
      (F := fun X a =>
        (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun) X))
      (G := fun X a =>
        (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul
            (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
              (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) X))
      ?hFint ?hGint ?hA ?hB ?hMono
  · intro X
    exact (Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
      hParentInt X X).const_mul (1 / 2 : ℝ)
  · intro X
    exact (Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
      hChildInt X X).const_mul (1 / 2 : ℝ)
  · intro X
    have hInt :=
      Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
        (B := fun a : RegCoeffField d => coarseBlockMatrix (cubeSet (originCube d k)) a.toFun)
        hParentInt X X
    calc
      (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) k) X)
          =
        (1 / 2 : ℝ) *
          ∫ a,
            blockVecDot X
              (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun) X)
            ∂(Cutoff.coefficientCutoffLaw M m) := by
          simpa [Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrix] using
            congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) hInt.symm
      _ =
        ∫ a,
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun) X)
          ∂(Cutoff.coefficientCutoffLaw M m) := by
          rw [integral_const_mul]
  · intro X
    have hInt :=
      Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
        (B := fun a : RegCoeffField d =>
          descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun))
        hChildInt X X
    calc
      ∫ a,
          (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul
              (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
                (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) X)
          ∂(Cutoff.coefficientCutoffLaw M m)
          =
        (1 / 2 : ℝ) *
          ∫ a,
            blockVecDot X
              (blockMatVecMul
                (descendantsAverageBlockMat (originCube d k) (Int.toNat (k - n))
                  (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) X)
            ∂(Cutoff.coefficientCutoffLaw M m) := by
          rw [integral_const_mul]
      _ =
        (1 / 2 : ℝ) * blockVecDot X
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n) X) := by
          rw [hInt, coefficientCutoffLaw_integral_descendantsAverageBlockMat_eq M m hnk]
  · intro X
    filter_upwards
      [(Cutoff.coefficientCutoffLaw_lawCarrier M
          m).coarseBlockMatrix_le_descendantsAverageBlockMat_ae hnk] with a ha
    exact ha X

/-- The annealed upper-left blocks of the genuine cutoff are nonincreasing in
the cube scale. -/
theorem coefficientCutoffLaw_matLoewnerLE_annealedBAtScale
    (M : ABKModel d) (m : ℤ) {n k : ℤ} (hnk : n ≤ k) :
    MatLoewnerLE (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M m) k)
      (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  Ch04.matLoewnerLE_annealedBAtScale_of_block
    (coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale M m hnk)

/-- The annealed inverse-star blocks of the genuine cutoff are nonincreasing in
the cube scale. -/
theorem coefficientCutoffLaw_matLoewnerLE_annealedSigmaStarInvAtScale
    (M : ABKModel d) (m : ℤ) {n k : ℤ} (hnk : n ≤ k) :
    MatLoewnerLE (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M m) k)
      (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M m) n) :=
  Ch04.matLoewnerLE_annealedSigmaStarInvAtScale_of_block
    (coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale M m hnk)

end

end Algsuperdiff.Section3.Provider.Annealed
