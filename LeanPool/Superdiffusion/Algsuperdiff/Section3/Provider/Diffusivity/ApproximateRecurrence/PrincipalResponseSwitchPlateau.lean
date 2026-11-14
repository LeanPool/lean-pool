/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.Comparator
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.CubeScalar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity

/-!
# PrincipalResponseSwitchPlateau

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the annealed limit matrix and the finite-cube plateau sandwich

This module supplies the two deterministic ingredients that the annealed switch
`e.use.also.for.the.upper.bound` of ABK26 opens with, namely the ordering
`bfAhom_L <= bfAhom_L(cu_n)` between the infinite-volume annealed matrix and its
finite-cube counterpart, together with the identification of the constant
comparator block matrix used by `mathcal E` with that same infinite-volume
matrix.

## The two objects

ABK26, `e.homs.defs`, defines the deterministic matrix

`bfAhom_m := diag(shom_m, shom_m^{-1}) := lim_{n -> infty} E[bfA_m(cu_n)]`,

with `shom_m` the running diffusivity `Annealed.sigmaBar M m`, and records
that the finite-cube matrices `bfAhom_m(cu_n)` are nonincreasing in `n` in
the Loewner order.  Combining the two gives the left half of the sandwich
`bfAhom_{m-h,*}(cu_n) <= bfAhom_{m-h} <= bfAhom_{m-h}(cu_n)` printed.

`mathcal E_{s,p,q}(cu_m; a, a_0)` normalizes its one-cube probe by the constant
block matrix `Ch02.constantBlockMatrix a_0`.  At the Section 3 comparator `a_0 =
shom_m Id` that constant block matrix is exactly `bfAhom_m`, which is what makes
the annealed probe `(bfAhom^{-1/2} e, bfAhom^{1/2} e)` of ABK26 the same probe
that `mathcal E` maximizes over; this is recorded below in
`constantBlockMatrix_isotropicComparatorMatrix`.

## Scope

Everything here is deterministic: no induction state, no bad events, no
recurrence parameters.

## Main results

* `blockVecDot_blockDiag_smul_one_vecDot`: the doubled quadratic form of
  a scalar block-diagonal matrix.
* `blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit`: the plateau
  ordering `bfAhom_L <= bfAhom_L(cu_n)`, at every pair of integers `L, n`.
* `sigmaBar_le_annealedCubeUpperLeft`, `inv_sigmaBar_le_annealedCubeLowerRight`:
  the two scalar consequences of that ordering.

## References

* ABK26, `e.homs.defs.U.diag`, `e.homs.defs`.
* ABK26 (`e.use.also.for.the.upper.bound` and its proof).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open Filter HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## Scalar matrix algebra -/

/-- The doubled quadratic form of a scalar block-diagonal matrix. -/
theorem blockVecDot_blockDiag_smul_one_vecDot (c c' : ℝ) (V : BlockVec d) :
    blockVecDot V
        (blockMatVecMul (Ch02.blockDiag (c • (1 : Mat d)) (c' • (1 : Mat d))) V) =
      c * vecDot V.1 V.1 + c' * vecDot V.2 V.2 := by
  have h1 : matVecMul (c • (1 : Mat d)) V.1 = c • V.1 := by
    simpa using matVecMul_scalarMatrix (d := d) c V.1
  have h2 : matVecMul (c' • (1 : Mat d)) V.2 = c' • V.2 := by
    simpa using matVecMul_scalarMatrix (d := d) c' V.2
  have h0 : ∀ x : Vec d, matVecMul (0 : Mat d) x = (0 : Vec d) := by
    intro x
    funext j
    simp [matVecMul]
  simp only [blockVecDot, blockMatVecMul, Ch02.blockDiag, h0, add_zero,
    zero_add, h1, h2, vecDot_smul_right]

/-! ## Convergence of the doubled quadratic form -/

private theorem tendsto_vecDot_matVecMul {A : ℕ → Mat d} {B : Mat d}
    (h : ∀ i j, Tendsto (fun k => A k i j) atTop (nhds (B i j))) (x y : Vec d) :
    Tendsto (fun k => vecDot x (matVecMul (A k) y)) atTop
      (nhds (vecDot x (matVecMul B y))) := by
  simp only [vecDot, matVecMul]
  refine tendsto_finsetSum _ ?_
  intro i _
  refine Tendsto.const_mul _ ?_
  refine tendsto_finsetSum _ ?_
  intro j _
  exact (h i j).mul_const (y j)

/-- Entrywise convergence of doubled block matrices passes to their doubled
quadratic forms. -/
theorem tendsto_blockVecDot_blockMatVecMul {A : ℕ → BlockMat d} {B : BlockMat d}
    (h : Tendsto (fun k => toFullBlockMat (A k)) atTop (nhds (toFullBlockMat B)))
    (V : BlockVec d) :
    Tendsto (fun k => blockVecDot V (blockMatVecMul (A k) V)) atTop
      (nhds (blockVecDot V (blockMatVecMul B V))) := by
  have hentry : ∀ alpha beta : BlockCoord d,
      Tendsto (fun k => toFullBlockMat (A k) alpha beta) atTop
        (nhds (toFullBlockMat B alpha beta)) := by
    intro alpha beta
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h alpha) beta
  have hUL : ∀ i j, Tendsto (fun k => (A k).upperLeft i j) atTop
      (nhds (B.upperLeft i j)) := fun i j => hentry (Sum.inl i) (Sum.inl j)
  have hUR : ∀ i j, Tendsto (fun k => (A k).upperRight i j) atTop
      (nhds (B.upperRight i j)) := fun i j => hentry (Sum.inl i) (Sum.inr j)
  have hLL : ∀ i j, Tendsto (fun k => (A k).lowerLeft i j) atTop
      (nhds (B.lowerLeft i j)) := fun i j => hentry (Sum.inr i) (Sum.inl j)
  have hLR : ∀ i j, Tendsto (fun k => (A k).lowerRight i j) atTop
      (nhds (B.lowerRight i j)) := fun i j => hentry (Sum.inr i) (Sum.inr j)
  have hsplit : ∀ C : BlockMat d,
      blockVecDot V (blockMatVecMul C V) =
        vecDot V.1 (matVecMul C.upperLeft V.1) +
            vecDot V.1 (matVecMul C.upperRight V.2) +
          (vecDot V.2 (matVecMul C.lowerLeft V.1) +
            vecDot V.2 (matVecMul C.lowerRight V.2)) := by
    intro C
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_add]
  simp only [hsplit]
  exact ((tendsto_vecDot_matVecMul hUL V.1 V.1).add
      (tendsto_vecDot_matVecMul hUR V.1 V.2)).add
    ((tendsto_vecDot_matVecMul hLL V.2 V.1).add
      (tendsto_vecDot_matVecMul hLR V.2 V.2))

/-! ## The plateau ordering -/

variable [NeZero d]

/-- **ABK26.**  The infinite-volume annealed matrix `bfAhom_L = diag(shom_L,
shom_L^{-1})` is below the finite-cube annealed matrix `bfAhom_L(cu_n)` in the
Loewner order, at every cube scale `n`.

This is the right half of the sandwich printed; it is the Loewner
monotonicity of together with the limit defining `bfAhom_L` in `e.homs.defs`.
-/
theorem blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit
    (M : ABKModel d) (m n : ℤ) :
    BlockMatLoewnerLE
      (Ch02.blockDiag ((Annealed.sigmaBar M m : ℝ) • (1 : Mat d))
        ((Annealed.sigmaBar M m : ℝ)⁻¹ • (1 : Mat d)))
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n) := by
  intro V
  have hlim := (Annealed.sigmaBar_characterization M m).2.1
  have htend := tendsto_blockVecDot_blockMatVecMul
    (A := fun k : ℕ =>
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) (k : ℤ))
    (B := Ch02.blockDiag ((Annealed.sigmaBar M m : ℝ) • (1 : Mat d))
      ((Annealed.sigmaBar M m : ℝ)⁻¹ • (1 : Mat d))) hlim V
  refine le_of_tendsto (htend.const_mul (1 / 2 : ℝ)) ?_
  filter_upwards [eventually_ge_atTop n.toNat] with k hk
  have hnk : n ≤ (k : ℤ) := le_trans (Int.self_le_toNat n) (by exact_mod_cast hk)
  exact Provider.Annealed.coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
    M m hnk V

/-! ## The two scalar consequences -/

/-- The coordinate potential probe `(e_i, 0)`. -/
def potentialProbe (i : Fin d) : BlockVec d :=
  (fun j => if j = i then (1 : ℝ) else 0, fun _ => (0 : ℝ))

/-- The coordinate flux probe `(0, e_i)`. -/
def fluxProbe (i : Fin d) : BlockVec d :=
  (fun _ => (0 : ℝ), fun j => if j = i then (1 : ℝ) else 0)

omit [NeZero d] in
private theorem vecDot_potentialProbe_fst (i : Fin d) :
    vecDot (potentialProbe (d := d) i).1 (potentialProbe (d := d) i).1 = 1 := by
  simp [potentialProbe, vecDot]

omit [NeZero d] in
private theorem vecDot_potentialProbe_snd (i : Fin d) :
    vecDot (potentialProbe (d := d) i).2 (potentialProbe (d := d) i).2 = 0 := by
  simp [potentialProbe, vecDot]

omit [NeZero d] in
private theorem vecDot_fluxProbe_fst (i : Fin d) :
    vecDot (fluxProbe (d := d) i).1 (fluxProbe (d := d) i).1 = 0 := by
  simp [fluxProbe, vecDot]

omit [NeZero d] in
private theorem vecDot_fluxProbe_snd (i : Fin d) :
    vecDot (fluxProbe (d := d) i).2 (fluxProbe (d := d) i).2 = 1 := by
  simp [fluxProbe, vecDot]

/-- **ABK26, upper-left block.**  The running diffusivity is below the
upper-left scalar of the finite-cube annealed matrix. -/
theorem sigmaBar_le_annealedCubeUpperLeft (M : ABKModel d) (m n : ℤ) {s t : ℝ}
    (hst : Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n =
      Ch02.blockDiag (s • (1 : Mat d)) (t • (1 : Mat d))) :
    (Annealed.sigmaBar M m : ℝ) ≤ s := by
  have hi : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hle := blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit M m n
    (potentialProbe (d := d) ⟨0, hi⟩)
  rw [hst] at hle
  rw [blockVecDot_blockDiag_smul_one_vecDot,
    blockVecDot_blockDiag_smul_one_vecDot,
    vecDot_potentialProbe_fst, vecDot_potentialProbe_snd] at hle
  linarith

/-- **ABK26, lower-right block.**  The inverse running diffusivity is
below the lower-right scalar of the finite-cube annealed matrix. -/
theorem inv_sigmaBar_le_annealedCubeLowerRight (M : ABKModel d) (m n : ℤ)
    {s t : ℝ}
    (hst : Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n =
      Ch02.blockDiag (s • (1 : Mat d)) (t • (1 : Mat d))) :
    ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤ t := by
  have hi : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hle := blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit M m n
    (fluxProbe (d := d) ⟨0, hi⟩)
  rw [hst] at hle
  rw [blockVecDot_blockDiag_smul_one_vecDot,
    blockVecDot_blockDiag_smul_one_vecDot,
    vecDot_fluxProbe_fst, vecDot_fluxProbe_snd] at hle
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
