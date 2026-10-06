/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.NearIsometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingExhaustion
public import LeanPool.HighContrastHomogenization.Provider.Transport.BridgeAlgebra

/-!
# High-contrast homogenization: Provider.Transport.TransportMeanDomination

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The mean of the filling, and its bridge normalization

`e.two.grid.whitney.average` is a pathwise statement: the coarse response of
a target cell of the new grid is below the weighted sum of the responses of the
old grid's cells that fill it, plus the below-start series.  Every estimate that
follows it reads the *annealed* blocks instead, and this file makes that passage
and the normalization that comes with it.

Three steps, in the order the proof uses them.

*The grouping map.*  A cell of the filling at a scale at or below the checkpoint
lies in a unique cell of the checkpoint scale, and that cell meets the target.
This is the index map under which the inherited rows of
`e.two.grid.old.history.factor` are grouped, and it is nothing but the
iterated parent taken the right number of times.

*The mean.*  Averaging the pathwise domination is monotone for the Loewner
order, so the annealed block of the target is below the same weighted sum of the
annealed blocks of the filling's cells plus the mean of the below-start term.
The only hypotheses are integrability of the three families, which the
bounded-window multiplier supplies.

*The normalization.*  Conjugating that mean domination by the inverse square root
of the new terminal block turns it into the printed
`K_W = S^tP_bar_WS - (1-m_W)S^tS + R_W` of `e.two.grid.whitney.mean.bound`, because
the bridge congruence `S = (E_t^q)^{1/2}(E_n^{q'})^{-1/2}` carries the old
relative mean `P_{r,t}^q` exactly onto the normalization of `E_r^q` by
`E_n^{q'}`.  That identity is the reason the bridge error enters additively and
never multiplies a cell response.

The total relative volume of any finite set of rows is at most one, because the
cells of the filling are pairwise disjoint and lie in the target; that is the
convexity budget `m_W ≤ 1` of the convexity bound for the mean penalty.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The grouping map -/

/-! ## The convexity budget of the filling -/

/-- **The total relative volume of a finite set of rows of the maximal filling is
at most one.**  The cells of the filling are pairwise disjoint and contained in
the target, so the sum of their volumes is at most the target's.  This is the
budget `m_W ≤ 1` that the convexity bound for the mean penalty consumes. -/
theorem sum_relative_volume_le_one {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j : ℤ} {y : Vec d} {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = fillingIndex q n (adaptedCellTranslate p j y) r) :
    ∑ r ∈ R, ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal ≤ 1 := by
  classical
  set W : Set (Vec d) := adaptedCellTranslate p j y with hW
  have hmem : ∀ r : ℤ, ∀ w ∈ Z r, w ∈ fillingIndex q n W r := by
    intro r w hw
    have hw' : w ∈ (↑(Z r) : Set (Fin d → ℤ)) := hw
    rwa [hZ r] at hw'
  have hdisj : ((R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))) :
      Set ((_ : ℤ) × (Fin d → ℤ))).PairwiseDisjoint
      fun x => adaptedCellAt q x.1 x.2 := by
    intro x hx yy hyy hne
    rw [Finset.mem_coe, Finset.mem_sigma] at hx hyy
    refine disjoint_of_mem_fillingIndex hq (hmem _ _ hx.2) (hmem _ _ hyy.2) ?_
    intro hpair
    exact hne (Sigma.ext (congrArg Prod.fst hpair) (heq_of_eq (congrArg Prod.snd hpair)))
  have hmeas : ∀ x ∈ (R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))),
      MeasurableSet (adaptedCellAt q x.1 x.2) := fun x _ =>
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq x.1 x.2).isOpen.measurableSet
  have hsub : (⋃ x ∈ (R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))),
      adaptedCellAt q x.1 x.2) ⊆ W := by
    refine Set.iUnion₂_subset fun x hx => ?_
    rw [Finset.mem_sigma] at hx
    exact adaptedCellAt_subset_of_mem_fillingIndex (hmem _ _ hx.2)
  have hsum : ∑ x ∈ (R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))),
      volume (adaptedCellAt q x.1 x.2) ≤ volume W := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  have hWtop : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top p j y
  have hWpos : (0 : ℝ) < (volume W).toReal :=
    ENNReal.toReal_pos (volume_adaptedCellTranslate_ne_zero hp j y) hWtop
  have hcelltop : ∀ x : (_ : ℤ) × (Fin d → ℤ), volume (adaptedCellAt q x.1 x.2) ≠ ⊤ := by
    intro x
    rw [Transport.adaptedCellAt_eq_adaptedCellTranslate]
    exact volume_adaptedCellTranslate_ne_top q x.1 _
  have hreal : ∑ x ∈ (R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))),
      (volume (adaptedCellAt q x.1 x.2)).toReal ≤ (volume W).toReal := by
    rw [← ENNReal.toReal_sum fun x _ => hcelltop x]
    exact ENNReal.toReal_mono hWtop hsum
  have hsplit : ∑ r ∈ R, ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
      (volume W).toReal =
      (∑ x ∈ (R.sigma Z : Finset ((_ : ℤ) × (Fin d → ℤ))),
        (volume (adaptedCellAt q x.1 x.2)).toReal) / (volume W).toReal := by
    rw [Finset.sum_div, Finset.sum_sigma']
  rw [hsplit, div_le_one hWpos]
  exact hreal

/-! ## The mean of the exhaustion -/

/-- **The annealed form of `e.two.grid.whitney.average`.**  Averaging the
pathwise domination of the target's coarse response by the weighted responses of
the filling plus the below-start term gives the same domination between the
annealed blocks, with the mean of the below-start term as the remainder.

Averaging is monotone for the Loewner order, and the integral of the finite
weighted sum is the weighted sum of the integrals; the only hypotheses are the
integrability of the target, of each selected cell, and of the below-start
term. -/
theorem annealedBlock_le_of_ae_le {P : Measure (CoeffSpace d)} {W : Set (Vec d)}
    {q : Mat d} {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)}
    {theta : ℤ → (Fin d → ℤ) → ℝ} {Gm : CoeffSpace d → FullBlockMat d}
    (hW : HasIntegrableCoarseBlock P W)
    (hcell : ∀ r ∈ R, ∀ w ∈ Z r, HasIntegrableCoarseBlock P (adaptedCellAt q r w))
    (hG : Integrable Gm P)
    (hpath : ∀ᵐ a ∂P, toFullBlockMat (coarseBlock W a) ≤
      ∑ r ∈ R, ∑ w ∈ Z r,
          theta r w • toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) + Gm a) :
    toFullBlockMat (annealedBlock P W) ≤
      ∑ r ∈ R, ∑ w ∈ Z r,
          theta r w • toFullBlockMat (annealedBlock P (adaptedCellAt q r w)) +
        ∫ a, Gm a ∂P := by
  classical
  have hintcell : ∀ r ∈ R, ∀ w ∈ Z r,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) P :=
    fun r hr w hw => integrable_toFullBlockMat (hcell r hr w hw)
  -- The generic finite-sum integral lemma resolves its ambient norm on the
  -- flattened carrier through the operator-norm scope, while the coarse
  -- response's own integrability comes from the entrywise one; the two
  -- interfaces are bridged entry by entry rather than at the matrix level.
  have hentryCell : ∀ r ∈ R, ∀ w ∈ Z r, ∀ α β : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) α β) P :=
    fun r hr w hw α β => ((hintcell r hr w hw).eval α).eval β
  have hentryTerm : ∀ r ∈ R, ∀ w ∈ Z r, ∀ α β : BlockCoord d,
      Integrable (fun a =>
        theta r w * toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) α β) P :=
    fun r hr w hw α β => (hentryCell r hr w hw α β).const_mul (theta r w)
  have hGentry : ∀ α β : BlockCoord d, Integrable (fun a => Gm a α β) P :=
    fun α β => (hG.eval α).eval β
  have hintmaj : Integrable (fun a => ∑ r ∈ R, ∑ w ∈ Z r,
      theta r w • toFullBlockMat (coarseBlock (adaptedCellAt q r w) a) + Gm a) P :=
    integrable_of_entries fun α β => by
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      exact (integrable_finsetSum R fun r hr =>
        integrable_finsetSum (Z r) fun w hw => hentryTerm r hr w hw α β).add (hGentry α β)
  have hmono := integral_mono' (integrable_toFullBlockMat hW) hintmaj hpath
  rw [toFullBlockMat_annealedBlock hW]
  refine hmono.trans (le_of_eq ?_)
  ext α β
  rw [Matrix.add_apply, entry_integral hintmaj α β, entry_integral hG α β]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_add
      (integrable_finsetSum R fun r hr =>
        integrable_finsetSum (Z r) fun w hw => hentryTerm r hr w hw α β)
      (hGentry α β)]
  refine congrArg (· + ∫ a, Gm a α β ∂P) ?_
  rw [integral_finsetSum R fun r hr =>
    integrable_finsetSum (Z r) fun w hw => hentryTerm r hr w hw α β]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [integral_finsetSum (Z r) fun w hw => hentryTerm r hr w hw α β]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [integral_const_mul, ← entry_integral (hintcell r hr w hw) α β,
    ← toFullBlockMat_annealedBlock (hcell r hr w hw)]

/-! ## The bridge normalization of the mean domination -/

/-- **The bridge congruence carries the old relative mean onto the new
normalization.**  With `S = (E_t^q)^{1/2}(E_n^{q'})^{-1/2}`, the congruence
`S^tP_{r,t}^qS` is the normalization of `E_r^q` by the new terminal block, the
two square roots of the old terminal block cancelling.  This is the identity
behind `e.two.grid.whitney.mean.bound`: the bridge never sees an individual
cell response, only the terminal normalization. -/
theorem bridgeMap_conj_relMean {P : Measure (CoeffSpace d)} {q q' : Mat d} {r t n : ℤ}
    (hH : (toFullBlockMat (adaptedMean P q t)).PosDef)
    (hF : (toFullBlockMat (adaptedMean P q' n)).PosDef) :
    (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
        toFullBlockMat (relMean P q r t) *
        bridgeMap (adaptedMean P q t) (adaptedMean P q' n) =
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
        toFullBlockMat (adaptedMean P q r) *
        matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) := by
  have hSt : (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ =
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
        matSqrt (toFullBlockMat (adaptedMean P q t)) := by
    rw [bridgeMap, Matrix.transpose_mul, transpose_matSqrt_inv hF,
      ← conjTranspose_eq_transpose' (matSqrt (toFullBlockMat (adaptedMean P q t))),
      (matSqrt_spec hH.posSemidef).1.isHermitian]
  rw [relMean, normalizedBlock, toFullBlockMat_ofFullBlockMat, hSt, bridgeMap]
  calc matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
        matSqrt (toFullBlockMat (adaptedMean P q t)) *
        (matSqrt ((toFullBlockMat (adaptedMean P q t))⁻¹) *
          toFullBlockMat (adaptedMean P q r) *
          matSqrt ((toFullBlockMat (adaptedMean P q t))⁻¹)) *
        (matSqrt (toFullBlockMat (adaptedMean P q t)) *
          matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹))
      = matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) *
          ((matSqrt (toFullBlockMat (adaptedMean P q t)) *
              matSqrt ((toFullBlockMat (adaptedMean P q t))⁻¹)) *
            toFullBlockMat (adaptedMean P q r) *
            (matSqrt ((toFullBlockMat (adaptedMean P q t))⁻¹) *
              matSqrt (toFullBlockMat (adaptedMean P q t)))) *
          matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) := by
        noncomm_ring
    _ = _ := by
        rw [matSqrt_mul_matSqrt_inv hH, matSqrt_inv_mul_matSqrt hH,
          Matrix.one_mul, Matrix.mul_one]

/-- **The normalized mean domination**, in the exact shape the cell gap of
`e.two.grid.whitney.mean.bound` and the nonlinear row consume:
`P_{j,n}^{q'} ≤ S^tP_bar_WS - (1-m_W)S^tS + R_W`.

Conjugating the annealed domination by the inverse square root of the new
terminal block is monotone, the bridge carries each old relative mean onto the
new normalization, and the unfilled mass is exactly the identity part of the
convex combination `P_bar_W`. -/
theorem relMean_le_of_annealedBlock_le {P : Measure (CoeffSpace d)} {q q' : Mat d}
    {j n t : ℤ} {R : Finset ℤ} {theta : ℤ → ℝ} {Pbar Rm : BlockMat d}
    {G : FullBlockMat d}
    (hH : (toFullBlockMat (adaptedMean P q t)).PosDef)
    (hF : (toFullBlockMat (adaptedMean P q' n)).PosDef)
    (hPbar : toFullBlockMat Pbar =
      ∑ r ∈ R, theta r • toFullBlockMat (relMean P q r t) +
        (1 - ∑ r ∈ R, theta r) • (1 : FullBlockMat d))
    (hRm : toFullBlockMat Rm =
      matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) * G *
        matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹))
    (hdom : toFullBlockMat (adaptedMean P q' j) ≤
      ∑ r ∈ R, theta r • toFullBlockMat (adaptedMean P q r) + G) :
    toFullBlockMat (relMean P q' j n) ≤
      (bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ * toFullBlockMat Pbar *
          bridgeMap (adaptedMean P q t) (adaptedMean P q' n) -
        (1 - ∑ r ∈ R, theta r) •
          ((bridgeMap (adaptedMean P q t) (adaptedMean P q' n))ᵀ *
            bridgeMap (adaptedMean P q t) (adaptedMean P q' n)) +
        toFullBlockMat Rm := by
  classical
  set C : FullBlockMat d := matSqrt ((toFullBlockMat (adaptedMean P q' n))⁻¹) with hC
  set S : FullBlockMat d := bridgeMap (adaptedMean P q t) (adaptedMean P q' n) with hS
  have hCherm : Cᴴ = C := by
    rw [hC, conjTranspose_eq_transpose']
    exact transpose_matSqrt_inv hF
  have hcarry : ∀ r : ℤ, Sᵀ * toFullBlockMat (relMean P q r t) * S =
      C * toFullBlockMat (adaptedMean P q r) * C := fun r => by
    rw [hS, hC]
    exact bridgeMap_conj_relMean hH hF
  have hconj := conj_le_conj' (C := C) hCherm hdom
  have hleft : C * toFullBlockMat (adaptedMean P q' j) * C =
      toFullBlockMat (relMean P q' j n) := by
    rw [relMean, normalizedBlock, toFullBlockMat_ofFullBlockMat, hC]
  have hL : C * (∑ r ∈ R, theta r • toFullBlockMat (adaptedMean P q r) + G) * C =
      (∑ r ∈ R, theta r • (C * toFullBlockMat (adaptedMean P q r) * C)) + C * G * C := by
    rw [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
    refine congrArg (· + C * G * C) (Finset.sum_congr rfl fun r _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hR2 : Sᵀ * toFullBlockMat Pbar * S =
      (∑ r ∈ R, theta r • (C * toFullBlockMat (adaptedMean P q r) * C)) +
        (1 - ∑ r ∈ R, theta r) • (Sᵀ * S) := by
    rw [hPbar, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
    have hlast : Sᵀ * ((1 - ∑ r ∈ R, theta r) • (1 : FullBlockMat d)) * S =
        (1 - ∑ r ∈ R, theta r) • (Sᵀ * S) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hlast]
    refine congrArg (· + (1 - ∑ r ∈ R, theta r) • (Sᵀ * S))
      (Finset.sum_congr rfl fun r _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul, hcarry r]
  have hright : C * (∑ r ∈ R, theta r • toFullBlockMat (adaptedMean P q r) + G) * C =
      Sᵀ * toFullBlockMat Pbar * S -
        (1 - ∑ r ∈ R, theta r) • (Sᵀ * S) + toFullBlockMat Rm := by
    rw [hL, hR2, hRm]
    abel
  rw [← hleft, ← hright]
  exact hconj

end

end Transport
end HighContrast
end HCPolySupport
