/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointHeadEnergyCarrier
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalWeakNormAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.HeadCellDeficitInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.QuadraticResponseRecombination
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RandomToAnnealedRecentring
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.AdjointRecentHeadEstimate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adjoint recent head, and the optimizer-energy partition it needs

This file completes, for the adjoint response coefficient, the recent head of the diagonal
weak-norm estimate: the two-halved assembly and the resulting bound at the estimate's own
carriers. It also proves that the pathwise optimizer energy of a parent adapted cell recombines,
in general and then on the adapted-cell tree, into the flat average of the depth-`n` subcell
energies, and establishes the integrability on the estimate's own cell of the doubled optimizer
field for both the recentred and adjoint coefficients — inputs the energy bound and the
cell-average steps both require.  It serves the cell-average estimate `l.weaknorms.moreproto`.
-/

section
/-!
## The recent head of the cell-average estimate, adjoint sign

The weak-norm estimate for the response controls the recent head of the cell-average defect for
two reflected coefficients: the recentred field `a_- = a - g` with response matrix
`E_-^t = respEhatMinus`, and the adjoint field `a_+ = a^t + g` with adjoint response matrix
`E_+^t = respEhatPlus`.  This file assembles the adjoint head: the one-sided `weakCellSum` half,
the `weakAverageSum` half, their composition into the printed summand, and the reduction of the
per-scale analytic input through the two energy facts.  Every statement is the adjoint-sign
counterpart of its recentred-sign original; only the carrier changes, and no constant or binder
order moves.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The `weakCellSum` half of the recent-head cell-average estimate for the adjoint sample
`a_+ = respCoeffPlus F a`, stated against the metric factor the estimate prints.  The spectral
bound `sqrt (blockSpecBound (normalizedBlock E_+ M_0))` replaces the operator norm delivered by
the reflected-defect comparison; on positive definite `E_+` and `M_0` the two coincide.  This is
the cell half of the response weak-norm estimate. -/
theorem weakCellSum_half_specBound_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
              (respCoeffPlus F a) := by
  obtain ⟨V, hV⟩ := weakCellSum_half_le_plus P jStar F t e hgrid a H u hu hE
  exact ⟨V, by rwa [respK0_specBound_eq_norm_plus P jStar F t hE hM0]⟩

/-- The two-halves composition for the adjoint sample with the child-maximizer family produced
before the per-scale analytic constraint: the same maximizer family then serves every admissible
per-scale family `A`.  The maximizers are chosen from the cell half alone, so moving `exists V`
outside `forall A` is a binder reorder and strictly strengthens the statement. -/
theorem recentHead_halves_forall_le_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∀ A : ℕ → ℝ,
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))) + A n)
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) with hK
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hL
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Real.sqrt_nonneg _
  obtain ⟨V, hV⟩ := weakCellSum_half_specBound_le_plus P jStar F t e hgrid a H u hu hE hM0
  refine ⟨V, fun A hscale => ?_⟩
  have hav := weakAverageSum_half_le_plus (K := K) (L := L) P γ hγ jStar H F t a hK0 hL0 A hE
    hgood hscale
  have hcs0 : (0 : ℝ) ≤ weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
      (respCoeffPlus F a) := weakCellSum_nonneg _ _ _ _ _
  have has0 : (0 : ℝ) ≤ weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
      (respEhatPlus P jStar F t) (respCoeffPlus F a) := weakAverageSum_nonneg _ _ _ _ _ _
  have hsplit : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))) + A n)
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffPlus F a) u))))
          + (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n := fun n _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hKL0 : (0 : ℝ) ≤ K * L := mul_nonneg hK0 hL0
  rw [← hK, ← hL] at hV
  refine (add_le_add hV hav).trans ?_
  have hcs16 : weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
        (respCoeffPlus F a)
      ≤ 16 * weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
        (respCoeffPlus F a) :=
    le_mul_of_one_le_left hcs0 (by norm_num : (1 : ℝ) ≤ 16)
  have has416 : 4 * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
        (respEhatPlus P jStar F t) (respCoeffPlus F a)
      ≤ 16 * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
        (respEhatPlus P jStar F t) (respCoeffPlus F a) :=
    mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 16) has0
  calc
    K * L * weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
          (respCoeffPlus F a)
        + 4 * K * L * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
            (respEhatPlus P jStar F t) (respCoeffPlus F a)
        = K * L * (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a)
              + 4 * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                  (respEhatPlus P jStar F t) (respCoeffPlus F a)) := by ring
    _ ≤ K * L * (16 * (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a)
              + weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                  (respEhatPlus P jStar F t) (respCoeffPlus F a))) := by
        apply mul_le_mul_of_nonneg_left _ hKL0
        calc
          weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a)
              + 4 * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                  (respEhatPlus P jStar F t) (respCoeffPlus F a)
              ≤ 16 * weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                    (respCoeffPlus F a)
                + 16 * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                    (respEhatPlus P jStar F t) (respCoeffPlus F a) :=
              add_le_add hcs16 has416
          _ = 16 * (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                    (respCoeffPlus F a)
                + weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                    (respEhatPlus P jStar F t) (respCoeffPlus F a)) := by ring
    _ = 16 * K * L * (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
              (respCoeffPlus F a)
            + weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
                (respEhatPlus P jStar F t) (respCoeffPlus F a)) := by ring

/-- The recent head of the cell-average estimate for the adjoint sample, against the actual parent
optimizer rather than a family of child maximizers.  The child maximizers are eliminated by the
recent-scale decomposition and the per-scale family is restricted to the explicit average-defect
family, leaving the analytic per-scale input as the only remaining hypothesis. -/
theorem recentHead_actual_le_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffPlus F a) u x -
                          optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffPlus F a) u x -
                          optimizerField (respCoeffPlus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))) ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  obtain ⟨V, hV⟩ := recentHead_halves_forall_le_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood
  refine ⟨V, fun h1v h2v hscale => ?_⟩
  refine le_trans ?_ (hV _ hscale)
  exact recentHead_scaleDecomposition_box_le (respGrid jStar F) t H (blockSqrt (respM0 F))
    (optimizerField (respCoeffPlus F a) u)
    (fun n w => optimizerField (respCoeffPlus F a)
      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))
    h1u h2u h1v h2v

/-- The recent head for the adjoint sample reduced to the two analytic energy facts.  The per-scale
input is discharged through `scaleInput_of_analytic_plus`: a per-cell energy family `G` bounds
the quadratic defect cellwise and its cell average is controlled by the response load
`respLsqPlus` times the averaged recent-defect size.  The side condition `0 <= respLsqPlus` is
discharged from the positive definiteness of the adjoint response matrix.  This is the adjoint
counterpart of the reduction of the recent-head estimate to the energy-map and difference-energy
bounds. -/
theorem recentHead_actual_of_analytic_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, ∃ G : (Fin d → ℤ) → ℝ,
        (∀ w ∈ triadicIndexBox d n,
          blockVecDot
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffPlus F a) u x -
                    optimizerField (respCoeffPlus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffPlus F a) u x -
                    optimizerField (respCoeffPlus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
            ≤ (Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
                * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                    * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 * G w) ∧
        ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
          ≤ 2 * respLsqPlus P jStar F t e
              * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
                  (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqPlus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
                (respCoeffPlus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
  classical
  -- The former side hypothesis `hLsq`, now discharged from `hE`.
  have hLsq : 0 ≤ respLsqPlus P jStar F t e := by
    rw [respLsqPlus]
    exact blockVecDot_nonneg_of_posSemidef _ hE.posSemidef _
  obtain ⟨V, hV⟩ := recentHead_actual_le_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine ⟨V, fun h1v h2v hin => hV h1v h2v (fun n => ?_)⟩
  obtain ⟨G, hcell, henergy⟩ := hin n
  exact scaleInput_of_analytic_plus P γ jStar F t e a n
    (fun w x => optimizerField (respCoeffPlus F a) u x -
      optimizerField (respCoeffPlus F a)
        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)
    G hLsq hcell henergy

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The finite-window head of the cell-average estimate at the carriers, adjoint sign

The recent head of `l.weaknorms.moreproto` is bounded by the two finite defect sums once two
analytic facts are supplied at each depth: a per-cell metric bound for the recent difference of
the parent optimizer and a child optimizer, and an averaged bound for the difference energies.
Both are now available at the estimate's own grid, sample, metric and maximizer, so the head
carries no analytic hypothesis of its own: the coefficient's positive definiteness comes from the
law-integrability of the coarse block on the cell, and every geometric input from invertibility of
the selected grid.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The finite-window head of the cell-average estimate, at the carriers.**  On the branch
where the all-scale maximum does not exceed `1`, the `3^{-n/2}`-weighted sum over the window
`n ≤ H` of the normalized `L²` averages of the recentred transported subcell averages is bounded
by `16 K L` times the sum of the two finite defect sums, where `K` is the square root of the
printed spectral bound of the normalized reference block and `L` the square root of the response
load. -/
theorem recentHead_carrier_plus (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a) u) -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffPlus F a) u))))
      ≤ 16 *
          Real.sqrt
            (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqPlus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
              (respCoeffPlus F a) +
            weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
              (respCoeffPlus F a)) := by
  classical
  have hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    respEhatPlus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    respMean_posDef_of_integrable hgrid t hint
  have h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hgrid t F a u n w
      hw j).1
  have h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun n _ w hw j =>
    (integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hgrid t F a u n w
      hw j).2
  obtain ⟨V, hV⟩ :=
    recentHead_actual_of_analytic_plus P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine hV (fun n _ w _ j =>
      (integrableOn_optimizerField_respCoeffPlus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).1)
    (fun n _ w _ j =>
      (integrableOn_optimizerField_respCoeffPlus_at (respGrid jStar F) hgrid
        (t - (n : ℤ)) w F a ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) j).2)
    (fun n => ?_)
  refine ⟨fun w => 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
    (fun x => vecDot
      (optimizerField (respCoeffPlus F a) u x -
        optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1
      (optimizerField (respCoeffPlus F a) u x -
        optimizerField (respCoeffPlus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2), ?_, ?_⟩
  · exact headCell_of_bridge_plus P γ jStar F t hgrid a n u
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) hm hEmean hE hM0 hbdd
  · exact headEnergy_carrier_plus P jStar F t e hgrid a n u hu
      (fun w => (V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)
      (fun w _ => (V n w).isMaximizer) hE

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The parent optimizer energy recombines over the depth-`n` subcells

The pathwise normalized optimizer energy `weakOptimizerEnergy U b u` is the square root of the
average of the doubled-optimizer energy density `x ↦ (X x).1 · (X x).2`, where `X = optimizerField
b u` is the doubled optimizer field.  The first statement below squares that definition: on a
region where the average is nonnegative, squaring the energy recovers the average.

The second statement is the partition identity that lets the per-cell energy map recombine into
the parent energy.  When the parent adapted cell is the almost-everywhere disjoint union of its
`3^{nd}` aligned depth-`n` subcells, all of them of equal volume, the *unweighted* flat average of
the subcell energy averages is the parent average.  The equal-volume hypothesis is what makes the
unweighted mean correct; without it the recombination would have to be the volume-weighted sum
`∑_w (|V w| / |U|) ⨍_{V w} g`.  It is stated through `.toReal`, and together with the positivity of
the parent volume it excludes a zero-volume subcell: a zero-volume cell would force the left side
of `hvolw` to vanish while the right side is positive.  The almost-everywhere partition step itself
is `average_over_aePartition`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Squaring the pathwise normalized optimizer energy recovers the average of the doubled field's
energy density, as soon as that average is nonnegative. -/
theorem sq_weakOptimizerEnergy {U : Set (Vec d)} (b : CoeffField d)
    (u : AHarmonicFunction b U)
    (hnn : 0 ≤ volumeAverage U (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2)) :
    weakOptimizerEnergy U b u ^ 2
      = volumeAverage U (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2) :=
  Real.sq_sqrt hnn

omit [NeZero d] in
/-- **The parent optimizer energy recombines over the depth-`n` subcells.**  Under the
almost-everywhere partition hypotheses, the flat average over the `3^{nd}` aligned depth-`n`
subcells of their energy averages is the squared pathwise optimizer energy of the parent adapted
cell. -/
theorem parent_energy_partition (q : Mat d) (t : ℤ) (n : ℕ) (b : CoeffField d)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
    (hmeas : ∀ w ∈ triadicIndexBox d n,
      MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hdisj : ∀ w ∈ triadicIndexBox d n, ∀ w' ∈ triadicIndexBox d n, w ≠ w' →
      Disjoint (adaptedCellAtCenter q (t - (n : ℤ)) w) (adaptedCellAtCenter q (t - (n : ℤ)) w'))
    (hsub : ∀ w ∈ triadicIndexBox d n,
      adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t)
    (hnull : volume (HighContrast.adaptedCell q t \
        ⋃ w ∈ triadicIndexBox d n, adaptedCellAtCenter q (t - (n : ℤ)) w) = 0)
    (hvolw : ∀ w ∈ triadicIndexBox d n,
      ((triadicIndexBox d n).card : ℝ) * (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal
        = (volume (HighContrast.adaptedCell q t)).toReal)
    (hint : IntegrableOn
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      (HighContrast.adaptedCell q t))
    (hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal)
    (hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hmain := average_over_aePartition (Z := triadicIndexBox d n)
    (V := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (U := HighContrast.adaptedCell q t)
    (g := fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
    hmeas hdisj hsub hnull hvolw hint hUpos hUfin hZne
  rw [sq_weakOptimizerEnergy (U := HighContrast.adaptedCell q t) b u hnn]
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The parent optimizer energy partition at the adapted cells

The partition identity recombines the flat average of the depth-`n` subcell energy averages
into the squared pathwise optimizer energy of the parent adapted cell.  In its general form
that identity carries nine geometric and integrability hypotheses.  For the aligned adapted
cells every geometric one of them is supplied by `IsUnit q` and the tree's cell lemmas: the
subcells are open hence measurable, pairwise disjoint, contained in the parent, omit only the
null grid seams, and have equal volume, and the parent cell has positive finite volume.  This
file discharges those hypotheses and lands the clean statement.

The nonnegativity of the averaged doubled-optimizer density and its integrability are not
available from `IsUnit q` alone: the coefficient field is an arbitrary matrix-valued field, so
`x ↦ (X x).1 · (X x).2` need not be nonnegative and need not be integrable.  They remain
explicit hypotheses rather than being replaced by a stronger ellipticity assumption.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The parent optimizer energy partition at the adapted cells.**  For an invertible grid
`q`, generation `t` and depth `n`, the flat average over the `3^{nd}` aligned depth-`n`
subcells of their averaged doubled-optimizer energy densities equals the squared pathwise
normalized optimizer energy of the parent adapted cell `HighContrast.adaptedCell q t`.  Every
geometric and finiteness hypothesis of the general partition identity is discharged from
`IsUnit q`; only the nonnegativity and the integrability of the averaged density remain as
hypotheses. -/
theorem parent_energy_partition_cell (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hnn : 0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2))
    (hint : IntegrableOn
      (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2)
      = weakOptimizerEnergy (HighContrast.adaptedCell q t) b u ^ 2 := by
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
  exact parent_energy_partition q t n b u hnn
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => volume_adaptedCellAtCenter_card_eq q hq t n w)
    hint hUpos hUfin

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the doubled optimizer field on the estimate's own cell

The cell-average steps of the diagonal weak-norm estimate move a matrix through the cell average
of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`.  Integrability of both slots and
of the scalar self-pairing `x ↦ blockVecDot X(x) X(x)` is needed on the estimate's own adapted
cell, not only on its aligned subcells.

The two slots are handled as in the subcell statements.  The gradient slot is the weak gradient of
an `H¹` function and is `L²` with no ellipticity hypothesis.  The flux slot `x ↦ b(x) ∇u(x)` is
`L²` because the tree supplies an a.e.-equal representative that is pointwise elliptic on the cell
(`exists_elliptic_representative_respCoeffMinus`, `…Plus`); the two fields agree almost everywhere,
so integrability transfers.  The self-pairing is `L¹` because the product of two `L²` scalar
components is `L¹` (Cauchy-Schwarz), and finite-measure `L²` is `L¹`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` -/

/-- **Both slots of the doubled optimizer field are `L²` on the adapted cell, for
`respCoeffMinus F a`.**  The gradient slot is the weak gradient of the `H¹` function carried by
the `AHarmonicFunction`, and the flux slot is `L²` through the a.e.-equal pointwise elliptic
representative of `respCoeffMinus F a` on the cell. -/
theorem memVectorL2_optimizerField_respCoeffMinus_cell (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (optimizerField (respCoeffMinus F a) u x).1) ∧
      MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (optimizerField (respCoeffMinus F a) u x).2) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using u.toH1.grad_memVectorL2
  · simpa [optimizerField] using
      memVectorL2_optimizerField_flux_of_aeEq (subset_refl _) hEll hae u

/-- **Both slots of the doubled optimizer field are integrable on the adapted cell, for
`respCoeffMinus F a`.**  Square-integrability on the finite-measure adapted cell gives
integrability of each component. -/
theorem integrableOn_optimizerField_respCoeffMinus_cell (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (HighContrast.adaptedCell q t) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (HighContrast.adaptedCell q t) := by
  obtain ⟨hmem1, hmem2⟩ :=
    memVectorL2_optimizerField_respCoeffMinus_cell q hq t F a u
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  exact ⟨MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem1) j),
    MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem2) j)⟩

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` -/

/-- **Both slots of the doubled optimizer field are `L²` on the adapted cell, for
`respCoeffPlus F a`.**  The transposed twin of
`memVectorL2_optimizerField_respCoeffMinus_cell`. -/
theorem memVectorL2_optimizerField_respCoeffPlus_cell (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (optimizerField (respCoeffPlus F a) u x).1) ∧
      MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (optimizerField (respCoeffPlus F a) u x).2) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using u.toH1.grad_memVectorL2
  · simpa [optimizerField] using
      memVectorL2_optimizerField_flux_of_aeEq (subset_refl _) hEll hae u

/-- **Both slots of the doubled optimizer field are integrable on the adapted cell, for
`respCoeffPlus F a`.**  The transposed twin of
`integrableOn_optimizerField_respCoeffMinus_cell`. -/
theorem integrableOn_optimizerField_respCoeffPlus_cell (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (HighContrast.adaptedCell q t) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (HighContrast.adaptedCell q t) := by
  obtain ⟨hmem1, hmem2⟩ :=
    memVectorL2_optimizerField_respCoeffPlus_cell q hq t F a u
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  exact ⟨MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem1) j),
    MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem2) j)⟩

end

end HCPolySupport.HighContrast.Multiscale
end
