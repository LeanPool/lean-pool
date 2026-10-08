/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseFormulas
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenteringAdjointIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The closed form of the adjoint centering pairing

The adjoint mirror of the centering-pairing identity: at the recentered
samples of the transposed coefficient, the pairing of the two annealed adjoint
optimizer averages has a closed form in the Schur data of the annealed block.
It is the primal closed form with the symmetric skew coordinate negated.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The adjoint centering pairing in closed Schur form.** -/
theorem centering_adjoint_pairing_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p r : Vec d) :
    vecDot
        (fun i ↦ ∫ a, averageGradient U
          ((a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K)).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U
            (a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)) p r) i ∂P)
        (fun i ↦ ∫ a, averageFlux U
          ((a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K)).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U
            (a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)) p r) i ∂P) =
      p ⬝ᵥ S *ᵥ p +
        (r - Response.responseSymmetric K *ᵥ p) ⬝ᵥ
          SStar⁻¹ *ᵥ (r - Response.responseSymmetric K *ᵥ p) -
        p ⬝ᵥ r +
        (r - Response.responseSymmetric K *ᵥ p) ⬝ᵥ
          (SStar⁻¹ * K * SStar⁻¹) *ᵥ (r - Response.responseSymmetric K *ᵥ p) -
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (r - Response.responseSymmetric K *ᵥ p) := by
  set g : Mat d := Response.responseSkew K with hgdef
  have hg : IsSkewMat g := by
    rw [hgdef]
    exact Response.is_skew_mat_response_skew K
  set q₀ : Vec d := r + matVecMul g p with hq₀
  -- the adjoint bridge
  have hbridge := Response.centeredAdjointResponse_subSkew U hint g hg p r
  rw [← hq₀] at hbridge
  -- covariance of the annealed adjoint energy
  have hneg : matVecMul (-g) p = -(matVecMul g p) := by
    funext i
    change ∑ j, (-g) i j * p j = -(∑ j, g i j * p j)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.neg_apply]
    ring
  have hres : (∫ a, responseJ U
        ((a.subSkew g hg).transpose.coeffOn U) p r ∂P) =
      ∫ a, responseJ U (a.transpose.coeffOn U) p q₀ ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
    change responseJ U ((a.subSkew g hg).transpose.coeffOn U) p r =
      responseJ U (a.transpose.coeffOn U) p q₀
    rw [CoeffSpace.transpose_subSkew]
    have h := Response.responseJ_subSkew U a.transpose (-g)
      (Response.isSkewMat_neg hg) p r
    have hload : r - matVecMul (-g) p = q₀ := by
      rw [hneg, sub_neg_eq_add, hq₀]
    rw [hload] at h
    exact h
  rw [hres] at hbridge
  -- the two annealed adjoint Schur formulas at the shifted load
  have hJ := Response.annealed_adjoint_responseJ_schur U hint hE p q₀
  have hcR := Response.centeredAdjointResponse_eq_schur U hint hStar hE p q₀
  rw [hJ, hcR] at hbridge
  -- the shifted vector is the negated symmetric-skew vector
  have hw : q₀ - K *ᵥ p = r - Response.responseSymmetric K *ᵥ p := by
    have hmv : matVecMul g p = g *ᵥ p := rfl
    have hsub : K *ᵥ p - g *ᵥ p = Response.responseSymmetric K *ᵥ p := by
      rw [← Matrix.sub_mulVec, hgdef, Response.sub_responseSkew]
    calc
      q₀ - K *ᵥ p = r + g *ᵥ p - K *ᵥ p := by rw [hq₀, hmv]
      _ = r - (K *ᵥ p - g *ᵥ p) := by abel
      _ = r - Response.responseSymmetric K *ᵥ p := by rw [hsub]
  rw [hw] at hbridge
  -- the skew coordinate is invisible to the load pairing
  have hgstar : Matrix.conjTranspose g = -g := by
    rwa [conjTranspose_eq_transpose']
  have hskewzero : p ⬝ᵥ g *ᵥ p = 0 :=
    Response.dotProduct_mulVec_of_skew hgstar p
  have hpq1 : vecDot p q₀ = p ⬝ᵥ r := by
    change p ⬝ᵥ q₀ = p ⬝ᵥ r
    rw [hq₀]
    change p ⬝ᵥ (r + g *ᵥ p) = p ⬝ᵥ r
    rw [dotProduct_add, hskewzero, add_zero]
  have hpq2 : p ⬝ᵥ q₀ = p ⬝ᵥ r := hpq1
  rw [hpq1, hpq2] at hbridge
  -- conclude
  have hkey :
      vecDot
          (fun i ↦ ∫ a, averageGradient U
            ((a.subSkew g hg).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U (a.subSkew g hg) p r) i ∂P)
          (fun i ↦ ∫ a, averageFlux U
            ((a.subSkew g hg).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U (a.subSkew g hg) p r) i ∂P) =
        p ⬝ᵥ S *ᵥ p +
          (r - Response.responseSymmetric K *ᵥ p) ⬝ᵥ
            SStar⁻¹ *ᵥ (r - Response.responseSymmetric K *ᵥ p) -
          p ⬝ᵥ r +
          (r - Response.responseSymmetric K *ᵥ p) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (r - Response.responseSymmetric K *ᵥ p) -
          ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (r - Response.responseSymmetric K *ᵥ p) := by
      linarith only [hbridge]
  exact hkey

end

end HCPolySupport.HighContrast.Quenched
