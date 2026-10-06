/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseFormulas
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenteringIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The closed form of the centering pairing

The centering term of the compact response reabsorption is the pairing of the
two annealed optimizer averages at the recentered samples.  Constant-skew
covariance and the two annealed Schur formulas give it a closed form in the
Schur data of the annealed block: every appearance of the antisymmetric skew
part cancels, leaving an expression in the symmetric skew coordinate alone.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The centering pairing in closed Schur form.** -/
theorem centering_pairing_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Book.Ch02.Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) (p r : Vec d) :
    vecDot
        (fun i ↦ ∫ a, averageGradient U
          ((a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K)).coeffOn U)
          (Response.centeredResponseOptimizer U
            (a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)) p r) i ∂P)
        (fun i ↦ ∫ a, averageFlux U
          ((a.subSkew (Response.responseSkew K)
            (Response.is_skew_mat_response_skew K)).coeffOn U)
          (Response.centeredResponseOptimizer U
            (a.subSkew (Response.responseSkew K)
              (Response.is_skew_mat_response_skew K)) p r) i ∂P) =
      p ⬝ᵥ S *ᵥ p +
        (r + Response.responseSymmetric K *ᵥ p) ⬝ᵥ
          SStar⁻¹ *ᵥ (r + Response.responseSymmetric K *ᵥ p) -
        p ⬝ᵥ r -
        (r + Response.responseSymmetric K *ᵥ p) ⬝ᵥ
          (SStar⁻¹ * K * SStar⁻¹) *ᵥ (r + Response.responseSymmetric K *ᵥ p) -
        ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (r + Response.responseSymmetric K *ᵥ p) := by
  set g : Mat d := Response.responseSkew K with hgdef
  have hg : IsSkewMat g := by
    rw [hgdef]
    exact Response.is_skew_mat_response_skew K
  set q₀ : Vec d := r - matVecMul g p with hq₀
  -- the bridge: recentered energy minus half the pairing is the centered call
  have hbridge := Response.centeredResponse_subSkew U hint g hg p r
  rw [← hq₀] at hbridge
  -- covariance of the annealed energy
  have hres : (∫ a, responseJ U ((a.subSkew g hg).coeffOn U) p r ∂P) =
      ∫ a, responseJ U (a.coeffOn U) p q₀ ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun a ↦
      Response.responseJ_subSkew U a g hg p r)
  rw [hres] at hbridge
  -- the two annealed Schur formulas at the shifted load
  have hJ := Response.annealed_responseJ_schur U hint hE p q₀
  have hcR := Response.centeredResponse_eq_schur U hint hStar hE p q₀
  rw [hJ, hcR] at hbridge
  -- the shifted vector is the symmetric-skew vector
  have hw : q₀ + K *ᵥ p = r + Response.responseSymmetric K *ᵥ p := by
    have hmv : matVecMul g p = g *ᵥ p := rfl
    have hsub : K *ᵥ p - g *ᵥ p = Response.responseSymmetric K *ᵥ p := by
      rw [← Matrix.sub_mulVec, hgdef, Response.sub_responseSkew]
    calc
      q₀ + K *ᵥ p = r - g *ᵥ p + K *ᵥ p := by rw [hq₀, hmv]
      _ = r + (K *ᵥ p - g *ᵥ p) := by abel
      _ = r + Response.responseSymmetric K *ᵥ p := by rw [hsub]
  rw [hw] at hbridge
  -- the skew coordinate is invisible to the load pairing
  have hgstar : Matrix.conjTranspose g = -g := by
    rwa [conjTranspose_eq_transpose']
  have hskewzero : p ⬝ᵥ g *ᵥ p = 0 :=
    Response.dotProduct_mulVec_of_skew hgstar p
  have hpq1 : vecDot p q₀ = p ⬝ᵥ r := by
    show p ⬝ᵥ q₀ = p ⬝ᵥ r
    rw [hq₀]
    show p ⬝ᵥ (r - g *ᵥ p) = p ⬝ᵥ r
    rw [dotProduct_sub, hskewzero, sub_zero]
  have hpq2 : p ⬝ᵥ q₀ = p ⬝ᵥ r := hpq1
  rw [hpq1, hpq2] at hbridge
  -- conclude
  have hkey :
      vecDot
          (fun i ↦ ∫ a, averageGradient U ((a.subSkew g hg).coeffOn U)
            (Response.centeredResponseOptimizer U (a.subSkew g hg) p r) i ∂P)
          (fun i ↦ ∫ a, averageFlux U ((a.subSkew g hg).coeffOn U)
            (Response.centeredResponseOptimizer U (a.subSkew g hg) p r) i ∂P) =
        p ⬝ᵥ S *ᵥ p +
          (r + Response.responseSymmetric K *ᵥ p) ⬝ᵥ
            SStar⁻¹ *ᵥ (r + Response.responseSymmetric K *ᵥ p) -
          p ⬝ᵥ r -
          (r + Response.responseSymmetric K *ᵥ p) ⬝ᵥ
            (SStar⁻¹ * K * SStar⁻¹) *ᵥ (r + Response.responseSymmetric K *ᵥ p) -
          ((SStar⁻¹ * S) *ᵥ p) ⬝ᵥ (r + Response.responseSymmetric K *ᵥ p) := by
      linarith only [hbridge]
  exact hkey

end

end HCPolySupport.HighContrast.Quenched
