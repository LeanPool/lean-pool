/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCenterIdentities
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseOrder
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCompactInsertion
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecenteredSharp

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCenterSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The calibrated profile centers in closed Schur form

At the recentered samples, the two independently annealed profile centers of
the one-step hub are the closed Schur pairs of the terminal adapted mean: the
recentered mean has Schur data `(S, σ*, k_sym)`, and the reflected-center
identities evaluate to the gradient component `-p + σ*⁻¹(r + k_sym p)` and
the flux component `(1 - k_sym σ*⁻¹) r - (S + k_sym σ*⁻¹ k_sym) p`, with the
sign of `k_sym` flipped for the adjoint.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- **The primal center in closed Schur form.** -/
theorem profilePrimalCenter_calibrated_eq [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    (p r : Vec d) :
    Response.profilePrimalCenter P hq t
        (fun a ↦ a.subSkew (Response.responseSkew K)
          (Response.is_skew_mat_response_skew K)) p r =
      ((-p + SStar⁻¹ *ᵥ (r + Response.responseSymmetric K *ᵥ p),
        (1 - Response.responseSymmetric K * SStar⁻¹) *ᵥ r -
          (S + Response.responseSymmetric K * SStar⁻¹ *
            Response.responseSymmetric K) *ᵥ p) : BlockVec d) := by
  have hE2 : toFullBlockMat
      (Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t)) =
      schurBlock S SStar (Response.responseSymmetric K) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock
      (Response.responseSkew K) hform
    rwa [Response.sub_responseSkew K] at h
  have hmean : Response.skewBlockCongr (Response.responseSkew K)
      (adaptedMean P q t) =
      ofFullBlockMat (schurBlock S SStar (Response.responseSymmetric K)) := by
    apply toFullBlockMat_injective
    simpa using hE2
  rw [Response.profilePrimalCenter_subSkew_eq hq t hint (Response.responseSkew K)
    (Response.is_skew_mat_response_skew K) p r, hmean]
  have hmain := Response.blockR_schur_mulVec_primal S SStar
    (Response.responseSymmetric K) p r
  rwa [Response.responseSymmetric_isHermitian K] at hmain

/-- **The adjoint center in closed Schur form.** -/
theorem profileAdjointCenter_calibrated_eq [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t)
    {S SStar K : Mat d}
    (hform : toFullBlockMat (adaptedMean P q t) = schurBlock S SStar K)
    (p r : Vec d) :
    Response.profileAdjointCenter P hq t
        (fun a ↦ a.subSkew (Response.responseSkew K)
          (Response.is_skew_mat_response_skew K)) p r =
      ((-p + SStar⁻¹ *ᵥ (r - Response.responseSymmetric K *ᵥ p),
        (1 + Response.responseSymmetric K * SStar⁻¹) *ᵥ r -
          (S + Response.responseSymmetric K * SStar⁻¹ *
            Response.responseSymmetric K) *ᵥ p) : BlockVec d) := by
  have hE2 : toFullBlockMat
      (Response.skewBlockCongr (Response.responseSkew K) (adaptedMean P q t)) =
      schurBlock S SStar (Response.responseSymmetric K) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock
      (Response.responseSkew K) hform
    rwa [Response.sub_responseSkew K] at h
  have hmean : Response.skewBlockCongr (Response.responseSkew K)
      (adaptedMean P q t) =
      ofFullBlockMat (schurBlock S SStar (Response.responseSymmetric K)) := by
    apply toFullBlockMat_injective
    simpa using hE2
  rw [Response.profileAdjointCenter_subSkew_eq hq t hint (Response.responseSkew K)
    (Response.is_skew_mat_response_skew K) p r, hmean]
  have hmain := Response.blockR_adjoint_schur_mulVec S SStar
    (Response.responseSymmetric K) p r
  rwa [Response.responseSymmetric_isHermitian K] at hmain

end

end HCPolySupport.HighContrast.Quenched
