/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusSelectedContourIdentity
public import LeanPool.FastDynamo.Global.HorizontalSpectralExtraction

/-!
# `lem:global-riesz-nonzero`

§7.2 of the paper ("The Riesz projection of the horizontal operator on `T²` is non-zero").  The
Neumann correction of `eq:global-resolvent` separates the true resolvent from the approximate
inverse `eq:Rapp` by

`(z - A_{ε,K_n})^{-1} - cR_app(z) = -cR_app(z)(id + E_n(z))^{-1}E_n(z)`,

so, after integration around `Γ_τ` and with `‖f_n‖₂ = 1`, `eq:parametrix-uniform-bound` and
`eq:error-small` give `eq:global-projection-error`

`|⟨Q_{ε,n} f_n, f_n⟩ - ⟨P_{δ_n} f_*, f_*⟩| ≤ (length Γ / 2π) C_app η_*/(1 - η_*) < 1/4`.

Combined with `eq:local-spectral-witness` (`Re⟨P_{δ_n} f_*, f_*⟩ > 1/2`) this gives
`Re⟨Q_{ε,n} f_n, f_n⟩ > 1/4`, hence `Q_{ε,n} ≠ 0`.

The `< 1/4` threshold is an explicit numerical hypothesis of the same shape as `eq:error-small`;
both are discharged once and for all by the parameter chain, from the single target `η_*` of
`FastDynamo.GlobalSeedInterface.errorTarget` (`Global/GlobalParameterChoiceConcrete.lean`):
`eq:error-small` is `GlobalParameterChoice.scaleErrorMajorant_lt_errorTarget` and the `< 1/4`
bound is `GlobalSeedInterface.mul_errorTarget_div_lt_quarter`.  Neither costs an extra
enlargement of `K_0`: `errorTarget` is a closed term of the seed interface and the `< 1/4`
bound is a theorem about it.  The paper correspondingly states `lem:global-riesz-nonzero`
for every `n ≥ 0` with no enlargement clause.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex MeasureTheory Metric Set

namespace TorusGlobalRieszNonzero

open ParametrixCutoffs
open ParametrixNeumannCorrection
open TorusChartC2Transfer
open TorusParametrixError
open TorusSelectedContourIdentity
open TorusSelectedWitness
open TorusTwoSummandParametrix

/-! ## The true-resolvent error for a Neumann-corrected parametrix -/

section Generic

universe ux ud

variable {X : Type ux} {D : Type ud}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]

omit [CompleteSpace D] in
/-- The paper's true-resolvent error `C_app η/(1-η)`, for **any** resolvent family whose
stored inverse is the Neumann-corrected parametrix, in particular for the builder
`hasResolventOnOfRightParametrixIndexZero` from a right parametrix of an index-zero pencil. -/
theorem norm_stateResolvent_sub_stateParametrix_le_of_inv
    {A : DomainOperator X D} {R : ℂ → X →L[ℂ] D} {S : Set ℂ} (h : HasResolventOn A S)
    (hinv : ∀ z ∈ S, h.inv z = correctedInverse A R z) {z : ℂ} (hz : z ∈ S) {M eta : ℝ}
    (hsmall : ‖rightError A R z‖ < 1) (hM : ‖stateParametrix A R z‖ ≤ M)
    (heta : ‖rightError A R z‖ ≤ eta) (hetalt : eta < 1) :
    ‖h.stateResolvent z - stateParametrix A R z‖ ≤ M * (eta / (1 - eta)) := by
  have hetanonneg : 0 ≤ eta := (norm_nonneg (rightError A R z)).trans heta
  have hMnonneg : 0 ≤ M := (norm_nonneg (stateParametrix A R z)).trans hM
  have hV : ‖Ring.inverse (rightCorrection A R z)‖ ≤ (1 - eta)⁻¹ := by
    apply (norm_ringInverse_rightCorrection_le A R z hsmall).trans
    exact (inv_le_inv₀ (sub_pos.mpr hsmall) (sub_pos.mpr hetalt)).2 (by linarith)
  have hVsub : ‖Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X‖ ≤
      (1 - eta)⁻¹ * eta := by
    calc ‖Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X‖ ≤
        ‖Ring.inverse (rightCorrection A R z)‖ * ‖rightError A R z‖ := by
          rw [ringInverse_rightCorrection_sub_id A R z hsmall, norm_neg]
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 - eta)⁻¹ * eta := mul_le_mul hV heta (norm_nonneg _) (by positivity)
  have hSR : h.stateResolvent z =
      (stateParametrix A R z).comp (Ring.inverse (rightCorrection A R z)) := by
    change A.embedding.comp (h.inv z) = _
    rw [hinv z hz]
    rfl
  have hdecomp : h.stateResolvent z - stateParametrix A R z =
      (stateParametrix A R z).comp
        (Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X) := by
    rw [hSR]
    apply ContinuousLinearMap.ext
    intro x
    change stateParametrix A R z (Ring.inverse (rightCorrection A R z) x) -
        stateParametrix A R z x =
      stateParametrix A R z (Ring.inverse (rightCorrection A R z) x - x)
    rw [map_sub]
  rw [hdecomp]
  calc ‖(stateParametrix A R z).comp
        (Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X)‖ ≤
      ‖stateParametrix A R z‖ *
        ‖Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * ((1 - eta)⁻¹ * eta) := mul_le_mul hM hVsub (norm_nonneg _) hMnonneg
    _ = M * (eta / (1 - eta)) := by rw [div_eq_mul_inv]; ring

omit [CompleteSpace D] in
/-- **`eq:global-projection-error`** in abstract
form: the normalized contour operator of a parametrix differs from the Riesz projection of the
Neumann-corrected resolvent by at most `r C_app η/(1-η)`. -/
theorem norm_rieszProjection_sub_contourOperator_le_of_inv
    {A : DomainOperator X D} {R : ℂ → X →L[ℂ] D} {c : ℂ} {r M eta : ℝ} (hr : 0 ≤ r)
    (h : HasResolventOn A (Metric.sphere c r))
    (hinv : ∀ z ∈ Metric.sphere c r, h.inv z = correctedInverse A R z)
    (hR : ContinuousOn R (Metric.sphere c r))
    (hsmall : ∀ z ∈ Metric.sphere c r, ‖rightError A R z‖ < 1)
    (hM : ∀ z ∈ Metric.sphere c r, ‖stateParametrix A R z‖ ≤ M)
    (heta : ∀ z ∈ Metric.sphere c r, ‖rightError A R z‖ ≤ eta) (hetalt : eta < 1) :
    ‖h.rieszProjection - contourOperator A R c r‖ ≤ r * (M * (eta / (1 - eta))) :=
  norm_rieszProjection_sub_contourOperator_le hr h R hR fun z hz ↦
    norm_stateResolvent_sub_stateParametrix_le_of_inv h hinv hz (hsmall z hz) (hM z hz)
      (heta z hz) hetalt

end Generic

/-! ## The error majorant of `eq:explicit-error` -/

/-- The error majorant of `eq:explicit-error` is nonnegative. -/
theorem scaleErrorMajorant_nonneg {C epsilon Rr : ℝ} (hC : 0 ≤ C) (heps : 0 ≤ epsilon)
    (hR : 0 < Rr) : 0 ≤ scaleErrorMajorant C epsilon Rr := by
  unfold scaleErrorMajorant
  have h1 : 0 ≤ Real.sqrt epsilon / Rr := div_nonneg (Real.sqrt_nonneg _) hR.le
  have h2 : 0 ≤ epsilon / Rr ^ 2 := div_nonneg heps (by positivity)
  nlinarith

/-! ## Comparing two operators on one unit test vector -/

/-- On a unit vector the real parts of two test inner products differ by at most the operator
distance. -/
theorem abs_re_inner_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P Q : E →L[ℂ] E) {f : E} (hf : ‖f‖ = 1) :
    |(inner ℂ f (P f) : ℂ).re - (inner ℂ f (Q f) : ℂ).re| ≤ ‖P - Q‖ := by
  have hlin : (inner ℂ f (P f) : ℂ) - inner ℂ f (Q f) = inner ℂ f ((P - Q) f) := by
    rw [sub_apply, inner_sub_right]
  calc |(inner ℂ f (P f) : ℂ).re - (inner ℂ f (Q f) : ℂ).re|
      = |((inner ℂ f (P f) : ℂ) - inner ℂ f (Q f)).re| := by rw [Complex.sub_re]
    _ = |(inner ℂ f ((P - Q) f) : ℂ).re| := by rw [hlin]
    _ ≤ ‖(inner ℂ f ((P - Q) f) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖f‖ * ‖(P - Q) f‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖f‖ * (‖P - Q‖ * ‖f‖) := by
        gcongr
        exact (P - Q).le_opNorm f
    _ = ‖P - Q‖ := by rw [hf]; ring

/-! ## `lem:global-riesz-nonzero` at the selected cell -/

section SelectedCell

variable {v : WholePlaneVelocityCoefficients} {s : WholePlaneExactScalingParameters}
  {u ubg : TransverseRealW1Inf} {p : WholePlane} {R deltaUpper bound Lstar : ℝ}
  {Gamma : SpectralCircle}

/-- `C_app = C_bg + C_n`, the uniform bound of `eq:parametrix-uniform-bound` at the cell.  The
input of the background summand carries `‖1 - φ_n‖ ≤ 1`, so no factor `2` appears. -/
def cellParametrixBound (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) : ℝ :=
  C.background.bound + selectedTransportedBound R s.epsilon deltaUpper bound

/-- The bound `C_app` is nonnegative. -/
theorem cellParametrixBound_nonneg (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) :
    0 ≤ cellParametrixBound C := by
  have h1 := C.background.bound_nonneg
  have h2 := selectedTransportedBound_nonneg (epsilon := s.epsilon) (deltaUpper := deltaUpper)
    C.radius_pos C.bound_nonneg
  unfold cellParametrixBound
  linarith

/-- The explicit error majorant of `eq:explicit-error` at the cell; it plays the role of the
paper's `η_*` (the paper only requires `sup ‖E_n(z)‖ < η_*`). -/
def cellErrorMajorant (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) : ℝ :=
  scaleErrorMajorant (parametrixErrorConstant C.background.bound
    (selectedTransportedBound R s.epsilon deltaUpper bound)) s.epsilon R

/-- The cell error majorant is nonnegative. -/
theorem cellErrorMajorant_nonneg
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) : 0 ≤ cellErrorMajorant C :=
  scaleErrorMajorant_nonneg
    (parametrixErrorConstant_nonneg C.background.bound_nonneg
      (selectedTransportedBound_nonneg (epsilon := s.epsilon) (deltaUpper := deltaUpper)
        C.radius_pos C.bound_nonneg))
    C.epsilon_nonneg C.radius_pos

/-- **`lem:global-contour-resolvent` at the cell**, stated on the shifted spectral circle
`Γ_τ = Γ - iτ` rather than on the preimage set `verticallyShiftedSet`. -/
def cellContourResolvent (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma)
    (heps : 0 < s.epsilon) (hmaj : cellErrorMajorant C < 1) :
    HasResolventOn (horizontalInductionOperator u s.epsilon s.K)
      (backgroundShiftedContour Gamma s.tau).boundary :=
  (globalContourResolvent C.parametrix heps
      (error_norm_lt_one_of_majorant C.parametrix heps.le hmaj)).mono
    (verticallyShiftedSet_boundary Gamma s.tau).symm.subset

/-- The shifted circle is exactly the parameter set of the two-summand datum. -/
theorem sphere_subset_verticallyShiftedSet (Gamma : SpectralCircle) (tau : ℝ) :
    Metric.sphere (backgroundShiftedContour Gamma tau).center Gamma.radius ⊆
      verticallyShiftedSet tau Gamma.boundary :=
  (verticallyShiftedSet_boundary Gamma tau).symm.subset

/-- **`eq:global-projection-error`** at the selected
cell: the global Riesz projection `Q_{ε,n}` differs from the normalized contour operator of
`eq:Rapp` by at most `r C_app η_*/(1 - η_*)`. -/
theorem norm_rieszProjection_sub_contourOperator_le_cell
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (heps : 0 < s.epsilon)
    (hmaj : cellErrorMajorant C < 1) :
    ‖(cellContourResolvent C heps hmaj).rieszProjection -
        contourOperator (horizontalInductionOperator u s.epsilon s.K)
          C.parametrix.approximateInverse (backgroundShiftedContour Gamma s.tau).center
          Gamma.radius‖ ≤
      Gamma.radius * (cellParametrixBound C *
        (cellErrorMajorant C / (1 - cellErrorMajorant C))) := by
  have hmem := sphere_subset_verticallyShiftedSet Gamma s.tau
  refine norm_rieszProjection_sub_contourOperator_le_of_inv Gamma.radius_pos.le
    (cellContourResolvent C heps hmaj) (fun _ _ ↦ rfl)
    (C.parametrix.continuousOn_approximateInverse.mono hmem) ?_ ?_ ?_ hmaj
  · intro z hz
    rw [C.parametrix.transfer_rightError_eq (hmem hz)]
    exact lt_of_le_of_lt (norm_error_le C.parametrix heps.le (hmem hz)) hmaj
  · intro z hz
    refine ContinuousLinearMap.opNorm_le_bound _ (cellParametrixBound_nonneg C) fun f ↦ ?_
    exact norm_stateParametrix_apply_le C.parametrix (hmem hz) f
  · intro z hz
    rw [C.parametrix.transfer_rightError_eq (hmem hz)]
    exact norm_error_le C.parametrix heps.le (hmem hz)

/-- **`Re⟨cR_app-contour f_n, f_n⟩ > 1/2`**: `eq:selected-contour-identity` transports
`eq:local-spectral-witness` to the torus. -/
theorem re_inner_contourOperator_placedWitness_gt_half
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (fstar : WholePlaneC2L2)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5)
    (hproj : 1 / 2 < (inner ℂ (C.localBound.resolvent.rieszProjection fstar) fstar : ℂ).re) :
    1 / 2 < (inner ℂ (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)
      (contourOperator (horizontalInductionOperator u s.epsilon s.K)
        C.parametrix.approximateInverse (backgroundShiftedContour Gamma s.tau).center
        Gamma.radius (placedWitness p R C.radius_pos s.ell s.ell_pos fstar)) : ℂ).re := by
  rw [inner_contourOperator_placedWitness C fstar hsupp hfit, ← re_inner_comm]
  exact hproj

/-- **`lem:global-riesz-nonzero`, quantitative form** (the last step of its proof):
`Re⟨Q_{ε,n} f_n, f_n⟩ > 1/2 - 1/4 = 1/4`. -/
theorem re_inner_rieszProjection_placedWitness_gt_quarter
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (heps : 0 < s.epsilon)
    (hmaj : cellErrorMajorant C < 1) (fstar : WholePlaneC2L2) (hnorm : ‖fstar‖ = 1)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5)
    (hproj : 1 / 2 < (inner ℂ (C.localBound.resolvent.rieszProjection fstar) fstar : ℂ).re)
    (hquarter : Gamma.radius * (cellParametrixBound C *
      (cellErrorMajorant C / (1 - cellErrorMajorant C))) < 1 / 4) :
    1 / 4 < (inner ℂ ((cellContourResolvent C heps hmaj).rieszProjection
        (placedWitness p R C.radius_pos s.ell s.ell_pos fstar))
      (placedWitness p R C.radius_pos s.ell s.ell_pos fstar) : ℂ).re := by
  have hfn : ‖placedWitness p R C.radius_pos s.ell s.ell_pos fstar‖ = 1 := by
    rw [norm_placedWitness p R C.radius_pos s.ell s.ell_pos fstar hsupp C.box hfit]
    exact hnorm
  have hdiff := abs_re_inner_sub_le (cellContourResolvent C heps hmaj).rieszProjection
    (contourOperator (horizontalInductionOperator u s.epsilon s.K)
      C.parametrix.approximateInverse (backgroundShiftedContour Gamma s.tau).center
      Gamma.radius) hfn
  have hbound := norm_rieszProjection_sub_contourOperator_le_cell C heps hmaj
  have hhalf := re_inner_contourOperator_placedWitness_gt_half C fstar hsupp hfit hproj
  rw [re_inner_comm]
  have habs := lt_of_le_of_lt (le_trans hdiff hbound) hquarter
  have hlow := (abs_lt.mp habs).1
  linarith

/-- **`lem:global-riesz-nonzero`**: the global
Riesz projection of the selected cell is non-zero. -/
theorem rieszProjection_ne_zero_cell
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (heps : 0 < s.epsilon)
    (hmaj : cellErrorMajorant C < 1) (fstar : WholePlaneC2L2) (hnorm : ‖fstar‖ = 1)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5)
    (hproj : 1 / 2 < (inner ℂ (C.localBound.resolvent.rieszProjection fstar) fstar : ℂ).re)
    (hquarter : Gamma.radius * (cellParametrixBound C *
      (cellErrorMajorant C / (1 - cellErrorMajorant C))) < 1 / 4) :
    (cellContourResolvent C heps hmaj).rieszProjection ≠ 0 :=
  ne_zero_of_inner_contour_test _ _
    (re_inner_rieszProjection_placedWitness_gt_quarter C heps hmaj fstar hnorm hsupp hfit hproj
      hquarter)

end SelectedCell

end TorusGlobalRieszNonzero

end

end FastDynamo
