/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ParameterChainWitnesses
public import LeanPool.FastDynamo.Global.TorusSelectedCellChartAgreement
public import LeanPool.FastDynamo.Global.TorusBackgroundParametrixBridge
public import LeanPool.FastDynamo.Global.TorusGlobalSpectralTransfer

/-!
# `prop:global-spectral-transfer` at the constructed velocity

The statement of `prop:global-spectral-transfer` and its proof at the end of §7.2.

`Global/TorusGlobalSpectralTransfer.lean` proves the proposition for an arbitrary bundled cell
datum `TorusSelectedContourIdentity.SelectedCellData` together with the two numerical thresholds
and the seed witness.  This module produces that datum at

* the velocity `u = Theta.velocity` of `eq:global-u`,
* the parameter chain of `Global/GlobalParameterChoiceConcrete.lean`,
* the two-component seed `Local/LocalSeedC2.lean`,

for **every** matching cell of a diffusivity — not only for the canonically selected one — and
discharges the two thresholds from the chain's own field `eq:error-small`
(`GlobalParameterChoice.scaleErrorMajorant_lt_errorTarget`) and from
`GlobalSeedInterface.mul_errorTarget_div_lt_quarter` (`eq:global-projection-error`).

The conclusion is the closing sentence of the paper's proof of `prop:global-spectral-transfer`,
"every eigenvalue in this region has real part at least `g_*`": an eigenpair of
`reducedInductionOperator u eps K_n` whose eigenvalue has real part at least the seed's growth
floor `g_*`, with a divergence-free `H²` amplitude.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace LocalSeedC2

open GlobalSeedInterface
open ScaleFamily.TorusCellPlacement
open TorusChartActionBridge
open TorusChartC2Transfer
open TorusGlobalRieszNonzero
open TorusParametrixError
open TorusSelectedContourIdentity
open TorusTwoSummandParametrix
open TransverseSmoothBumpPeriodization

variable (s : LocalSeedC2)
  (Theta : GlobalParameterChoice s.toGlobalSeedInterface
    s.toGlobalSeedInterface.errorConstant s.toGlobalSeedInterface.errorTarget)

variable {epsilon : ℝ} (hpos : 0 < epsilon)
  (c : ScaleFamily.MatchingCell Theta.scaleFamily epsilon)

/-! ## The bundled cell datum -/

/-- **The seed side at an arbitrary matching cell** (`cor:scaled-local-resolvents`): the seed's
uniform `L² → H²` resolvent bound (stronger than the `L² → H¹` bound
`eq:local-continuation-bound` of the paper) restated at the cell's exact-scaling parameters,
evaluated at the chain's own axial shift `tau`. -/
def matchingCellSeedBound :
    WholePlaneLocalResolventBound s.coefficients (c.exactScalingParameters Theta.tau).N
      (c.exactScalingParameters Theta.tau).delta s.contour.boundary s.resolventBound :=
  s.scaledResolventBoundData (c.exactScalingParameters Theta.tau) rfl c.delta_mem_interval

/-- **The background side at an arbitrary matching cell** (`prop:background-resolvent`)
as §7 parametrix data on the contour `Gamma_tau`. -/
def matchingCellBackgroundDatum :
    BackgroundParametrixData (Theta.backgroundParameters.velocity c.index)
      (c.exactScalingParameters Theta.tau).epsilon (c.exactScalingParameters Theta.tau).K
      (verticallyShiftedSet (c.exactScalingParameters Theta.tau).tau s.contour.boundary) :=
  BackgroundParametrixData.ofTorusBackgroundResolventData hpos.le
    Theta.backgroundParameters.backgroundResolventConstant_nonneg
    ((Theta.backgroundParameters.boundaryResolventData c.index hpos
      (Theta.matchingCell_lower c) (Theta.matchingCell_upper c)).mono
        (subset_of_eq (verticallyShiftedSet_boundary s.contour Theta.tau)))

/-- **The bundled cell hypotheses of §6 at an arbitrary matching cell.**  Every field is a fact
of the parameter chain: the two no-wrap conditions and the three velocity facts of
`Global/TorusSelectedCellVelocityFacts.lean`, the chart coefficient agreement of
`Global/TorusSelectedCellChartAgreement.lean`, the seed bound `cor:scaled-local-resolvents` and
the background datum `prop:background-resolvent`. -/
def matchingCellData :
    SelectedCellData s.coefficients (c.exactScalingParameters Theta.tau) Theta.velocity
      (Theta.backgroundParameters.velocity c.index)
      (pairToWholePlane (Theta.scaleFamily.cellCenter c.index))
      (Theta.scaleFamily.bufferRadius c.index)
      s.toGlobalSeedInterface.parameters.deltaPlus s.resolventBound s.contour where
  radius_pos := Theta.scaleFamily.bufferRadius_pos c.index
  box := closedHalfBufferBall_subset_iocFundamentalBox Theta.placement _
  boxAux := by
    rw [auxOutputRadius_div_two]
    exact closedThreeQuarterBufferBall_subset_iocFundamentalBox Theta.placement _
  localBound := matchingCellSeedBound s Theta c
  bound_nonneg := s.resolventBound_nonneg
  epsilon_nonneg := hpos.le
  delta_nonneg := c.delta_pos.le
  delta_le := c.admissible.2
  agree := by
    rw [auxOutputRadius_div_two]
    exact chartCoefficientAgreement_parameterizedFullGlobalW1Inf s.smoothingWidth Theta.placement
      s.angularSpeed s.axialSpeed Theta.tau Theta.tau_nonneg _
  background := matchingCellBackgroundDatum s Theta hpos c
  innerRadius := Theta.scaleFamily.bufferRadius c.index / 10
  outerRadius := Theta.scaleFamily.bufferRadius c.index / 2
  inner_le := le_rfl
  outer_ge := le_rfl
  localized := transverseVelocityLocalized_parameterizedFullGlobalW1Inf s.smoothingWidth
    Theta.placement s.angularSpeed s.axialSpeed Theta.tau Theta.tau_nonneg _
  value_agree := fun i : Fin 3 ↦ value_agrees_selectedBackgroundVelocity_off_core s.smoothingWidth
    Theta.placement s.angularSpeed s.axialSpeed Theta.tau Theta.tau_nonneg _ i
  deriv_agree := fun j : Fin 2 ↦ deriv_agrees_selectedBackgroundVelocity_off_core s.smoothingWidth
    Theta.placement s.angularSpeed s.axialSpeed Theta.tau Theta.tau_nonneg _ j

/-! ## The two numerical thresholds -/

/-- The uniform bound `C_app = C_bg + C_n` on the approximate inverse of the bundled datum
(`eq:parametrix-uniform-bound`).  The background input carries the sharp
`‖1 - φ_n‖ ≤ 1`, so no factor `2` appears. -/
theorem cellParametrixBound_matchingCellData :
    cellParametrixBound (matchingCellData s Theta hpos c) =
      s.toGlobalSeedInterface.backgroundConstant +
        selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
          s.toGlobalSeedInterface.parameters.deltaPlus s.resolventBound := rfl

/-- **`eq:local-spectral-witness` at the bundled datum**: the seed's witness clause
`Re<P_{delta_n} f_*, f_*> > 1/2`, read at the cell's rescaled diffusivity. -/
theorem re_inner_projection_matchingCellData :
    1 / 2 < (inner ℂ ((matchingCellData s Theta hpos c).localBound.resolvent.rieszProjection
      s.witness) s.witness : ℂ).re :=
  s.re_inner_projection_witness_gt _ c.delta_mem_interval

/-- **`eq:error-small` at the bundled datum**, in the form the Neumann series consumes. -/
theorem cellErrorMajorant_matchingCellData_lt_one
    (hbase : s.parameters.kStar ≤ Theta.baseIndex) :
    cellErrorMajorant (matchingCellData s Theta hpos c) < 1 :=
  lt_of_lt_of_le (Theta.scaleErrorMajorant_lt_errorTarget hbase c)
    s.toGlobalSeedInterface.errorTarget_le_one

/-- **`eq:global-projection-error` at the bundled datum**: the Neumann remainder,
multiplied by the contour prefactor `length(Gamma)/(2 pi) = r_Gamma` and by the uniform bound
`C_app`, stays below `1/4`.  The two inputs are the chain's own `eq:error-small` and the
cell-uniform majorant `C_loc` of the transported selected bound. -/
theorem projectionError_matchingCellData_lt_quarter
    (hbase : s.parameters.kStar ≤ Theta.baseIndex) :
    s.contour.radius * (cellParametrixBound (matchingCellData s Theta hpos c) *
      (cellErrorMajorant (matchingCellData s Theta hpos c) /
        (1 - cellErrorMajorant (matchingCellData s Theta hpos c)))) < 1 / 4 := by
  have hrad : 0 < s.contour.radius := s.contour.radius_pos
  have hloc : selectedTransportedBound (Theta.scaleFamily.bufferRadius c.index) epsilon
      s.toGlobalSeedInterface.parameters.deltaPlus s.resolventBound ≤
      s.toGlobalSeedInterface.selectedConstant := Theta.selectedTransportedBound_le hbase c
  have hbg := s.toGlobalSeedInterface.backgroundConstant_nonneg
  have hsel := s.toGlobalSeedInterface.selectedConstant_nonneg
  have hCapp : cellParametrixBound (matchingCellData s Theta hpos c) ≤
      s.toGlobalSeedInterface.approximateInverseConstant := by
    rw [cellParametrixBound_matchingCellData]
    unfold GlobalSeedInterface.approximateInverseConstant
    linarith
  have hCapp0 : 0 ≤ cellParametrixBound (matchingCellData s Theta hpos c) :=
    cellParametrixBound_nonneg _
  have hA0 : 0 ≤ s.contour.radius * cellParametrixBound (matchingCellData s Theta hpos c) :=
    mul_nonneg hrad.le hCapp0
  have hP1 : 1 ≤ s.toGlobalSeedInterface.projectionConstant :=
    s.toGlobalSeedInterface.one_le_projectionConstant
  have hAle : s.contour.radius * cellParametrixBound (matchingCellData s Theta hpos c) ≤
      10 * s.toGlobalSeedInterface.projectionConstant := by
    have hstep : s.contour.radius * cellParametrixBound (matchingCellData s Theta hpos c) ≤
        s.contour.radius * s.toGlobalSeedInterface.approximateInverseConstant :=
      mul_le_mul_of_nonneg_left hCapp hrad.le
    have hexp : s.toGlobalSeedInterface.projectionConstant =
        (1 + s.contour.radius) * (1 + s.toGlobalSeedInterface.approximateInverseConstant) := rfl
    have happ : 0 ≤ s.toGlobalSeedInterface.approximateInverseConstant :=
      s.toGlobalSeedInterface.approximateInverseConstant_nonneg
    nlinarith
  have hkey := s.toGlobalSeedInterface.mul_errorTarget_div_lt_quarter hA0 hAle
  have heta0 : 0 ≤ cellErrorMajorant (matchingCellData s Theta hpos c) :=
    cellErrorMajorant_nonneg _
  have hetalt : cellErrorMajorant (matchingCellData s Theta hpos c) <
      s.toGlobalSeedInterface.errorTarget := Theta.scaleErrorMajorant_lt_errorTarget hbase c
  have hhalf : s.toGlobalSeedInterface.errorTarget ≤ 1 / 2 :=
    s.toGlobalSeedInterface.errorTarget_le_half
  have hmono : cellErrorMajorant (matchingCellData s Theta hpos c) /
      (1 - cellErrorMajorant (matchingCellData s Theta hpos c)) ≤
      s.toGlobalSeedInterface.errorTarget / (1 - s.toGlobalSeedInterface.errorTarget) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc s.contour.radius * (cellParametrixBound (matchingCellData s Theta hpos c) *
        (cellErrorMajorant (matchingCellData s Theta hpos c) /
          (1 - cellErrorMajorant (matchingCellData s Theta hpos c))))
      = s.contour.radius * cellParametrixBound (matchingCellData s Theta hpos c) *
        (cellErrorMajorant (matchingCellData s Theta hpos c) /
          (1 - cellErrorMajorant (matchingCellData s Theta hpos c))) := by ring
    _ ≤ s.contour.radius * cellParametrixBound (matchingCellData s Theta hpos c) *
        (s.toGlobalSeedInterface.errorTarget / (1 - s.toGlobalSeedInterface.errorTarget)) :=
      mul_le_mul_of_nonneg_left hmono hA0
    _ < 1 / 4 := hkey

/-! ## `lem:global-contour-resolvent` at the constructed velocity -/

/-- **`lem:global-contour-resolvent` at an arbitrary matching cell**: the whole
shifted contour `Gamma_tau` lies in the resolvent set of the torus induction operator of the
global velocity in the cell's axial sector.  Every hypothesis is a field of `matchingCellData`,
and the numeric threshold is the chain's own `eq:error-small`. -/
def matchingCellShiftedContourResolvent (hbase : s.parameters.kStar ≤ Theta.baseIndex) :
    HasResolventOn
      (horizontalInductionOperator Theta.velocity epsilon (Theta.fourierIndex c))
      Theta.backgroundParameters.shiftedBoundary :=
  cellContourResolvent (v := s.coefficients) (s := c.exactScalingParameters Theta.tau)
    (u := Theta.velocity) (ubg := Theta.backgroundParameters.velocity c.index)
    (p := pairToWholePlane (Theta.scaleFamily.cellCenter c.index))
    (R := Theta.scaleFamily.bufferRadius c.index)
    (deltaUpper := s.toGlobalSeedInterface.parameters.deltaPlus) (bound := s.resolventBound)
    (Gamma := s.contour) (matchingCellData s Theta hpos c) hpos
    (cellErrorMajorant_matchingCellData_lt_one s Theta hpos c hbase)

/-! ## The transfer -/

include hpos in
/-- **`prop:global-spectral-transfer` at the constructed velocity** (including the eigenvalue
bound `Re lambda ≥ g_*`), at an arbitrary matching cell of an arbitrary admissible
diffusivity: the reduced induction operator in the cell's axial sector `K_n` has an eigenpair
whose eigenvalue has real part at least the seed's growth floor `g_*`, whose amplitude is an
`H²(T²; ℂ³)` field with vanishing fixed-sector divergence, and whose axial lift is a
divergence-free eigenmode of the auxiliary all-frequency operator. -/
theorem exists_growing_reducedInduction_eigenpair_matchingCell
    (hbase : s.parameters.kStar ≤ Theta.baseIndex) :
    ∃ (lam : ℂ) (b : TransverseC3H2),
      s.growthFloor ≤ lam.re ∧
        (reducedInductionOperator Theta.velocity epsilon
          (Theta.fourierIndex c)).IsEigenpair lam b ∧
          (productInductionOperator Theta.velocity epsilon).IsEigenpair lam
            (axialLiftH2 (Theta.fourierIndex c) b) ∧
            fixedSectorDivergence (Theta.fourierIndex c) b = 0 ∧
              productDivergenceFromH2 (axialLiftH2 (Theta.fourierIndex c) b) = 0 :=
  TorusGlobalSpectralTransfer.exists_growing_reducedInduction_eigenpair_cell
    (v := s.coefficients) (s := c.exactScalingParameters Theta.tau) (u := Theta.velocity)
    (ubg := Theta.backgroundParameters.velocity c.index)
    (p := pairToWholePlane (Theta.scaleFamily.cellCenter c.index))
    (R := Theta.scaleFamily.bufferRadius c.index)
    (deltaUpper := s.toGlobalSeedInterface.parameters.deltaPlus) (bound := s.resolventBound)
    (Lstar := s.witnessSupportRadius) (Gamma := s.contour)
    (matchingCellData s Theta hpos c) Theta.velocity_isTransverseDivergenceFree hpos
    (Theta.fourierIndex_ne_zero c)
    (cellErrorMajorant_matchingCellData_lt_one s Theta hpos c hbase)
    s.witness s.norm_witness s.witness_ae_zero (le_of_lt (Theta.witnessSupport c.index))
    (re_inner_projection_matchingCellData s Theta hpos c)
    (projectionError_matchingCellData_lt_quarter s Theta hpos c hbase)

end LocalSeedC2

/-! ## The concrete chain -/

namespace HorizontalMode

open GlobalSeedInterface

/-- **`prop:global-spectral-transfer` at the concrete chain and an arbitrary matching cell.**
For every `0 < eps` and every cell of the chain's scale family matched to `eps`, the reduced
induction operator at the constructed velocity has a growing eigenpair in that cell's axial
sector, with the seed's growth floor `g_*` as the uniform rate. -/
theorem exists_growing_reducedInduction_eigenpair_matchingCell {epsilon : ℝ} (hpos : 0 < epsilon)
    (c : ScaleFamily.MatchingCell mainParameterChoice.scaleFamily epsilon) :
    ∃ (lam : ℂ) (b : TransverseC3H2),
      globalSeedInterface.growthFloor ≤ lam.re ∧
        (reducedInductionOperator mainParameterChoice.velocity epsilon
          (mainParameterChoice.fourierIndex c)).IsEigenpair lam b ∧
          (productInductionOperator mainParameterChoice.velocity epsilon).IsEigenpair lam
            (axialLiftH2 (mainParameterChoice.fourierIndex c) b) ∧
            fixedSectorDivergence (mainParameterChoice.fourierIndex c) b = 0 ∧
              productDivergenceFromH2
                (axialLiftH2 (mainParameterChoice.fourierIndex c) b) = 0 :=
  localSeedC2.exists_growing_reducedInduction_eigenpair_matchingCell mainParameterChoice hpos c
    kStar_le_mainParameterChoice_baseIndex

/-- **The contour resolvent of `lem:global-contour-resolvent` at the concrete chain**: for
every `eps` in `(0, eps_0]` the shifted contour `Gamma_tau` lies in the resolvent
set of the torus induction operator of the constructed velocity, in the axial sector
`K_{n(eps)}` of the canonically selected matching cell. -/
def mainSelectedCellResolvent {epsilon : ℝ} (hpos : 0 < epsilon)
    (hle : epsilon ≤ mainParameterChoice.eps0) :
    HasResolventOn
      (horizontalInductionOperator mainParameterChoice.velocity epsilon
        (mainParameterChoice.fourierIndex (mainParameterChoice.matchingCell hpos hle)))
      mainParameterChoice.backgroundParameters.shiftedBoundary :=
  localSeedC2.matchingCellShiftedContourResolvent mainParameterChoice hpos
    (mainParameterChoice.matchingCell hpos hle) kStar_le_mainParameterChoice_baseIndex

end HorizontalMode

end

end FastDynamo
