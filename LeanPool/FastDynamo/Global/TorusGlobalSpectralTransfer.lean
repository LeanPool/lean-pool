/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusGlobalRieszNonzero

/-!
# `prop:global-spectral-transfer` on a selected cell

The statement and the proof of `prop:global-spectral-transfer` in the paper.  Combining

* `lem:global-contour-resolvent` — `Γ_τ ⊂ ρ(A_{ε,K_n})`
  (`TorusGlobalRieszNonzero.cellContourResolvent`), and
* `lem:global-riesz-nonzero` — `Q_{ε,n} ≠ 0` for every `n ≥ 0`, with no enlargement of `K_0`
  (`TorusGlobalRieszNonzero.rieszProjection_ne_zero_cell`),

with `lem:torus-sector-basic` (the resolvent is compact, so the spectrum inside `Γ_τ` consists of
isolated eigenvalues of finite algebraic multiplicity) gives an eigenvalue of `A_{ε,K_n}` inside
`Γ_τ`.  Translation by `-iτ` preserves real parts, so every eigenvalue in this region has real
part at least `g_*`.  The proposition only asserts that such an eigenvalue exists (the paper
names it `λ_ε = α_ε + iω_ε` in the proof of `thm:main`), and the Lean keeps the existential
form.

The finish bridge `lem:axial-recovery` turns the two-component eigenpair into a three-component
eigenpair of `reducedInductionOperator` with `fixedSectorDivergence K b = 0`, i.e. into the
divergence-free field the main theorem consumes.

Everything is stated for one selected cell, i.e. for one value of the bundled data
`TorusSelectedContourIdentity.SelectedCellData`; the paper's "for every `n ≥ 0` and every
`ε = δ_nℓ_n²` with `δ_n ∈ I`" is the universal quantification over that datum, whose fields carry
the cell index and the diffusivity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex MeasureTheory Metric Set

namespace TorusGlobalSpectralTransfer

open HorizontalSpectralExtraction
open ParametrixNeumannCorrection
open TorusChartC2Transfer
open TorusGlobalRieszNonzero
open TorusParametrixError
open TorusSelectedContourIdentity
open TorusSelectedWitness
open TorusTwoSummandParametrix

variable {v : WholePlaneVelocityCoefficients} {s : WholePlaneExactScalingParameters}
  {u ubg : TransverseRealW1Inf} {p : WholePlane} {R deltaUpper bound Lstar : ℝ}
  {Gamma : SpectralCircle}

/-- **`prop:global-spectral-transfer`, two-component form**: the horizontal torus operator of
the selected cell has an eigenvalue
of real part at least the growth floor `g_*` of the seed contour, with an `H²(T²; ℂ²)`
eigenfunction.

The hypotheses are exactly the bundled cell datum `C`, the two numerical thresholds `hmaj`
(error majorant `< 1`, cf. `eq:error-small`) and `hquarter` (the `< 1/4` of
`eq:global-projection-error`), and the seed witness `f_*` of `prop:local-seed` with its three
properties: unit norm, support in `closedBall(0, L_*)` transported by `eq:scaled-witness-support`
(itself a consequence of `L_* ≤ R_v`, in the proof
of `lem:global-riesz-nonzero`), and `eq:local-spectral-witness`.  The paper chooses `K_0` so that
both thresholds hold; here they are explicit hypotheses, and the support fit is the non-strict
`L_* ℓ_n ≤ R_n/5` (the paper derives the strict `L_* ℓ_n < R_n/5`). -/
theorem exists_growing_horizontalInduction_eigenpair_cell
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma) (heps : 0 < s.epsilon)
    (hmaj : cellErrorMajorant C < 1) (fstar : WholePlaneC2L2) (hnorm : ‖fstar‖ = 1)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5)
    (hproj : 1 / 2 < (inner ℂ (C.localBound.resolvent.rieszProjection fstar) fstar : ℂ).re)
    (hquarter : Gamma.radius * (cellParametrixBound C *
      (cellErrorMajorant C / (1 - cellErrorMajorant C))) < 1 / 4) :
    ∃ (lam : ℂ) (hfun : TransverseC2H2),
      Gamma.growthFloor ≤ lam.re ∧
        (horizontalInductionOperator u s.epsilon s.K).IsEigenpair lam hfun := by
  obtain ⟨lam, hfun, hfloor, heigen⟩ :=
    exists_growthFloor_horizontalInduction_eigenpair_of_rieszProjection_ne_zero
      u s.epsilon s.K (backgroundShiftedContour Gamma s.tau) (cellContourResolvent C heps hmaj)
      (rieszProjection_ne_zero_cell C heps hmaj fstar hnorm hsupp hfit hproj hquarter)
  refine ⟨lam, hfun, ?_, heigen⟩
  rwa [backgroundShiftedContour_growthFloor] at hfloor

/-- **`prop:global-spectral-transfer`, three-component form**: the same eigenvalue carries an
eigenfunction of the reduced induction operator with vanishing fixed-sector divergence, through
the finish bridge `lem:axial-recovery` of `FastDynamo/Finish/AxialRecovery.lean`. -/
theorem exists_growing_reducedInduction_eigenpair_cell
    (C : SelectedCellData v s u ubg p R deltaUpper bound Gamma)
    (hdiv : IsTransverseDivergenceFree u) (heps : 0 < s.epsilon) (hK : s.K ≠ 0)
    (hmaj : cellErrorMajorant C < 1) (fstar : WholePlaneC2L2) (hnorm : ‖fstar‖ = 1)
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
    (hfit : Lstar * s.ell ≤ R / 5)
    (hproj : 1 / 2 < (inner ℂ (C.localBound.resolvent.rieszProjection fstar) fstar : ℂ).re)
    (hquarter : Gamma.radius * (cellParametrixBound C *
      (cellErrorMajorant C / (1 - cellErrorMajorant C))) < 1 / 4) :
    ∃ (lam : ℂ) (b : TransverseC3H2),
      Gamma.growthFloor ≤ lam.re ∧
        (reducedInductionOperator u s.epsilon s.K).IsEigenpair lam b ∧
          (productInductionOperator u s.epsilon).IsEigenpair lam (axialLiftH2 s.K b) ∧
            fixedSectorDivergence s.K b = 0 ∧
              productDivergenceFromH2 (axialLiftH2 s.K b) = 0 := by
  obtain ⟨lam, b, hfloor, hred, hprod, hsector, hlift⟩ :=
    exists_growing_reducedInduction_eigenpair_of_horizontal_rieszProjection_ne_zero_full
      u hdiv heps hK (backgroundShiftedContour Gamma s.tau) (cellContourResolvent C heps hmaj)
      (rieszProjection_ne_zero_cell C heps hmaj fstar hnorm hsupp hfit hproj hquarter)
  refine ⟨lam, b, ?_, hred, hprod, hsector, hlift⟩
  rwa [backgroundShiftedContour_growthFloor] at hfloor

end TorusGlobalSpectralTransfer

end

end FastDynamo
