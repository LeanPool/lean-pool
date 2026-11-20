/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusBackgroundMultiplier
public import LeanPool.FastDynamo.Global.TorusBackgroundVelocity
public import LeanPool.FastDynamo.Global.TorusCellAxialPlateauBridge

/-!
# The parameter choices of the background resolvent estimate

This module closes the parameter chain of the proof of `prop:background-resolvent`.  The
analytic content — the weighted energy estimate `eq:background-coercivity` (proved in
`Global/TorusBackgroundWeightedEnergy.lean`), the multiplier `beta_n` and the background
velocity `u^bg_n` — is built in `Global/TorusBackgroundMultiplier.lean` and
`Global/TorusBackgroundVelocity.lean`.  What is added here is the *choice of parameters*:

* the contour `Gamma` and the translated region `cG_tau = {zeta - i tau : zeta in cG}`,
* the axial shift `tau` of `eq:axial-separation-choice`, through the explicit
  threshold `backgroundTauThreshold` of `Global/BackgroundMultiplierScalarAlgebra.lean`,
* the enlargement of `K_0` of `eq:background-diffusion-small`, in the form
  `C_1 delta_+ ell_0 <= g_*/4`,

and the verification that these choices produce a `BackgroundCoercivity` structure at every
point of `cG_tau`, for every selected cell `n` and every admissible diffusivity.

## Main definitions

* `backgroundShiftedContour Gamma tau` — the vertically translated spectral circle; its closed
  region is `cG_tau` and its boundary is `Gamma_tau`.
* `BackgroundParameters` — the interface record holding the contour, the bound `M` on
  `|Im zeta|`, the diffusivity window `[delta_-, delta_+]`, the axial shift `tau` and the two
  smallness hypotheses.
* `BackgroundParameters.coercivity` — the ten-field `BackgroundCoercivity` witness at every
  `z` of `cG_tau`.

## Dictionary to the paper

| paper | here |
|---|---|
| `cG` | `B.contour.closedRegion` |
| `g_*` | `B.contour.growthFloor` |
| `M = max_cG |Im zeta|` | `B.imBound` |
| `c_q = (q-1)/(q+1)` | `backgroundRatioGap r.q` |
| `C_0` | `backgroundCoercivityConstant ...` (explicit) |
| `C_1` | `backgroundDiffusionConstant = 18 ‖vartheta'‖_inf^2` |
| `d(K_0)^2 = ell_0` | `P.scaleFamily.ell 0` |
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set

/-! ## The explicit constants `C_0` and `C_1` -/

namespace ScaleFamily.TorusCellPlacement

/-- `C_w = C_v / sqrt(delta_-)`: the transport constant of
`eq:background-local-coefficients`.  It comes from
`|beta_n (u^bg_n)_⊥| ≤ C_v ell_n = C_v delta_n^{-1/2} sqrt(eps) ≤ C_v delta_-^{-1/2} sqrt(eps)`. -/
def backgroundTransportConstant (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed diffusivityLower : ℝ) : ℝ :=
  parameterizedHelicalValueBound hw angularSpeed axialSpeed / Real.sqrt diffusivityLower

/-- The transport constant is nonnegative. -/
theorem backgroundTransportConstant_nonneg (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed diffusivityLower : ℝ) :
    0 ≤ backgroundTransportConstant hw angularSpeed axialSpeed diffusivityLower :=
  div_nonneg (parameterizedHelicalValueBound_nonneg hw angularSpeed axialSpeed)
    (Real.sqrt_nonneg _)

/-- `C_0' = C_v N`: the bound on the local axial multiplier
`|2 pi K_n beta_n sum_{m ≠ n} (u_m^loc)_3|` of `eq:background-local-coefficients`, obtained
from `|r F(r)| ≤ 1` and `2 pi K_n ell_m = N r_m` (the paper's `2 pi K_n ell_m = 2 pi r_m`,
read with `ell_m = k_*/K_m`).
It is `tau`-free, which is what makes the order "`tau` then `K_0`" non-circular. -/
def backgroundAxialPhaseConstant (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed wavenumber : ℝ) : ℝ :=
  parameterizedHelicalValueBound hw angularSpeed axialSpeed * wavenumber

/-- The local axial multiplier constant is nonnegative when the local wavenumber is. -/
theorem backgroundAxialPhaseConstant_nonneg (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed : ℝ) {wavenumber : ℝ} (hN : 0 ≤ wavenumber) :
    0 ≤ backgroundAxialPhaseConstant hw angularSpeed axialSpeed wavenumber :=
  mul_nonneg (parameterizedHelicalValueBound_nonneg hw angularSpeed axialSpeed) hN

/-- `C_0 = C_0' + 2 C_w^2 + 4 C_s` of `eq:background-coercivity`.
Every summand is independent of `tau`, `K_0`, `n` and
`delta_n`. -/
def backgroundCoercivityConstant (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed diffusivityLower wavenumber : ℝ) : ℝ :=
  backgroundAxialPhaseConstant hw angularSpeed axialSpeed wavenumber +
    2 * backgroundTransportConstant hw angularSpeed axialSpeed diffusivityLower ^ 2 +
    4 * parameterizedHelicalFirstDerivativeBound hw angularSpeed axialSpeed

/-- `C_0 ≥ 0`. -/
theorem backgroundCoercivityConstant_nonneg (hw : PonomarenkoSmoothingWidth)
    (angularSpeed axialSpeed diffusivityLower : ℝ) {wavenumber : ℝ} (hN : 0 ≤ wavenumber) :
    0 ≤ backgroundCoercivityConstant hw angularSpeed axialSpeed diffusivityLower wavenumber := by
  have h1 := backgroundAxialPhaseConstant_nonneg hw angularSpeed axialSpeed hN
  have h2 : (0 : ℝ) ≤
      backgroundTransportConstant hw angularSpeed axialSpeed diffusivityLower ^ 2 := sq_nonneg _
  have h3 := parameterizedHelicalFirstDerivativeBound_nonneg hw angularSpeed axialSpeed
  unfold backgroundCoercivityConstant
  linarith

/-- `C_1 = 18 ‖vartheta'‖_inf^2` of `eq:background-diffusion-small`:
the constant produced by the gradient bound
`gradSupNormSq beta_n ≤ 2 (3 ‖vartheta'‖_inf R_0/ell_n)^2`. -/
def backgroundDiffusionConstant : ℝ := 18 * (axialPlateauLipschitzConstant : ℝ) ^ 2

/-- `C_1 ≥ 0`. -/
theorem backgroundDiffusionConstant_nonneg : 0 ≤ backgroundDiffusionConstant := by
  unfold backgroundDiffusionConstant
  positivity

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-! ## The placed core sits inside the axial plateau -/

section Core

variable {supportRadius : ℝ} (P : TorusCellPlacement (r := r) supportRadius)

/-- Every point of a placed local core has its canonical `(0,1]^2` representative inside the
closed three-quarter buffer disc, where the axial plateau is identically one.  This is the
geometric input for `s_n = r_m` on `supp u_m^loc` (proof of `prop:background-resolvent`); it
uses only the placement's support-fit field `supportRadius * ell_m < R_m/10`. -/
theorem pairEuclideanDist_representative_le_of_mem_torusLocalCoreDisk (m : ℕ)
    {q : TransverseTorus} (hq : q ∈ P.torusLocalCoreDisk m) :
    pairEuclideanDist (transverseIocRepresentative q) (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4 := by
  obtain ⟨x, hx, rfl⟩ := hq
  have hdist : dist x (P.scaleFamily.cellCenter m) < supportRadius * P.scaleFamily.ell m := hx
  have hfit := P.supportFit m
  have hR := P.scaleFamily.bufferRadius_pos m
  have hpair : pairEuclideanDist x (P.scaleFamily.cellCenter m) ≤
      3 * P.scaleFamily.bufferRadius m / 4 := by
    have h2 := pairEuclideanDist_le_two_mul_dist x (P.scaleFamily.cellCenter m)
    linarith
  rw [P.transverseIocRepresentative_eq_of_dist_le_three_quarters m hpair]
  exact hpair

/-- **`beta_n = F(r_m)` on the core of cell `m`** (from `s_n = r_m` on `supp u_m^loc`): on the
plateau the axial cut-off is one, so the placed series takes the constant value
`Psi_{r_m}(1) = F(r_m) + 1`. -/
theorem backgroundShiftedGlobalTorus_sub_one_eq_of_mem_torusLocalCoreDisk (n m : ℕ)
    {q : TransverseTorus} (hq : q ∈ P.torusLocalCoreDisk m) :
    P.backgroundShiftedGlobalTorus n q - 1 =
      ((backgroundMultiplierF (P.scaleFamily.cellRatio n m) : ℝ) : ℂ) := by
  have hcore := P.pairEuclideanDist_representative_le_of_mem_torusLocalCoreDisk m hq
  have hbuffer := P.torusLocalCoreDisk_subset_torusBufferDisk m hq
  have hkey : P.backgroundCellTorus (P.scaleFamily.cellRatio n m) m q =
      ((backgroundCellProfile (P.scaleFamily.cellRatio n m) 1 : ℝ) : ℂ) := by
    conv_lhs => rw [← transverseTorusPoint_transverseIocRepresentative q]
    exact P.backgroundCellTorus_eq_of_core _ m hcore
  rw [P.backgroundShiftedGlobalTorus_eq_cell_of_mem_buffer n hbuffer,
    backgroundShiftedCellTorus, hkey, backgroundCellProfile, mul_one]
  push_cast
  ring

/-- **`(u^ax)_3 = a_m` on the core of cell `m`**: the axial plateau of cell `m` is one there and
every other cell's axial field vanishes. -/
theorem axialOffsetGlobalTorus_apply_two_of_mem_torusLocalCoreDisk (tau : ℝ) (m : ℕ)
    {q : TransverseTorus} (hq : q ∈ P.torusLocalCoreDisk m) :
    P.axialOffsetGlobalTorus tau q 2 = P.scaleFamily.axialAmplitude tau m := by
  have hcore := P.pairEuclideanDist_representative_le_of_mem_torusLocalCoreDisk m hq
  rw [P.axialOffsetGlobalTorus_eq_axialAmplitude_of_representative_core tau m hcore]
  simp

end Core

/-! ## The parameter record -/

/--
**The parameter hypotheses of `prop:background-resolvent`**, as an interface record.

The fields are exactly the paper's data, in the paper's order of choice:
the local data and `q` are already fixed by `hw`, `angularSpeed`, `axialSpeed` and `P`; then the
contour `Gamma` (hence `g_*` and `M`) and the diffusivity window `I = [delta_-, delta_+]`; then
`tau` by `eq:axial-separation-choice`; and only then `K_0`, through
`eq:background-diffusion-small`, which constrains `ell_0 = d(K_0)^2`.

The record carries no operator and no spectral statement; it is purely the scalar parameter
chain consumed by `BackgroundParameters.coercivity`.
-/
structure BackgroundParameters {p : LocalSeedParameters} {r : ScaleRatios p}
    (hw : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (hw : ℝ)))
    (angularSpeed axialSpeed : ℝ) where
  /-- The spectral circle `Gamma`, whose closed region is `cG`. -/
  contour : SpectralCircle
  /-- `g_* > 0`: the closed region lies in the open right half-plane. -/
  growthFloor_pos : 0 < contour.growthFloor
  /-- `M`, an upper bound for `|Im zeta|` on `cG` (the paper takes `M = max_cG |Im zeta|`). -/
  imBound : ℝ
  /-- `|Im zeta| ≤ M` on `cG`. -/
  abs_im_le : ∀ ζ ∈ contour.closedRegion, |ζ.im| ≤ imBound
  /-- `delta_-`, the left endpoint of the admissible diffusivity window `I`. -/
  diffusivityLower : ℝ
  /-- `delta_+`, the right endpoint of the admissible diffusivity window `I`. -/
  diffusivityUpper : ℝ
  /-- `delta_- > 0`. -/
  diffusivityLower_pos : 0 < diffusivityLower
  /-- The axial shift `tau` of `eq:axial-separation-choice`. -/
  tau : ℝ
  /-- **`eq:axial-separation-choice`**: `tau` is above the
  explicit threshold `max (2M^2/g_*) (2(C_0+1)/c_q^2)`, hence satisfies both
  `M^2/(2 tau) ≤ g_*/4` and `tau c_q^2/2 ≥ C_0 + 1`. -/
  tau_ge : backgroundTauThreshold contour.growthFloor imBound
      (backgroundCoercivityConstant hw angularSpeed axialSpeed diffusivityLower p.wavenumber)
      (backgroundRatioGap r.q) ≤ tau
  /-- **`eq:background-diffusion-small`**:
  `C_1 delta_+ d(K_0)^2 = C_1 delta_+ ell_0 ≤ g_*/4`, the final enlargement of `K_0`. -/
  diffusion_small : backgroundDiffusionConstant * diffusivityUpper * P.scaleFamily.ell 0 ≤
      contour.growthFloor / 4

namespace BackgroundParameters

variable {p : LocalSeedParameters} {r : ScaleRatios p}
  {hw : PonomarenkoSmoothingWidth} {P : TorusCellPlacement (r := r) (1 + (hw : ℝ))}
  {angularSpeed axialSpeed : ℝ}

/-- The ratio gap `c_q` is positive because `q > 1`. -/
theorem ratioGap_pos (_B : BackgroundParameters hw P angularSpeed axialSpeed) :
    0 < backgroundRatioGap r.q :=
  backgroundRatioGap_pos r.one_lt_q

/-- `C_0 ≥ 0`, the input of the threshold lemmas. -/
theorem coercivityConstant_nonneg (B : BackgroundParameters hw P angularSpeed axialSpeed) :
    0 ≤ backgroundCoercivityConstant hw angularSpeed axialSpeed B.diffusivityLower
      p.wavenumber :=
  backgroundCoercivityConstant_nonneg hw angularSpeed axialSpeed B.diffusivityLower
    p.wavenumber_pos.le

/-- The chosen axial shift is strictly positive. -/
theorem tau_pos (B : BackgroundParameters hw P angularSpeed axialSpeed) : 0 < B.tau :=
  backgroundTauThreshold_pos_of_le B.coercivityConstant_nonneg B.ratioGap_pos B.tau_ge

/-- The chosen axial shift is nonnegative, the form required by the placed axial velocity. -/
theorem tau_nonneg (B : BackgroundParameters hw P angularSpeed axialSpeed) : 0 ≤ B.tau :=
  B.tau_pos.le

/-- **First half of `eq:axial-separation-choice`**: `M^2/(2 tau) ≤ g_*/4`. -/
theorem phaseDefect_le (B : BackgroundParameters hw P angularSpeed axialSpeed) :
    B.imBound ^ 2 / (2 * B.tau) ≤ B.contour.growthFloor / 4 :=
  backgroundTauThreshold_phase_error_le B.growthFloor_pos B.coercivityConstant_nonneg
    B.ratioGap_pos B.tau_ge

/-- **Second half of `eq:axial-separation-choice`**: `tau c_q^2/2 ≥ C_0 + 1`. -/
theorem separation_ge (B : BackgroundParameters hw P angularSpeed axialSpeed) :
    backgroundCoercivityConstant hw angularSpeed axialSpeed B.diffusivityLower p.wavenumber +
        1 ≤ B.tau * backgroundRatioGap r.q ^ 2 / 2 :=
  backgroundTauThreshold_separation_ge B.ratioGap_pos B.tau_ge

/-- The paper's `cG_tau = {zeta - i tau : zeta in cG}`. -/
def shiftedRegion (B : BackgroundParameters hw P angularSpeed axialSpeed) : Set ℂ :=
  (backgroundShiftedContour B.contour B.tau).closedRegion

/-- The paper's `Gamma_tau`, the boundary of `cG_tau`. -/
def shiftedBoundary (B : BackgroundParameters hw P angularSpeed axialSpeed) : Set ℂ :=
  (backgroundShiftedContour B.contour B.tau).boundary

/-- `Gamma_tau ⊆ cG_tau`. -/
theorem shiftedBoundary_subset_shiftedRegion
    (B : BackgroundParameters hw P angularSpeed axialSpeed) :
    B.shiftedBoundary ⊆ B.shiftedRegion :=
  boundary_subset_closedRegion _

/-- Every `z ∈ cG_tau` has `Re z ≥ g_*`. -/
theorem growthFloor_le_re (B : BackgroundParameters hw P angularSpeed axialSpeed) {z : ℂ}
    (hz : z ∈ B.shiftedRegion) : B.contour.growthFloor ≤ z.re := by
  have := SpectralCircle.growthFloor_le_re (Γ := backgroundShiftedContour B.contour B.tau) hz
  simpa using this

/-- Every `z ∈ cG_tau` has `|Im z + tau| ≤ M`, since `z + i tau ∈ cG`. -/
theorem abs_im_add_tau_le (B : BackgroundParameters hw P angularSpeed axialSpeed) {z : ℂ}
    (hz : z ∈ B.shiftedRegion) : |z.im + B.tau| ≤ B.imBound := by
  have hmem : z + Complex.I * (B.tau : ℂ) ∈ B.contour.closedRegion :=
    (mem_backgroundShiftedContour_closedRegion_iff B.contour B.tau z).1 hz
  have him : (z + Complex.I * (B.tau : ℂ)).im = z.im + B.tau := by
    simp [Complex.add_im, Complex.mul_im]
  simpa [him] using B.abs_im_le _ hmem

/-- The background velocity `u^bg_n` of `eq:background-velocity` at the chosen axial shift. -/
def velocity (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) :
    TransverseRealW1Inf :=
  selectedBackgroundVelocity hw P angularSpeed axialSpeed B.tau
    B.tau_nonneg n

/-- The Fourier index `K_n` of the selected cell, as an integer. -/
def fourierIndex (_B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) : ℤ :=
  (P.scaleFamily.fourierIndex n : ℤ)

/-- The background operator `A^bg_{eps,n}` of `eq:background-operator` at the chosen axial
shift. -/
def operator (B : BackgroundParameters hw P angularSpeed axialSpeed) (epsilon : ℝ) (n : ℕ) :
    DomainOperator TransverseC2L2 TransverseC2H2 :=
  selectedBackgroundOperator hw P angularSpeed axialSpeed B.tau
    B.tau_nonneg epsilon (B.fourierIndex n) n

/-! ## The ten fields of `BackgroundCoercivity` -/

/-- **The `phase` hypothesis of `BackgroundCoercivity`**, i.e.
`eq:background-phase-positive` merged with the local axial multiplier of
`eq:background-local-coefficients` (the two zeroth-order pieces of `I₂` and `I₄` in
`eq:background-testing`).

On the core of a nonselected cell `m` the axial cut-off is one, so `s_n = r_m` is separated
from `1` by the ratio gap and Young's inequality gives the localised gain `tau c_q^2/2`; the
local axial velocity costs at most `C_v N` there, by `|r F(r)| ≤ 1` and
`2 pi K_n ell_m = N r_m`.
Off the cores the local axial velocity vanishes and only the uniform loss `M^2/(2 tau)`
remains. -/
theorem phase_bound (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) :
    ∀ᵐ q ∂transverseMeasure,
      (P.nonselectedCores n).indicator
            (fun _ ↦ B.tau * backgroundRatioGap r.q ^ 2 / 2 -
              backgroundAxialPhaseConstant hw angularSpeed axialSpeed p.wavenumber) q -
          B.imBound ^ 2 / (2 * B.tau) ≤
        ((P.backgroundMultiplier n).value q).re *
          (z.im + 2 * Real.pi * ((B.fourierIndex n : ℤ) : ℝ) *
            ((transverseW1InfComplexValueCoordLInf 2 (B.velocity n)) q).re) := by
  have htau := B.tau_pos
  have habs := B.abs_im_add_tau_le hz
  have hCv := parameterizedHelicalValueBound_nonneg hw angularSpeed axialSpeed
  have hN := p.wavenumber_pos.le
  have hKn : (0 : ℝ) ≤ 2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) := by positivity
  simp only [velocity, fourierIndex, Int.cast_natCast, backgroundMultiplier_value]
  filter_upwards [P.backgroundMultiplierValueLInf_coe_ae n,
    transverseW1InfComplexValueCoord_two_selectedBackgroundVelocity_coe_ae
      hw P angularSpeed axialSpeed B.tau B.tau_nonneg n] with q hbeta haxial
  rw [hbeta, haxial, Complex.add_re, Complex.ofReal_re]
  by_cases hq : q ∈ P.nonselectedCores n
  · obtain ⟨m, hmn, hqm⟩ := (P.mem_nonselectedCores_iff n q).mp hq
    rw [Set.indicator_of_mem hq,
      P.backgroundShiftedGlobalTorus_sub_one_eq_of_mem_torusLocalCoreDisk n m hqm,
      P.axialOffsetGlobalTorus_apply_two_of_mem_torusLocalCoreDisk B.tau m hqm,
      Complex.ofReal_re]
    have hr0 : 0 ≤ P.scaleFamily.cellRatio n m := P.scaleFamily.cellRatio_nonneg n m
    have hsep : r.q ≤ P.scaleFamily.cellRatio n m ∨ P.scaleFamily.cellRatio n m ≤ r.q⁻¹ := by
      have hd := P.scaleFamily.nonselected_frequencyRatio_dichotomy hmn
      have hcr : P.scaleFamily.cellRatio n m = P.scaleFamily.frequencyRatio n m :=
        P.scaleFamily.ell_ratio_eq_frequencyRatio n m
      rw [hcr]
      exact hd
    have hlower := backgroundMultiplierF_phase_lower_bound_ratioGap r.one_lt_q hr0 htau habs hsep
    have hratio := P.scaleFamily.axialAmplitude_eq_tau_mul_cellRatio B.tau n m
    have hid :
        backgroundMultiplierF (P.scaleFamily.cellRatio n m) *
            (z.im + 2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
              ((selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re +
                P.scaleFamily.axialAmplitude B.tau m)) =
          backgroundMultiplierF (P.scaleFamily.cellRatio n m) *
              (z.im + B.tau + B.tau * (P.scaleFamily.cellRatio n m - 1)) +
            backgroundMultiplierF (P.scaleFamily.cellRatio n m) *
              (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
                (selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re) := by
      linear_combination backgroundMultiplierF (P.scaleFamily.cellRatio n m) * hratio
    rw [hid]
    have hlocal :
        -(backgroundAxialPhaseConstant hw angularSpeed axialSpeed p.wavenumber) ≤
          backgroundMultiplierF (P.scaleFamily.cellRatio n m) *
            (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
              (selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re) := by
      have hre : |(selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re| ≤
          parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell m :=
        le_trans (Complex.abs_re_le_norm _)
          (le_trans (PiLp.norm_apply_le _ 2)
            (norm_selectedBackgroundHelicalSource_le_of_mem_core
              hw P angularSpeed axialSpeed n hmn hqm))
      have hkl : 2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) * P.scaleFamily.ell m =
          p.wavenumber * P.scaleFamily.cellRatio n m := by
        have hmatch := P.scaleFamily.axial_wavenumber_match n
        have hl : P.scaleFamily.ell n ≠ 0 := (P.scaleFamily.ell_pos n).ne'
        rw [ScaleFamily.cellRatio]
        field_simp
        linear_combination P.scaleFamily.ell m * hmatch
      have hFabs : P.scaleFamily.cellRatio n m *
          |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| ≤ 1 := by
        have hmul := abs_mul_backgroundMultiplierF_le_one hr0
        rwa [abs_mul, abs_of_nonneg hr0] at hmul
      have habsF : |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| ≤ 1 :=
        abs_backgroundMultiplierF_le_one hr0
      have hmain : |backgroundMultiplierF (P.scaleFamily.cellRatio n m) *
          (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
            (selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re)| ≤
          backgroundAxialPhaseConstant hw angularSpeed axialSpeed p.wavenumber := by
        rw [abs_mul, abs_mul, abs_of_nonneg hKn,
          backgroundAxialPhaseConstant]
        have hstep : |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| *
            (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
              |(selectedBackgroundHelicalSource hw P angularSpeed axialSpeed n q 2).re|) ≤
            |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| *
              (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
                (parameterizedHelicalValueBound hw angularSpeed axialSpeed *
                  P.scaleFamily.ell m)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hre hKn
        have hfinal : |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| *
            (2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
              (parameterizedHelicalValueBound hw angularSpeed axialSpeed *
                P.scaleFamily.ell m)) =
            parameterizedHelicalValueBound hw angularSpeed axialSpeed *
              (p.wavenumber * (P.scaleFamily.cellRatio n m *
                |backgroundMultiplierF (P.scaleFamily.cellRatio n m)|)) := by
          linear_combination (parameterizedHelicalValueBound hw angularSpeed axialSpeed *
            |backgroundMultiplierF (P.scaleFamily.cellRatio n m)|) * hkl
        rw [hfinal] at hstep
        refine le_trans hstep ?_
        have hle : p.wavenumber * (P.scaleFamily.cellRatio n m *
            |backgroundMultiplierF (P.scaleFamily.cellRatio n m)|) ≤ p.wavenumber * 1 :=
          mul_le_mul_of_nonneg_left hFabs hN
        nlinarith [hle, hCv]
      linarith [(abs_le.mp hmain).1]
    linarith [hlower, hlocal]
  · rw [Set.indicator_of_notMem hq,
      selectedBackgroundHelicalSource_eq_zero_of_notMem hw P angularSpeed axialSpeed n hq]
    obtain ⟨s, hs0, hsF, hsA⟩ := P.exists_backgroundShiftedGlobalTorus_sub_one_eq B.tau n q
    rw [hsF, Complex.ofReal_re]
    have hlower := backgroundMultiplierF_phase_lower_bound hs0 htau habs
    have hzero : ((0 : C3) 2).re = 0 := by simp
    rw [hzero]
    have hid : backgroundMultiplierF s *
          (z.im + 2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
            (0 + P.axialOffsetGlobalTorus B.tau q 2)) =
        backgroundMultiplierF s * (z.im + B.tau + B.tau * (s - 1)) := by
      linear_combination backgroundMultiplierF s * hsA
    rw [hid]
    have hsq : (0 : ℝ) ≤ B.tau / 2 * ((s - 1) / (1 + s)) ^ 2 := by positivity
    linarith [hlower, hsq]

/-- **The `transport` hypothesis of `BackgroundCoercivity`**, i.e. the amplitude half of
`eq:background-local-coefficients`, componentwise with `w = (u^bg_n)_⊥`:
`|w_j| |beta_n| ≤ C_v ell_n 1_{cC_n} ≤ C_v delta_-^{-1/2} sqrt(eps) 1_{cC_n}`.

On the core of the nonselected cell `m` one has `|w| ≤ C_v ell_m` and `|beta_n| = |F(r_m)|`,
so the product is `C_v ell_n |r_m F(r_m)| ≤ C_v ell_n`; off the cores `w` vanishes. -/
theorem transport_bound (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε) (j : Fin 2) :
    ∀ᵐ q ∂transverseMeasure,
      ‖(transverseW1InfComplexValueCoordLInf j.castSucc (B.velocity n)) q‖ *
          ‖((P.backgroundMultiplier n).value) q‖ ≤
        (P.nonselectedCores n).indicator
          (fun _ ↦ backgroundTransportConstant hw angularSpeed axialSpeed B.diffusivityLower *
            Real.sqrt ε) q := by
  have hCv := parameterizedHelicalValueBound_nonneg hw angularSpeed axialSpeed
  have hd : 0 < Real.sqrt B.diffusivityLower := Real.sqrt_pos.mpr B.diffusivityLower_pos
  have hsqrt : Real.sqrt B.diffusivityLower * P.scaleFamily.ell n ≤ Real.sqrt ε := by
    have h1 : Real.sqrt (B.diffusivityLower * P.scaleFamily.ell n ^ 2) ≤ Real.sqrt ε :=
      Real.sqrt_le_sqrt hlow
    rwa [Real.sqrt_mul B.diffusivityLower_pos.le,
      Real.sqrt_sq (P.scaleFamily.ell_pos n).le] at h1
  have hell : parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell n ≤
      backgroundTransportConstant hw angularSpeed axialSpeed B.diffusivityLower *
        Real.sqrt ε := by
    rw [backgroundTransportConstant, div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hCv]
  simp only [velocity, backgroundMultiplier_value]
  have hcore : ∀ᵐ q ∂transverseMeasure, ∀ m : ℕ, m ≠ n → q ∈ P.torusLocalCoreDisk m →
      ‖(transverseW1InfComplexValueCoordLInf j.castSucc
          (selectedBackgroundVelocity hw P angularSpeed axialSpeed B.tau B.tau_nonneg n)) q‖ ≤
        parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell m := by
    rw [ae_all_iff]
    intro m
    by_cases hmn : m = n
    · exact Filter.Eventually.of_forall fun _ hne ↦ absurd hmn hne
    · have hb :=
        norm_transverseW1InfComplexValueCoord_selectedBackgroundVelocity_le_of_mem_core
          hw P angularSpeed axialSpeed B.tau B.tau_nonneg n hmn j
      filter_upwards [hb] with q hbound _ hmem
      exact hbound hmem
  filter_upwards [hcore, P.backgroundMultiplierValueLInf_coe_ae n,
    transverseW1InfComplexValueCoord_selectedBackgroundVelocity_eq_zero_of_notMem
      hw P angularSpeed axialSpeed B.tau B.tau_nonneg n j] with q hbound hbeta hvanish
  by_cases hq : q ∈ P.nonselectedCores n
  · rw [Set.indicator_of_mem hq, hbeta]
    obtain ⟨m, hmn, hqm⟩ := (P.mem_nonselectedCores_iff n q).mp hq
    have hr0 : 0 ≤ P.scaleFamily.cellRatio n m := P.scaleFamily.cellRatio_nonneg n m
    rw [P.backgroundShiftedGlobalTorus_sub_one_eq_of_mem_torusLocalCoreDisk n m hqm,
      Complex.norm_real, Real.norm_eq_abs]
    have hFabs : P.scaleFamily.cellRatio n m *
        |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| ≤ 1 := by
      have hmul := abs_mul_backgroundMultiplierF_le_one hr0
      rwa [abs_mul, abs_of_nonneg hr0] at hmul
    have hlnz : P.scaleFamily.ell n ≠ 0 := (P.scaleFamily.ell_pos n).ne'
    have hlm : P.scaleFamily.ell m =
        P.scaleFamily.ell n * P.scaleFamily.cellRatio n m := by
      rw [ScaleFamily.cellRatio]
      field_simp
    have hstep : ‖(transverseW1InfComplexValueCoordLInf j.castSucc
          (selectedBackgroundVelocity hw P angularSpeed axialSpeed B.tau B.tau_nonneg n)) q‖ *
            |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| ≤
        parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell m *
          |backgroundMultiplierF (P.scaleFamily.cellRatio n m)| :=
      mul_le_mul_of_nonneg_right (hbound m hmn hqm) (abs_nonneg _)
    refine le_trans hstep (le_trans ?_ hell)
    have hln : (0 : ℝ) ≤ P.scaleFamily.ell n := (P.scaleFamily.ell_pos n).le
    calc parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell m *
            |backgroundMultiplierF (P.scaleFamily.cellRatio n m)|
        = parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell n *
            (P.scaleFamily.cellRatio n m *
              |backgroundMultiplierF (P.scaleFamily.cellRatio n m)|) := by
          rw [hlm]; ring
      _ ≤ parameterizedHelicalValueBound hw angularSpeed axialSpeed * P.scaleFamily.ell n * 1 :=
          mul_le_mul_of_nonneg_left hFabs (mul_nonneg hCv hln)
      _ = parameterizedHelicalValueBound hw angularSpeed axialSpeed *
            P.scaleFamily.ell n := by ring
  · rw [Set.indicator_of_notMem hq, hvanish hq, norm_zero, zero_mul]

/--
**The full coercivity witness of `eq:background-coercivity`** under the parameter choices
`eq:axial-separation-choice` and `eq:background-diffusion-small`.

For every selected cell `n`, every diffusivity `eps` with `delta_n = eps/ell_n^2` in the window
`[delta_-, delta_+]`, and every `z` of the translated region `cG_tau`, the ten fields of
`BackgroundCoercivity` hold for the background multiplier `beta_n`, the background velocity
`u^bg_n` and the nonselected cores `cC_n`.  The retained growth rate is `g_*/2`:
`g_* - M^2/(2 tau) - C_1 delta_+ d(K_0)^2 ≥ g_* - g_*/4 - g_*/4`.
-/
def coercivity (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ) {ε : ℝ}
    (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) :
    BackgroundCoercivity (P.backgroundMultiplier n) (B.velocity n) ε (B.fourierIndex n) z
      (P.nonselectedCores n) where
  measurable := P.measurableSet_nonselectedCores n
  eps_pos := heps
  norm_value_le_one := P.norm_backgroundMultiplier_value_le_one n
  divergenceFree :=
    selectedBackgroundVelocity_isTransverseDivergenceFree hw P angularSpeed axialSpeed
      B.tau B.tau_nonneg n
  phaseFloor := B.tau * backgroundRatioGap r.q ^ 2 / 2 -
    backgroundAxialPhaseConstant hw angularSpeed axialSpeed p.wavenumber
  phaseDefect := B.imBound ^ 2 / (2 * B.tau)
  transportConstant :=
    backgroundTransportConstant hw angularSpeed axialSpeed B.diffusivityLower
  stretchingConstant := parameterizedHelicalFirstDerivativeBound hw angularSpeed axialSpeed
  transportConstant_nonneg :=
    backgroundTransportConstant_nonneg hw angularSpeed axialSpeed B.diffusivityLower
  stretchingConstant_nonneg :=
    parameterizedHelicalFirstDerivativeBound_nonneg hw angularSpeed axialSpeed
  phase := B.phase_bound n hz
  transport := fun j ↦ B.transport_bound n hlow j
  stretching := fun j ↦
    norm_transverseW1InfHorizontalDeriv_selectedBackgroundVelocity_le
      hw P angularSpeed axialSpeed B.tau B.tau_nonneg n j
  core_nonneg := by
    have hsep := B.separation_ge
    rw [backgroundCoercivityConstant] at hsep
    linarith
  growth := B.contour.growthFloor / 2
  growth_pos := by linarith [B.growthFloor_pos]
  growth_le := by
    have hre := B.growthFloor_le_re hz
    have hdefect := B.phaseDefect_le
    have hk : (0 : ℝ) ≤ ε * (2 * Real.pi * ((B.fourierIndex n : ℤ) : ℝ)) ^ 2 :=
      mul_nonneg heps.le (sq_nonneg _)
    have hgrad := P.gradSupNormSq_backgroundMultiplier_le n
    have hln : (0 : ℝ) < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
    have hlnz : P.scaleFamily.ell n ≠ 0 := hln.ne'
    have hdelta : ε / P.scaleFamily.ell n ^ 2 ≤ B.diffusivityUpper := by
      rw [div_le_iff₀ (by positivity)]
      exact hupp
    have h1 : ε * (P.backgroundMultiplier n).gradSupNormSq ≤
        ε * (2 * (3 * (axialPlateauLipschitzConstant : ℝ) *
          (P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n)) ^ 2) :=
      mul_le_mul_of_nonneg_left hgrad heps.le
    have heq : ε * (2 * (3 * (axialPlateauLipschitzConstant : ℝ) *
          (P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n)) ^ 2) =
        18 * (axialPlateauLipschitzConstant : ℝ) ^ 2 *
          P.scaleFamily.bufferRadius 0 ^ 2 * (ε / P.scaleFamily.ell n ^ 2) := by
      field_simp
      ring
    have h2 : 18 * (axialPlateauLipschitzConstant : ℝ) ^ 2 *
          P.scaleFamily.bufferRadius 0 ^ 2 * (ε / P.scaleFamily.ell n ^ 2) ≤
        18 * (axialPlateauLipschitzConstant : ℝ) ^ 2 *
          P.scaleFamily.bufferRadius 0 ^ 2 * B.diffusivityUpper :=
      mul_le_mul_of_nonneg_left hdelta (by positivity)
    have h3 : 18 * (axialPlateauLipschitzConstant : ℝ) ^ 2 *
          P.scaleFamily.bufferRadius 0 ^ 2 * B.diffusivityUpper =
        backgroundDiffusionConstant * B.diffusivityUpper * P.scaleFamily.ell 0 := by
      rw [backgroundDiffusionConstant, P.scaleFamily.bufferRadius_sq 0]
      ring
    rw [heq] at h1
    linarith [B.diffusion_small]

/-- The background operator `A^bg_{eps,n}` has injective pencil at every point of `cG_tau`.
This is the hypothesis of
`DomainOperator.hasResolventAt_of_compactStateResolvent_of_pencil_injective`; it is the first
of the two consequences of `eq:background-coercivity`. -/
theorem pencil_injective (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) :
    Function.Injective ((B.operator ε n).pencil z) :=
  (B.coercivity n heps hlow hupp hz).pencil_injective

/-- **`eq:bg-resolvent`** in the a-priori form:
`‖h‖₂ + sqrt(eps)‖∇_⊥ h‖₂ ≤ C ‖(z - A^bg_{eps,n})h‖₂` with the explicit constant
`C = backgroundResolventConstant (g_*/2) = 2 sqrt 2/g_* + 2 sqrt 2/sqrt(g_*)`, which depends on
no parameter other than the growth floor. -/
theorem norm_add_sqrt_eps_gradientEnergy_le
    (B : BackgroundParameters hw P angularSpeed axialSpeed) (n : ℕ)
    {ε : ℝ} (heps : 0 < ε) (hlow : B.diffusivityLower * P.scaleFamily.ell n ^ 2 ≤ ε)
    (hupp : ε ≤ B.diffusivityUpper * P.scaleFamily.ell n ^ 2)
    {z : ℂ} (hz : z ∈ B.shiftedRegion) (h : TransverseC2H2) :
    ‖transverseH2Embedding h‖ + Real.sqrt (ε * transverseGradientEnergy h) ≤
      BackgroundCoercivity.backgroundResolventConstant (B.contour.growthFloor / 2) *
        ‖(B.operator ε n).pencil z h‖ :=
  (B.coercivity n heps hlow hupp hz).norm_add_sqrt_eps_gradientEnergy_le h

end BackgroundParameters

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
