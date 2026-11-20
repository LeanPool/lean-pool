/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.LocalSeedC2
public import LeanPool.FastDynamo.Local.HorizontalSeedWitness
public import LeanPool.FastDynamo.Local.HorizontalModeEigenpair

/-!
# The concrete local seed at `N = 2π`

This module constructs the `LocalSeedC2` variant of Proposition 2.2 (`prop:local-seed`) at
`k_* = 1`, the paper's axial wavenumber `N = 2π`. The witness is an `L²` field supported in
a disk almost everywhere. The record allows widths in `(0,1)`, and this construction chooses
a width at most `1/2`. The paper requires a smooth compactly supported witness and a strictly
smaller width.

The ingredients, in the order of the proof of `prop:local-seed`:

* `PonomarenkoSegmentRoot.exists_certifiedInterfaceData_two_pi` supplies the angular
  speed `Ω` and the transverse root `κ` at `ϱ = 32`, with `Re λ_* ≥ 448 - 4π²` (the paper
  takes `ϱ` sufficiently large and proves `Re λ_* ≥ (7/16)ϱ² - 4π² > 0`, `eq:local-eigenvalue`;
  `ϱ = 32` and the resulting numerals are choices of the formalisation);
* `HorizontalMode.horizontalModeWeakIdentity_holds` supplies the eigenmode, so
* `HorizontalMode.modeIsolation` supplies the contour `Γ` with
  `g_* ≥ (3/4) Re λ_* ≥ (3/4)(448 - 4π²)` (the paper's `eq:spectral-gap` only asserts
  `g_* > 0`);
* `HorizontalMode.exists_seedThresholds` and `HorizontalMode.exists_seedNeumannData`
  supply the thresholds `h₁`, `η₁` and the uniform `L² → H¹` bound `K_res`;
* `HorizontalMode.exists_horizontalSeedWitness` supplies `L_*` and `f_*` with
  `Re⟨P⁰ f_*, f_*⟩ > 3/4`;
* `Local/HorizontalSeedUniformResolvent.lean` turns the `δ`-dependent pieces into
  one `δ`-uniform `L² → H²` bound `L` and identifies the Riesz projection of the strong
  generator with that of the form generator.

The smoothing width is `h = min(h₀, h₁, 1/2)` and the diffusivity interval is
`I = [1 - η, 1 + η]` with `η = min(η₀, η₁, 1/2)`, so that `0 < 1/2 ≤ δ₋ < 1 < δ₊ ≤ 3/2`.

## Main results

* `HorizontalMode.exists_localSeedC2_two_pi` — the existence statement;
* `HorizontalMode.localSeedC2` — the chosen inhabitant;
* `HorizontalMode.localSeedC2_kStar`, `HorizontalMode.localSeedC2_wavenumber`,
  `HorizontalMode.seedGrowthFloorBound_le_localSeedC2_growthFloor`,
  `HorizontalMode.localSeedC2_angularSpeed_pos` — the numeric facts the main parameter chain uses.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory HorizontalWeakForm PonomarenkoFreeOmegaInterface

namespace HorizontalMode

/-! ## The numeric growth floor -/

/-- **The growth floor of the concrete seed**, `g_* ≥ (3/4)(448 - 4π²) ≈ 306`, at
`k_* = 1`.  The explicit value is a choice of the formalisation (`ϱ = 32` and the contour
radius `r ≤ Re λ_*/4`); the paper only asserts `g_* > 0`. -/
def seedGrowthFloorBound : ℝ := 3 / 4 * (448 - (2 * Real.pi) ^ 2)

private theorem exists_circle_graph_bound (center : ℂ) (radius embedding solution : ℝ)
    (hradius : 0 ≤ radius) (hembedding : 0 ≤ embedding) (hsolution : 0 ≤ solution) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ z ∈ Metric.sphere center radius,
      ∀ t : ℝ, 0 ≤ t → t ≤ solution → t + (1 + ‖z‖ * (embedding * t)) ≤ bound := by
  have hcenter : 0 ≤ ‖center‖ + radius := add_nonneg (norm_nonneg _) hradius
  refine ⟨solution + (1 + (‖center‖ + radius) * (embedding * solution)), ?_, ?_⟩
  · exact add_nonneg hsolution
      (add_nonneg zero_le_one (mul_nonneg hcenter (mul_nonneg hembedding hsolution)))
  · intro z hz t ht0 ht
    have hmul := mul_le_mul (norm_le_of_mem_sphere hz)
      (mul_le_mul_of_nonneg_left ht hembedding) (mul_nonneg hembedding ht0) hcenter
    exact add_le_add ht (add_le_add_right hmul 1)

private theorem exists_bound_with_projection (N delta : ℝ)
    (coefficients : WholePlaneVelocityCoefficients) (form : ComplexForm WholePlaneC2H1)
    (hdelta : delta ≠ 0) (hgradient : coefficients.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      form b phi = horizontalWeakFormDelta N delta coefficients.value b phi)
    {center : ℂ} {radius : ℝ}
    (resolvent : HasResolventOn (horizontalAssociatedOperator form) (Metric.sphere center radius))
    {pairBound graphBound : ℝ}
    (hpair : ‖horizontalStrongPairMap N delta coefficients form‖ ≤ pairBound)
    (hpair0 : 0 ≤ pairBound)
    (hgraph : ∀ z ∈ Metric.sphere center radius, ‖resolvent.inv z‖ ≤ graphBound) :
    ∃ bound : WholePlaneLocalResolventBound coefficients N delta (Metric.sphere center radius)
      (‖wholePlaneH2OfPair C2‖ * (pairBound * graphBound)),
      bound.resolvent.rieszProjection = resolvent.rieszProjection := by
  refine ⟨horizontalLocalResolventBoundOfBounds N delta coefficients form
    hdelta hgradient hform resolvent hpair hpair0 hgraph le_rfl, ?_⟩
  exact horizontalStrongResolvent_rieszProjection N delta coefficients form
    hdelta hgradient hform resolvent

private theorem exists_smoothed_resolvent_bound
    {N Omega delta : ℝ} {h : PonomarenkoSmoothingWidth}
    {w : WholePlaneC3LInf} {lambda : ℂ} {iso : HorizontalIsolation N w lambda}
    (data : HorizontalNeumannData N delta (horizontalSmoothedModeVelocity N Omega h) w lambda iso)
    (hdelta : delta ≠ 0) {pairBound graphBound : ℝ}
    (hpair : ‖horizontalStrongPairMap N delta (smoothedModeCoefficients N Omega h)
      (horizontalWeakFormDelta N delta (horizontalSmoothedModeVelocity N Omega h))‖ ≤ pairBound)
    (hpair0 : 0 ≤ pairBound)
    (hgraph : ∀ z ∈ Metric.sphere lambda iso.radius, ‖data.contourResolvent.inv z‖ ≤ graphBound) :
    ∃ bound : WholePlaneLocalResolventBound (smoothedModeCoefficients N Omega h) N delta
      (Metric.sphere lambda iso.radius) (‖wholePlaneH2OfPair C2‖ * (pairBound * graphBound)),
      bound.resolvent.rieszProjection = data.projection := by
  let coefficients := smoothedModeCoefficients N Omega h
  let form := horizontalWeakFormDelta N delta (horizontalSmoothedModeVelocity N Omega h)
  have hform (b phi : WholePlaneC2H1) :
      form b phi = horizontalWeakFormDelta N delta coefficients.value b phi :=
    congrArg (fun v ↦ horizontalWeakFormDelta N delta v b phi)
      (smoothedModeCoefficients_value N Omega h).symm
  have hgradient : coefficients.HasWeakGradient :=
    smoothedModeCoefficients_hasWeakGradient N Omega h
  let resolvent : HasResolventOn (horizontalAssociatedOperator form)
      (Metric.sphere lambda iso.radius) := data.contourResolvent
  exact exists_bound_with_projection N delta coefficients form
    hdelta hgradient hform resolvent hpair hpair0 hgraph

/-! ## The construction -/

/--
**The concrete `L²`-witness variant of Proposition 2.2** (`prop:local-seed`).

At `k_* = 1`, the variant has a witness with almost-everywhere disk support, a width parameter
of type `PonomarenkoSmoothingWidth`, and the growth floor `g_* ≥ (3/4)(448 - 4π²)`.
-/
theorem exists_localSeedC2_two_pi :
    ∃ s : LocalSeedC2, s.parameters.kStar = 1 ∧
      s.parameters.wavenumber = 2 * Real.pi ∧
      seedGrowthFloorBound ≤ s.growthFloor ∧ 0 < s.angularSpeed := by
  obtain ⟨Omega, kappa, hd, -, hfloor⟩ := exists_certifiedInterfaceData_two_pi
  let iso := modeIsolation hd
  have hweak := horizontalModeWeakIdentity_holds hd
  obtain ⟨Lstar, f, hLstar, hf, hsupp, hwitness⟩ := exists_horizontalSeedWitness hd hweak
  obtain ⟨h0, eta0, _K, _Kdiff, Kres, hh0, heta0, _hK0, _hKd0, hKres0, hmain⟩ :=
    exists_seedNeumannData hd
  obtain ⟨h1, eta1, hh1, heta1, hthr⟩ := exists_seedThresholds hd
  have hj0 : (0 : ℝ) ≤ ‖wholePlaneH1Embedding C2‖ :=
    ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)
  obtain ⟨eta, hetapos, hetahalf, hetale0, hetale1⟩ :
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧ eta ≤ eta0 ∧ eta ≤ eta1 :=
    ⟨min (min eta0 eta1) (1 / 2), lt_min (lt_min heta0 heta1) (by norm_num),
      min_le_right _ _, le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _)⟩
  obtain ⟨hw, hhw0, hhw1⟩ :
      ∃ hw : PonomarenkoSmoothingWidth, (hw : ℝ) ≤ h0 ∧ (hw : ℝ) ≤ h1 :=
    ⟨⟨min (min h0 h1) (1 / 2), lt_min (lt_min hh0 hh1) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩,
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _)⟩
  obtain ⟨C, hC0, hCle⟩ := exists_circle_graph_bound
    (horizontalEigenvalue (2 * Real.pi) kappa) iso.radius
    ‖wholePlaneH1Embedding C2‖ Kres iso.radius_pos.le hj0 hKres0
  obtain ⟨P, hP0, hPle⟩ : ∃ P : ℝ, 0 ≤ P ∧
      ∀ delta : ℝ, 1 - eta ≤ delta → delta ≤ 1 + eta →
        ‖horizontalStrongPairMap (2 * Real.pi) delta
          (smoothedModeCoefficients (2 * Real.pi) Omega hw)
          (horizontalWeakFormDelta (2 * Real.pi) delta
            (horizontalSmoothedModeVelocity (2 * Real.pi) Omega hw))‖ ≤ P :=
    ⟨horizontalStrongPairBound (2 * Real.pi) (1 - eta) (1 + eta)
        (smoothedModeCoefficients (2 * Real.pi) Omega hw),
      horizontalStrongPairBound_nonneg _ _ _ _,
      fun delta hlo hup =>
        norm_horizontalStrongPairMap_le_bound _ _ _ (by linarith) hlo hup⟩
  have hresult : ∀ delta ∈ Set.Icc (1 - eta) (1 + eta),
      ∃ B : WholePlaneLocalResolventBound (smoothedModeCoefficients (2 * Real.pi) Omega hw)
          (2 * Real.pi) delta (Metric.sphere (horizontalEigenvalue (2 * Real.pi) kappa) iso.radius)
          (‖wholePlaneH2OfPair C2‖ * (P * C)),
        1 / 2 < (inner ℂ (B.resolvent.rieszProjection f) f).re := by
    intro delta hdelta
    obtain ⟨hlo, hup⟩ := hdelta
    have habs : |delta - 1| ≤ eta := abs_le.mpr ⟨by linarith, by linarith⟩
    have hdpos : (0 : ℝ) < delta := by linarith
    have hne : delta ≠ 0 := ne_of_gt hdpos
    have hKres := (hmain hw delta hhw0 (le_trans habs hetale0)).1
    obtain ⟨nd, -, hndinner⟩ := hthr hw delta hhw1 (le_trans habs hetale1)
    obtain ⟨bound, hprojection⟩ := exists_smoothed_resolvent_bound
      (N := 2 * Real.pi) (Omega := Omega) (h := hw) (iso := iso)
      nd hne (hPle delta hlo hup) hP0 fun z hz ↦
        (nd.norm_contourResolvent_inv_le hz).trans
          (hCle z hz _ (ContinuousLinearMap.opNorm_nonneg _) (hKres z hz))
    refine ⟨bound, ?_⟩
    rw [hprojection]
    exact re_inner_gt_half_of_lt_quarter hwitness (hndinner f hf)
  obtain ⟨s, hk, hN, -, -, hG, -, hOmega, -, -, -, -⟩ :=
    LocalSeedC2.exists_localSeedC2_of_data 1 one_pos (N := 2 * Real.pi) (by norm_num)
      (1 - eta) (1 + eta) (by linarith) (by linarith) (by linarith)
      iso.contour iso.growthFloor_pos hw Omega
      (jumpAxialSpeed (2 * Real.pi) Omega) rfl (‖wholePlaneH2OfPair C2‖ * (P * C))
      (mul_nonneg (ContinuousLinearMap.opNorm_nonneg (wholePlaneH2OfPair C2))
        (mul_nonneg hP0 hC0)) Lstar hLstar f hf hsupp hresult
  refine ⟨s, hk, hN, ?_, ?_⟩
  · have hgf : s.growthFloor = iso.contour.growthFloor := by
      change s.parameters.contour.growthFloor = _
      rw [hG]
    rw [hgf]
    have hge := iso.growthFloor_ge
    have hre : (448 : ℝ) - (2 * Real.pi) ^ 2 ≤
        (horizontalEigenvalue (2 * Real.pi) kappa).re := hfloor.2.2.2
    simp only [seedGrowthFloorBound]
    linarith
  · rw [hOmega]
    exact hd.omega_pos

/-- **The concrete two-component local seed** at `N = 2π`. -/
def localSeedC2 : LocalSeedC2 := Classical.choose exists_localSeedC2_two_pi

/-- `k_* = 1`, so the concrete seed's wavenumber is `N = 2π`. -/
theorem localSeedC2_kStar : localSeedC2.parameters.kStar = 1 :=
  (Classical.choose_spec exists_localSeedC2_two_pi).1

/-- The concrete seed's axial wavenumber is `N = 2π`. -/
theorem localSeedC2_wavenumber : localSeedC2.parameters.wavenumber = 2 * Real.pi :=
  (Classical.choose_spec exists_localSeedC2_two_pi).2.1

/-- **The numeric growth floor of the concrete seed**: `g_* ≥ (3/4)(448 - 4π²)`. -/
theorem seedGrowthFloorBound_le_localSeedC2_growthFloor :
    seedGrowthFloorBound ≤ localSeedC2.growthFloor :=
  (Classical.choose_spec exists_localSeedC2_two_pi).2.2.1

/-- The concrete seed's helical angular speed `Ω` is strictly positive (`omega_pos` of the
certified interface data).  It is what makes the global velocity's chart representative fail to
be `C¹` at the accumulation point. -/
theorem localSeedC2_angularSpeed_pos : 0 < localSeedC2.angularSpeed :=
  (Classical.choose_spec exists_localSeedC2_two_pi).2.2.2

/-- **The seed-side inputs of the global parameter chain**, at the concrete seed. -/
def globalSeedInterface : GlobalSeedInterface := localSeedC2.toGlobalSeedInterface

/-- The global interface of the concrete seed has the concrete seed's scalar data. -/
@[simp] theorem globalSeedInterface_parameters :
    globalSeedInterface.parameters = localSeedC2.parameters := rfl

/-- The growth floor seen by the global parameter chain is the concrete seed's. -/
theorem seedGrowthFloorBound_le_globalSeedInterface_growthFloor :
    seedGrowthFloorBound ≤ globalSeedInterface.growthFloor :=
  seedGrowthFloorBound_le_localSeedC2_growthFloor

/-- The angular speed seen by the global parameter chain is the concrete seed's, hence positive. -/
theorem globalSeedInterface_angularSpeed_pos : 0 < globalSeedInterface.angularSpeed :=
  localSeedC2_angularSpeed_pos

/-- The angular speed of the constructed velocity is nonzero, the hypothesis of the qualitative
regularity statements of `Global/TorusGlobalVelocityRegularity.lean`. -/
theorem globalSeedInterface_angularSpeed_ne_zero : globalSeedInterface.angularSpeed ≠ 0 :=
  ne_of_gt globalSeedInterface_angularSpeed_pos

end HorizontalMode

end

end FastDynamo
