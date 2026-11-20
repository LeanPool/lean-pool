/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalSeedUniformResolvent
public import LeanPool.FastDynamo.Global.GlobalParameterChoice

/-!
# The two-component local seed record `prop:local-seed`

This record gives an `L²`-witness variant of Proposition 2.2 (`prop:local-seed`).
Its witness is supported in a disk almost everywhere and its width parameter belongs to
`(0,1)`. The paper requires a smooth compactly supported witness and a width in `(0,1/2)`.
The data are

`(N, v, I, Γ, 𝒢, g_*, f_*, L_*)`

with the four clauses

* (i)   `v = v_h` is a compactly supported smooth helical velocity with `Div_⊥ v_⊥ = 0`,
  angular profile `ω = Ω χ_h` and axial profile `w = U χ_h`, `U = -Ω/N`.  The paper states
  this outside the proposition, as `eq:smooth-local-velocity`, and the proposition
  then reads "for the reference velocity profile on `ℝ²`, `v = v_h`, from
  `eq:smooth-local-velocity`";
* (ii)  `Γ ⊂ ρ(𝓛_δ)` for every `δ ∈ I = [δ₋, δ₊]`, with one uniform resolvent bound `L`
  (`eq:local-continuation-bound`).  The paper asks for the `L² → H¹` norm;
  what this structure carries is the
  stronger `L² → H²` bound, of which the paper's is a corollary through `H² ↪ H¹`;
* (iii) `Re⟨P_δ f_*, f_*⟩ > 1/2` for every `δ ∈ I`, where `f_*` is a unit `L²` field supported
  in `D(0, L_*)` and `P_δ` is the Riesz projection of `𝓛_δ` on `Γ`
  (`eq:local-spectral-witness`);
* (iv)  `g_* = min_𝒢 Re ζ > 0` (`eq:spectral-gap`).

`LocalSeedParameters` (`Local/SeedParameters.lean`) already carries `N = 2π k_*`,
`I = [δ₋, δ₊]` with `0 < δ₋ < 1 < δ₊`, the contour `Γ` and `g_* = Γ.growthFloor > 0`, so
clause (iv) is one of its fields and `LocalSeedC2` extends it with the velocity data, the
resolvent clause and the witness clause.

## Design notes

* The velocity is stored through its three parameters `(h, Ω, U)` rather than as an abstract
  Schwartz map: the global velocity layer (`Global/TorusHelicalSource.lean`,
  `Global/TorusFullVelocityConcrete.lean`, `Global/GlobalParameterChoice.lean`) is
  parameterised by exactly that triple, and `GlobalSeedInterface` stores exactly that triple.
  `LocalSeedC2.velocity` and `LocalSeedC2.coefficients` are then *definitions*, so the
  `SchwartzMap` view and the `WholePlaneVelocityCoefficients` view used by
  `horizontalLocalOperator` are provably — indeed definitionally — the same velocity.
* `P_δ` is the Riesz projection of the **strong** operator `horizontalLocalOperator N δ v`,
  because that is the operator whose Riesz projection the selected-cell transfer
  (`eq:selected-contour-identity`, through `Reduction/ExactScalingC2.lean`) moves to the torus.
  `Local/HorizontalSeedUniformResolvent.lean` shows it coincides with the Riesz projection of
  the form operator, which is where `Local/HorizontalRieszPerturbation.lean` proves the
  quantitative statement.
* The spectral-witness construction in `Local/HorizontalSeedWitness.lean` supplies the
  almost-everywhere support certificate needed by the downstream proofs.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped SchwartzMap

/-! ## The record -/

/--
**The two-component `L²`-witness variant** of Proposition 2.2 (`prop:local-seed`).
The width is in `(0,1)`, and the `L²` witness vanishes outside the support disk almost everywhere.

The scalar prefix `parameters` supplies `N = 2π k_*`, the diffusivity interval
`I = [δ₋, δ₊]` with `0 < δ₋ < 1 < δ₊`, the contour `Γ` with closed interior `𝒢`, and the
growth floor `g_* = Γ.growthFloor > 0`, which is clause (iv).  The remaining fields are the
velocity of clause (i), the uniform resolvent bound of clause (ii) and the spectral witness of
clause (iii).
-/
structure LocalSeedC2 where
  /-- The scalar and contour data `N = 2π k_*`, `I = [δ₋, δ₊]`, `Γ`, `𝒢`, `g_* > 0`. -/
  parameters : LocalSeedParameters
  /-- The smoothing width `h ∈ (0,1)` of the radial cutoff `χ_h`. -/
  smoothingWidth : PonomarenkoSmoothingWidth
  /-- The angular speed `Ω` of the helical profile. -/
  angularSpeed : ℝ
  /-- The axial speed `U` of the helical profile. -/
  axialSpeed : ℝ
  /-- The paper's normalisation `U = -Ω/N` (`eq:jump-flow`), which is what makes the
  axial phase `Ω + N U` vanish. -/
  axialSpeed_eq : axialSpeed = -angularSpeed / parameters.wavenumber
  /-- The uniform `L² → H²` resolvent bound `L`.  The paper's
  `eq:local-continuation-bound` is its `L² → H¹` corollary. -/
  resolventBound : ℝ
  /-- `L ≥ 0`. -/
  resolventBound_nonneg : 0 ≤ resolventBound
  /-- **Clause (ii).**  For every admissible rescaled diffusivity the contour lies in the
  resolvent set of `𝓛_δ` and the resolvent obeys the single bound `L`. -/
  resolvents : ∀ delta ∈ parameters.interval,
    WholePlaneLocalResolventBound
      (wholePlaneSchwartzVelocityCoefficients
        (parameterizedSmoothedVelocity smoothingWidth angularSpeed axialSpeed))
      parameters.wavenumber delta parameters.contour.boundary resolventBound
  /-- The support radius `L_*` of the spectral witness. -/
  witnessSupportRadius : ℝ
  /-- `L_* ≥ 1`. -/
  one_le_witnessSupportRadius : 1 ≤ witnessSupportRadius
  /-- The spectral witness `f_*`. -/
  witness : WholePlaneC2L2
  /-- `‖f_*‖₂ = 1`. -/
  norm_witness : ‖witness‖ = 1
  /-- `supp f_* ⊂ D(0, L_*)`, in the almost-everywhere form carried by an `L²` class. -/
  witness_ae_zero : ∀ᵐ y ∂(volume : Measure WholePlane),
    witnessSupportRadius < ‖y‖ → (witness : WholePlane → C2) y = 0
  /-- **Clause (iii), `eq:local-spectral-witness`.**  The Riesz projection of `𝓛_δ` on `Γ`
  has quadratic form larger than `1/2` at `f_*`, uniformly in `δ ∈ I`. -/
  re_inner_projection_witness : ∀ (delta : ℝ) (hdelta : delta ∈ parameters.interval),
    1 / 2 <
      (inner ℂ ((resolvents delta hdelta).resolvent.rieszProjection witness) witness).re

namespace LocalSeedC2

variable (s : LocalSeedC2)

/-! ## Scalar data -/

/-- The local axial wavenumber `N = 2π k_*`. -/
abbrev wavenumber : ℝ := s.parameters.wavenumber

/-- The admissible interval `I = [δ₋, δ₊]` of rescaled diffusivities. -/
abbrev interval : Set ℝ := s.parameters.interval

/-- The spectral contour `Γ`. -/
abbrev contour : SpectralCircle := s.parameters.contour

/-- The growth floor `g_* = min_𝒢 Re ζ`. -/
abbrev growthFloor : ℝ := s.parameters.contour.growthFloor

/-- **Clause (iv)**: `g_* > 0`. -/
theorem growthFloor_pos : 0 < s.growthFloor :=
  s.parameters.growthFloor_pos

/-- The support radius of the witness is positive. -/
theorem witnessSupportRadius_pos : 0 < s.witnessSupportRadius :=
  lt_of_lt_of_le zero_lt_one s.one_le_witnessSupportRadius

/-! ## Clause (i): the velocity -/

/-- **The seed velocity `v_h`**: the smoothed helical field with angular speed `Ω`, axial
speed `U` and radial cutoff `χ_h`. -/
def velocity : SchwartzMap WholePlane C3 :=
  parameterizedSmoothedVelocity s.smoothingWidth s.angularSpeed s.axialSpeed

/-- The bounded coefficient package of the seed velocity, the argument of
`horizontalLocalOperator`. -/
def coefficients : WholePlaneVelocityCoefficients :=
  wholePlaneSchwartzVelocityCoefficients s.velocity

/-! ## Clause (ii): the resolvent family -/

/-- The uniform resolvent bound at one admissible diffusivity, restated through the named
coefficient package. -/
def resolventBoundData (delta : ℝ) (hdelta : delta ∈ s.interval) :
    WholePlaneLocalResolventBound s.coefficients s.wavenumber delta s.contour.boundary
      s.resolventBound :=
  s.resolvents delta hdelta

/-- The chosen `L² → H²` resolvent of `𝓛_δ` on `Γ`. -/
def resolver (delta : ℝ) (hdelta : delta ∈ s.interval) :
    HasResolventOn (horizontalLocalOperator s.wavenumber delta s.coefficients)
      s.contour.boundary :=
  (s.resolventBoundData delta hdelta).resolvent

/-- **`eq:local-continuation-bound`, in its stronger `H²` form**: `‖R_δ(ζ)‖_{L²→H²} ≤ L` on
`Γ`, uniformly in `δ ∈ I`.  The paper states the `L² → H¹` bound, which follows. -/
theorem norm_resolver_le (delta : ℝ) (hdelta : delta ∈ s.interval) (z : ℂ)
    (hz : z ∈ s.contour.boundary) :
    ‖(s.resolver delta hdelta).inv z‖ ≤ s.resolventBound :=
  (s.resolventBoundData delta hdelta).norm_inv_le z hz

/-! ## Clause (iii): the Riesz projection and the witness -/

/-- **The Riesz projection `P_δ`** of the strong local generator `𝓛_δ` on `Γ`. -/
def projection (delta : ℝ) (hdelta : delta ∈ s.interval) :
    WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  (s.resolver delta hdelta).rieszProjection

/-- **`eq:local-spectral-witness`**: `Re⟨P_δ f_*, f_*⟩ > 1/2`. -/
theorem re_inner_projection_witness_gt (delta : ℝ) (hdelta : delta ∈ s.interval) :
    1 / 2 < (inner ℂ (s.projection delta hdelta s.witness) s.witness).re :=
  s.re_inner_projection_witness delta hdelta

/-! ## The interface consumed by the global parameter chain -/

/-- **The seed-side inputs of the global parameter chain.**  Every field of
`GlobalSeedInterface` (`Global/GlobalParameterChoice.lean`) is a field or an immediate
consequence of a field of `LocalSeedC2`. -/
def toGlobalSeedInterface : GlobalSeedInterface where
  parameters := s.parameters
  smoothingWidth := s.smoothingWidth
  angularSpeed := s.angularSpeed
  axialSpeed := s.axialSpeed
  witnessSupportRadius := s.witnessSupportRadius
  witnessSupportRadius_pos := s.witnessSupportRadius_pos
  resolventBound := s.resolventBound
  resolventBound_nonneg := s.resolventBound_nonneg

/-- The interface keeps the seed's scalar and contour data. -/
@[simp] theorem toGlobalSeedInterface_parameters :
    s.toGlobalSeedInterface.parameters = s.parameters := rfl

/-- The interface keeps the seed's smoothing width. -/
@[simp] theorem toGlobalSeedInterface_smoothingWidth :
    s.toGlobalSeedInterface.smoothingWidth = s.smoothingWidth := rfl

/-- The interface keeps the seed's angular speed. -/
@[simp] theorem toGlobalSeedInterface_angularSpeed :
    s.toGlobalSeedInterface.angularSpeed = s.angularSpeed := rfl

/-- The interface keeps the seed's axial speed. -/
@[simp] theorem toGlobalSeedInterface_axialSpeed :
    s.toGlobalSeedInterface.axialSpeed = s.axialSpeed := rfl

/-- **`L_*` is the witness support radius**, so `eq:scaled-witness-support` is a condition on
the seed's own witness. -/
@[simp] theorem toGlobalSeedInterface_witnessSupportRadius :
    s.toGlobalSeedInterface.witnessSupportRadius = s.witnessSupportRadius := rfl

/-- **`L` is the seed resolvent bound**, so `cor:scaled-local-resolvents` is applied with the
seed's own constant. -/
@[simp] theorem toGlobalSeedInterface_resolventBound :
    s.toGlobalSeedInterface.resolventBound = s.resolventBound := rfl

/-- The interface's growth floor is the seed's. -/
@[simp] theorem toGlobalSeedInterface_growthFloor :
    s.toGlobalSeedInterface.growthFloor = s.growthFloor := rfl

/-- The interface's contour is the seed's. -/
@[simp] theorem toGlobalSeedInterface_contour :
    s.toGlobalSeedInterface.contour = s.contour := rfl

/-! ## A constructor -/

/--
**Constructor for `LocalSeedC2` from the raw data.**

The hypothesis `hres` bundles clause (ii) and clause (iii) of `prop:local-seed`: for every
admissible rescaled diffusivity there is a resolvent family on `Γ` with the uniform bound `L`
*whose Riesz projection satisfies `eq:local-spectral-witness` at `f_*`*.  Bundling them is what
lets the record store one chosen resolvent per `δ` and assert the witness clause for exactly
that choice.
-/
theorem exists_localSeedC2_of_data (kStar : ℕ) (hkStar : 0 < kStar) {N : ℝ}
    (hN : 2 * Real.pi * (kStar : ℝ) = N)
    (deltaMinus deltaPlus : ℝ) (hdm : 0 < deltaMinus) (hdm1 : deltaMinus < 1)
    (hdp : 1 < deltaPlus) (Gamma : SpectralCircle) (hg : 0 < Gamma.growthFloor)
    (hw : PonomarenkoSmoothingWidth) (Omega U : ℝ) (hU : U = -Omega / N)
    (L : ℝ) (hL0 : 0 ≤ L) (Lstar : ℝ) (hLstar : 1 ≤ Lstar)
    (f : WholePlaneC2L2) (hf : ‖f‖ = 1)
    (hsupp : ∀ᵐ y ∂(volume : Measure WholePlane),
      Lstar < ‖y‖ → (f : WholePlane → C2) y = 0)
    (hres : ∀ delta ∈ Set.Icc deltaMinus deltaPlus,
      ∃ B : WholePlaneLocalResolventBound
          (wholePlaneSchwartzVelocityCoefficients
            (parameterizedSmoothedVelocity hw Omega U))
          N delta Gamma.boundary L,
        1 / 2 < (inner ℂ (B.resolvent.rieszProjection f) f).re) :
    ∃ s : LocalSeedC2,
      s.parameters.kStar = kStar ∧ s.parameters.wavenumber = N ∧
        s.parameters.deltaMinus = deltaMinus ∧ s.parameters.deltaPlus = deltaPlus ∧
        s.parameters.contour = Gamma ∧ s.smoothingWidth = hw ∧ s.angularSpeed = Omega ∧
        s.axialSpeed = U ∧ s.resolventBound = L ∧ s.witnessSupportRadius = Lstar ∧
        s.witness = f := by
  subst hN
  refine ⟨{
      parameters := ⟨kStar, hkStar, deltaMinus, deltaPlus, hdm, hdm1, hdp, Gamma, hg⟩,
      smoothingWidth := hw,
      angularSpeed := Omega,
      axialSpeed := U,
      axialSpeed_eq := hU,
      resolventBound := L,
      resolventBound_nonneg := hL0,
      resolvents := fun delta hdelta => Classical.choose (hres delta hdelta),
      witnessSupportRadius := Lstar,
      one_le_witnessSupportRadius := hLstar,
      witness := f,
      norm_witness := hf,
      witness_ae_zero := hsupp,
      re_inner_projection_witness := fun delta hdelta =>
        Classical.choose_spec (hres delta hdelta) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The selected-cell transfer -/

/-- The seed's uniform bound, restated at the axial wavenumber recorded by a selected cell's
exact-scaling parameters.  This is the hypothesis of `cor:scaled-local-resolvents`. -/
def scaledResolventBoundData (es : WholePlaneExactScalingParameters)
    (hN : es.N = s.wavenumber) (hdelta : es.delta ∈ s.interval) :
    WholePlaneLocalResolventBound s.coefficients es.N es.delta s.contour.boundary
      s.resolventBound := by
  have hb := s.resolventBoundData es.delta hdelta
  rw [← hN] at hb
  exact hb

/--
**The selected-cell transfer at the seed's parameters** (`cor:scaled-local-resolvents`).

Whenever the exact-scaling parameters of a selected cell match the seed — the same axial
wavenumber `N` and a rescaled diffusivity `δ_n ∈ I` — the conjugated local resolvent is a
resolvent of the selected whole-plane operator on the translated contour `Γ_τ`, where
`τ = es.tau`.  Calling this with `es.tau = B.tau` is what makes the torus background
resolvent and the rescaled local resolvent live on exactly the same contour.
-/
def scaledResolvent (pt : WholePlane) (es : WholePlaneExactScalingParameters)
    (hN : es.N = s.wavenumber) (hdelta : es.delta ∈ s.interval) :
    HasResolventOn (selectedScaledOperator s.coefficients pt es)
      (backgroundShiftedContour s.contour es.tau).boundary :=
  scaledLocalResolventOnShiftedContour s.coefficients pt es
    (s.scaledResolventBoundData es hN hdelta)

end LocalSeedC2

end

end FastDynamo
