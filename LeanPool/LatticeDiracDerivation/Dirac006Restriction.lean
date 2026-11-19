/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac006Restriction.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac006

/-!
# DIRAC-006 action-restriction bridge

This supporting module closes the first gap identified by independent review.
The aligned eight-site fields are not treated as an unrelated scalar model.
Instead, the native two-field Lagrangian is pulled back through the explicit
`alignedEightSiteState` embedding.  The theorem below proves both the exact
equality of the full and restricted actions and the commutation of restriction
with arbitrary real directional variation of all retained amplitudes and
velocities.

Nothing here changes the native action, adds a projector to the evolution, or
assumes a Dirac equation.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

/-- The velocity on the cube corners whose `psi` part at `corner` is `tetraCorner corner` scaled by
`psiVelocity corner` and whose `chi` part is `companion corner` scaled by `chiVelocity corner`. -/
def restrictedAlignedEightSiteVelocity
    (psiVelocity chiVelocity : Cell8) : Velocity CubeCorner where
  psiDot corner := c3ScaleComplex (psiVelocity corner) (tetraCorner corner)
  chiDot corner := c3ScaleComplex (chiVelocity corner) (companion corner)

/-- The site potential `(ρχ - chi0 ^ 2) ^ 2 / 4 + ρχ * ρψ / 2 + ρψ ^ 2 / 4`, where `ρψ` and `ρχ` are
the squared norms of `psiAmplitude` and `chiAmplitude`. -/
def restrictedSitePotential
    (chi0 : ℝ) (psiAmplitude chiAmplitude : ℂ) : ℝ :=
  let rhoPsi := Complex.normSq psiAmplitude
  let rhoChi := Complex.normSq chiAmplitude
  (rhoChi - chi0 ^ 2) ^ 2 / 4 + rhoChi * rhoPsi / 2 + rhoPsi ^ 2 / 4

/-- The kinetic energy `∑ |psiVelocity corner|² / 2 + B * ∑ |chiVelocity corner|² / 2` of two
eight-corner velocity amplitudes. -/
def restrictedEightSiteKinetic
    (B : ℝ) (psiVelocity chiVelocity : Cell8) : ℝ :=
  (∑ corner, Complex.normSq (psiVelocity corner)) / 2 +
    B * (∑ corner, Complex.normSq (chiVelocity corner)) / 2

/-- The sum over the cube corners of `restrictedSitePotential` plus the sum over the edges of the
`restrictedBondEnergy` of the product amplitudes at the ends of each bond. -/
def restrictedEightSitePotential [Fintype Edge]
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) : ℝ :=
  (∑ corner, restrictedSitePotential chi0
      (psiAmplitude corner) (chiAmplitude corner)) +
    ∑ edge, restrictedBondEnergy chi0 (bond edge).weight
      (productAmplitude psiAmplitude chiAmplitude (bond edge).source)
      (productAmplitude psiAmplitude chiAmplitude (bond edge).target)

/-- The Lagrangian `restrictedEightSiteKinetic - restrictedEightSitePotential` of the eight-corner
amplitudes and velocities. -/
def restrictedEightSiteLagrangian [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (psiVelocity chiVelocity : Cell8)
    (bond : Edge → Bond CubeCorner) : ℝ :=
  restrictedEightSiteKinetic B psiVelocity chiVelocity -
    restrictedEightSitePotential chi0 psiAmplitude chiAmplitude bond

theorem density_aligned_complex_scale (z : ℂ) (u : C3)
    (hu : density u = 1) :
    density (c3ScaleComplex z u) = Complex.normSq z := by
  unfold density c3ScaleComplex
  simp_rw [Complex.normSq_mul]
  change (∑ i, Complex.normSq (u i)) = 1 at hu
  rw [← Finset.mul_sum, hu, mul_one]

theorem aligned_site_potential_is_restricted
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (corner : CubeCorner) :
    sitePotential chi0 (alignedEightSiteState psiAmplitude chiAmplitude) corner =
      restrictedSitePotential chi0
        (psiAmplitude corner) (chiAmplitude corner) := by
  unfold sitePotential restrictedSitePotential alignedEightSiteState
  dsimp
  rw [density_aligned_complex_scale _ _ (tetra_corner_density_one corner),
    density_aligned_complex_scale _ _ (companion_density_one corner)]

theorem aligned_kinetic_is_restricted
    (B : ℝ) (psiVelocity chiVelocity : Cell8) :
    kinetic B (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) =
      restrictedEightSiteKinetic B psiVelocity chiVelocity := by
  unfold kinetic restrictedEightSiteKinetic restrictedAlignedEightSiteVelocity
  have hpsi : (∑ corner, density
      (c3ScaleComplex (psiVelocity corner) (tetraCorner corner))) =
      ∑ corner, Complex.normSq (psiVelocity corner) := by
    apply Finset.sum_congr rfl
    intro corner _
    exact density_aligned_complex_scale _ _
      (tetra_corner_density_one corner)
  have hchi : (∑ corner, density
      (c3ScaleComplex (chiVelocity corner) (companion corner))) =
      ∑ corner, Complex.normSq (chiVelocity corner) := by
    apply Finset.sum_congr rfl
    intro corner _
    exact density_aligned_complex_scale _ _
      (companion_density_one corner)
  rw [hpsi, hchi]

theorem aligned_potential_is_restricted [Fintype Edge]
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (bond : Edge → Bond CubeCorner) :
    potential chi0 (alignedEightSiteState psiAmplitude chiAmplitude) bond =
      restrictedEightSitePotential chi0 psiAmplitude chiAmplitude bond := by
  unfold potential restrictedEightSitePotential
  congr 1
  · apply Finset.sum_congr rfl
    intro corner _
    exact aligned_site_potential_is_restricted
      chi0 psiAmplitude chiAmplitude corner
  · apply Finset.sum_congr rfl
    intro edge _
    exact aligned_exterior_area_is_restricted_bond
      chi0 psiAmplitude chiAmplitude (bond edge)

theorem aligned_lagrangian_is_restricted [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (psiVelocity chiVelocity : Cell8)
    (bond : Edge → Bond CubeCorner) :
    lagrangian chi0 B
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) bond =
      restrictedEightSiteLagrangian chi0 B psiAmplitude chiAmplitude
        psiVelocity chiVelocity bond := by
  unfold lagrangian restrictedEightSiteLagrangian
  rw [aligned_kinetic_is_restricted, aligned_potential_is_restricted]

theorem aligned_psi_normal_momentum_zero
    (psiVelocity chiVelocity : Cell8) (eta : CubeCorner → C3)
    (hnormal : PsiNormalDirection eta) :
    psiMomentumPair
      (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) eta = 0 := by
  unfold psiMomentumPair restrictedAlignedEightSiteVelocity
  apply Finset.sum_eq_zero
  intro corner _
  rw [c3_real_pair_eq_inner_re]
  change (c3Inner
    (c3ScaleComplex (psiVelocity corner) (tetraCorner corner))
    (eta corner)).re = 0
  rw [c3_inner_scale_left, hnormal corner]
  simp

theorem aligned_chi_normal_momentum_zero
    (B : ℝ) (psiVelocity chiVelocity : Cell8) (eta : CubeCorner → C3)
    (hnormal : ChiNormalDirection eta) :
    chiMomentumPair B
      (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) eta = 0 := by
  unfold chiMomentumPair restrictedAlignedEightSiteVelocity
  rw [show (∑ corner : CubeCorner,
      c3RealPair (c3ScaleComplex (chiVelocity corner) (companion corner))
        (eta corner)) = 0 by
    apply Finset.sum_eq_zero
    intro corner _
    rw [c3_real_pair_eq_inner_re]
    change (c3Inner
      (c3ScaleComplex (chiVelocity corner) (companion corner))
      (eta corner)).re = 0
    rw [c3_inner_scale_left, hnormal corner]
    simp]
  ring

/-- The real line `base + eps * direction` through `base` in the direction `direction` in the space
of eight-corner amplitudes. -/
def cell8RealLine (base direction : Cell8) (eps : ℝ) : Cell8 :=
  fun corner => base corner + (eps : ℂ) * direction corner

theorem aligned_state_line_is_amplitude_line
    (psiAmplitude chiAmplitude psiDirection chiDirection : Cell8)
    (eps : ℝ) :
    stateLine
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (alignedEightSiteState psiDirection chiDirection) eps =
      alignedEightSiteState
        (cell8RealLine psiAmplitude psiDirection eps)
        (cell8RealLine chiAmplitude chiDirection eps) := by
  apply congrArg₂ State.mk <;> funext corner component <;>
    simp [c3Line, c3Add, c3ScaleReal,
      alignedEightSiteState, c3ScaleComplex, cell8RealLine] <;> ring

theorem aligned_velocity_line_is_amplitude_line
    (psiVelocity chiVelocity psiDirection chiDirection : Cell8)
    (eps : ℝ) :
    velocityLine
        (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity)
        (restrictedAlignedEightSiteVelocity psiDirection chiDirection) eps =
      restrictedAlignedEightSiteVelocity
        (cell8RealLine psiVelocity psiDirection eps)
        (cell8RealLine chiVelocity chiDirection eps) := by
  apply congrArg₂ Velocity.mk <;> funext corner component <;>
    simp [c3Line, c3Add, c3ScaleReal,
      restrictedAlignedEightSiteVelocity, c3ScaleComplex, cell8RealLine] <;> ring

/-!
The decisive pullback identity: differentiating the explicit restricted
action is exactly differentiating the advertised native action along the
embedded sector.  The derivative on the right was derived from the full
two-field action in DIRAC-003; it is not postulated in this module.
-/
theorem restricted_action_variation_is_native_variation [Fintype Edge]
    (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (psiVelocity chiVelocity : Cell8)
    (psiDirection chiDirection : Cell8)
    (psiVelocityDirection chiVelocityDirection : Cell8)
    (bond : Edge → Bond CubeCorner) :
    HasDerivAt
      (fun eps : ℝ =>
        restrictedEightSiteLagrangian chi0 B
          (cell8RealLine psiAmplitude psiDirection eps)
          (cell8RealLine chiAmplitude chiDirection eps)
          (cell8RealLine psiVelocity psiVelocityDirection eps)
          (cell8RealLine chiVelocity chiVelocityDirection eps) bond)
      (lagrangianStateFirstVariation chi0
          (alignedEightSiteState psiAmplitude chiAmplitude)
          (alignedEightSiteState psiDirection chiDirection) bond +
        kineticVelocityFirstVariation B
          (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity)
          (restrictedAlignedEightSiteVelocity
            psiVelocityDirection chiVelocityDirection)) 0 := by
  have h := lagrangian_state_velocity_hasDerivAt chi0 B
    (alignedEightSiteState psiAmplitude chiAmplitude)
    (alignedEightSiteState psiDirection chiDirection)
    (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity)
    (restrictedAlignedEightSiteVelocity psiVelocityDirection chiVelocityDirection)
    bond
  convert h using 1
  funext eps
  rw [aligned_state_line_is_amplitude_line,
    aligned_velocity_line_is_amplitude_line,
    aligned_lagrangian_is_restricted]

/-- The results of this file collected in one proposition, for the C19 bonds of the cube: the
Lagrangian of `alignedEightSiteState` equals `restrictedEightSiteLagrangian`, its derivative along
`cell8RealLine` is the first variation of the full Lagrangian, and the forces and momentum pairings
vanish on normal directions. -/
structure Dirac006ActionRestrictionCertificate : Prop where
  exactActionRestriction : ∀
      (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
      (psiVelocity chiVelocity : Cell8)
      ,
    lagrangian chi0 B
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity)
        (c19Bond cubeC19Geometry) =
      restrictedEightSiteLagrangian chi0 B psiAmplitude chiAmplitude
        psiVelocity chiVelocity (c19Bond cubeC19Geometry)
  restrictionCommutesWithVariation : ∀
      (chi0 B : ℝ) (psiAmplitude chiAmplitude : Cell8)
      (psiVelocity chiVelocity : Cell8)
      (psiDirection chiDirection : Cell8)
      (psiVelocityDirection chiVelocityDirection : Cell8)
      ,
    HasDerivAt
      (fun eps : ℝ =>
        restrictedEightSiteLagrangian chi0 B
          (cell8RealLine psiAmplitude psiDirection eps)
          (cell8RealLine chiAmplitude chiDirection eps)
          (cell8RealLine psiVelocity psiVelocityDirection eps)
          (cell8RealLine chiVelocity chiVelocityDirection eps)
          (c19Bond cubeC19Geometry))
      (lagrangianStateFirstVariation chi0
          (alignedEightSiteState psiAmplitude chiAmplitude)
          (alignedEightSiteState psiDirection chiDirection)
          (c19Bond cubeC19Geometry) +
        kineticVelocityFirstVariation B
          (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity)
          (restrictedAlignedEightSiteVelocity
            psiVelocityDirection chiVelocityDirection)) 0
  psiNormalVariationVanishes : ∀
      (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8) eta,
    PsiNormalDirection eta →
      psiEulerLagrangeForce chi0
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (c19Bond cubeC19Geometry) eta = 0
  chiNormalVariationVanishes : ∀
      (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8) eta,
    ChiNormalDirection eta →
      chiEulerLagrangeForce chi0
        (alignedEightSiteState psiAmplitude chiAmplitude)
        (c19Bond cubeC19Geometry) eta = 0
  psiNormalMomentumVanishes : ∀
      (psiVelocity chiVelocity : Cell8) eta,
    PsiNormalDirection eta →
      psiMomentumPair
        (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) eta = 0
  chiNormalMomentumVanishes : ∀
      (B : ℝ) (psiVelocity chiVelocity : Cell8) eta,
    ChiNormalDirection eta →
      chiMomentumPair B
        (restrictedAlignedEightSiteVelocity psiVelocity chiVelocity) eta = 0

theorem dirac006_action_restriction_bridge :
    Dirac006ActionRestrictionCertificate where
  exactActionRestriction := fun chi0 B psiAmplitude chiAmplitude
      psiVelocity chiVelocity =>
    aligned_lagrangian_is_restricted chi0 B psiAmplitude chiAmplitude
      psiVelocity chiVelocity (c19Bond cubeC19Geometry)
  restrictionCommutesWithVariation := fun chi0 B psiAmplitude chiAmplitude
      psiVelocity chiVelocity psiDirection chiDirection
      psiVelocityDirection chiVelocityDirection =>
    restricted_action_variation_is_native_variation chi0 B
      psiAmplitude chiAmplitude psiVelocity chiVelocity
      psiDirection chiDirection psiVelocityDirection chiVelocityDirection
      (c19Bond cubeC19Geometry)
  psiNormalVariationVanishes := fun chi0 psiAmplitude chiAmplitude eta h =>
    aligned_psi_cross_block_zero chi0 psiAmplitude chiAmplitude
      (c19Bond cubeC19Geometry) eta h
  chiNormalVariationVanishes := fun chi0 psiAmplitude chiAmplitude eta h =>
    aligned_chi_cross_block_zero chi0 psiAmplitude chiAmplitude
      (c19Bond cubeC19Geometry) eta h
  psiNormalMomentumVanishes := fun psiVelocity chiVelocity eta h =>
    aligned_psi_normal_momentum_zero psiVelocity chiVelocity eta h
  chiNormalMomentumVanishes := fun B psiVelocity chiVelocity eta h =>
    aligned_chi_normal_momentum_zero B psiVelocity chiVelocity eta h

end
end LeanDirac
