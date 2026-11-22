/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativeVariation
public import LeanPool.LatticeDiracDerivation.V2.C19Fourier

/-!
# Native uniform-vacuum tangent

This module starts only from the two-field native action.  It does not use
the prepared tetrahedral rays, a spinor, or a Dirac matrix.  It identifies
the two complex transverse `Psi` channels about the native vacuum

`Psi = 0`, `chi = (0,0,r)`

and proves their exact finite-amplitude local and bond energies.  The
quadratic part is therefore two identical massive scalar C19 sectors; the
quartic remainder is retained explicitly.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type} {Edge : Type*}

open Complex
noncomputable section

/-- The action's axial vacuum representative.  Internal rotations give the
other equivalent representatives. -/
def uniformAxialVacuum (r : ℝ) : State Site where
  psi := fun _ _ => 0
  chi := fun _ component => if component = 2 then (r : ℂ) else 0

/-- The full zero-Psi vacuum manifold.  This is used to state, rather than
hide, the native orientation degeneracy of the action. -/
def zeroPsiVacuumTexture (chiField : Site → C3) : State Site where
  psi := fun _ _ => 0
  chi := chiField

theorem zero_psi_vacuum_texture_site_zero
    (r : ℝ) (chiField : Site → C3)
    (hnorm : ∀ site, density (chiField site) = r ^ 2) (site : Site) :
    sitePotential r (zeroPsiVacuumTexture chiField) site = 0 := by
  unfold sitePotential
  dsimp [zeroPsiVacuumTexture]
  rw [hnorm site]
  simp [density]

theorem zero_psi_vacuum_texture_bond_zero
    (r : ℝ) (chiField : Site → C3) (edge : Bond Site) :
    exteriorAreaBond r (zeroPsiVacuumTexture chiField) edge = 0 := by
  simp [exteriorAreaBond, zeroPsiVacuumTexture, wedge, difference, density]

/-- Any sitewise chi orientation of the correct magnitude is a zero-energy
vacuum when Psi vanishes.  Thus the free theorem below selects a uniform
vacuum sector; it does not claim the action dynamically aligns that sector. -/
theorem zero_psi_vacuum_texture_potential_zero
    [Fintype Site] [Fintype Edge]
    (r : ℝ) (chiField : Site → C3)
    (hnorm : ∀ site, density (chiField site) = r ^ 2)
    (bond : Edge → Bond Site) :
    potential r (zeroPsiVacuumTexture chiField) bond = 0 := by
  simp [potential, zero_psi_vacuum_texture_site_zero r chiField hnorm,
    zero_psi_vacuum_texture_bond_zero]

/-- Two independent complex transverse wave amplitudes, embedded into the
native three-component `Psi` field with `chi` left on its vacuum value. -/
def uniformTransverseState (r eps : ℝ) (f g : Site → ℂ) : State Site where
  psi := fun site component =>
    if component = 0 then (eps : ℂ) * f site
    else if component = 1 then (eps : ℂ) * g site
    else 0
  chi := fun _ component => if component = 2 then (r : ℂ) else 0

/-- The native velocity with only the two transverse components varying. -/
def uniformTransverseVelocity (eps : ℝ) (fDot gDot : Site → ℂ) :
    Velocity Site where
  psiDot := fun site component =>
    if component = 0 then (eps : ℂ) * fDot site
    else if component = 1 then (eps : ℂ) * gDot site
    else 0
  chiDot := fun _ _ => 0

/-- Add the native Psi component parallel to the chosen vacuum axis. -/
def uniformTransverseLongitudinalState
    (r eps eta : ℝ) (f g h : Site → ℂ) : State Site where
  psi := fun site component =>
    if component = 0 then (eps : ℂ) * f site
    else if component = 1 then (eps : ℂ) * g site
    else (eta : ℂ) * h site
  chi := fun _ component => if component = 2 then (r : ℂ) else 0

theorem uniform_transverse_longitudinal_density
    (r eps eta : ℝ) (f g h : Site → ℂ) (site : Site) :
    density ((uniformTransverseLongitudinalState r eps eta f g h).psi site) =
      eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) +
        eta ^ 2 * Complex.normSq (h site) := by
  simp [uniformTransverseLongitudinalState, density, Fin.sum_univ_succ,
    Complex.normSq_mul]
  ring_nf

theorem uniform_transverse_longitudinal_wedge
    (r eps eta : ℝ) (f g h : Site → ℂ) (site : Site) :
    wedge ((uniformTransverseLongitudinalState r eps eta f g h).chi site)
        ((uniformTransverseLongitudinalState r eps eta f g h).psi site) =
      wedge ((uniformTransverseState r eps f g).chi site)
        ((uniformTransverseState r eps f g).psi site) := by
  funext component
  fin_cases component <;>
    simp [uniformTransverseLongitudinalState, uniformTransverseState,
      wedge]

theorem uniform_transverse_longitudinal_bond_eq
    (r eps eta : ℝ) (f g h : Site → ℂ) (edge : Bond Site) :
    exteriorAreaBond r
        (uniformTransverseLongitudinalState r eps eta f g h) edge =
      exteriorAreaBond r (uniformTransverseState r eps f g) edge := by
  unfold exteriorAreaBond
  simp_rw [uniform_transverse_longitudinal_wedge]

theorem uniform_transverse_longitudinal_site_potential
    (r eps eta : ℝ) (f g h : Site → ℂ) (site : Site) :
    sitePotential r
        (uniformTransverseLongitudinalState r eps eta f g h) site =
      r ^ 2 / 2 *
          (eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) +
            eta ^ 2 * Complex.normSq (h site)) +
        (eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) +
          eta ^ 2 * Complex.normSq (h site)) ^ 2 / 4 := by
  unfold sitePotential
  rw [uniform_transverse_longitudinal_density]
  have hchi : density
      ((uniformTransverseLongitudinalState r eps eta f g h).chi site) =
        r ^ 2 := by
    simp [uniformTransverseLongitudinalState, density,
      Fin.sum_univ_succ, Complex.normSq]
    ring
  rw [hchi]
  ring

theorem uniform_axial_vacuum_site_potential_zero
    (r : ℝ) (site : Site) :
    sitePotential r (uniformAxialVacuum r) site = 0 := by
  simp [sitePotential, uniformAxialVacuum, density, Fin.sum_univ_succ,
    Complex.normSq, pow_two]

theorem uniform_axial_vacuum_bond_zero
    (r : ℝ) (edge : Bond Site) :
    exteriorAreaBond r (uniformAxialVacuum r) edge = 0 := by
  simp [exteriorAreaBond, uniformAxialVacuum, wedge, difference, density]

theorem uniform_axial_vacuum_potential_zero
    [Fintype Site] [Fintype Edge]
    (r : ℝ) (bond : Edge → Bond Site) :
    potential r (uniformAxialVacuum r) bond = 0 := by
  simp [potential, uniform_axial_vacuum_site_potential_zero,
    uniform_axial_vacuum_bond_zero]

/-- For positive vacuum scale and nonnegative bond weights, the uniform
vacuum is a global zero-energy minimum of the same native potential. -/
theorem uniform_axial_vacuum_is_global_minimum
    [Fintype Site] [Fintype Edge]
    (r : ℝ) (hr : 0 < r) (bond : Edge → Bond Site)
    (hweight : ∀ edge, 0 ≤ (bond edge).weight) (state : State Site) :
    potential r (uniformAxialVacuum r) bond ≤ potential r state bond := by
  rw [uniform_axial_vacuum_potential_zero]
  exact potential_nonnegative r state bond hr hweight

theorem uniform_transverse_psi_density
    (r eps : ℝ) (f g : Site → ℂ) (site : Site) :
    density ((uniformTransverseState r eps f g).psi site) =
      eps ^ 2 * (Complex.normSq (f site) + Complex.normSq (g site)) := by
  simp [uniformTransverseState, density, Fin.sum_univ_succ,
    Complex.normSq_mul]
  ring_nf

theorem uniform_transverse_chi_density
    (r eps : ℝ) (f g : Site → ℂ) (site : Site) :
    density ((uniformTransverseState r eps f g).chi site) = r ^ 2 := by
  simp [uniformTransverseState, density, Fin.sum_univ_succ, Complex.normSq]
  ring

theorem uniform_transverse_kinetic
    [Fintype Site] (B eps : ℝ) (fDot gDot : Site → ℂ) :
    kinetic B (uniformTransverseVelocity eps fDot gDot) =
      eps ^ 2 / 2 * ∑ site,
        (Complex.normSq (fDot site) + Complex.normSq (gDot site)) := by
  unfold kinetic uniformTransverseVelocity density
  simp only [Fin.sum_univ_succ]
  simp only [↓reduceIte, map_mul, normSq_ofReal, Fin.isValue, Fin.succ_zero_eq_one, one_ne_zero,
    Fin.succ_one_eq_two, Fin.reduceEq, map_zero, Finset.univ_eq_empty, Fin.succ_ne_zero,
    Finset.sum_empty, add_zero, Finset.sum_const_zero, mul_zero, zero_div]
  rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro site _
  ring

theorem uniform_transverse_wedge
    (r eps : ℝ) (f g : Site → ℂ) (site : Site) :
    wedge ((uniformTransverseState r eps f g).chi site)
        ((uniformTransverseState r eps f g).psi site) =
      fun component =>
        if component = 1 then -((r * eps : ℝ) : ℂ) * f site
        else if component = 2 then -((r * eps : ℝ) : ℂ) * g site
        else 0 := by
  funext component
  fin_cases component <;> simp [uniformTransverseState, wedge] <;> ring

/-- Exact onsite expansion.  Its quadratic coefficient is the native mass
`r ^ 2`; the action's quartic self-interaction is displayed, not dropped. -/
theorem uniform_transverse_site_potential
    (r eps : ℝ) (f g : Site → ℂ) (site : Site) :
    sitePotential r (uniformTransverseState r eps f g) site =
      r ^ 2 * eps ^ 2 *
          (Complex.normSq (f site) + Complex.normSq (g site)) / 2 +
        eps ^ 4 *
          (Complex.normSq (f site) + Complex.normSq (g site)) ^ 2 / 4 := by
  unfold sitePotential
  rw [uniform_transverse_psi_density, uniform_transverse_chi_density]
  ring

/-- Exact bond expansion.  The native exterior-area term becomes the sum of
the ordinary C19 bond energies of the two transverse complex channels. -/
theorem uniform_transverse_bond_energy
    (r eps : ℝ) (hr : r ≠ 0) (f g : Site → ℂ) (edge : Bond Site) :
    exteriorAreaBond r (uniformTransverseState r eps f g) edge =
      edge.weight * eps ^ 2 / 2 *
        (Complex.normSq (f edge.target - f edge.source) +
          Complex.normSq (g edge.target - g edge.source)) := by
  unfold exteriorAreaBond
  rw [uniform_transverse_wedge, uniform_transverse_wedge]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  simp [difference, density, Fin.sum_univ_succ, Complex.normSq,
    Complex.mul_re, Complex.mul_im]
  field_simp [hr2]
  ring

/-- The energy from a scalar transverse increment on a weighted bond. -/
def uniformScalarBondEnergy (weight : ℝ) (source target : ℂ) : ℝ :=
  weight / 2 * Complex.normSq (source - target)

theorem uniform_transverse_bond_is_two_scalar_bonds
    (r eps : ℝ) (hr : r ≠ 0) (f g : Site → ℂ) (edge : Bond Site) :
    exteriorAreaBond r (uniformTransverseState r eps f g) edge =
      eps ^ 2 *
        (uniformScalarBondEnergy edge.weight (f edge.source) (f edge.target) +
          uniformScalarBondEnergy edge.weight (g edge.source) (g edge.target)) := by
  rw [uniform_transverse_bond_energy r eps hr]
  unfold uniformScalarBondEnergy
  rw [show Complex.normSq (f edge.target - f edge.source) =
      Complex.normSq (f edge.source - f edge.target) by
        rw [show f edge.target - f edge.source =
          -(f edge.source - f edge.target) by ring, Complex.normSq_neg],
    show Complex.normSq (g edge.target - g edge.source) =
      Complex.normSq (g edge.source - g edge.target) by
        rw [show g edge.target - g edge.source =
          -(g edge.source - g edge.target) by ring, Complex.normSq_neg]]
  ring

/-- The exact quadratic form seen by the two transverse channels. -/
def uniformTransverseQuadratic [Fintype Site] [Fintype Edge]
    (r : ℝ) (f g : Site → ℂ) (bond : Edge → Bond Site) : ℝ :=
  r ^ 2 * ∑ site,
      (Complex.normSq (f site) + Complex.normSq (g site)) / 2 +
    ∑ edge, (bond edge).weight / 2 *
      (Complex.normSq (f (bond edge).target - f (bond edge).source) +
        Complex.normSq (g (bond edge).target - g (bond edge).source))

/-- Exact full-potential expansion about the native vacuum.  This is the
action-level statement that the Hessian consists of two identical massive
C19 scalar sectors. -/
theorem uniform_transverse_potential_expansion
    [Fintype Site] [Fintype Edge]
    (r eps : ℝ) (hr : r ≠ 0) (f g : Site → ℂ)
    (bond : Edge → Bond Site) :
    potential r (uniformTransverseState r eps f g) bond =
      eps ^ 2 * uniformTransverseQuadratic r f g bond +
        eps ^ 4 / 4 * ∑ site,
          (Complex.normSq (f site) + Complex.normSq (g site)) ^ 2 := by
  unfold potential uniformTransverseQuadratic
  simp_rw [uniform_transverse_site_potential,
    uniform_transverse_bond_energy r eps hr f g]
  rw [mul_add]
  repeat rw [Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]
  ring_nf

/-- The transport part of the transverse energy for a character mode. -/
def uniformTransverseCharacterTransportEnergy
    (r eps : ℝ) (first second : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℝ :=
  ∑ direction,
    exteriorAreaBond r
      (uniformTransverseState r eps
        (fun x => cubicLatticeCharacter momentum x * first)
        (fun x => cubicLatticeCharacter momentum x * second))
      (infiniteC19Bond site direction)

/-- The two native transverse channels have the exact same C19 momentum
symbol, with no prepared corner rays used in the calculation. -/
theorem uniform_transverse_character_has_c19_symbol
    (r eps : ℝ) (hr : r ≠ 0) (first second : ℂ)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    uniformTransverseCharacterTransportEnergy r eps first second momentum site =
      eps ^ 2 / 2 *
        (Complex.normSq first + Complex.normSq second) *
          c19TransportSymbol momentum := by
  unfold uniformTransverseCharacterTransportEnergy c19TransportSymbol
  simp_rw [uniform_transverse_bond_energy r eps hr]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  simp only [infiniteC19Bond]
  rw [cubic_character_neighbor]
  rw [show
      cubicLatticeCharacter momentum site *
          c19Character momentum direction * first -
          cubicLatticeCharacter momentum site * first =
        cubicLatticeCharacter momentum site *
          ((c19Character momentum direction - 1) * first) by ring,
    show
      cubicLatticeCharacter momentum site *
          c19Character momentum direction * second -
          cubicLatticeCharacter momentum site * second =
        cubicLatticeCharacter momentum site *
          ((c19Character momentum direction - 1) * second) by ring]
  simp only [Complex.normSq_mul, cubic_character_normSq_one, one_mul]
  rw [show Complex.normSq (c19Character momentum direction - 1) =
      Complex.normSq (1 - c19Character momentum direction) by
        rw [show c19Character momentum direction - 1 =
          -(1 - c19Character momentum direction) by ring,
          Complex.normSq_neg]]
  ring

/-- The native vacuum is an exact critical point of the full two-field
potential.  No prepared period-two background is assumed. -/
theorem uniform_axial_vacuum_first_variation_zero
    [Fintype Site] [Fintype Edge]
    (r : ℝ) (direction : State Site) (bond : Edge → Bond Site) :
    potentialFirstVariation r (uniformAxialVacuum r) direction bond = 0 := by
  unfold potentialFirstVariation
  have hsite : ∀ site,
      sitePotentialFirstVariation r (uniformAxialVacuum r) direction site = 0 := by
    intro site
    simp [sitePotentialFirstVariation, uniformAxialVacuum, density,
      Fin.sum_univ_succ, c3RealPair, Complex.normSq, pow_two]
  have hbond : ∀ edge,
      exteriorAreaBondFirstVariation r (uniformAxialVacuum r) direction
        (bond edge) = 0 := by
    intro edge
    simp [exteriorAreaBondFirstVariation, bondAreaDifference,
      uniformAxialVacuum, wedge, difference, c3RealPair]
  simp [hsite, hbond]

end
end LeanDirac.V2
