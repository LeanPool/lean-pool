/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac006.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac005

/-!
DIRAC-006: native repeated-lattice local transport symbol.

This gate does not choose four components.  It first restricts the admitted
two-field bond energy to the invariant unit-cell sector from DIRAC-005.  The
result is an exact scalar bond energy for the native product amplitude
`chiAmplitude * psiAmplitude`.  The C19 lattice character then gives the
finite-momentum coefficient of that transport directly from the eighteen
declared neighbor directions and their weights.  The repeated-lattice result
below is proved on an actual native `State`: each site carries the admitted
Psi ray and companion chi ray, while the product amplitude carries the lattice
character.  The scalar restricted-bond calculation is therefore a lemma in
the native proof, not a replacement model.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open BigOperators Complex

def productAmplitude (psiAmplitude chiAmplitude : Cell8)
    (corner : CubeCorner) : ℂ :=
  chiAmplitude corner * psiAmplitude corner

theorem aligned_area_is_product_amplitude
    (psiAmplitude chiAmplitude : Cell8) (corner : CubeCorner) :
    wedge ((alignedEightSiteState psiAmplitude chiAmplitude).chi corner)
      ((alignedEightSiteState psiAmplitude chiAmplitude).psi corner) =
      c3ScaleComplex (-(productAmplitude psiAmplitude chiAmplitude corner))
        unitArea := by
  rw [show (alignedEightSiteState psiAmplitude chiAmplitude).chi corner =
      c3ScaleComplex (chiAmplitude corner) (companion corner) by rfl,
    show (alignedEightSiteState psiAmplitude chiAmplitude).psi corner =
      c3ScaleComplex (psiAmplitude corner) (tetraCorner corner) by rfl,
    wedge_scale_left, wedge_scale_right, wedge_companion_tetra]
  funext component
  simp [c3ScaleComplex, c3Neg, productAmplitude]
  ring

theorem density_scaled_unit_area (z : ℂ) :
    density (c3ScaleComplex z unitArea) = Complex.normSq z := by
  simp [density, c3ScaleComplex, unitArea, Fin.sum_univ_succ,
    Complex.normSq]

def restrictedBondEnergy (chi0 weight : ℝ)
    (sourceProduct targetProduct : ℂ) : ℝ :=
  weight / (2 * chi0 ^ 2) * Complex.normSq (sourceProduct - targetProduct)

theorem aligned_exterior_area_is_restricted_bond
    (chi0 : ℝ) (psiAmplitude chiAmplitude : Cell8)
    (edge : Bond CubeCorner) :
    exteriorAreaBond chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) edge =
      restrictedBondEnergy chi0 edge.weight
        (productAmplitude psiAmplitude chiAmplitude edge.source)
        (productAmplitude psiAmplitude chiAmplitude edge.target) := by
  unfold exteriorAreaBond restrictedBondEnergy
  rw [aligned_area_is_product_amplitude,
    aligned_area_is_product_amplitude]
  congr 1
  rw [show difference
      (c3ScaleComplex
        (-(productAmplitude psiAmplitude chiAmplitude edge.source)) unitArea)
      (c3ScaleComplex
        (-(productAmplitude psiAmplitude chiAmplitude edge.target)) unitArea) =
      c3ScaleComplex
        (productAmplitude psiAmplitude chiAmplitude edge.source -
          productAmplitude psiAmplitude chiAmplitude edge.target) unitArea by
      funext component
      simp [difference, c3ScaleComplex]
      ring]
  exact density_scaled_unit_area _

abbrev LatticeMomentum := Fin 3 → ℝ
abbrev InfiniteCubicSite := Fin 3 → ℤ

def infiniteC19Neighbor (site : InfiniteCubicSite)
    (direction : C19Neighbor) : InfiniteCubicSite :=
  fun axis => site axis + c19Coord axis direction

def latticePhase (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℝ :=
  ∑ axis, momentum axis * (site axis : ℝ)

def c19PhaseAngle (momentum : LatticeMomentum)
    (direction : C19Neighbor) : ℝ :=
  ∑ axis, momentum axis * (c19Coord axis direction : ℝ)

def c19Character (momentum : LatticeMomentum)
    (direction : C19Neighbor) : ℂ :=
  Complex.exp (I * (c19PhaseAngle momentum direction : ℂ))

def cubicLatticeCharacter (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℂ :=
  Complex.exp (I * (latticePhase momentum site : ℂ))

theorem lattice_phase_neighbor (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    latticePhase momentum (infiniteC19Neighbor site direction) =
      latticePhase momentum site + c19PhaseAngle momentum direction := by
  unfold latticePhase infiniteC19Neighbor c19PhaseAngle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro axis _
  push_cast
  ring

theorem cubic_character_neighbor (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    cubicLatticeCharacter momentum (infiniteC19Neighbor site direction) =
      cubicLatticeCharacter momentum site * c19Character momentum direction := by
  unfold cubicLatticeCharacter c19Character
  rw [lattice_phase_neighbor]
  push_cast
  rw [mul_add, Complex.exp_add]

theorem cubic_character_normSq_one (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    Complex.normSq (cubicLatticeCharacter momentum site) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [cubicLatticeCharacter, Complex.norm_exp_I_mul_ofReal]

def c19IntegerWeight (direction : C19Neighbor) : ℤ :=
  if direction.val < 6 then 2 else 1

theorem c19_weight_is_integer_weight (direction : C19Neighbor) :
    c19Weight direction = (c19IntegerWeight direction : ℝ) := by
  unfold c19Weight c19IntegerWeight
  split <;> norm_num

def c19FirstMoment (axis : Fin 3) : ℤ :=
  ∑ direction, c19IntegerWeight direction * c19Coord axis direction

def c19SecondMoment (axis other : Fin 3) : ℤ :=
  ∑ direction, c19IntegerWeight direction *
    c19Coord axis direction * c19Coord other direction

theorem c19_first_moment_zero (axis : Fin 3) :
    c19FirstMoment axis = 0 := by
  fin_cases axis <;> decide

theorem c19_second_moment_isotropic (axis other : Fin 3) :
    c19SecondMoment axis other = if axis = other then 12 else 0 := by
  fin_cases axis <;> fin_cases other <;> decide

def c19TransportSymbol (momentum : LatticeMomentum) : ℝ :=
  ∑ direction,
    c19Weight direction *
      Complex.normSq (1 - c19Character momentum direction)

theorem c19_transport_symbol_nonnegative (momentum : LatticeMomentum) :
    0 ≤ c19TransportSymbol momentum := by
  unfold c19TransportSymbol
  exact Finset.sum_nonneg (fun direction _ =>
    mul_nonneg (le_of_lt (c19_weight_positive direction))
      (Complex.normSq_nonneg _))

theorem c19_character_zero (direction : C19Neighbor) :
    c19Character (fun _ => 0) direction = 1 := by
  simp [c19Character, c19PhaseAngle]

theorem c19_transport_symbol_zero :
    c19TransportSymbol (fun _ => 0) = 0 := by
  simp [c19TransportSymbol, c19_character_zero]

theorem restricted_bond_character_factorization
    (chi0 weight : ℝ) (q phase : ℂ) :
    restrictedBondEnergy chi0 weight q (phase * q) =
      weight / (2 * chi0 ^ 2) *
        (Complex.normSq q * Complex.normSq (1 - phase)) := by
  unfold restrictedBondEnergy
  rw [show q - phase * q = (1 - phase) * q by ring,
    Complex.normSq_mul]
  ring

def restrictedCharacterTransportEnergy (chi0 : ℝ) (q : ℂ)
    (momentum : LatticeMomentum) : ℝ :=
  ∑ direction,
    restrictedBondEnergy chi0 (c19Weight direction) q
      (c19Character momentum direction * q)

theorem restricted_character_energy_has_c19_symbol
    (chi0 : ℝ) (q : ℂ) (momentum : LatticeMomentum) :
    restrictedCharacterTransportEnergy chi0 q momentum =
      Complex.normSq q / (2 * chi0 ^ 2) * c19TransportSymbol momentum := by
  unfold restrictedCharacterTransportEnergy c19TransportSymbol
  simp_rw [restricted_bond_character_factorization]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  ring

theorem repeated_character_bond_factorization
    (chi0 weight : ℝ) (q : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    restrictedBondEnergy chi0 weight
      (cubicLatticeCharacter momentum site * q)
      (cubicLatticeCharacter momentum
        (infiniteC19Neighbor site direction) * q) =
      weight / (2 * chi0 ^ 2) *
        (Complex.normSq q *
          Complex.normSq (1 - c19Character momentum direction)) := by
  rw [cubic_character_neighbor]
  rw [show
      (cubicLatticeCharacter momentum site *
        c19Character momentum direction) * q =
      c19Character momentum direction *
        (cubicLatticeCharacter momentum site * q) by ring]
  rw [restricted_bond_character_factorization, Complex.normSq_mul,
    cubic_character_normSq_one]
  ring

def repeatedCharacterTransportEnergy (chi0 : ℝ) (q : ℂ)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) : ℝ :=
  ∑ direction,
    restrictedBondEnergy chi0 (c19Weight direction)
      (cubicLatticeCharacter momentum site * q)
      (cubicLatticeCharacter momentum
        (infiniteC19Neighbor site direction) * q)

theorem repeated_character_energy_has_c19_symbol
    (chi0 : ℝ) (q : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    repeatedCharacterTransportEnergy chi0 q momentum site =
      Complex.normSq q / (2 * chi0 ^ 2) * c19TransportSymbol momentum := by
  unfold repeatedCharacterTransportEnergy c19TransportSymbol
  simp_rw [repeated_character_bond_factorization]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  ring

/-!
Native repeated-state bridge.  `cornerAt` may be any labeling by the eight
admitted rays; in particular it may be the period-two corner labeling used by
DIRAC-005.  No ray label evolves independently: it only specifies the prepared
native Psi/chi state whose bond energy is evaluated below.
-/

def integerParityBit (coordinate : ℤ) : Bool :=
  decide (coordinate % 2 = 1)

theorem integer_parity_bit_add_one (coordinate : ℤ) :
    integerParityBit (coordinate + 1) = !integerParityBit coordinate := by
  by_cases h : coordinate % 2 = 1
  · have hnext : (coordinate + 1) % 2 ≠ 1 := by omega
    simp [integerParityBit, h, hnext]
  · have hzero : coordinate % 2 = 0 := by omega
    have hnext : (coordinate + 1) % 2 = 1 := by omega
    simp [integerParityBit, hzero, hnext]

theorem integer_parity_bit_add_neg_one (coordinate : ℤ) :
    integerParityBit (coordinate + -1) = !integerParityBit coordinate := by
  by_cases h : coordinate % 2 = 1
  · have hnext : (coordinate + -1) % 2 ≠ 1 := by omega
    simp [integerParityBit, h, hnext]
  · have hzero : coordinate % 2 = 0 := by omega
    have hnext : (coordinate + -1) % 2 = 1 := by omega
    simp [integerParityBit, hzero, hnext]

def cornerFromParity : Bool → Bool → Bool → CubeCorner
  | false, false, false => 0
  | false, false, true => 1
  | false, true, false => 2
  | false, true, true => 3
  | true, false, false => 4
  | true, false, true => 5
  | true, true, false => 6
  | true, true, true => 7

def periodTwoCornerAt (site : InfiniteCubicSite) : CubeCorner :=
  cornerFromParity (integerParityBit (site 0))
    (integerParityBit (site 1)) (integerParityBit (site 2))

theorem period_two_corner_neighbor (site : InfiniteCubicSite)
    (direction : C19Neighbor) :
    periodTwoCornerAt (infiniteC19Neighbor site direction) =
      cubeC19Neighbor (periodTwoCornerAt site) direction := by
  fin_cases direction <;>
    simp [periodTwoCornerAt, infiniteC19Neighbor, c19Coord,
      cubeC19Neighbor, integer_parity_bit_add_one,
      integer_parity_bit_add_neg_one, cornerFromParity] <;>
    cases h0 : integerParityBit (site 0) <;>
    cases h1 : integerParityBit (site 1) <;>
    cases h2 : integerParityBit (site 2) <;>
    rfl

def repeatedAlignedCharacterState
    (cornerAt : InfiniteCubicSite → CubeCorner)
    (psiAmplitude chiAmplitude : ℂ) (momentum : LatticeMomentum) :
    State InfiniteCubicSite where
  psi site := c3ScaleComplex
    (cubicLatticeCharacter momentum site * psiAmplitude)
    (tetraCorner (cornerAt site))
  chi site := c3ScaleComplex chiAmplitude (companion (cornerAt site))

def infiniteC19Bond (site : InfiniteCubicSite)
    (direction : C19Neighbor) : Bond InfiniteCubicSite where
  source := site
  target := infiniteC19Neighbor site direction
  weight := c19Weight direction

theorem repeated_aligned_character_area
    (cornerAt : InfiniteCubicSite → CubeCorner)
    (psiAmplitude chiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    wedge
      ((repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum).chi site)
      ((repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum).psi site) =
      c3ScaleComplex
        (-(cubicLatticeCharacter momentum site *
          (chiAmplitude * psiAmplitude))) unitArea := by
  rw [show
      (repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum).chi site =
          c3ScaleComplex chiAmplitude (companion (cornerAt site)) by rfl,
    show
      (repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum).psi site =
          c3ScaleComplex
            (cubicLatticeCharacter momentum site * psiAmplitude)
            (tetraCorner (cornerAt site)) by rfl,
    wedge_scale_left, wedge_scale_right, wedge_companion_tetra]
  funext component
  simp [c3ScaleComplex, c3Neg]
  ring

theorem repeated_aligned_native_bond_is_restricted
    (chi0 : ℝ) (cornerAt : InfiniteCubicSite → CubeCorner)
    (psiAmplitude chiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) (direction : C19Neighbor) :
    exteriorAreaBond chi0
      (repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum)
      (infiniteC19Bond site direction) =
      restrictedBondEnergy chi0 (c19Weight direction)
        (cubicLatticeCharacter momentum site *
          (chiAmplitude * psiAmplitude))
        (cubicLatticeCharacter momentum
          (infiniteC19Neighbor site direction) *
            (chiAmplitude * psiAmplitude)) := by
  unfold exteriorAreaBond restrictedBondEnergy infiniteC19Bond
  rw [repeated_aligned_character_area, repeated_aligned_character_area]
  congr 1
  rw [show difference
      (c3ScaleComplex
        (-(cubicLatticeCharacter momentum site *
          (chiAmplitude * psiAmplitude))) unitArea)
      (c3ScaleComplex
        (-(cubicLatticeCharacter momentum
          (infiniteC19Neighbor site direction) *
            (chiAmplitude * psiAmplitude))) unitArea) =
      c3ScaleComplex
        (cubicLatticeCharacter momentum site *
            (chiAmplitude * psiAmplitude) -
          cubicLatticeCharacter momentum
            (infiniteC19Neighbor site direction) *
              (chiAmplitude * psiAmplitude)) unitArea by
        funext component
        simp [difference, c3ScaleComplex]
        ring]
  exact density_scaled_unit_area _

def nativeRepeatedCharacterTransportEnergy
    (chi0 : ℝ) (cornerAt : InfiniteCubicSite → CubeCorner)
    (psiAmplitude chiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) : ℝ :=
  ∑ direction,
    exteriorAreaBond chi0
      (repeatedAlignedCharacterState cornerAt psiAmplitude chiAmplitude
        momentum)
      (infiniteC19Bond site direction)

theorem native_repeated_state_energy_has_c19_symbol
    (chi0 : ℝ) (cornerAt : InfiniteCubicSite → CubeCorner)
    (psiAmplitude chiAmplitude : ℂ) (momentum : LatticeMomentum)
    (site : InfiniteCubicSite) :
    nativeRepeatedCharacterTransportEnergy chi0 cornerAt
        psiAmplitude chiAmplitude momentum site =
      Complex.normSq (chiAmplitude * psiAmplitude) /
          (2 * chi0 ^ 2) * c19TransportSymbol momentum := by
  unfold nativeRepeatedCharacterTransportEnergy c19TransportSymbol
  simp_rw [repeated_aligned_native_bond_is_restricted]
  simp_rw [repeated_character_bond_factorization]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  ring

theorem native_period_two_state_energy_has_c19_symbol
    (chi0 : ℝ) (psiAmplitude chiAmplitude : ℂ)
    (momentum : LatticeMomentum) (site : InfiniteCubicSite) :
    nativeRepeatedCharacterTransportEnergy chi0 periodTwoCornerAt
        psiAmplitude chiAmplitude momentum site =
      Complex.normSq (chiAmplitude * psiAmplitude) /
          (2 * chi0 ^ 2) * c19TransportSymbol momentum :=
  native_repeated_state_energy_has_c19_symbol chi0 periodTwoCornerAt
    psiAmplitude chiAmplitude momentum site

def productTangent (psi0 chi0 dPsi dChi : ℂ) : ℂ :=
  chi0 * dPsi + psi0 * dChi

theorem product_amplitude_first_order_expansion
    (psi0 chi0 dPsi dChi eps : ℂ) :
    (chi0 + eps * dChi) * (psi0 + eps * dPsi) - chi0 * psi0 =
      eps * productTangent psi0 chi0 dPsi dChi +
        eps ^ 2 * (dChi * dPsi) := by
  unfold productTangent
  ring

structure Dirac006Certificate : Prop where
  exactSectorBond : ∀ chi0 psiAmplitude chiAmplitude edge,
    exteriorAreaBond chi0
      (alignedEightSiteState psiAmplitude chiAmplitude) edge =
      restrictedBondEnergy chi0 edge.weight
        (productAmplitude psiAmplitude chiAmplitude edge.source)
        (productAmplitude psiAmplitude chiAmplitude edge.target)
  symbolNonnegative : ∀ momentum, 0 ≤ c19TransportSymbol momentum
  zeroMomentum : c19TransportSymbol (fun _ => 0) = 0
  integerWeightsMatch : ∀ direction,
    c19Weight direction = (c19IntegerWeight direction : ℝ)
  characterShift : ∀ momentum site direction,
    cubicLatticeCharacter momentum (infiniteC19Neighbor site direction) =
      cubicLatticeCharacter momentum site * c19Character momentum direction
  periodTwoCornerNeighbor : ∀ site direction,
    periodTwoCornerAt (infiniteC19Neighbor site direction) =
      cubeC19Neighbor (periodTwoCornerAt site) direction
  firstMomentZero : ∀ axis, c19FirstMoment axis = 0
  isotropicSecondMoment : ∀ axis other,
    c19SecondMoment axis other = if axis = other then 12 else 0
  characterFactorization : ∀ chi0 q momentum,
    restrictedCharacterTransportEnergy chi0 q momentum =
      Complex.normSq q / (2 * chi0 ^ 2) * c19TransportSymbol momentum
  repeatedLatticeFactorization : ∀ chi0 q momentum site,
    repeatedCharacterTransportEnergy chi0 q momentum site =
      Complex.normSq q / (2 * chi0 ^ 2) * c19TransportSymbol momentum
  nativeRepeatedStateFactorization : ∀ chi0 cornerAt
      psiAmplitude chiAmplitude momentum site,
    nativeRepeatedCharacterTransportEnergy chi0 cornerAt
        psiAmplitude chiAmplitude momentum site =
      Complex.normSq (chiAmplitude * psiAmplitude) /
          (2 * chi0 ^ 2) * c19TransportSymbol momentum
  nativePeriodTwoStateFactorization : ∀ chi0 psiAmplitude
      chiAmplitude momentum site,
    nativeRepeatedCharacterTransportEnergy chi0 periodTwoCornerAt
        psiAmplitude chiAmplitude momentum site =
      Complex.normSq (chiAmplitude * psiAmplitude) /
          (2 * chi0 ^ 2) * c19TransportSymbol momentum
  nativeProductLinearization : ∀ psi0 chi0 dPsi dChi eps,
    (chi0 + eps * dChi) * (psi0 + eps * dPsi) - chi0 * psi0 =
      eps * productTangent psi0 chi0 dPsi dChi +
        eps ^ 2 * (dChi * dPsi)

theorem dirac006_native_transport_symbol : Dirac006Certificate where
  exactSectorBond := aligned_exterior_area_is_restricted_bond
  symbolNonnegative := c19_transport_symbol_nonnegative
  zeroMomentum := c19_transport_symbol_zero
  integerWeightsMatch := c19_weight_is_integer_weight
  characterShift := cubic_character_neighbor
  periodTwoCornerNeighbor := period_two_corner_neighbor
  firstMomentZero := c19_first_moment_zero
  isotropicSecondMoment := c19_second_moment_isotropic
  characterFactorization := restricted_character_energy_has_c19_symbol
  repeatedLatticeFactorization := repeated_character_energy_has_c19_symbol
  nativeRepeatedStateFactorization :=
    native_repeated_state_energy_has_c19_symbol
  nativePeriodTwoStateFactorization :=
    native_period_two_state_energy_has_c19_symbol
  nativeProductLinearization := product_amplitude_first_order_expansion

end
end LeanDirac
