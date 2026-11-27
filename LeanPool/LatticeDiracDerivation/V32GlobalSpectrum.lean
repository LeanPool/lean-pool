/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32FrameworkLock
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # V3.2 global spectrum and the finite-C19 first-order obstruction

The unchanged action has an exact scalar finite-C19 normal-mode spectrum.
The oriented cubical first-order operator derived in V3.1 instead squares to
the quadratic (continuum) C19 symbol.  This file proves both statements and
identifies their exact difference.  Consequently it does not relabel the
continuum Dirac root as an exact finite-lattice Hamiltonian.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex



/-- The V3.2 E xa ct C19 En er gy Sq definition used by this stage. -/
def v32ExactC19EnergySq (mass : ℝ) (momentum : LatticeMomentum) : ℝ :=
  uniformVacuumModalSquare mass momentum

/-- The V3.2 E xa ct C19 Po si ti ve En er gy definition used by this stage. -/
def v32ExactC19PositiveEnergy (mass : ℝ) (momentum : LatticeMomentum) : ℝ :=
  Real.sqrt (v32ExactC19EnergySq mass momentum)

/-- The V3.2 E xa ct C19 Ne ga ti ve En er gy definition used by this stage. -/
def v32ExactC19NegativeEnergy (mass : ℝ) (momentum : LatticeMomentum) : ℝ :=
  -v32ExactC19PositiveEnergy mass momentum

theorem v32_exact_c19_energy_sq_eq
    (mass : ℝ) (momentum : LatticeMomentum) :
    v32ExactC19EnergySq mass momentum =
      mass ^ 2 + c19TransportSymbol momentum := by
  rfl

theorem v32_exact_c19_energy_sq_nonnegative
    (mass : ℝ) (momentum : LatticeMomentum) :
    0 ≤ v32ExactC19EnergySq mass momentum := by
  exact uniform_vacuum_modal_square_nonnegative mass momentum

theorem v32_exact_c19_energy_sq_ge_mass_sq
    (mass : ℝ) (momentum : LatticeMomentum) :
    mass ^ 2 ≤ v32ExactC19EnergySq mass momentum := by
  rw [v32_exact_c19_energy_sq_eq]
  linarith [c19_transport_symbol_nonnegative momentum]

theorem v32_exact_c19_positive_energy_nonnegative
    (mass : ℝ) (momentum : LatticeMomentum) :
    0 ≤ v32ExactC19PositiveEnergy mass momentum := by
  exact Real.sqrt_nonneg _

theorem v32_exact_c19_positive_energy_square
    (mass : ℝ) (momentum : LatticeMomentum) :
    v32ExactC19PositiveEnergy mass momentum ^ 2 =
      v32ExactC19EnergySq mass momentum := by
  exact Real.sq_sqrt (v32_exact_c19_energy_sq_nonnegative mass momentum)

theorem v32_exact_c19_negative_energy_square
    (mass : ℝ) (momentum : LatticeMomentum) :
    v32ExactC19NegativeEnergy mass momentum ^ 2 =
      v32ExactC19EnergySq mass momentum := by
  simp [v32ExactC19NegativeEnergy,
    v32_exact_c19_positive_energy_square]

theorem v32_exact_c19_positive_energy_ge_abs_mass
    (mass : ℝ) (momentum : LatticeMomentum) :
    |mass| ≤ v32ExactC19PositiveEnergy mass momentum := by
  rw [v32ExactC19PositiveEnergy, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (v32_exact_c19_energy_sq_ge_mass_sq mass momentum)

theorem v32_exact_c19_massive_gap
    (mass : ℝ) (momentum : LatticeMomentum) (hmass : mass ≠ 0) :
    0 < v32ExactC19PositiveEnergy mass momentum := by
  have habs : 0 < |mass| := abs_pos.mpr hmass
  exact lt_of_lt_of_le habs
    (v32_exact_c19_positive_energy_ge_abs_mass mass momentum)

theorem v32_exact_c19_branches_are_real
    (mass : ℝ) (momentum : LatticeMomentum) :
    v32ExactC19NegativeEnergy mass momentum ≤ 0 ∧
      0 ≤ v32ExactC19PositiveEnergy mass momentum := by
  constructor
  · exact neg_nonpos.mpr (v32_exact_c19_positive_energy_nonnegative _ _)
  · exact v32_exact_c19_positive_energy_nonnegative _ _

theorem v32_oriented_root_exact_iff_remainder_zero
    (mass : ℝ) (momentum : LatticeMomentum) :
    (∀ amplitude : CubicalCell8,
      nativeC19OrientedMassiveRoot mass momentum
          (nativeC19OrientedMassiveRoot mass momentum amplitude) =
        fun corner =>
          ((v32ExactC19EnergySq mass momentum : ℝ) : ℂ) *
            amplitude corner) ↔
      c19SpatialRemainder momentum = 0 := by
  constructor
  · intro hexact
    let amplitude : CubicalCell8 := fun _ => 1
    have hroot := congrFun (hexact amplitude) (0 : CubicalCorner)
    have hcontinuum := congrFun
      (native_c19_root_square_is_exact_hessian_minus_remainder
        mass momentum amplitude) (0 : CubicalCorner)
    simp only [amplitude, v32ExactC19EnergySq, mul_one] at hroot hcontinuum
    rw [hcontinuum] at hroot
    have hreal :
        uniformVacuumModalSquare mass momentum - c19SpatialRemainder momentum =
          uniformVacuumModalSquare mass momentum := by
      exact_mod_cast hroot
    exact sub_eq_self.mp hreal
  · intro hremainder amplitude
    rw [native_c19_root_square_is_exact_hessian_minus_remainder]
    simp [v32ExactC19EnergySq, hremainder]

theorem v32_oriented_root_exact_at_rest (mass : ℝ) :
    ∀ amplitude : CubicalCell8,
      nativeC19OrientedMassiveRoot mass (fun _ => 0)
          (nativeC19OrientedMassiveRoot mass (fun _ => 0) amplitude) =
        fun corner =>
          ((v32ExactC19EnergySq mass (fun _ => 0) : ℝ) : ℂ) *
            amplitude corner := by
  exact (v32_oriented_root_exact_iff_remainder_zero mass (fun _ => 0)).2
    c19_spatial_remainder_zero_at_origin

/-- The V3.2 P iA xi sM om en tu m definition used by this stage. -/
def v32PiAxisMomentum : LatticeMomentum := fun axis =>
  if axis = 0 then Real.pi else 0

theorem v32_pi_axis_remainder_exact :
    c19SpatialRemainder v32PiAxisMomentum = 48 - 12 * Real.pi ^ 2 := by
  rw [c19_spatial_remainder_is_bond_error_sum]
  simp [v32PiAxisMomentum, c19PhaseAngle, c19Weight, c19Coord,
    Fin.sum_univ_succ, Real.cos_neg]
  ring

theorem v32_pi_axis_remainder_nonzero :
    c19SpatialRemainder v32PiAxisMomentum ≠ 0 := by
  rw [v32_pi_axis_remainder_exact]
  nlinarith [Real.pi_gt_three]

theorem v32_pi_axis_transport_exact :
    c19TransportSymbol v32PiAxisMomentum = 48 := by
  rw [c19_symbol_exact_quadratic_plus_remainder,
    v32_pi_axis_remainder_exact]
  simp [c19QuadraticSymbol, v32PiAxisMomentum]

/-- The V3.2 O dd Tr an sp or tC oe ff ic ie nt s definition used by this stage. -/
def V32OddTransportCoefficients {n : Nat}
    (coefficient : LatticeMomentum → Fin n → ℝ) : Prop :=
  ∀ momentum component,
    coefficient (fun axis => -momentum axis) component =
      -coefficient momentum component

/-- The V3.2 A xi sP er io di cT ra ns po rt Co ef fi ci en ts definition used by this stage. -/
def V32AxisPeriodicTransportCoefficients {n : Nat}
    (coefficient : LatticeMomentum → Fin n → ℝ) : Prop :=
  ∀ momentum component axis,
    coefficient
        (fun other => momentum other +
          if other = axis then 2 * Real.pi else 0)
        component =
      coefficient momentum component

theorem v32_odd_periodic_transport_vanishes_at_pi_axis
    {n : Nat} (coefficient : LatticeMomentum → Fin n → ℝ)
    (hodd : V32OddTransportCoefficients coefficient)
    (hperiodic : V32AxisPeriodicTransportCoefficients coefficient) :
    ∀ component, coefficient v32PiAxisMomentum component = 0 := by
  intro component
  let negativePi : LatticeMomentum := fun axis =>
    -v32PiAxisMomentum axis
  have hshift :
      (fun other => negativePi other +
        if other = (0 : Fin 3) then 2 * Real.pi else 0) =
        v32PiAxisMomentum := by
    funext other
    fin_cases other
    · simp [negativePi, v32PiAxisMomentum]
      ring
    · simp [negativePi, v32PiAxisMomentum]
    · simp [negativePi, v32PiAxisMomentum]
  have hperiod := hperiodic negativePi component (0 : Fin 3)
  rw [hshift] at hperiod
  have hoddAt := hodd v32PiAxisMomentum component
  change coefficient negativePi component =
      -coefficient v32PiAxisMomentum component at hoddAt
  rw [hoddAt] at hperiod
  linarith

theorem v32_no_odd_periodic_sum_of_squares_factorization
    {n : Nat} (coefficient : LatticeMomentum → Fin n → ℝ)
    (hodd : V32OddTransportCoefficients coefficient)
    (hperiodic : V32AxisPeriodicTransportCoefficients coefficient) :
    ¬ (∀ momentum,
      ∑ component, coefficient momentum component ^ 2 =
        c19TransportSymbol momentum) := by
  intro hfactor
  have hzero := v32_odd_periodic_transport_vanishes_at_pi_axis
    coefficient hodd hperiodic
  have hpi := hfactor v32PiAxisMomentum
  rw [v32_pi_axis_transport_exact] at hpi
  have hsumzero :
      ∑ component, coefficient v32PiAxisMomentum component ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro component _
    rw [hzero component]
    norm_num
  linarith

/-- The V3.2 C19 Bo nd Di ff er en ce definition used by this stage. -/
def v32C19BondDifference
    (momentum : LatticeMomentum) (direction : C19Neighbor) : ℂ :=
  (Real.sqrt (c19Weight direction) : ℂ) *
    (1 - c19Character momentum direction)

theorem v32_c19_bond_difference_norm_sq
    (momentum : LatticeMomentum) (direction : C19Neighbor) :
    Complex.normSq (v32C19BondDifference momentum direction) =
      c19Weight direction *
        Complex.normSq (1 - c19Character momentum direction) := by
  rw [v32C19BondDifference, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  have hsqrt : Real.sqrt (c19Weight direction) *
      Real.sqrt (c19Weight direction) = c19Weight direction := by
    simpa [pow_two] using
      Real.sq_sqrt (le_of_lt (c19_weight_positive direction))
  rw [hsqrt]

theorem v32_exact_c19_symbol_is_local_bond_sum
    (momentum : LatticeMomentum) :
    c19TransportSymbol momentum =
      ∑ direction, Complex.normSq
        (v32C19BondDifference momentum direction) := by
  unfold c19TransportSymbol
  apply Finset.sum_congr rfl
  intro direction _
  rw [v32_c19_bond_difference_norm_sq]

theorem v32_no_global_exact_local_oriented_root :
    ¬ (∀ mass momentum amplitude,
      nativeC19OrientedMassiveRoot mass momentum
          (nativeC19OrientedMassiveRoot mass momentum amplitude) =
        fun corner =>
          ((v32ExactC19EnergySq mass momentum : ℝ) : ℂ) *
            amplitude corner) := by
  intro hglobal
  have hzero := (v32_oriented_root_exact_iff_remainder_zero
    1 v32PiAxisMomentum).1 (hglobal 1 v32PiAxisMomentum)
  exact v32_pi_axis_remainder_nonzero hzero

/-- The V3.2 C on ti nu um En er gy Sq definition used by this stage. -/
def v32ContinuumEnergySq (mass px py pz : ℝ) : ℝ :=
  mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2

/-- The V3.2 C on ti nu um Ha mi lt on ia n definition used by this stage. -/
def v32ContinuumHamiltonian
    (mass px py pz : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  cubicalStandardHamiltonian (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) z

theorem v32_continuum_energy_sq_nonnegative
    (mass px py pz : ℝ) :
    0 ≤ v32ContinuumEnergySq mass px py pz := by
  unfold v32ContinuumEnergySq
  positivity

theorem v32_continuum_energy_sq_pos_of_mass_pos
    (mass px py pz : ℝ) (hmass : 0 < mass) :
    0 < v32ContinuumEnergySq mass px py pz := by
  unfold v32ContinuumEnergySq
  nlinarith [sq_nonneg px, sq_nonneg py, sq_nonneg pz]

theorem v32_continuum_hamiltonian_square
    (mass px py pz : ℝ) (z : CubicalCell4) :
    v32ContinuumHamiltonian mass px py pz
        (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        (v32ContinuumEnergySq mass px py pz : ℂ) * z component := by
  simpa [v32ContinuumHamiltonian, v32ContinuumEnergySq,
    Complex.ofReal_pow] using
    cubical_standard_hamiltonian_square
      (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) z

theorem v32_continuum_hamiltonian_is_hermitian
    (mass px py pz : ℝ) (z w : CubicalCell4) :
    cubicalCell4Inner z (v32ContinuumHamiltonian mass px py pz w) =
      cubicalCell4Inner (v32ContinuumHamiltonian mass px py pz z) w := by
  apply Complex.ext <;>
    simp [cubicalCell4Inner, v32ContinuumHamiltonian,
      cubicalStandardHamiltonian, cubicalStandardBeta,
      cubicalStandardSpatial, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      Fin.sum_univ_four, Complex.mul_re, Complex.mul_im] <;> ring

theorem v32_rest_hamiltonian_square (mass : ℝ) (z : CubicalCell4) :
    v32ContinuumHamiltonian mass 0 0 0
        (v32ContinuumHamiltonian mass 0 0 0 z) =
      fun component => (mass ^ 2 : ℂ) * z component := by
  simpa [v32ContinuumEnergySq] using
    v32_continuum_hamiltonian_square mass 0 0 0 z

/-- The bundled V3.2 G lo ba lS pe ct ru mC er ti fi ca te. -/
structure V32GlobalSpectrumCertificate : Prop where
  framework : V32FrameworkLockCertificate
  exactFiniteEnergyNonnegative : ∀ mass momentum,
    0 ≤ v32ExactC19EnergySq mass momentum
  exactFiniteMassiveGap : ∀ mass momentum, mass ≠ 0 →
    0 < v32ExactC19PositiveEnergy mass momentum
  exactFiniteBranchesReal : ∀ mass momentum,
    v32ExactC19NegativeEnergy mass momentum ≤ 0 ∧
      0 ≤ v32ExactC19PositiveEnergy mass momentum
  exactFiniteBranchSquares : ∀ mass momentum,
    v32ExactC19PositiveEnergy mass momentum ^ 2 =
        v32ExactC19EnergySq mass momentum ∧
      v32ExactC19NegativeEnergy mass momentum ^ 2 =
        v32ExactC19EnergySq mass momentum
  localRootObstruction : ∀ mass momentum,
    (∀ amplitude : CubicalCell8,
      nativeC19OrientedMassiveRoot mass momentum
          (nativeC19OrientedMassiveRoot mass momentum amplitude) =
        fun corner =>
          ((v32ExactC19EnergySq mass momentum : ℝ) : ℂ) *
            amplitude corner) ↔
      c19SpatialRemainder momentum = 0
  noGlobalExactLocalRoot :
    ¬ (∀ mass momentum amplitude,
      nativeC19OrientedMassiveRoot mass momentum
          (nativeC19OrientedMassiveRoot mass momentum amplitude) =
        fun corner =>
          ((v32ExactC19EnergySq mass momentum : ℝ) : ℂ) *
            amplitude corner)
  oddPeriodicLocalFactorizationNoGo : ∀ {n : Nat}
    (coefficient : LatticeMomentum → Fin n → ℝ),
    V32OddTransportCoefficients coefficient →
    V32AxisPeriodicTransportCoefficients coefficient →
    ¬ (∀ momentum,
      ∑ component, coefficient momentum component ^ 2 =
        c19TransportSymbol momentum)
  exactLocalBondDecomposition : ∀ momentum,
    c19TransportSymbol momentum =
      ∑ direction, Complex.normSq
        (v32C19BondDifference momentum direction)
  energyNonnegative : ∀ mass px py pz,
    0 ≤ v32ContinuumEnergySq mass px py pz
  massiveGap : ∀ mass px py pz, 0 < mass →
    0 < v32ContinuumEnergySq mass px py pz
  exactSquare : ∀ mass px py pz z,
    v32ContinuumHamiltonian mass px py pz
        (v32ContinuumHamiltonian mass px py pz z) =
      fun component =>
        (v32ContinuumEnergySq mass px py pz : ℂ) * z component
  hermitian : ∀ mass px py pz z w,
    cubicalCell4Inner z (v32ContinuumHamiltonian mass px py pz w) =
      cubicalCell4Inner (v32ContinuumHamiltonian mass px py pz z) w
  restSquare : ∀ mass z,
    v32ContinuumHamiltonian mass 0 0 0
        (v32ContinuumHamiltonian mass 0 0 0 z) =
      fun component => (mass ^ 2 : ℂ) * z component

theorem v32_global_spectrum : V32GlobalSpectrumCertificate where
  framework := v32_framework_lock
  exactFiniteEnergyNonnegative := v32_exact_c19_energy_sq_nonnegative
  exactFiniteMassiveGap := v32_exact_c19_massive_gap
  exactFiniteBranchesReal := v32_exact_c19_branches_are_real
  exactFiniteBranchSquares := fun mass momentum =>
    ⟨v32_exact_c19_positive_energy_square mass momentum,
      v32_exact_c19_negative_energy_square mass momentum⟩
  localRootObstruction := v32_oriented_root_exact_iff_remainder_zero
  noGlobalExactLocalRoot := v32_no_global_exact_local_oriented_root
  oddPeriodicLocalFactorizationNoGo :=
    v32_no_odd_periodic_sum_of_squares_factorization
  exactLocalBondDecomposition := v32_exact_c19_symbol_is_local_bond_sum
  energyNonnegative := v32_continuum_energy_sq_nonnegative
  massiveGap := v32_continuum_energy_sq_pos_of_mass_pos
  exactSquare := v32_continuum_hamiltonian_square
  hermitian := v32_continuum_hamiltonian_is_hermitian
  restSquare := v32_rest_hamiltonian_square

end
end LeanDirac.V2
