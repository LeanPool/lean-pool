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

public import LeanPool.LatticeDiracDerivation.V32Robustness

/-! # V3.2 Stage 14: theorem-backed transport observables for V4 -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 M om en tu mC om po ne nt definition used by this stage. -/
def v32MomentumComponent (px py pz : ℝ) (axis : Fin 3) : ℝ :=
  if axis = 0 then px else if axis = 1 then py else pz

/-- The V3.2 P os it iv eG ro up Ve lo ci ty definition used by this stage. -/
def v32PositiveGroupVelocity
    (energy px py pz : ℝ) (axis : Fin 3) : ℝ :=
  c19ContinuumSpeed * v32MomentumComponent px py pz axis / energy

/-- The V3.2 N eg at iv eG ro up Ve lo ci ty definition used by this stage. -/
def v32NegativeGroupVelocity
    (energy px py pz : ℝ) (axis : Fin 3) : ℝ :=
  -v32PositiveGroupVelocity energy px py pz axis

/-- The V3.2 G ro up Sp ee dS q definition used by this stage. -/
def v32GroupSpeedSq (energy px py pz : ℝ) : ℝ :=
  ∑ axis, v32PositiveGroupVelocity energy px py pz axis ^ 2

theorem v32_group_velocity_is_current_over_density
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass) (henergy : energy ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) (axis : Fin 3) :
    cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      v32PositiveGroupVelocity energy px py pz axis *
        cubicalCell4Density
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) := by
  rw [normalized_positive_frequency_current mass energy px py pz
    hpositive hshell q axis]
  rw [normalized_positive_frequency_density mass energy px py pz
    hpositive hshell q]
  fin_cases axis <;>
    simp [v32PositiveGroupVelocity, v32MomentumComponent] <;>
    field_simp [henergy]

theorem v32_energy_branch_reverses_group_velocity
    (energy px py pz : ℝ) (axis : Fin 3) :
    v32NegativeGroupVelocity energy px py pz axis =
      -v32PositiveGroupVelocity energy px py pz axis := rfl

theorem v32_group_speed_sq_formula
    (energy px py pz : ℝ) (henergy : energy ≠ 0) :
    v32GroupSpeedSq energy px py pz =
      c19ContinuumSpeed ^ 2 * (px ^ 2 + py ^ 2 + pz ^ 2) / energy ^ 2 := by
  simp [v32GroupSpeedSq, v32PositiveGroupVelocity,
    v32MomentumComponent, Fin.sum_univ_succ]
  field_simp [henergy]
  ring

theorem v32_group_speed_bounded_by_lattice_speed_sq
    (mass energy px py pz : ℝ) (henergy : energy ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    v32GroupSpeedSq energy px py pz ≤ c19ContinuumSpeed ^ 2 := by
  rw [v32_group_speed_sq_formula energy px py pz henergy]
  have he2 : 0 < energy ^ 2 := sq_pos_of_ne_zero henergy
  have hc2 : 0 ≤ c19ContinuumSpeed ^ 2 := sq_nonneg _
  have hp : px ^ 2 + py ^ 2 + pz ^ 2 ≤ energy ^ 2 := by
    nlinarith [sq_nonneg mass]
  apply (div_le_iff₀ he2).2
  nlinarith

/-- The bundled V3.2 T ra ns po rt Ob se rv ab le Ce rt if ic at e. -/
structure V32TransportObservableCertificate : Prop where
  currentIsMomentumResponse : UniformVacuumCurrentCertificate
  exactFreeChain : CompleteFreeDiracCertificate
  restCurrentZero : ∀ axis r, r ≠ 0 → ∀ position,
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0
  finiteC19CurrentError : ∀ momentum axis q radius,
    0 ≤ radius → (∀ coordinate, |momentum coordinate| ≤ radius) →
      |finiteC19CurrentRemainder momentum axis q| ≤
        16 * radius ^ 3 * uniformCell2Density q
  currentOverDensityVelocity : ∀ mass energy px py pz,
    0 < energy + mass → energy ≠ 0 →
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
    ∀ q axis,
      cubicalDiracCurrent axis
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
        v32PositiveGroupVelocity energy px py pz axis *
          cubicalCell4Density
            (normalizedPositiveFrequencyEmbedding mass energy px py pz q)
  branchVelocitySign : ∀ energy px py pz axis,
    v32NegativeGroupVelocity energy px py pz axis =
      -v32PositiveGroupVelocity energy px py pz axis
  speedBoundSq : ∀ mass energy px py pz,
    energy ≠ 0 → energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 →
      v32GroupSpeedSq energy px py pz ≤ c19ContinuumSpeed ^ 2

theorem v32_transport_observables : V32TransportObservableCertificate where
  currentIsMomentumResponse := uniform_vacuum_current_bridge
  exactFreeChain := complete_first_principles_free_dirac
  restCurrentZero := uniform_positive_rest_dirac_current_zero
  finiteC19CurrentError := finite_c19_current_remainder_bound
  currentOverDensityVelocity := v32_group_velocity_is_current_over_density
  branchVelocitySign := v32_energy_branch_reverses_group_velocity
  speedBoundSq := v32_group_speed_bounded_by_lattice_speed_sq


end
end LeanDirac.V2
