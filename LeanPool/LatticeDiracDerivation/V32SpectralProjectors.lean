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

public import LeanPool.LatticeDiracDerivation.V32GlobalSpectrum

/-!
# V3.2 Stage 3: spectral projectors

The projectors in this file are constructed only from the Hamiltonian proved in
Stage 2.  The hypotheses on `energy` say that it is a nonzero square root of
the already-derived dispersion relation; no branch or physical scale is
inserted.
-/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 S pe ct ra lP ro je ct or definition used by this stage. -/
def v32SpectralProjector
    (sign : ℝ) (mass px py pz energy : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    (1 / 2 : ℂ) *
      (z component + (sign / energy : ℝ) *
        v32ContinuumHamiltonian mass px py pz z component)

/-- The V3.2 P os it iv eP ro je ct or definition used by this stage. -/
def v32PositiveProjector := v32SpectralProjector 1
/-- The V3.2 N eg at iv eP ro je ct or definition used by this stage. -/
def v32NegativeProjector := v32SpectralProjector (-1)

theorem v32_projectors_complete
    (mass px py pz energy : ℝ) (z : CubicalCell4) :
    (fun component =>
      v32PositiveProjector mass px py pz energy z component +
        v32NegativeProjector mass px py pz energy z component) = z := by
  funext component
  simp [v32PositiveProjector, v32NegativeProjector, v32SpectralProjector]
  ring

theorem v32_spectral_projector_idempotent
    (sign mass px py pz energy : ℝ)
    (hsign : sign ^ 2 = 1)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32SpectralProjector sign mass px py pz energy
        (v32SpectralProjector sign mass px py pz energy z) =
      v32SpectralProjector sign mass px py pz energy z := by
  have hsq := v32_continuum_hamiltonian_square mass px py pz z
  funext component
  have hsqc := congrFun hsq component
  have hlinear :
      v32ContinuumHamiltonian mass px py pz
          (v32SpectralProjector sign mass px py pz energy z) component =
        (1 / 2 : ℂ) *
          (v32ContinuumHamiltonian mass px py pz z component +
            (sign / energy : ℝ) *
              v32ContinuumHamiltonian mass px py pz
                (v32ContinuumHamiltonian mass px py pz z) component) := by
    fin_cases component <;>
      simp [v32SpectralProjector, v32ContinuumHamiltonian,
        cubicalStandardHamiltonian, cubicalStandardSpatial,
        cubicalStandardBeta, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring
  simp only [v32SpectralProjector]
  rw [hlinear, hsqc]
  have hsignC : (sign : ℂ) ^ 2 = 1 := by exact_mod_cast hsign
  have henergyC : (energy : ℂ) ^ 2 = (v32ContinuumEnergySq mass px py pz : ℂ) := by
    exact_mod_cast henergy
  have hneC : (energy : ℂ) ≠ 0 := by exact_mod_cast hne
  have hdiv : ((sign / energy : ℝ) : ℂ) = (sign : ℂ) / (energy : ℂ) := by
    norm_num
  rw [hdiv]
  field_simp [hneC]
  ring_nf at hsignC henergyC ⊢
  rw [hsignC, henergyC]
  ring

theorem v32_positive_projector_idempotent
    (mass px py pz energy : ℝ)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32PositiveProjector mass px py pz energy
        (v32PositiveProjector mass px py pz energy z) =
      v32PositiveProjector mass px py pz energy z := by
  exact v32_spectral_projector_idempotent 1 mass px py pz energy (by norm_num)
    henergy hne z

theorem v32_negative_projector_idempotent
    (mass px py pz energy : ℝ)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32NegativeProjector mass px py pz energy
        (v32NegativeProjector mass px py pz energy z) =
      v32NegativeProjector mass px py pz energy z := by
  exact v32_spectral_projector_idempotent (-1) mass px py pz energy (by norm_num)
    henergy hne z

theorem v32_projectors_orthogonal
    (mass px py pz energy : ℝ)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32PositiveProjector mass px py pz energy
        (v32NegativeProjector mass px py pz energy z) = 0 := by
  have hsq := v32_continuum_hamiltonian_square mass px py pz z
  funext component
  have hsqc := congrFun hsq component
  have hlinear :
      v32ContinuumHamiltonian mass px py pz
          (v32NegativeProjector mass px py pz energy z) component =
        (1 / 2 : ℂ) *
          (v32ContinuumHamiltonian mass px py pz z component -
            (1 / energy : ℝ) *
              v32ContinuumHamiltonian mass px py pz
                (v32ContinuumHamiltonian mass px py pz z) component) := by
    fin_cases component <;>
      simp [v32NegativeProjector, v32SpectralProjector,
        v32ContinuumHamiltonian, cubicalStandardHamiltonian,
        cubicalStandardSpatial, cubicalStandardBeta,
        cubicalStandardAlphaX, cubicalStandardAlphaY,
        cubicalStandardAlphaZ] <;> ring
  simp only [v32PositiveProjector, v32NegativeProjector,
    v32SpectralProjector]
  have hlinear' := hlinear
  simp only [v32NegativeProjector] at hlinear'
  rw [hlinear', hsqc]
  simp only [Pi.zero_apply]
  have henergyC : (energy : ℂ) ^ 2 = (v32ContinuumEnergySq mass px py pz : ℂ) := by
    exact_mod_cast henergy
  have hneC : (energy : ℂ) ≠ 0 := by exact_mod_cast hne
  have honeDiv : ((1 / energy : ℝ) : ℂ) = (1 : ℂ) / (energy : ℂ) := by
    norm_num
  have hnegDiv : (((-1) / energy : ℝ) : ℂ) = (-1 : ℂ) / (energy : ℂ) := by
    norm_num
  rw [honeDiv, hnegDiv]
  field_simp [hneC]
  ring_nf at henergyC ⊢
  rw [henergyC]
  ring

theorem v32_spectral_projector_is_eigenbranch
    (sign mass px py pz energy : ℝ)
    (hsign : sign ^ 2 = 1)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32ContinuumHamiltonian mass px py pz
        (v32SpectralProjector sign mass px py pz energy z) =
      fun component =>
        ((sign * energy : ℝ) : ℂ) *
          v32SpectralProjector sign mass px py pz energy z component := by
  have hsq := v32_continuum_hamiltonian_square mass px py pz z
  funext component
  have hsqc := congrFun hsq component
  have hlinear :
      v32ContinuumHamiltonian mass px py pz
          (v32SpectralProjector sign mass px py pz energy z) component =
        (1 / 2 : ℂ) *
          (v32ContinuumHamiltonian mass px py pz z component +
            (sign / energy : ℝ) *
              v32ContinuumHamiltonian mass px py pz
                (v32ContinuumHamiltonian mass px py pz z) component) := by
    fin_cases component <;>
      simp [v32SpectralProjector, v32ContinuumHamiltonian,
        cubicalStandardHamiltonian, cubicalStandardSpatial,
        cubicalStandardBeta, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring
  rw [hlinear, hsqc]
  simp only [v32SpectralProjector]
  have hsignC : (sign : ℂ) ^ 2 = 1 := by exact_mod_cast hsign
  have henergyC : (energy : ℂ) ^ 2 =
      (v32ContinuumEnergySq mass px py pz : ℂ) := by
    exact_mod_cast henergy
  have hneC : (energy : ℂ) ≠ 0 := by exact_mod_cast hne
  have hdiv : ((sign / energy : ℝ) : ℂ) =
      (sign : ℂ) / (energy : ℂ) := by norm_num
  rw [hdiv]
  push_cast
  field_simp [hneC]
  have hsignMul : (sign : ℂ) * (sign : ℂ) = 1 := by
    simpa [pow_two] using hsignC
  have henergyMul : (energy : ℂ) * (energy : ℂ) =
      (v32ContinuumEnergySq mass px py pz : ℂ) := by
    simpa [pow_two] using henergyC
  rw [← henergyMul]
  ring_nf
  rw [hsignC]
  ring

theorem v32_positive_projector_is_positive_branch
    (mass px py pz energy : ℝ)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32ContinuumHamiltonian mass px py pz
        (v32PositiveProjector mass px py pz energy z) =
      fun component =>
        (energy : ℂ) *
          v32PositiveProjector mass px py pz energy z component := by
  simpa [v32PositiveProjector] using
    v32_spectral_projector_is_eigenbranch
      1 mass px py pz energy (by norm_num) henergy hne z

theorem v32_negative_projector_is_negative_branch
    (mass px py pz energy : ℝ)
    (henergy : energy ^ 2 = v32ContinuumEnergySq mass px py pz)
    (hne : energy ≠ 0) (z : CubicalCell4) :
    v32ContinuumHamiltonian mass px py pz
        (v32NegativeProjector mass px py pz energy z) =
      fun component =>
        (-energy : ℂ) *
          v32NegativeProjector mass px py pz energy z component := by
  simpa [v32NegativeProjector] using
    v32_spectral_projector_is_eigenbranch
      (-1) mass px py pz energy (by norm_num) henergy hne z

/-- The V3.2 U ni tP ha se definition used by this stage. -/
def v32UnitPhase (angle : ℝ) : ℂ :=
  (Real.cos angle : ℂ) - Complex.I * (Real.sin angle : ℂ)

theorem v32_unit_phase_norm_sq (angle : ℝ) :
    Complex.normSq (v32UnitPhase angle) = 1 := by
  simp [v32UnitPhase, Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  simpa [pow_two] using Real.cos_sq_add_sin_sq angle

/-- The V3.2 B ra nc hE vo lu ti on definition used by this stage. -/
def v32BranchEvolution
    (sign mass px py pz energy time : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    v32UnitPhase (sign * energy * time) *
      v32SpectralProjector sign mass px py pz energy z component

theorem v32_branch_evolution_preserves_projected_density
    (sign mass px py pz energy time : ℝ) (z : CubicalCell4) :
    cubicalCell4Density
        (v32BranchEvolution sign mass px py pz energy time z) =
      cubicalCell4Density
        (v32SpectralProjector sign mass px py pz energy z) := by
  simp [cubicalCell4Density, v32BranchEvolution,
    Complex.normSq_mul, v32_unit_phase_norm_sq]

theorem v32_projected_density_nonnegative
    (sign mass px py pz energy : ℝ) (z : CubicalCell4) :
    0 ≤ cubicalCell4Density
      (v32SpectralProjector sign mass px py pz energy z) := by
  unfold cubicalCell4Density
  exact Finset.sum_nonneg (fun component _ => Complex.normSq_nonneg _)

/-- The bundled V3.2 S pe ct ra lP ro je ct or Ce rt if ic at e. -/
structure V32SpectralProjectorCertificate : Prop where
  complete : ∀ mass px py pz energy z,
    (fun component =>
      v32PositiveProjector mass px py pz energy z component +
        v32NegativeProjector mass px py pz energy z component) = z
  positiveIdempotent : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32PositiveProjector mass px py pz energy
          (v32PositiveProjector mass px py pz energy z) =
        v32PositiveProjector mass px py pz energy z
  negativeIdempotent : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32NegativeProjector mass px py pz energy
          (v32NegativeProjector mass px py pz energy z) =
        v32NegativeProjector mass px py pz energy z
  orthogonal : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32PositiveProjector mass px py pz energy
          (v32NegativeProjector mass px py pz energy z) = 0
  positiveInvariant : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32ContinuumHamiltonian mass px py pz
          (v32PositiveProjector mass px py pz energy z) =
        fun component => (energy : ℂ) *
          v32PositiveProjector mass px py pz energy z component
  negativeInvariant : ∀ mass px py pz energy,
    energy ^ 2 = v32ContinuumEnergySq mass px py pz → energy ≠ 0 → ∀ z,
      v32ContinuumHamiltonian mass px py pz
          (v32NegativeProjector mass px py pz energy z) =
        fun component => (-energy : ℂ) *
          v32NegativeProjector mass px py pz energy z component
  projectedDensityNonnegative : ∀ sign mass px py pz energy z,
    0 ≤ cubicalCell4Density
      (v32SpectralProjector sign mass px py pz energy z)
  branchEvolutionPreservesDensity : ∀ sign mass px py pz energy time z,
    cubicalCell4Density
        (v32BranchEvolution sign mass px py pz energy time z) =
      cubicalCell4Density
        (v32SpectralProjector sign mass px py pz energy z)

theorem v32_spectral_projectors : V32SpectralProjectorCertificate where
  complete := v32_projectors_complete
  positiveIdempotent := v32_positive_projector_idempotent
  negativeIdempotent := v32_negative_projector_idempotent
  orthogonal := v32_projectors_orthogonal
  positiveInvariant := v32_positive_projector_is_positive_branch
  negativeInvariant := v32_negative_projector_is_negative_branch
  projectedDensityNonnegative := v32_projected_density_nonnegative
  branchEvolutionPreservesDensity :=
    v32_branch_evolution_preserves_projected_density


end

end LeanDirac.V2
