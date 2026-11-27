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

public import LeanPool.LatticeDiracDerivation.V32SpectralProjectors

/-! # V3.2 Stage 9: exact low-momentum energy reduction -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 M om en tu mS q definition used by this stage. -/
def v32MomentumSq (px py pz : ℝ) : ℝ := px ^ 2 + py ^ 2 + pz ^ 2

theorem v32_rest_energy_subtraction_exact
    (mass energy px py pz : ℝ)
    (hshell : energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz)
    (hden : energy + mass ≠ 0) :
    energy - mass = v32MomentumSq px py pz / (energy + mass) := by
  field_simp [hden]
  nlinarith

theorem v32_nonrelativistic_first_correction_exact
    (mass energy px py pz : ℝ)
    (hmass : mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz)
    (hden : energy + mass ≠ 0) :
    energy - mass - v32MomentumSq px py pz / (2 * mass) =
      -(v32MomentumSq px py pz) ^ 2 /
        (2 * mass * (energy + mass) ^ 2) := by
  have hlead := v32_rest_energy_subtraction_exact mass energy px py pz hshell hden
  rw [hlead]
  field_simp [hmass, hden]
  nlinarith [hshell]

/-- On the positive-energy branch the lower two coordinates are not an
independent input.  They are fixed exactly by the momentum response of the
upper two coordinates.  This is the algebraic elimination used in the free
Schrodinger limit. -/
theorem v32_positive_lower_component_elimination
    (mass energy px py pz : ℝ) (_hden : energy + mass ≠ 0)
    (q : UniformCell2) :
    cubicalCell4LowerHalf
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      fun component =>
        ((energy + mass : ℝ) : ℂ)⁻¹ *
          positivePauliSpatial px py pz
            (cubicalCell4Upper
              (normalizedPositiveFrequencyEmbedding
                mass energy px py pz q)) component := by
  let spinor := normalizedPositiveFrequencyEmbedding mass energy px py pz q
  have hupper : cubicalCell4Upper spinor =
      fun component => (positiveFrequencyScale mass energy : ℂ) * q component := by
    funext component
    fin_cases component <;> rfl
  have hlower : cubicalCell4LowerHalf spinor =
      fun component => (positiveFrequencyRatio mass energy : ℂ) *
        positivePauliSpatial px py pz q component := by
    funext component
    fin_cases component <;> rfl
  change cubicalCell4LowerHalf spinor = fun component =>
    ((energy + mass : ℝ) : ℂ)⁻¹ *
      positivePauliSpatial px py pz (cubicalCell4Upper spinor) component
  rw [hlower, hupper]
  funext component
  have hlinear :
      positivePauliSpatial px py pz
          (fun index => (positiveFrequencyScale mass energy : ℂ) * q index) component =
        (positiveFrequencyScale mass energy : ℂ) *
          positivePauliSpatial px py pz q component := by
    change cubicalSpatialLowerLinear px py pz
        ((positiveFrequencyScale mass energy : ℂ) • q) component = _
    rw [(cubicalSpatialLowerLinear px py pz).map_smul]
    rfl
  rw [hlinear, positiveFrequencyRatio]
  push_cast
  field_simp [show ((energy : ℂ) + (mass : ℂ)) ≠ 0 by exact_mod_cast _hden]

/-- After the rest oscillation is removed, the upper component obeys the
exact free kinetic-energy multiplier.  The usual `p ^ 2/(2m)` multiplier and
its complete relativistic correction are the two terms on the right. -/
theorem v32_free_schrodinger_multiplier_with_exact_remainder
    (mass energy px py pz : ℝ)
    (hmass : mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz)
    (hden : energy + mass ≠ 0) :
    energy - mass =
      v32MomentumSq px py pz / (2 * mass) -
        (v32MomentumSq px py pz) ^ 2 /
          (2 * mass * (energy + mass) ^ 2) := by
  have h := v32_nonrelativistic_first_correction_exact
    mass energy px py pz hmass hshell hden
  linear_combination h

/-- The bundled V3.2 N on re la ti vi st ic Li mi tC er ti fi ca te. -/
structure V32NonrelativisticLimitCertificate : Prop where
  exactRestSubtraction : ∀ mass energy px py pz,
    energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz →
      energy + mass ≠ 0 →
      energy - mass = v32MomentumSq px py pz / (energy + mass)
  firstCorrection : ∀ mass energy px py pz,
    mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz →
    energy + mass ≠ 0 →
    energy - mass - v32MomentumSq px py pz / (2 * mass) =
      -(v32MomentumSq px py pz) ^ 2 /
        (2 * mass * (energy + mass) ^ 2)
  lowerComponentElimination : ∀ mass energy px py pz,
    energy + mass ≠ 0 → ∀ q,
      cubicalCell4LowerHalf
          (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
        fun component =>
          ((energy + mass : ℝ) : ℂ)⁻¹ *
            positivePauliSpatial px py pz
              (cubicalCell4Upper
                (normalizedPositiveFrequencyEmbedding
                  mass energy px py pz q)) component
  freeSchrodingerMultiplier : ∀ mass energy px py pz,
    mass ≠ 0 →
    energy ^ 2 = mass ^ 2 + v32MomentumSq px py pz →
    energy + mass ≠ 0 →
    energy - mass =
      v32MomentumSq px py pz / (2 * mass) -
        (v32MomentumSq px py pz) ^ 2 /
          (2 * mass * (energy + mass) ^ 2)

theorem v32_nonrelativistic_limit : V32NonrelativisticLimitCertificate where
  exactRestSubtraction := v32_rest_energy_subtraction_exact
  firstCorrection := v32_nonrelativistic_first_correction_exact
  lowerComponentElimination := v32_positive_lower_component_elimination
  freeSchrodingerMultiplier :=
    v32_free_schrodinger_multiplier_with_exact_remainder


end
end LeanDirac.V2
