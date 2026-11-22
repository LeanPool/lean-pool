/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.C19PlaneWave
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Quantized characters of the finite cubic torus -/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The native momentum labels of the finite cubic torus.  This has exactly
`L ^ 3` elements, the same number as `PeriodicCubicSite L`. -/
abbrev PeriodicCubicMomentum (L : ℕ) := Fin 3 → ZMod L

/-- The product character of the three cyclic axes, written as one standard
additive character. -/
def periodicQuantizedCharacter (L : ℕ) [NeZero L]
    (mode : PeriodicCubicMomentum L) (site : PeriodicCubicSite L) : ℂ :=
  ZMod.stdAddChar (∑ axis : Fin 3, mode axis * site axis)

/-- Real momentum chart for a finite-torus label.  The use of `ZMod.val`
chooses the usual representatives `0,...,L-1`; different representatives
give the same character. -/
def periodicQuantizedMomentum (L : ℕ)
    (mode : PeriodicCubicMomentum L) : LatticeMomentum :=
  fun axis => 2 * Real.pi * (mode axis).val / L

private theorem periodic_quantized_step_sum
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (direction : C19Neighbor) :
    (∑ axis : Fin 3,
        mode axis * (c19Coord axis direction : ZMod L)) =
      ((∑ axis : Fin 3,
          ((mode axis).val : ℤ) * c19Coord axis direction : ℤ) : ZMod L) := by
  push_cast
  apply Finset.sum_congr rfl
  intro axis _
  simp only [ZMod.natCast_zmod_val]

private theorem periodic_quantized_phase
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (direction : C19Neighbor) :
    ZMod.stdAddChar
        (∑ axis : Fin 3,
          mode axis * (c19Coord axis direction : ZMod L)) =
      c19Character (periodicQuantizedMomentum L mode) direction := by
  rw [periodic_quantized_step_sum]
  rw [ZMod.stdAddChar_coe]
  unfold c19Character c19PhaseAngle periodicQuantizedMomentum
  congr 1
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  ring_nf

theorem periodic_quantized_character_normSq_one
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (site : PeriodicCubicSite L) :
    Complex.normSq (periodicQuantizedCharacter L mode site) = 1 := by
  rw [periodicQuantizedCharacter, ZMod.stdAddChar_apply]
  exact Circle.normSq_coe _

theorem periodic_quantized_character_neighbor
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (site : PeriodicCubicSite L) (direction : C19Neighbor) :
    periodicQuantizedCharacter L mode
        (periodicC19Neighbor L site direction) =
      periodicQuantizedCharacter L mode site *
        c19Character (periodicQuantizedMomentum L mode) direction := by
  unfold periodicQuantizedCharacter periodicC19Neighbor
  simp only [mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  rw [periodic_quantized_phase]

end
end LeanDirac.V2
