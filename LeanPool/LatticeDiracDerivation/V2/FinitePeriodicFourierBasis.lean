/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicTangent
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Completeness of the quantized periodic C19 modes

`FinitePeriodicTangent` constructs a compatible C19 mode for every label in
`(ZMod L) ^ 3`.  This module proves those labels give every complex character
of the finite cubic torus, and hence index a basis of all complex scalar
fields on that torus.  No continuum momentum or spinor premise is used.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- The quantized mode as an additive character of the entire finite torus. -/
def periodicQuantizedAddChar (L : ℕ) [NeZero L]
    (mode : PeriodicCubicMomentum L) :
    AddChar (PeriodicCubicSite L) ℂ where
  toFun := periodicQuantizedCharacter L mode
  map_zero_eq_one' := by
    simp [periodicQuantizedCharacter]
  map_add_eq_mul' := by
    intro first second
    unfold periodicQuantizedCharacter
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
      AddChar.map_add_eq_mul]

/-- Unit displacement in one lattice axis. -/
def periodicCubicAxisUnit (L : ℕ) (axis : Fin 3) : PeriodicCubicSite L :=
  fun component => if component = axis then 1 else 0

theorem periodic_quantized_add_char_axis_unit
    (L : ℕ) [NeZero L] (mode : PeriodicCubicMomentum L)
    (axis : Fin 3) :
    periodicQuantizedAddChar L mode (periodicCubicAxisUnit L axis) =
      ZMod.stdAddChar (mode axis) := by
  unfold periodicQuantizedAddChar periodicQuantizedCharacter
    periodicCubicAxisUnit
  fin_cases axis <;>
    simp [Fin.sum_univ_succ]

/-- Different momentum labels give different finite-torus characters. -/
theorem periodic_quantized_add_char_injective
    (L : ℕ) [NeZero L] :
    Function.Injective (periodicQuantizedAddChar L) := by
  intro first second heq
  funext axis
  have hvalue := congrArg
    (fun character : AddChar (PeriodicCubicSite L) ℂ =>
      character (periodicCubicAxisUnit L axis)) heq
  rw [periodic_quantized_add_char_axis_unit,
    periodic_quantized_add_char_axis_unit] at hvalue
  exact ZMod.injective_stdAddChar hvalue

/-- There are exactly as many quantized labels as complex characters of the
finite cubic torus, so the preceding injection is a bijection. -/
theorem periodic_quantized_add_char_bijective
    (L : ℕ) [NeZero L] :
    Function.Bijective (periodicQuantizedAddChar L) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨periodic_quantized_add_char_injective L, ?_⟩
  simp [PeriodicCubicMomentum]

/-- The complete Fourier basis of scalar fields on the actual finite cubic
torus.  Through `periodic_quantized_add_char_bijective`, its basis labels are
equivalent to the explicit quantized C19 labels constructed above. -/
def periodicCubicFourierBasis (L : ℕ) [NeZero L] :
    Module.Basis (AddChar (PeriodicCubicSite L) ℂ) ℂ
      (PeriodicCubicSite L → ℂ) :=
  AddChar.complexBasis (PeriodicCubicSite L)

theorem periodic_cubic_fourier_basis_is_character
    (L : ℕ) [NeZero L]
    (character : AddChar (PeriodicCubicSite L) ℂ) :
    periodicCubicFourierBasis L character = character := by
  exact congrFun (AddChar.coe_complexBasis (PeriodicCubicSite L)) character

end
end LeanDirac.V2
