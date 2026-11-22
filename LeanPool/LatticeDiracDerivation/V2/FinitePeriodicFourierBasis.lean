/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.FinitePeriodicCharacters
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Completeness of the quantized periodic C19 modes

The quantized labels in `(ZMod L) ^ 3` give all complex characters of the
finite cubic torus, and hence index a basis of its complex scalar fields.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

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
