/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Periodicity after extension from the upper half-plane

This elementary bridge is shared by the modular-function and derivative developments.
Keeping it separate lets the modular-function modules build without the derivative theory.
-/

@[expose] public section

namespace Chudnovsky

open UpperHalfPlane Complex Function

/-- A `1`-translation-invariant function on `ℍ` extends to a `1`-periodic function on `ℂ`. -/
lemma periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} (hf : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) :
    Periodic (f ∘ ofComplex) 1 := by
  intro w
  rcases lt_or_ge 0 w.im with hw | hw
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    have h := hf ⟨w, hw⟩
    convert h using 2
    ext
    simp [add_comm]
  · have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hw1 (by simpa using hw)]

end Chudnovsky
