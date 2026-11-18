/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness along a nilpotent ideal

Every module is adically complete along a nilpotent ideal: the `I`-adic filtration is eventually
zero, so the module is Hausdorff and every Cauchy sequence is eventually constant.

## Main statements

* `IsAdicComplete.of_isNilpotent`: if `I` is nilpotent, every `R`-module is `I`-adically
  complete.
-/

public section

open Submodule

variable {R : Type*} [CommRing R] {I : Ideal R} (M : Type*) [AddCommGroup M] [Module R M]

/-- A module is adically complete along a nilpotent ideal. -/
theorem IsAdicComplete.of_isNilpotent (hI : IsNilpotent I) : IsAdicComplete I M := by
  obtain ⟨k, hk⟩ := hI
  have h {n : ℕ} (hn : k ≤ n) : (I ^ n • ⊤ : Submodule R M) = ⊥ := by
    rw [le_bot_iff.1 ((Ideal.pow_le_pow_right hn).trans_eq hk), Submodule.bot_smul]
  refine { haus' x hx := ?_, prec' f hf := ⟨f k, fun n ↦ ?_⟩ }
  · simpa [h le_rfl, SModEq.zero] using hx k
  · rcases le_total n k with hn | hn
    · exact hf hn
    · rw [SModEq.bot.1 (h le_rfl ▸ hf hn : f k ≡ f n [SMOD (⊥ : Submodule R M)])]
