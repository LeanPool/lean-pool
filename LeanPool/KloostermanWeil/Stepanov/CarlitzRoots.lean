/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.RecurrencePackage


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Carlitz spectral roots

Connects the two spectral roots of the Carlitz recurrence to the formulation in Harcos
(2015), equation (2).
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open KloostermanWeil.Carlitz

noncomputable def carlitzAlpha
    (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℂ :=
  if ht : t = 0 then 0
  else Classical.choose (carlitz_spectral_roots_Kext p ht)

noncomputable def carlitzBeta
    (p : ℕ) [Fact p.Prime] (t : ZMod p) : ℂ :=
  if ht : t = 0 then 0
  else Classical.choose (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))

theorem carlitzAlpha_add_beta
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    carlitzAlpha p t + carlitzBeta p t = -Kext p 1 t := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).1

theorem carlitzAlpha_mul_beta
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0) :
    carlitzAlpha p t * carlitzBeta p t = (p : ℂ) := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).2.1

theorem Kext_eq_neg_root_power_sum
    (p : ℕ) [Fact p.Prime] {t : ZMod p} (ht : t ≠ 0)
    (r : ℕ) :
    Kext p (r + 1) t =
      -(carlitzAlpha p t ^ (r + 1) +
        carlitzBeta p t ^ (r + 1)) := by
  simp only [carlitzAlpha, carlitzBeta, dite_eq_right ht]
  exact (Classical.choose_spec (Classical.choose_spec
    (carlitz_spectral_roots_Kext p ht))).2.2 r



theorem Kext_eq_neg_root_power_sum_pos
    (p n : ℕ) [Fact p.Prime] {t : ZMod p}
    (ht : t ≠ 0) (hn : n ≠ 0) :
    letI : NeZero n := ⟨hn⟩
    KloostermanWeil.Carlitz.Kext p n t =
      -(carlitzAlpha p t ^ n + carlitzBeta p t ^ n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [Nat.succ_eq_add_one] using
    Kext_eq_neg_root_power_sum p ht r


end KloostermanWeil.Stepanov
