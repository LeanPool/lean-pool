/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroWeyl
public import LeanPool.VacuumBellSeparation.FreeField.SourceEmbeddingConstruction

/-!
# The literal time-zero Weyl relations

These are the multiplication and adjoint identities in Section 2.1,
on the original vacuum Hilbert space and with the integral symplectic form.
The exact Gram identity supplies the factor one half in the phase.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem timeZeroOneParticleInner_im {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    (timeZeroOneParticleInner m u v).im = timeZeroSymplectic u v / 2 := by
  rw [timeZeroGram_identity hm]
  simp [Complex.mul_im]; ring

/-- The manuscript's exact Weyl phase in the literal integral symplectic form. -/
theorem FreeFieldVacuum.timeZeroWeyl_mul_symplectic (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u v : TimeZeroSource) :
    V.timeZeroWeyl hm u * V.timeZeroWeyl hm v =
      Complex.exp (-(Complex.I * (timeZeroSymplectic u v : ℂ) / 2)) •
        V.timeZeroWeyl hm (u + v) := by
  rw [V.timeZeroWeyl_mul hm, timeZeroOneParticleInner_im hm]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, mul_div_assoc]

theorem FreeFieldVacuum.timeZeroWeyl_zero (V : FreeFieldVacuum m H)
    (hm : 0 < m) : V.timeZeroWeyl hm 0 = 1 := by
  have hinner : timeZeroOneParticleInner m 0 0 = 0 := by
    rw [← inner_timeZeroL2 hm]
    change ⟪timeZeroLinear hm 0, timeZeroLinear hm 0⟫_ℂ = 0
    rw [map_zero, inner_zero_left]
  have hidem : V.timeZeroWeyl hm 0 * V.timeZeroWeyl hm 0 = V.timeZeroWeyl hm 0 := by
    simpa only [hinner, Complex.zero_im, Complex.ofReal_zero, mul_zero, neg_zero,
      Complex.exp_zero, one_smul, add_zero] using V.timeZeroWeyl_mul hm 0 0
  have hu := Unitary.star_mul_self_of_mem (V.timeZeroWeyl_mem_unitary hm 0)
  calc
    V.timeZeroWeyl hm 0 =
        (star (V.timeZeroWeyl hm 0) * V.timeZeroWeyl hm 0) * V.timeZeroWeyl hm 0 := by
      rw [hu, one_mul]
    _ = star (V.timeZeroWeyl hm 0) * (V.timeZeroWeyl hm 0 * V.timeZeroWeyl hm 0) :=
      mul_assoc _ _ _
    _ = 1 := by rw [hidem, hu]

/-- Adjoint reverses the actual compact real source label. -/
theorem FreeFieldVacuum.timeZeroWeyl_star_eq_neg (V : FreeFieldVacuum m H)
    (hm : 0 < m) (u : TimeZeroSource) :
    star (V.timeZeroWeyl hm u) = V.timeZeroWeyl hm (-u) := by
  have him : (timeZeroOneParticleInner m u (-u)).im = 0 := by
    rw [← inner_timeZeroL2 hm]
    change (⟪timeZeroLinear hm u, timeZeroLinear hm (-u)⟫_ℂ).im = 0
    rw [map_neg, inner_neg_right, Complex.neg_im]
    change -RCLike.im (⟪timeZeroLinear hm u, timeZeroLinear hm u⟫_ℂ) = 0
    rw [inner_self_im, neg_zero]
  have hinv : V.timeZeroWeyl hm u * V.timeZeroWeyl hm (-u) = 1 := by
    rw [V.timeZeroWeyl_mul hm, him, Complex.ofReal_zero, mul_zero, neg_zero,
      Complex.exp_zero, one_smul, add_neg_cancel, V.timeZeroWeyl_zero hm]
  have hu := Unitary.star_mul_self_of_mem (V.timeZeroWeyl_mem_unitary hm u)
  calc
    star (V.timeZeroWeyl hm u) = star (V.timeZeroWeyl hm u) * 1 := (mul_one _).symm
    _ = star (V.timeZeroWeyl hm u) * (V.timeZeroWeyl hm u * V.timeZeroWeyl hm (-u)) := by
      rw [hinv]
    _ = (star (V.timeZeroWeyl hm u) * V.timeZeroWeyl hm u) * V.timeZeroWeyl hm (-u) :=
      (mul_assoc _ _ _).symm
    _ = V.timeZeroWeyl hm (-u) := by rw [hu, one_mul]

end VacuumBellSeparation
