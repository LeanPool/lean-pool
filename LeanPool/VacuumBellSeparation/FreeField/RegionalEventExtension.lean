/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalEffectExhaustion
public import LeanPool.VacuumBellSeparation.Bell.EventConstantUpper

/-!
# Actual regional Rényi event inequalities from uniform finite estimates

Positive powers are continuous even at zero. Thus the established canonical
effect exhaustion passes both denominator-free inequalities to the full
physical algebras.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace ENNReal

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem canonical_forward_event_bound_extends_to_local
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3))) {r K : ℝ} (hr : 1 < r)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ E ∈ effects (canonicalSourceAlgebra V hm S),
      ∀ P ∈ effects (canonicalSourceAlgebra V hm T),
        (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ r ≤
          K * ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (r - 1))
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ r ≤
      K * ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ (r - 1) := by
  let f : ℝ × ℝ × ℝ → ℝ := fun p => p.2.2 ^ r - K * (p.1 * p.2.1) ^ (r - 1)
  have hf : Continuous f := by
    exact ((Real.continuous_rpow_const (lt_trans zero_lt_one hr).le).comp
      (continuous_snd.comp continuous_snd)).sub
        (continuous_const.mul ((Real.continuous_rpow_const (sub_pos.mpr hr).le).comp
          (continuous_fst.mul (continuous_fst.comp continuous_snd))))
  have h := canonical_effect_inequality_extends_to_local V hm U W f hf
    (fun S T hS hT E hE P hP => sub_nonpos.mpr (hfinite S T hS hT E hE P hP)) hE hP
  exact sub_nonpos.mp h

theorem canonical_reverse_event_bound_extends_to_local
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    (U W : Set (EuclideanSpace ℝ (Fin 3))) {r K : ℝ} (hr : 1 < r)
    (hfinite : ∀ S T : Submodule ℝ TimeZeroSource,
      IsCanonicalSourceSystem U S → IsCanonicalSourceSystem W T →
      ∀ E ∈ effects (canonicalSourceAlgebra V hm S),
      ∀ P ∈ effects (canonicalSourceAlgebra V hm T),
        ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ r ≤
          K * (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ (r - 1))
    {E P : H →L[ℂ] H} (hE : E ∈ effects (timeZeroLocalAlgebra V hm U))
    (hP : P ∈ effects (timeZeroLocalAlgebra V hm W)) :
    ((⟪V.vacuum, E V.vacuum⟫_ℂ).re * (⟪V.vacuum, P V.vacuum⟫_ℂ).re) ^ r ≤
      K * (⟪V.vacuum, (E * P) V.vacuum⟫_ℂ).re ^ (r - 1) := by
  let f : ℝ × ℝ × ℝ → ℝ := fun p => (p.1 * p.2.1) ^ r - K * p.2.2 ^ (r - 1)
  have hf : Continuous f := by
    exact ((Real.continuous_rpow_const (lt_trans zero_lt_one hr).le).comp
      (continuous_fst.mul (continuous_fst.comp continuous_snd))).sub
        (continuous_const.mul ((Real.continuous_rpow_const (sub_pos.mpr hr).le).comp
          (continuous_snd.comp continuous_snd)))
  have h := canonical_effect_inequality_extends_to_local V hm U W f hf
    (fun S T hS hT E hE P hP => sub_nonpos.mpr (hfinite S T hS hT E hE P hP)) hE hP
  exact sub_nonpos.mp h

end VacuumBellSeparation
