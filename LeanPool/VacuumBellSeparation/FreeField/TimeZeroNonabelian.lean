/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticNondegenerate
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroSymplecticAlgebra
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroWeylRelations
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroAlgebra

/-!
# Noncommuting actual local Weyl operators

A smooth bump supplies a nonzero localized real source. Its literal
quarter-turn supplies a nonzero symplectic partner. Real rescaling sets
the symplectic pairing to pi, so the two Weyl phases are opposite.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

/-- A nonempty open spatial region contains an actual nonzero compact source. -/
theorem exists_nonzero_localizedTimeZeroSource
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u : TimeZeroSource, u ∈ localizedTimeZeroSources U ∧ u ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hf, hcompact, hsmooth, _, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  let g : SpatialTestFunction := ⟨f, hsmooth, hcompact⟩
  refine ⟨(g, 0), ⟨hf, ?_⟩, ?_⟩
  · change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ U
    simp
  · intro hzero
    have hz := congrArg (fun u : TimeZeroSource => u.1.1 x) hzero
    change f x = 0 at hz
    rw [hfx] at hz
    exact one_ne_zero hz

variable {m : ℝ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem FreeFieldVacuum.timeZeroWeyl_not_commute_of_symplectic_pi
    (V : FreeFieldVacuum m H) (hm : 0 < m) (u v : TimeZeroSource)
    (huv : timeZeroSymplectic u v = Real.pi) :
    V.timeZeroWeyl hm u * V.timeZeroWeyl hm v ≠
      V.timeZeroWeyl hm v * V.timeZeroWeyl hm u := by
  have hvu : timeZeroSymplectic v u = -Real.pi := by
    rw [timeZeroSymplectic_skew v u, huv]
  have hminus : Complex.exp (-(Complex.I * (Real.pi : ℂ) / 2)) = -Complex.I := by
    have he : -(Complex.I * (Real.pi : ℂ) / 2) = -(Real.pi : ℂ) / 2 * Complex.I := by ring
    rw [he]
    exact Complex.exp_neg_pi_div_two_mul_I
  have hplus : Complex.exp (-(Complex.I * ((-Real.pi : ℝ) : ℂ) / 2)) = Complex.I := by
    rw [Complex.ofReal_neg]
    have he : -(Complex.I * -(Real.pi : ℂ) / 2) = (Real.pi : ℂ) / 2 * Complex.I := by ring
    rw [he]
    exact Complex.exp_pi_div_two_mul_I
  intro hcomm
  rw [V.timeZeroWeyl_mul_symplectic hm u v, V.timeZeroWeyl_mul_symplectic hm v u,
    huv, hvu, hminus, hplus, add_comm v u] at hcomm
  have hvec := congrArg (fun A : H →L[ℂ] H => A V.vacuum) hcomm
  change (-Complex.I) • (V.timeZeroWeyl hm (u + v) V.vacuum) =
    Complex.I • (V.timeZeroWeyl hm (u + v) V.vacuum) at hvec
  have hz : V.timeZeroWeyl hm (u + v) V.vacuum ≠ 0 := by
    intro hzero
    have hn := ContinuousLinearMap.norm_map_of_mem_unitary
      (V.timeZeroWeyl_mem_unitary hm (u + v)) V.vacuum
    rw [hzero, norm_zero, V.vacuum_norm] at hn
    exact zero_ne_one hn
  have hi : -Complex.I = Complex.I := smul_left_injective ℂ hz hvec
  have him := congrArg Complex.im hi
  norm_num at him

/-- Nonabelianity is proved from physical source pairs in the original H. -/
theorem FreeFieldVacuum.timeZeroLocalAlgebra_nonabelian
    (V : FreeFieldVacuum m H) (hm : 0 < m)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ A ∈ timeZeroLocalAlgebra V hm U, ∃ B ∈ timeZeroLocalAlgebra V hm U,
      A * B ≠ B * A := by
  obtain ⟨u, hu, hune⟩ := exists_nonzero_localizedTimeZeroSource hU hne
  obtain ⟨v, hv, hσ⟩ := exists_local_symplectic_partner hu hune
  let w := (Real.pi / timeZeroSymplectic u v) • u
  have hw : w ∈ localizedTimeZeroSources U :=
    (localizedTimeZeroSources U).smul_mem _ hu
  have hwv : timeZeroSymplectic w v = Real.pi := by
    dsimp only [w]
    rw [timeZeroSymplectic_smul_left, div_mul_cancel₀ _ hσ]
  exact ⟨V.timeZeroWeyl hm w,
    V.timeZeroWeyl_mem_timeZeroLocalAlgebra hm w hw.1 hw.2,
    V.timeZeroWeyl hm v,
    V.timeZeroWeyl_mem_timeZeroLocalAlgebra hm v hv.1 hv.2,
    V.timeZeroWeyl_not_commute_of_symplectic_pi hm w v hwv⟩

end VacuumBellSeparation
