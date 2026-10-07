/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnergyInequalityOfMixedTerm
public import LeanPool.CIVAxisymmetric.Closure.EnstrophyGronwall

/-!
`exists_closure_gronwall_bound_of_exists_energy_inequality` composes the substitution step
`deriv_le_of_closure_energy` of `eq:aniso:closure:energy` with the Grönwall step
`closure_gronwall_bound` of `lem:aniso:closure`: from the energy inequality in the form
`∃ Cstar ≥ 1, …` (as produced by `CIV.energy_inequality_of_mixed_term_bound`) together with the
`G`, `W` decay data, it gives the enstrophy decay `Y + 1 ≤ C' (−t)^{−C_*η}`.
`eta_sixteenth_valid` records that the manuscript's choice `η = 1/(16 C_*)` satisfies the
Grönwall step's smallness hypothesis `0 < η ∧ 2η < 1`, and
`exists_closure_gronwall_bound_sixteenth_eta` shows that this choice collapses the decay exponent
`C_* η` to the universal constant `1/16`, independent of `C_*` — the fact behind the remark of
`eq:aniso:closure:energy` that `2 C_* η = 1/8 < 1`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem exists_closure_gronwall_bound_of_exists_energy_inequality
    {Y M G W : ℝ → ℝ} {tη η Cη : ℝ} (htη : tη < 0) (hη : 0 < η ∧ 2 * η < 1) (hCη : 0 ≤ Cη)
    (hM : ∀ t ∈ Ioo tη 0, 0 ≤ M t) (hY : ∀ t ∈ Ioo tη 0, 0 ≤ Y t)
    (hG : ∀ t ∈ Ioo tη 0, G t ≤ η / (-t))
    (hW0 : ∀ t ∈ Ioo tη 0, 0 ≤ W t) (hW : ∀ t ∈ Ioo tη 0, W t ≤ Cη * (-t) ^ (-η))
    (hcont : ∀ t ∈ Ico tη 0, ContinuousOn Y (Icc tη t))
    (hderiv : ∀ t ∈ Ioo tη 0, HasDerivWithinAt Y (deriv Y t) (Ici t) t)
    (hY0 : 0 ≤ Y tη)
    (hex : ∃ Cstar : ℝ, 1 ≤ Cstar ∧
      ∀ t ∈ Ioo tη 0, deriv Y t + M t ≤ Cstar * (G t + W t ^ 2 + 1) * (Y t + 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ t ∈ Ioo tη 0, Y t + 1 ≤ C' * (-t) ^ (-(Cstar * η)) := by
  obtain ⟨Cstar, hCstar1, henergy⟩ := hex
  have hCstar0 : (0 : ℝ) ≤ Cstar := le_trans zero_le_one hCstar1
  have hineq := deriv_le_of_closure_energy hCstar0 hM hY hG hW0 hW henergy
  obtain ⟨C', hC'0, hbound⟩ := closure_gronwall_bound htη hCstar0 hη hCη hcont hderiv hY0 hineq
  exact ⟨Cstar, hCstar1, C', hC'0, hbound⟩

theorem eta_sixteenth_valid {Cstar : ℝ} (hCstar : 1 ≤ Cstar) :
    0 < (1 : ℝ) / (16 * Cstar) ∧ 2 * ((1 : ℝ) / (16 * Cstar)) < 1 := by
  have hCpos : 0 < Cstar := lt_of_lt_of_le one_pos hCstar
  have h_first : 0 < (1 : ℝ) / (16 * Cstar) := by
    positivity
  have h_second : 2 * ((1 : ℝ) / (16 * Cstar)) < 1 := by
    have h_eq : 2 * ((1 : ℝ) / (16 * Cstar)) = (1 : ℝ) / (8 * Cstar) := by
      field_simp [hCpos.ne']
      ring
    rw [h_eq]
    have h_denom_pos : 0 < 8 * Cstar := by positivity
    rw [div_lt_one h_denom_pos]
    have h_ineq : (1 : ℝ) < 8 * Cstar := by
      linarith only [hCstar]
    linarith only [h_ineq]
  exact And.intro h_first h_second

theorem exists_closure_gronwall_bound_sixteenth_eta
    {Y M G W : ℝ → ℝ} {tη Cη : ℝ} (htη : tη < 0) (hCη : 0 ≤ Cη)
    (hM : ∀ t ∈ Ioo tη 0, 0 ≤ M t) (hY : ∀ t ∈ Ioo tη 0, 0 ≤ Y t)
    (hW0 : ∀ t ∈ Ioo tη 0, 0 ≤ W t)
    (hcont : ∀ t ∈ Ico tη 0, ContinuousOn Y (Icc tη t))
    (hderiv : ∀ t ∈ Ioo tη 0, HasDerivWithinAt Y (deriv Y t) (Ici t) t)
    (hY0 : 0 ≤ Y tη)
    (hex : ∃ Cstar : ℝ, 1 ≤ Cstar ∧
      (∀ t ∈ Ioo tη 0, deriv Y t + M t ≤ Cstar * (G t + W t ^ 2 + 1) * (Y t + 1)) ∧
      (∀ t ∈ Ioo tη 0, G t ≤ (1 / (16 * Cstar)) / (-t)) ∧
      (∀ t ∈ Ioo tη 0, W t ≤ Cη * (-t) ^ (-(1 / (16 * Cstar))))) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Ioo tη 0, Y t + 1 ≤ C' * (-t) ^ (-(1 / 16 : ℝ)) := by
  obtain ⟨Cstar, hCstar1, henergy, hG, hW⟩ := hex
  have hCstar0 : 0 ≤ Cstar := le_trans zero_le_one hCstar1
  have hη := eta_sixteenth_valid hCstar1
  have hineq := deriv_le_of_closure_energy hCstar0 hM hY hG hW0 hW henergy
  obtain ⟨C', hC'0, hbound⟩ := closure_gronwall_bound htη hCstar0 hη hCη hcont hderiv hY0 hineq
  have hCstar_pos : 0 < Cstar := lt_of_lt_of_le one_pos hCstar1
  have hexp : Cstar * ((1 : ℝ) / (16 * Cstar)) = (1 / 16 : ℝ) := by
    field_simp [hCstar_pos.ne']
  refine ⟨C', hC'0, fun t ht => ?_⟩
  have hbound_t := hbound t ht
  calc
    Y t + 1 ≤ C' * (-t) ^ (-(Cstar * ((1 : ℝ) / (16 * Cstar)))) := hbound_t
    _ = C' * (-t) ^ (-(1 / 16 : ℝ)) := by rw [hexp]

end CIV
