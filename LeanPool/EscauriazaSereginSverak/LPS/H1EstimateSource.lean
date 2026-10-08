/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1Estimate
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergyIdentity

/-!
# The `H¹` estimate for strong solutions

Source-facing forms of `lem:lps-H1-estimate`: a strong solution with finite
Serrin norm has its gradient energy plus the integrated Laplacian energy
bounded by the initial gradient energy times an exponential of the Serrin
norm. The chain-rule identity is supplied by the `H¹` energy identity of
`prop:lps-local-strong`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `H¹` estimate for a strong solution with finite Serrin norm of order
`s > 3` (`lem:lps-H1-estimate`), with a constant depending only on `s`. -/
theorem lps_h1_estimate {s : ℝ} (hs : 3 < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ},
      IsLpsStrongSolution t₀ t₁ u Du p →
      (∫⁻ t in Ioo t₀ t₁,
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤ →
      ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
        ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu ∧
        MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
        MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
        ∀ t ∈ Icc t₀ t₁,
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) +
              ∫ τ in t₀..t, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, τ) i j j) ^ 2 ≤
            (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) *
              Real.exp (C * ∫ τ in t₀..t,
                (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, τ)))
                  (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3))) := by
  obtain ⟨C, hC, hEst⟩ := lps_h1_estimate_finite hs
  refine ⟨C, hC, ?_⟩
  intro t₀ t₁ u Du p hU hmix
  obtain ⟨D2u, Dtu, hD, hM2, hMt, hId, -⟩ := ESS.LPS.lps_unregularised_h1_energy_identity hU
  exact ⟨D2u, Dtu, hD, hM2, hMt, hEst hU hD hM2 hMt hId hmix⟩

/-- The endpoint `H¹` estimate for a strong solution with finite `L²_t L∞_x`
norm (`lem:lps-H1-estimate`, case `s = ∞`), with absolute constant. -/
theorem lps_h1_estimate_endpoint :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ},
      IsLpsStrongSolution t₀ t₁ u Du p →
      (∫⁻ t in Ioo t₀ t₁,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤ →
      ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
        ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ t₁) u Du D2u Dtu ∧
        MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
        MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ t₁))) ∧
        ∀ t ∈ Icc t₀ t₁,
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) +
              ∫ τ in t₀..t, ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, τ) i j j) ^ 2 ≤
            (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) *
              Real.exp (C * ∫ τ in t₀..t,
                (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, τ))) ⊤ volume).toReal ^ 2) := by
  obtain ⟨C, hC, hEst⟩ := lps_h1_estimate_infinite
  refine ⟨C, hC, ?_⟩
  intro t₀ t₁ u Du p hU hmix
  obtain ⟨D2u, Dtu, hD, hM2, hMt, hId, -⟩ := ESS.LPS.lps_unregularised_h1_energy_identity hU
  exact ⟨D2u, Dtu, hD, hM2, hMt, hEst hU hD hM2 hMt hId hmix⟩

end ESS

end
