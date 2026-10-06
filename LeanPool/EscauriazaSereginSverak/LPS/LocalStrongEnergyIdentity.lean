/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergy

/-!
# Energy identities of a strong solution

A strong solution satisfies the `H¹` energy identity, with the specified
time derivative and Laplacian, and the kinetic energy equality on every
subinterval of its lifespan (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The unregularized energy identities of a strong solution: the weak
derivative witnesses are square integrable, the squared gradient changes by
minus twice the pairing of the time derivative with the Laplacian, and the
kinetic energy satisfies the equality on every closed subinterval
(`prop:lps-local-strong`). -/
theorem lps_unregularised_h1_energy_identity
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : ESS.IsLpsStrongSolution t₀ T u Du p) :
    ∃ D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3,
      ∃ Dtu : ParabolicPoint → Vec3,
        HasSpaceTimeWeakDerivs Set.univ (Ioo t₀ T) u Du D2u Dtu ∧
        MemLp D2u 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) ∧
        MemLp Dtu 2 (volume.restrict (spaceTimeSet Set.univ (Ioo t₀ T))) ∧
        (∀ s t : ℝ, s ∈ Icc t₀ T → t ∈ Icc t₀ T → s ≤ t →
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
            (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
              2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
                ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j) ∧
        (∀ s t : ℝ, s ∈ Icc t₀ T → t ∈ Icc t₀ T → s ≤ t →
          (∫ x : Vec3, ∑ i : Fin 3, (u (x, t) i) ^ 2) +
              2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
                ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
            ∫ x : Vec3, ∑ i : Fin 3, (u (x, s) i) ^ 2) := by
  obtain ⟨D2u, Dtu, hDerivs, hMemU, hMemDu, hMemD2u, hMemDtu⟩ :=
    lps_strong_solution_derivative_data hU
  have hMemP : MemLp p 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) :=
    hU.2.2.2.2.1
  exact ⟨D2u, Dtu, hDerivs, hMemD2u, hMemDtu,
    lps_strong_h1_energy_identity hU hDerivs hMemU hMemDu hMemD2u hMemDtu,
    lps_strong_kinetic_energy_identity hU hDerivs hMemU hMemDu hMemD2u hMemDtu hMemP⟩

end ESS.LPS

end
