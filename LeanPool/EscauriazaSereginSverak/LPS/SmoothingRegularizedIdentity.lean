/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedEquationWords
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedIdentitySpatial

/-!
# Ordered regularized energy identity

The differentiated pointwise momentum equation and the time derivative
of the squared Sobolev energy give the exact high-order energy identity.
The time differentiation is a separate Hilbert-space chain rule.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The regularized pointwise equation and the squared-energy chain
rule imply the exact ordered high-order identity
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_regularized_ordered_energy_identity
    (m : ℕ) (u v q : Vec3 → Vec3) (p : Vec3 → ℝ) (E' : ℝ)
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x => u x i)) 2 volume)
    (hvL2 : ∀ (j : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x => v x j)) 2 volume)
    (hpL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α p) 2 volume)
    (hdiv : ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => u y i) i x = 0)
    (hPDE : ∀ (i : Fin 3) (x : Vec3),
      q x i =
        (∑ j : Fin 3,
          spatialDeriv (spatialDeriv (fun y => u y i) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv (fun y => v y j * u y i) j x) -
          spatialDeriv p i x)
    (hchain : E' = 2 *
      (∑ i : Fin 3, ∑ α ∈ sobolevWords m,
        ∫ x : Vec3,
          wordDeriv α (fun y => u y i) x *
            wordDeriv α (fun y => q y i) x)) :
    E' + 2 *
      (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2) =
      2 * (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u y i) x *
            wordDeriv α (fun y => v y j * u y i) x) := by
  have hwords (i : Fin 3) (α : List (Fin 3))
      (hα : α ∈ sobolevWords m) (x : Vec3) :=
    lps_regularized_equation_wordDeriv u v q p hu hv hp hPDE i α x
  have hspatial := lps_ordered_spatial_energy_identity
    m u v q p hu hv hp huL2 hvL2 hpL2 hdiv hwords
  nlinarith only [hspatial, hchain]

end ESS
