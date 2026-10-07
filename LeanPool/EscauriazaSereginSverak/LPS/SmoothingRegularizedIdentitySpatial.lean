/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSpatialEnergyComponent
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressureWords
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductAll

/-!
# Spatial part of the regularized Sobolev identity

Pair each ordered derivative of the momentum equation with the
corresponding velocity derivative. Heat integration by parts produces
the gradient energy, tensor integration by parts produces the
transport pairing, and solenoidality cancels pressure.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial pairings in the ordered regularized energy identity
(`eq:lps-regularized-Hm-identity`). The derivative-level momentum
equation is the output of differentiating the regularized evolution. -/
theorem lps_ordered_spatial_energy_identity
    (m : ℕ) (u v q : Vec3 → Vec3) (p : Vec3 → ℝ)
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
    (hPDE : ∀ (i : Fin 3) (α : List (Fin 3)), α ∈ sobolevWords m →
      ∀ x : Vec3,
        wordDeriv α (fun y => q y i) x =
          (∑ j : Fin 3,
            spatialDeriv
              (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x) -
          (∑ j : Fin 3,
            spatialDeriv
              (wordDeriv α (fun y => v y j * u y i)) j x) -
            spatialDeriv (wordDeriv α p) i x) :
    (∑ i : Fin 3, ∑ α ∈ sobolevWords m,
      ∫ x : Vec3, wordDeriv α (fun y => u y i) x *
        wordDeriv α (fun y => q y i) x) +
      (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2) =
      ∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u y i) x *
            wordDeriv α (fun y => v y j * u y i) x := by
  let W := sobolevWords m
  have hcomponent (i : Fin 3) (α : List (Fin 3)) (hα : α ∈ W) :
      (∫ x : Vec3, wordDeriv α (fun y => u y i) x *
        wordDeriv α (fun y => q y i) x) +
        (∑ j : Fin 3,
          ∫ x : Vec3, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2) =
        (∑ j : Fin 3,
          ∫ x : Vec3,
            wordDeriv (α ++ [j]) (fun y => u y i) x *
              wordDeriv α (fun y => v y j * u y i) x) -
          ∫ x : Vec3,
            wordDeriv α (fun y => u y i) x *
              spatialDeriv (wordDeriv α p) i x := by
    let h : Vec3 → ℝ := wordDeriv α (fun y => u y i)
    let r : Vec3 → ℝ := wordDeriv α (fun y => q y i)
    let P : Vec3 → ℝ := wordDeriv α p
    let F : Fin 3 → Vec3 → ℝ :=
      fun j => wordDeriv α (fun y => v y j * u y i)
    have hH : ContDiff ℝ (⊤ : ℕ∞) h := contDiff_wordDeriv (hu i) α
    have hF (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (F j) :=
      contDiff_wordDeriv ((hv j).mul (hu i)) α
    have hH1 (j : Fin 3) : MemLp (spatialDeriv h j) 2 volume := by
      rw [← wordDeriv_append]
      exact huL2 i (α ++ [j])
    have hH2 (j : Fin 3) :
        MemLp (spatialDeriv (spatialDeriv h j) j) 2 volume := by
      rw [← wordDeriv_append, ← wordDeriv_append]
      exact huL2 i ((α ++ [j]) ++ [j])
    have hF0 (j : Fin 3) : MemLp (F j) 2 volume :=
      lps_smooth_product_all_word_memLp (hv j) (hu i)
        (hvL2 j) (huL2 i) α
    have hF1 (j : Fin 3) : MemLp (spatialDeriv (F j) j) 2 volume := by
      rw [← wordDeriv_append]
      exact lps_smooth_product_all_word_memLp (hv j) (hu i)
        (hvL2 j) (huL2 i) (α ++ [j])
    have hP1 : MemLp (spatialDeriv P i) 2 volume := by
      rw [← wordDeriv_append]
      exact hpL2 (α ++ [i])
    have hspatial := lps_spatial_energy_component i hH hF
      (huL2 i α) hH1 hH2 hF0 hF1 hP1 (hPDE i α hα)
    simpa only [h, r, P, F, ← wordDeriv_append] using hspatial
  have hpressure (α : List (Fin 3)) :
      (∑ i : Fin 3,
        ∫ x : Vec3,
          wordDeriv α (fun y => u y i) x *
            spatialDeriv (wordDeriv α p) i x) = 0 := by
    apply lps_wordDeriv_pressure_pairing_zero hu hp hdiv α
    · intro i
      exact huL2 i α
    · intro i
      rw [← wordDeriv_append]
      exact huL2 i (α ++ [i])
    · exact hpL2 α
    · intro i
      rw [← wordDeriv_append]
      exact hpL2 (α ++ [i])
  change (∑ i : Fin 3, ∑ α ∈ W,
    ∫ x : Vec3, wordDeriv α (fun y => u y i) x *
      wordDeriv α (fun y => q y i) x) +
    (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
      ∫ x : Vec3, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2) =
    ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
      ∫ x : Vec3, wordDeriv (α ++ [j]) (fun y => u y i) x *
        wordDeriv α (fun y => v y j * u y i) x
  have hsum :
      (∑ i : Fin 3, ∑ α ∈ W,
        ((∫ x : Vec3, wordDeriv α (fun y => u y i) x *
          wordDeriv α (fun y => q y i) x) +
          ∑ j : Fin 3,
            ∫ x : Vec3, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2)) =
      ∑ i : Fin 3, ∑ α ∈ W,
        ((∑ j : Fin 3,
          ∫ x : Vec3,
            wordDeriv (α ++ [j]) (fun y => u y i) x *
              wordDeriv α (fun y => v y j * u y i) x) -
          ∫ x : Vec3, wordDeriv α (fun y => u y i) x *
            spatialDeriv (wordDeriv α p) i x) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro α hα
    exact hcomponent i α hα
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have hpressum :
      (∑ i : Fin 3, ∑ α ∈ W,
        ∫ x : Vec3, wordDeriv α (fun y => u y i) x *
          spatialDeriv (wordDeriv α p) i x) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [hpressure]
    simp
  rw [hpressum, sub_zero] at hsum
  exact hsum

end ESS
