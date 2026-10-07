/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedEquationWords
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductAll
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedMomentum
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierPhysical

/-!
# Square-integrability of ordered regularized momentum derivatives

Every ordered spatial derivative of the regularized momentum right-hand
side belongs to spatial `L²` when the velocity and canonical pressure
have square-integrable derivatives of all orders.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The differentiated heat, tensor-divergence and pressure terms are
square-integrable at every ordered spatial word
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_regularized_equation_all_word_memLp
    (u v q : Vec3 → Vec3) (p : Vec3 → ℝ)
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x => u x i)) 2 volume)
    (hvL2 : ∀ (j : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x => v x j)) 2 volume)
    (hpL2 : ∀ α : List (Fin 3), MemLp (wordDeriv α p) 2 volume)
    (hPDE : ∀ (i : Fin 3) (x : Vec3),
      q x i =
        (∑ j : Fin 3,
          spatialDeriv (spatialDeriv (fun y => u y i) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv (fun y => v y j * u y i) j x) -
        spatialDeriv p i x)
    (i : Fin 3) (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x => q x i)) 2 volume := by
  have hheat (j : Fin 3) : MemLp
      (spatialDeriv
        (spatialDeriv (wordDeriv α (fun y => u y i)) j) j) 2 volume := by
    rw [← wordDeriv_append, ← wordDeriv_append]
    exact huL2 i ((α ++ [j]) ++ [j])
  have hflux (j : Fin 3) : MemLp
      (spatialDeriv (wordDeriv α (fun y => v y j * u y i)) j) 2 volume := by
    rw [← wordDeriv_append]
    exact lps_smooth_product_all_word_memLp (hv j) (hu i)
      (hvL2 j) (huL2 i) (α ++ [j])
  have hpressure : MemLp (spatialDeriv (wordDeriv α p) i) 2 volume := by
    rw [← wordDeriv_append]
    exact hpL2 (α ++ [i])
  have hright : MemLp
      (fun x : Vec3 =>
        (∑ j : Fin 3,
          spatialDeriv
            (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv
            (wordDeriv α (fun y => v y j * u y i)) j x) -
        spatialDeriv (wordDeriv α p) i x) 2 volume :=
    ((memLp_finsetSum Finset.univ (fun j _ => hheat j)).sub
      (memLp_finsetSum Finset.univ (fun j _ => hflux j))).sub hpressure
  have heq : (fun x : Vec3 => wordDeriv α (fun y => q y i) x) =
      fun x : Vec3 =>
        (∑ j : Fin 3,
          spatialDeriv
            (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv
            (wordDeriv α (fun y => v y j * u y i)) j x) -
        spatialDeriv (wordDeriv α p) i x := by
    funext x
    exact lps_regularized_equation_wordDeriv u v q p hu hv hp hPDE i α x
  change MemLp (fun x : Vec3 => wordDeriv α (fun y => q y i) x) 2 volume
  rw [heq]
  exact hright

/-- On a smooth regularized slice, every ordered spatial derivative of
the actual momentum right-hand side belongs to spatial `L²`
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_regR12TimeRHS_all_word_memLp
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (t : ℝ)
    (hJ : IsInJ (fun x : Vec3 => u (x, t)))
    (hu : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => p (x, t)))
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume)
    (hpL2 : ∀ α : List (Fin 3),
      MemLp (wordDeriv α (fun x : Vec3 => p (x, t))) 2 volume)
    (i : Fin 3) (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12TimeRHS ρ ε hε u p (x, t) i)) 2 volume := by
  let U : Vec3 → Vec3 := fun x => u (x, t)
  let V : Vec3 → Vec3 := fun x =>
    CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t)
  let Q : Vec3 → Vec3 := fun x i =>
    CKN.Leray.regR12TimeRHS ρ ε hε u p (x, t) i
  let P : Vec3 → ℝ := fun x => p (x, t)
  have hvData := lps_regUniformMollifiedVelocity_smooth_memLp
    ρ ε hε u t hJ.1 hu huL2
  have hPDE (j : Fin 3) (x : Vec3) :
      Q x j =
        (∑ k : Fin 3,
          spatialDeriv (spatialDeriv (fun y => U y j) k) k x) -
        (∑ k : Fin 3,
          spatialDeriv (fun y => V y k * U y j) k x) -
        spatialDeriv P j x :=
    lps_regR12TimeRHS_divergence ρ ε hε u p t hJ hu x j
  exact lps_regularized_equation_all_word_memLp U V Q P
    hu hvData.1 hp huL2 hvData.2 hpL2 hPDE i α

end ESS
