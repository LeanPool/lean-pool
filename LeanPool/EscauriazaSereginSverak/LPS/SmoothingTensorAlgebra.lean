/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevAlgebra

/-!
# Ordered Sobolev bound for the transport tensor

The scalar `H^m` algebra estimate applies componentwise to the
advecting-velocity tensor, with one constant independent of the
regularizing scale.
-/

public section

open CKN

open MeasureTheory Set
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- For `m ≥ 2`, the ordered `H^m` energy of `v ⊗ u` is bounded
by the product of the componentwise energies of `v` and `u`
(`eq:lps-Hm-energy`). -/
theorem lps_smooth_transport_tensor_normSq (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v u : Vec3 → Vec3),
      (∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j)) →
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) →
      (∀ (j : Fin 3) (α : List (Fin 3)), α.length ≤ m →
        MemLp (wordDeriv α (fun x => v x j)) 2 volume) →
      (∀ (i : Fin 3) (α : List (Fin 3)), α.length ≤ m →
        MemLp (wordDeriv α (fun x => u x i)) 2 volume) →
      (∀ (i j : Fin 3) (α : List (Fin 3)), α.length ≤ m →
        MemLp (wordDeriv α (fun x => v x j * u x i)) 2 volume) ∧
      (∑ i : Fin 3, ∑ j : Fin 3,
        sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x => v x j * u x i))) ≤
        C * (∑ j : Fin 3,
          sobolevNormSqOn m univ
            (fun α => wordDeriv α (fun x => v x j))) *
          (∑ i : Fin 3,
            sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x => u x i))) := by
  obtain ⟨C, hC, hproduct⟩ := lps_smooth_product_normSq m hm
  refine ⟨C, hC, ?_⟩
  intro v u hv hu hvL2 huL2
  have hpair (i j : Fin 3) :=
    hproduct (fun x => v x j) (fun x => u x i)
      (hv j) (hu i) (hvL2 j) (huL2 i)
  refine ⟨fun i j α hα => (hpair i j).1 α hα, ?_⟩
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
      sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => v x j * u x i))) ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          C * sobolevNormSqOn m univ
            (fun α => wordDeriv α (fun x => v x j)) *
              sobolevNormSqOn m univ
                (fun α => wordDeriv α (fun x => u x i)) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => (hpair i j).2
    _ = C * (∑ j : Fin 3,
          sobolevNormSqOn m univ
            (fun α => wordDeriv α (fun x => v x j))) *
          (∑ i : Fin 3,
            sobolevNormSqOn m univ
              (fun α => wordDeriv α (fun x => u x i))) := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]

end ESS
