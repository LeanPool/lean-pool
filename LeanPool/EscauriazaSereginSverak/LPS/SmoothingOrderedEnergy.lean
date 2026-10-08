/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportRegularized
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEnergyScalar

/-!
# Corrected ordered energy inequality

The scale-independent transport estimate and the exact regularized
energy identity imply the corrected high-order differential inequality.
The identity is supplied by differentiating the regularized projected
equation; its heat and pressure pairings are handled separately.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The exact regularized energy identity yields the corrected
`H^m` differential inequality once the transport tensor is bounded
(`eq:lps-Hm-energy`). -/
theorem lps_corrected_ordered_energy_of_identity (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
        (u : ParabolicPoint → Vec3) (t : ℝ) (E' : ℝ),
        IsInJ (fun x : Vec3 => u (x, t)) →
        (∀ i : Fin 3,
          ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i)) →
        (∀ (i : Fin 3) (α : List (Fin 3)),
          MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume) →
        let W := sobolevWords m
        let N := ∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x : Vec3 => u (x, t) i))
        let D := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
          ∫ x, wordDeriv (α ++ [j]) (fun y : Vec3 => u (y, t) i) x ^ 2
        let K := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
          ∫ x,
            wordDeriv (α ++ [j]) (fun y : Vec3 => u (y, t) i) x *
            wordDeriv α (fun y : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (y, t) j *
                u (y, t) i) x
        E' + 2 * D = 2 * K →
          E' + D ≤ C * N ^ 2 := by
  obtain ⟨C, hC, htransport⟩ := lps_regularized_transport_pairing_bound m hm
  refine ⟨C, hC, ?_⟩
  intro ρ ε hε u t E' hJ huSmooth huL2 W N D K hidentity
  have hD : 0 ≤ D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro α _
    apply Finset.sum_nonneg
    intro j _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hN : 0 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro α _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hK : K ≤ Real.sqrt C * N * Real.sqrt D :=
    htransport ρ ε hε u t hJ huSmooth huL2
  exact lps_corrected_energy_from_tensor hD hN hC
    (le_of_eq hidentity) hK

end ESS
