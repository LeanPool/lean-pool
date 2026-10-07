/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct

/-!
# Solenoidal ordered derivatives

Every ordered spatial derivative of a smooth divergence-free field is
divergence free. This permits the pressure cancellation in
`eq:lps-regularized-Hm-identity` at every Sobolev order.
-/

public section

open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_wordDeriv_zero (α : List (Fin 3)) :
    wordDeriv α (fun _ : Vec3 => (0 : ℝ)) = fun _ => 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
      change wordDeriv α (spatialDeriv (fun _ : Vec3 => (0 : ℝ)) j) = _
      have hz : spatialDeriv (fun _ : Vec3 => (0 : ℝ)) j = fun _ => 0 := by
        funext x
        simp [spatialDeriv]
      rw [hz, ih]

/-- Ordered spatial derivatives preserve classical solenoidality
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_wordDeriv_solenoidal
    {u : Vec3 → Vec3}
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => u y i) i x = 0)
    (α : List (Fin 3)) (x : Vec3) :
    ∑ i : Fin 3,
      spatialDeriv (wordDeriv α (fun y => u y i)) i x = 0 := by
  have hsmooth (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (fun y => u y i) i) :=
    contDiff_wordDeriv (hu i) [i]
  have hsum := congrFun (localDivCurlSmooth_wordDeriv_sum α hsmooth) x
  have hdivFun : (fun y : Vec3 =>
      ∑ i : Fin 3, spatialDeriv (fun z => u z i) i y) =
        (fun _ => (0 : ℝ)) := by
    funext y
    exact hdiv y
  rw [hdivFun, lps_wordDeriv_zero] at hsum
  have hcomm (i : Fin 3) :
      wordDeriv α (spatialDeriv (fun y => u y i) i) x =
        spatialDeriv (wordDeriv α (fun y => u y i)) i x := by
    exact congrFun (localDivCurlSmooth_wordDeriv_spatialDeriv (hu i) α i) x
  simpa only [hcomm] using hsum.symm

end ESS
