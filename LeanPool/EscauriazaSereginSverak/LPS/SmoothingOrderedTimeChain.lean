/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHilbertChain
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall

/-!
# Ordered Sobolev energy time chain

Differentiable `L²` trajectories for the finitely many ordered
derivatives produce the exact time derivative of the `H^m` energy.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Differentiable `L²` curves of every ordered derivative imply the
time-chain identity in `eq:lps-regularized-Hm-identity`. -/
theorem lps_ordered_energy_time_chain
    (m : ℕ) (u q : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ∀ (s : ℝ) (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => u (x, s) i)) 2 volume)
    (hq : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => q (x, t) i)) 2 volume)
    (hcurve : ∀ (i : Fin 3) (α : List (Fin 3)), α ∈ sobolevWords m →
      HasDerivAt
        (fun s : ℝ => (hu s i α).toLp
          (wordDeriv α (fun x : Vec3 => u (x, s) i)))
        ((hq i α).toLp (wordDeriv α (fun x : Vec3 => q (x, t) i))) t) :
    HasDerivAt
      (fun s : ℝ => ∑ i : Fin 3, ∑ α ∈ sobolevWords m,
        ∫ x : Vec3, wordDeriv α (fun y => u (y, s) i) x ^ 2)
      (2 * (∑ i : Fin 3, ∑ α ∈ sobolevWords m,
        ∫ x : Vec3,
          wordDeriv α (fun y => u (y, t) i) x *
            wordDeriv α (fun y => q (y, t) i) x)) t := by
  let W := sobolevWords m
  let F : Fin 3 → List (Fin 3) → ℝ → Lp ℝ 2 volume :=
    fun i α s => (hu s i α).toLp
      (wordDeriv α (fun x : Vec3 => u (x, s) i))
  let G : Fin 3 → List (Fin 3) → Lp ℝ 2 volume :=
    fun i α => (hq i α).toLp
      (wordDeriv α (fun x : Vec3 => q (x, t) i))
  have hword (i : Fin 3) (α : List (Fin 3)) (hα : α ∈ W) :
      HasDerivAt (fun s => ‖F i α s‖ ^ 2)
        (2 * inner ℝ (F i α t) (G i α)) t :=
    (hcurve i α hα).norm_sq
  have hinner (i : Fin 3) :
      HasDerivAt (fun s => ∑ α ∈ W, ‖F i α s‖ ^ 2)
        (∑ α ∈ W, 2 * inner ℝ (F i α t) (G i α)) t :=
    HasDerivAt.fun_sum (u := W) (fun α hα => hword i α hα)
  have htotal : HasDerivAt
      (fun s => ∑ i : Fin 3, ∑ α ∈ W, ‖F i α s‖ ^ 2)
      (∑ i : Fin 3, ∑ α ∈ W, 2 * inner ℝ (F i α t) (G i α)) t :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hinner i)
  have henergy (s : ℝ) :
      (∑ i : Fin 3, ∑ α ∈ W, ‖F i α s‖ ^ 2) =
      ∑ i : Fin 3, ∑ α ∈ W,
        ∫ x : Vec3, wordDeriv α (fun y => u (y, s) i) x ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro α _
    exact lps_scalar_l2_toLp_norm_sq_integral (hu s i α)
  have hpair :
      (∑ i : Fin 3, ∑ α ∈ W,
        2 * inner ℝ (F i α t) (G i α)) =
      2 * (∑ i : Fin 3, ∑ α ∈ W,
        ∫ x : Vec3,
          wordDeriv α (fun y => u (y, t) i) x *
            wordDeriv α (fun y => q (y, t) i) x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [lps_scalar_l2_toLp_inner_integral (hu t i α) (hq i α)]
  convert htotal using 1
  · funext s
    exact (henergy s).symm
  · exact hpair.symm

end ESS
