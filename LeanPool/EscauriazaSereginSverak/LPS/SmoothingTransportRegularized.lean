/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierPhysical

/-!
# Scale-independent regularized transport pairing

The differentiated tensor of the actual regularized transport field
has an energy pairing bounded by its unmollified velocity's ordered
Sobolev energy and gradient dissipation. The constant depends only on
the order, not on the mollifier profile or scale.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The high-order transport pairing of the regularized equation has
a mollifier-independent bound (`eq:lps-Hm-energy`). -/
theorem lps_regularized_transport_pairing_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
        (u : ParabolicPoint → Vec3) (t : ℝ),
        IsInJ (fun x : Vec3 => u (x, t)) →
        (∀ i : Fin 3,
          ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i)) →
        (∀ (i : Fin 3) (α : List (Fin 3)),
          MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume) →
        let W := sobolevWords m
        let Nu := ∑ i : Fin 3, sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x : Vec3 => u (x, t) i))
        let D := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
          ∫ x, wordDeriv (α ++ [j]) (fun y : Vec3 => u (y, t) i) x ^ 2
        (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
          ∫ x,
            wordDeriv (α ++ [j]) (fun y : Vec3 => u (y, t) i) x *
            wordDeriv α (fun y : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (y, t) j *
                u (y, t) i) x) ≤
          Real.sqrt C * Nu * Real.sqrt D := by
  obtain ⟨C, hC, hbound⟩ := lps_ordered_transport_pairing_contractive m hm
  refine ⟨C, hC, ?_⟩
  intro ρ ε hε u t hJ huSmooth huL2 W Nu D
  let v : Vec3 → Vec3 := fun x =>
    CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t)
  have hvm := lps_regUniformMollifiedVelocity_smooth_memLp
    ρ ε hε u t hJ.1 huSmooth huL2
  have hcontract := lps_regUniformMollifiedVelocity_sobolevNormSq_le
    ρ ε hε u t hJ.1 huSmooth huL2 m
  exact hbound v (fun x : Vec3 => u (x, t))
    hvm.1 huSmooth
    (fun j α _ => hvm.2 j α)
    (fun i α _ => huL2 i α)
    hcontract

end ESS
