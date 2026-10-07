/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedMomentum
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedEnergy
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierPhysical
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSolenoidalPhysical

/-!
# Ordered energy of a regularized velocity slice

The physical mollifier, pointwise solenoidality, and divergence form
identify every spatial term of the high-order regularized energy
identity. The time-chain identity is supplied by its `L²` trajectory.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The actual regularized momentum right-hand side satisfies the exact
ordered energy identity once its `L²` time-chain identity is known
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_regR12_ordered_energy_identity_of_time_chain
    (m : ℕ) (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (t E' : ℝ)
    (hJ : IsInJ (fun x : Vec3 => u (x, t)))
    (hu : ∀ i : Fin 3,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i))
    (hp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => p (x, t)))
    (huL2 : ∀ (i : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume)
    (hpL2 : ∀ α : List (Fin 3),
      MemLp (wordDeriv α (fun x : Vec3 => p (x, t))) 2 volume)
    (hchain : E' = 2 *
      (∑ i : Fin 3, ∑ α ∈ sobolevWords m,
        ∫ x : Vec3,
          wordDeriv α (fun y => u (y, t) i) x *
            wordDeriv α (fun y : Vec3 =>
              CKN.Leray.regR12TimeRHS ρ ε hε u p (y, t) i) x)) :
    E' + 2 *
      (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u (y, t) i) x ^ 2) =
      2 * (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
        ∫ x : Vec3,
          wordDeriv (α ++ [j]) (fun y => u (y, t) i) x *
            wordDeriv α (fun y : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (y, t) j *
                u (y, t) i) x) := by
  let U : Vec3 → Vec3 := fun x => u (x, t)
  let V : Vec3 → Vec3 := fun x =>
    CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t)
  let Q : Vec3 → Vec3 := fun x i =>
    CKN.Leray.regR12TimeRHS ρ ε hε u p (x, t) i
  let P : Vec3 → ℝ := fun x => p (x, t)
  have hvData := lps_regUniformMollifiedVelocity_smooth_memLp
    ρ ε hε u t hJ.1 hu huL2
  have hdiv : ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => U y i) i x = 0 :=
    lps_smooth_isInJ_solenoidal hJ hu
  have hPDE (i : Fin 3) (x : Vec3) :
      Q x i =
        (∑ j : Fin 3,
          spatialDeriv (spatialDeriv (fun y => U y i) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv (fun y => V y j * U y i) j x) -
          spatialDeriv P i x :=
    lps_regR12TimeRHS_divergence ρ ε hε u p t hJ hu x i
  exact lps_regularized_ordered_energy_identity m U V Q P E'
    hu hvData.1 hp huL2 hvData.2 hpL2 hdiv hPDE hchain

/-- The regularized momentum equation obeys the corrected high-order
energy inequality with a constant independent of the mollifier scale,
provided its `L²` time-chain identity holds (`eq:lps-Hm-energy`). -/
theorem lps_regR12_corrected_energy_of_time_chain
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
        (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
        (t E' : ℝ),
        IsInJ (fun x : Vec3 => u (x, t)) →
        (∀ i : Fin 3,
          ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) i)) →
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => p (x, t)) →
        (∀ (i : Fin 3) (α : List (Fin 3)),
          MemLp (wordDeriv α (fun x : Vec3 => u (x, t) i)) 2 volume) →
        (∀ α : List (Fin 3),
          MemLp (wordDeriv α (fun x : Vec3 => p (x, t))) 2 volume) →
        E' = 2 *
          (∑ i : Fin 3, ∑ α ∈ sobolevWords m,
            ∫ x : Vec3,
              wordDeriv α (fun y => u (y, t) i) x *
                wordDeriv α (fun y : Vec3 =>
                  CKN.Leray.regR12TimeRHS ρ ε hε u p (y, t) i) x) →
        E' +
          (∑ i : Fin 3, ∑ α ∈ sobolevWords m, ∑ j : Fin 3,
            ∫ x : Vec3,
              wordDeriv (α ++ [j]) (fun y => u (y, t) i) x ^ 2) ≤
          C * (∑ i : Fin 3, sobolevNormSqOn m univ
            (fun α => wordDeriv α (fun x : Vec3 => u (x, t) i))) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := lps_corrected_ordered_energy_of_identity m hm
  refine ⟨C, hC, ?_⟩
  intro ρ ε hε u p t E' hJ hu hp huL2 hpL2 hchain
  have hidentity := lps_regR12_ordered_energy_identity_of_time_chain
    m ρ ε hε u p t E' hJ hu hp huL2 hpL2 hchain
  exact hbound ρ ε hε u t E' hJ hu huL2 hidentity

end ESS
