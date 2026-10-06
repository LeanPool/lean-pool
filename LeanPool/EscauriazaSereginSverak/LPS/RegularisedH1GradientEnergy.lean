/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Calculus
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1IBP
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Increment
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedActualRHS
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedSmooth
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressurePairing
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSolenoidalPhysical
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSolenoidalWords
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierPhysical

/-!
# Increment of the regularized gradient energy

For the regularized velocity `U_ε` of `thm:regularised` of the CKN manuscript, the increment of `‖∇U_ε‖₂²` over a positive
time interval is the time integral of the pairing of the momentum right-hand side against
`-Δ(U_ε(a) + U_ε(c))`, and the pressure part of this pairing vanishes
(`lem:lps-regularized-Hk-start`, `prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The regularized velocity of `thm:regularised` of the CKN manuscript for the datum `b`. -/
@[expose] abbrev lpsRegU (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) : ParabolicPoint → Vec3 :=
  CKN.Leray.regR12Velocity ρ ε hε b hb

/-- The canonical regularized pressure of `thm:regularised` of the CKN manuscript. -/
@[expose] abbrev lpsRegP (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) : ParabolicPoint → ℝ :=
  CKN.Leray.forcedQuadPressure ρ ε hε (CKN.Leray.regR12Curve ρ ε hε b hb)

/-- The mollified transport velocity `J_ε U_ε`. -/
@[expose] abbrev lpsRegV (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) : ParabolicPoint → Vec3 :=
  CKN.Leray.regUniformMollifiedVelocity ρ ε hε (lpsRegU ρ ε hε b hb)

/-- The time derivative field of the regularized velocity. -/
@[expose] abbrev lpsRegQ (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) : ParabolicPoint → Vec3 :=
  fun z i => CKN.Leray.regR12TimeRHS ρ ε hε (lpsRegU ρ ε hε b hb) (lpsRegP ρ ε hε b hb) z i

/-- The squared `L²` norm of the spatial gradient of the regularized velocity at time `t`. -/
@[expose] def lpsRegGradEnergy (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ x : Vec3, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2

section slice

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- Every nonnegative-time slice of the regularized velocity is smooth. -/
theorem lps_regR12_slice_smooth (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, t) i) :=
  lps_regR12Velocity_slice_contDiff ρ ε hε b hb t ht i

/-- Every ordered spatial derivative of a nonnegative-time slice of the regularized velocity is square integrable. -/
theorem lps_regR12_slice_memLp (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x : Vec3 => lpsRegU ρ ε hε b hb (x, t) i)) 2 volume :=
  lps_regR12Velocity_all_word_memLp_slice ρ ε hε b hb t ht i α

/-- Change of the squared gradient norm of one velocity component between two times, as a pairing against minus the Laplacian of the sum. -/
theorem lps_regR12_gradient_energy_difference (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (i : Fin 3) :
    (∫ x : Vec3, (lpsRegU ρ ε hε b hb (x, c) i - lpsRegU ρ ε hε b hb (x, a) i) *
      (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) =
      (∑ j : Fin 3, ∫ x : Vec3, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, c) i) j x ^ 2) -
        ∑ j : Fin 3, ∫ x : Vec3, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, a) i) j x ^ 2 :=
  lps_gradient_energy_difference (lps_regR12_slice_smooth ρ ε hε b hb a ha i)
    (lps_regR12_slice_smooth ρ ε hε b hb c hc i)
    (lps_regR12_slice_memLp ρ ε hε b hb a ha i [])
    (fun j => lps_regR12_slice_memLp ρ ε hε b hb a ha i [j])
    (fun j => lps_regR12_slice_memLp ρ ε hε b hb a ha i [j, j])
    (lps_regR12_slice_memLp ρ ε hε b hb c hc i [])
    (fun j => lps_regR12_slice_memLp ρ ε hε b hb c hc i [j])
    (fun j => lps_regR12_slice_memLp ρ ε hε b hb c hc i [j, j])

/-- The Laplacian of every regularized velocity component slice is square integrable. -/
theorem lps_regR12_lap_memLp (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, t) i)) 2 volume := by
  unfold spatialLaplacian
  exact memLp_finsetSum _ fun j _ => lps_regR12_slice_memLp ρ ε hε b hb t ht i [j, j]

/-- The increment of the squared gradient norm of the regularized velocity between positive times is the time integral of the pairing of the momentum right-hand side against minus the Laplacian of the sum (`prop:lps-local-strong`). -/
theorem lps_regR12_gradient_energy_increment {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    IntervalIntegrable (fun r => ∑ i : Fin 3, ∫ x : Vec3, lpsRegQ ρ ε hε b hb (x, r) i *
      (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) volume a c ∧
    lpsRegGradEnergy ρ ε hε b hb c - lpsRegGradEnergy ρ ε hε b hb a =
      ∫ r in a..c, ∑ i : Fin 3, ∫ x : Vec3, lpsRegQ ρ ε hε b hb (x, r) i *
        (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
          spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) := by
  have hc0 : 0 ≤ c := ha.le.trans hac
  have hW (i : Fin 3) : MemLp (fun x => -(spatialLaplacian
      (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
      spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) 2 volume :=
    ((lps_regR12_lap_memLp ρ ε hε b hb a ha.le i).add
      (lps_regR12_lap_memLp ρ ε hε b hb c hc0 i)).neg
  have hinc (i : Fin 3) := lps_regR12_time_pairing_increment ρ ε hε b hb ha hac _ (hW i) i
  refine ⟨?_, ?_⟩
  · exact IntervalIntegrable.sum (Finset.univ : Finset (Fin 3)) (fun i _ => (hinc i).1)
  · rw [intervalIntegral.integral_finsetSum (fun i _ => (hinc i).1)]
    unfold lpsRegGradEnergy
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← lps_regR12_gradient_energy_difference ρ ε hε b hb a c ha.le hc0 i]
    rw [← (hinc i).2]
    have hm (s : ℝ) (hs : 0 ≤ s) : Integrable (fun x => lpsRegU ρ ε hε b hb (x, s) i *
        (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
          spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) volume :=
      (lps_regR12_slice_memLp ρ ε hε b hb s hs i []).integrable_mul (hW i)
    rw [← integral_sub (hm c hc0) (hm a ha.le)]
    congr 1; funext x; ring

end slice

/-- The transport term `(J_ε U · ∇) U_i` of the regularized velocity at time `t`. -/
@[expose] def lpsRegTransport (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) (i : Fin 3) (t : ℝ) : Vec3 → ℝ :=
  fun x => ∑ k : Fin 3, lpsRegV ρ ε hε b hb (x, t) k *
    spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x

/-- The momentum right-hand side is the Laplacian minus the transport term minus the pressure gradient. -/
theorem lps_regR12_Q_eq (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) (x : Vec3) (t : ℝ) (i : Fin 3) :
    lpsRegQ ρ ε hε b hb (x, t) i =
      spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, t) i) x -
        lpsRegTransport ρ ε hε b hb i t x -
        spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x := rfl

section slice2

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- A derivative of the negative of a sum of smooth functions. -/
theorem lps_spatialDeriv_neg_add {f g : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun x => -(f x + g x)) i x = -(spatialDeriv f i x + spatialDeriv g i x) := by
  have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  simp only [spatialDeriv]
  rw [fderiv_fun_neg, fderiv_fun_add hfd hgd]
  simp

/-- The pressure gradient pairs to zero with the solenoidal field `-Δ(U_ε(a) + U_ε(c))` (`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_pressure_pairing_zero {a c r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hr : 0 < r) :
    ∑ i : Fin 3, ∫ x : Vec3, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, r)) i x *
      (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) = 0 := by
  let W : Vec3 → Vec3 := fun x i => -(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)
  have hsa := lps_regR12_slice_smooth ρ ε hε b hb a ha
  have hsc := lps_regR12_slice_smooth ρ ε hε b hb c hc
  have hLa (i : Fin 3) := lps_spatialLaplacian_contDiff (hsa i)
  have hLc (i : Fin 3) := lps_spatialLaplacian_contDiff (hsc i)
  have hL2a (i : Fin 3) (α : List (Fin 3)) (_ : α.length ≤ 3) :=
    lps_regR12_slice_memLp ρ ε hε b hb a ha i α
  have hL2c (i : Fin 3) (α : List (Fin 3)) (_ : α.length ≤ 3) :=
    lps_regR12_slice_memLp ρ ε hε b hb c hc i α
  have hpz := lps_solenoidal_pressure_pairing_zero (h := W)
    (p := fun x => lpsRegP ρ ε hε b hb (x, r))
    (fun i => ((hLa i).add (hLc i)).neg)
    (lps_regR12Pressure_slice_contDiff ρ ε hε b hb r hr)
    (fun i => ((lps_regR12_lap_memLp ρ ε hε b hb a ha i).add
      (lps_regR12_lap_memLp ρ ε hε b hb c hc i)).neg)
    (fun i => by
      have h1 := lps_spatialDeriv_spatialLaplacian_memLp (hsa i) (hL2a i) i
      have h2 := lps_spatialDeriv_spatialLaplacian_memLp (hsc i) (hL2c i) i
      have e : spatialDeriv (fun x => W x i) i =
          -(spatialDeriv (spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i)) i +
            spatialDeriv (spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i)) i) := by
        funext x
        exact lps_spatialDeriv_neg_add (lps_spatialLaplacian_contDiff (hsa i))
          (lps_spatialLaplacian_contDiff (hsc i)) i x
      rw [e]
      exact (h1.add h2).neg)
    (lps_regR12Pressure_all_word_memLp_slice ρ ε hε b hb r hr [])
    (fun i => lps_regR12Pressure_all_word_memLp_slice ρ ε hε b hb r hr [i])
    (fun x => by
      have hda := lps_spatialLaplacian_solenoidal (u := fun y => lpsRegU ρ ε hε b hb (y, a))
        hsa (lps_smooth_isInJ_solenoidal (lps_regR12Velocity_slice_isInJ ρ ε hε b hb a ha) hsa) x
      have hdc := lps_spatialLaplacian_solenoidal (u := fun y => lpsRegU ρ ε hε b hb (y, c))
        hsc (lps_smooth_isInJ_solenoidal (lps_regR12Velocity_slice_isInJ ρ ε hε b hb c hc) hsc) x
      have e : ∀ i : Fin 3, spatialDeriv (fun x => W x i) i x =
          -(spatialDeriv (spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i)) i x +
            spatialDeriv (spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i)) i x) := fun i =>
        lps_spatialDeriv_neg_add (lps_spatialLaplacian_contDiff (hsa i))
          (lps_spatialLaplacian_contDiff (hsc i)) i x
      simp only [e, Finset.sum_neg_distrib, Finset.sum_add_distrib, hda, hdc]
      simp)
  simpa only [mul_comm] using hpz

end slice2

end ESS.LPS

end
