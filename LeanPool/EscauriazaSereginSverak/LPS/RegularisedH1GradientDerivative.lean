/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1TimeContinuity

/-!
# The differentiated energy identity for the regularized velocity

The squared gradient norm `‖∇U_ε(t)‖₂²` of the regularized velocity is differentiable at every
positive
time, with derivative `-2‖∇²U_ε‖₂² + 2⟨(J_ε U_ε · ∇) U_ε, ΔU_ε⟩`. The pressure does not enter
(`eq:lps-uniform-H1`, `lem:lps-regularized-Hk-start`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- Minus the Laplacian of the regularized velocity. -/
@[expose] def lpsRegNegLap (i : Fin 3) (t : ℝ) : Vec3 → ℝ := fun x => -lpsRegLap ρ ε hε b hb i t x

/-- Minus the Laplacian of the regularized velocity is square integrable. -/
theorem lps_regR12_negLap_memLp {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) :
    MemLp (lpsRegNegLap ρ ε hε b hb i t) 2 volume :=
  (lps_regR12_lap_memLp ρ ε hε b hb t ht i).neg

/-- Minus the Laplacian of the regularized velocity is `L²`-continuous in time at positive times. -/
theorem lps_regR12_negLap_path_continuousAt {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    ContinuousAt (lpsPath (lpsRegNegLap ρ ε hε b hb i)
      (fun _ hs => lps_regR12_negLap_memLp ρ ε hε b hb hs i)) a := by
  have h : lpsPath (lpsRegNegLap ρ ε hε b hb i)
      (fun _ hs => lps_regR12_negLap_memLp ρ ε hε b hb hs i) = fun r =>
      -lpsPath (lpsRegLap ρ ε hε b hb i)
        (fun _ hs => lps_regR12_lap_memLp ρ ε hε b hb _ hs i) r :=
    funext fun r => lps_lpsPath_neg (fun t x => rfl) r
  rw [h]
  exact (lps_regR12_lap_path_continuousAt ρ ε hε b hb ha i).neg

/-- The `L²` path of the pressure-free momentum right-hand side (clamped at time zero). -/
@[expose] def lpsRegRPath (i : Fin 3) : ℝ → Lp ℝ 2 (volume : Measure Vec3) :=
  lpsPath (lpsRegR ρ ε hε b hb i) (fun _ hs => lps_regR12_R_memLp ρ ε hε b hb hs i)

/-- The `L²` path of minus the Laplacian of the regularized velocity (clamped at time zero). -/
@[expose] def lpsRegNegLapPath (i : Fin 3) : ℝ → Lp ℝ 2 (volume : Measure Vec3) :=
  lpsPath (lpsRegNegLap ρ ε hε b hb i) (fun _ hs => lps_regR12_negLap_memLp ρ ε hε b hb hs i)

/--
The pairing of the pressure-free right-hand side against `-Δ(U_ε(a) + U_ε(c))` equals that of
the full momentum right-hand side, because the pressure gradient is orthogonal to this
solenoidal field (`lem:lps-regularized-Hk-start`).
-/
theorem lps_regR12_inner_eq_Q_pairing {a c r : ℝ} (ha : 0 < a) (hc : 0 < c) (hr : 0 < r) :
    ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i r)
      (lpsRegNegLapPath ρ ε hε b hb i a + lpsRegNegLapPath ρ ε hε b hb i c) =
    ∑ i : Fin 3, ∫ x : Vec3, lpsRegQ ρ ε hε b hb (x, r) i *
      (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) := by
  have hW (i : Fin 3) : MemLp (fun x => -(spatialLaplacian
      (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
      spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) 2 volume :=
    ((lps_regR12_lap_memLp ρ ε hε b hb a ha.le i).add
      (lps_regR12_lap_memLp ρ ε hε b hb c hc.le i)).neg
  have hR (i : Fin 3) := lps_regR12_R_memLp ρ ε hε b hb hr.le i
  have hp (i : Fin 3) : MemLp (spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, r)) i) 2 volume :=
    lps_regR12Pressure_all_word_memLp_slice ρ ε hε b hb r hr [i]
  have hpz := lps_regR12_pressure_pairing_zero ρ ε hε b hb ha.le hc.le hr
  have e1 (i : Fin 3) :
      inner ℝ (lpsRegRPath ρ ε hε b hb i r)
        (lpsRegNegLapPath ρ ε hε b hb i a + lpsRegNegLapPath ρ ε hε b hb i c) =
      ∫ x, lpsRegR ρ ε hε b hb i r x * (-(spatialLaplacian
        (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) := by
    unfold lpsRegRPath lpsRegNegLapPath
    rw [inner_add_right, lps_inner_lpsPath, lps_inner_lpsPath, max_eq_left hr.le,
      max_eq_left ha.le, max_eq_left hc.le]
    have i1 : Integrable (fun x => lpsRegR ρ ε hε b hb i r x * lpsRegNegLap ρ ε hε b hb i a x)
      volume :=
      (hR i).integrable_mul (lps_regR12_negLap_memLp ρ ε hε b hb ha.le i)
    have i2 : Integrable (fun x => lpsRegR ρ ε hε b hb i r x * lpsRegNegLap ρ ε hε b hb i c x)
      volume :=
      (hR i).integrable_mul (lps_regR12_negLap_memLp ρ ε hε b hb hc.le i)
    rw [← integral_add i1 i2]
    congr 1; funext x
    simp only [lpsRegNegLap, lpsRegLap]
    ring
  have e2 (i : Fin 3) :
      ∫ x, lpsRegQ ρ ε hε b hb (x, r) i * (-(spatialLaplacian
        (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) =
      (∫ x, lpsRegR ρ ε hε b hb i r x * (-(spatialLaplacian
        (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) -
      ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, r)) i x * (-(spatialLaplacian
        (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x)) := by
    have j1 : Integrable (fun x => lpsRegR ρ ε hε b hb i r x * (-(spatialLaplacian
        (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) volume :=
      (hR i).integrable_mul (hW i)
    have j2 : Integrable (fun x => spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, r)) i x *
        (-(spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, a) i) x +
        spatialLaplacian (fun y => lpsRegU ρ ε hε b hb (y, c) i) x))) volume :=
      (hp i).integrable_mul (hW i)
    rw [← integral_sub j1 j2]
    congr 1; funext x
    rw [lps_regR12_Q_eq]
    simp only [lpsRegR, lpsRegLap]
    ring
  simp only [e1, e2]
  rw [Finset.sum_sub_distrib, hpz, sub_zero]

/--
The increment of the squared gradient norm of the regularized velocity between two positive
times, in either order, is the time integral of the paired pressure-free right-hand side
(`prop:lps-local-strong`).
-/
theorem lps_regR12_gradient_energy_increment_any {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntervalIntegrable (fun r => ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i r)
      (lpsRegNegLapPath ρ ε hε b hb i a + lpsRegNegLapPath ρ ε hε b hb i c)) volume a c ∧
    lpsRegGradEnergy ρ ε hε b hb c - lpsRegGradEnergy ρ ε hε b hb a =
      ∫ r in a..c, ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i r)
        (lpsRegNegLapPath ρ ε hε b hb i a + lpsRegNegLapPath ρ ε hε b hb i c) := by
  rcases le_total a c with hac | hca
  · obtain ⟨hint, hinc⟩ := lps_regR12_gradient_energy_increment ρ ε hε b hb ha hac
    refine ⟨?_, ?_⟩
    · refine hint.congr (fun r hr => ?_)
      have hr0 : 0 < r := by
        rcases Set.mem_uIoc.mp hr with h | h <;> linarith only [h.1, ha, hc]
      exact (lps_regR12_inner_eq_Q_pairing ρ ε hε b hb ha hc hr0).symm
    · rw [hinc]
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr0 : 0 < r := by
        rcases Set.mem_uIcc.mp hr with h | h <;> linarith only [h.1, ha, hc]
      exact (lps_regR12_inner_eq_Q_pairing ρ ε hε b hb ha hc hr0).symm
  · obtain ⟨hint, hinc⟩ := lps_regR12_gradient_energy_increment ρ ε hε b hb hc hca
    have hsym (r : ℝ) : ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i r)
        (lpsRegNegLapPath ρ ε hε b hb i a + lpsRegNegLapPath ρ ε hε b hb i c) =
        ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i r)
        (lpsRegNegLapPath ρ ε hε b hb i c + lpsRegNegLapPath ρ ε hε b hb i a) := by
      simp only [add_comm]
    simp only [hsym]
    refine ⟨?_, ?_⟩
    · refine hint.symm.congr (fun r hr => ?_)
      have hr0 : 0 < r := by
        rcases Set.mem_uIoc.mp hr with h | h <;> linarith only [h.1, ha, hc]
      exact (lps_regR12_inner_eq_Q_pairing ρ ε hε b hb hc ha hr0).symm
    · rw [intervalIntegral.integral_symm, ← neg_sub, hinc]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr0 : 0 < r := by
        rcases Set.mem_uIcc.mp hr with h | h <;> linarith only [h.1, ha, hc]
      exact (lps_regR12_inner_eq_Q_pairing ρ ε hε b hb hc ha hr0).symm

/--
The squared gradient norm of the regularized velocity is differentiable at every positive time,
with derivative twice the pairing of the pressure-free right-hand side against `-ΔU_ε`
(`eq:lps-uniform-H1`).
-/
theorem lps_regR12_gradient_energy_hasDerivAt {a : ℝ} (ha : 0 < a) :
    HasDerivAt (lpsRegGradEnergy ρ ε hε b hb)
      (2 * ∑ i : Fin 3, ∫ x : Vec3, lpsRegR ρ ε hε b hb i a x *
        (-lpsRegLap ρ ε hε b hb i a x)) a := by
  have h := lps_hasDerivAt_of_pair_increment (φ := lpsRegGradEnergy ρ ε hε b hb)
    (R := fun i => lpsRegRPath ρ ε hε b hb i) (Θ := fun i => lpsRegNegLapPath ρ ε hε b hb i)
    (a := a) (fun i => lps_regR12_R_path_continuousAt ρ ε hε b hb ha i)
    (fun i => lps_regR12_negLap_path_continuousAt ρ ε hε b hb ha i)
    (by
      filter_upwards [lt_mem_nhds ha] with c hc
      exact lps_regR12_gradient_energy_increment_any ρ ε hε b hb ha hc)
  have e : (∑ i : Fin 3, ∫ x : Vec3, lpsRegR ρ ε hε b hb i a x *
        (-lpsRegLap ρ ε hε b hb i a x)) =
      ∑ i : Fin 3, inner ℝ (lpsRegRPath ρ ε hε b hb i a) (lpsRegNegLapPath ρ ε hε b hb i a) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold lpsRegRPath lpsRegNegLapPath
    rw [lps_inner_lpsPath, max_eq_left ha.le]
    rfl
  rw [e]
  exact h

end

/--
The squared `L²` norm of the second spatial derivatives of the regularized velocity at time `t`.
-/
@[expose] def lpsRegHessEnergy (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    ∫ x : Vec3, spatialDeriv (spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j) k x ^ 2

/-- The pairing of the transport term with the Laplacian of the regularized velocity. -/
@[expose] def lpsRegTransportPairing (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : CKN.IsInJ b) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ x : Vec3, lpsRegTransport ρ ε hε b hb i t x * lpsRegLap ρ ε hε b hb i t x

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/--
The squared `L²` norm of the Laplacian of the regularized velocity is the squared `L²` norm of
its second derivatives.
-/
theorem lps_regR12_lap_sq_eq_hess {t : ℝ} (ht : 0 ≤ t) :
    (∑ i : Fin 3, ∫ x : Vec3, lpsRegLap ρ ε hε b hb i t x ^ 2) =
      lpsRegHessEnergy ρ ε hε b hb t := by
  unfold lpsRegHessEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lps_laplacian_sq_eq_hessian_sq (lps_regR12_slice_smooth ρ ε hε b hb t ht i)
    (fun α _ => lps_regR12_slice_memLp ρ ε hε b hb t ht i α)

/--
The derivative of the squared gradient norm of the regularized velocity is `-2‖∇²U_ε‖₂² + 2⟨(J_ε
U_ε · ∇) U_ε, ΔU_ε⟩` (`eq:lps-uniform-H1`).
-/
theorem lps_regR12_gradient_energy_deriv_eq {t : ℝ} (ht : 0 ≤ t) :
    2 * ∑ i : Fin 3, ∫ x : Vec3, lpsRegR ρ ε hε b hb i t x * (-lpsRegLap ρ ε hε b hb i t x) =
      -2 * lpsRegHessEnergy ρ ε hε b hb t + 2 * lpsRegTransportPairing ρ ε hε b hb t := by
  rw [← lps_regR12_lap_sq_eq_hess ρ ε hε b hb ht]
  unfold lpsRegTransportPairing
  have h (i : Fin 3) :
      ∫ x : Vec3, lpsRegR ρ ε hε b hb i t x * (-lpsRegLap ρ ε hε b hb i t x) =
        -(∫ x : Vec3, lpsRegLap ρ ε hε b hb i t x ^ 2) +
          ∫ x : Vec3, lpsRegTransport ρ ε hε b hb i t x * lpsRegLap ρ ε hε b hb i t x := by
    have i1 : Integrable (fun x => lpsRegLap ρ ε hε b hb i t x ^ 2) volume :=
      (lps_regR12_lap_memLp ρ ε hε b hb t ht i).integrable_sq
    have i2 : Integrable (fun x => lpsRegTransport ρ ε hε b hb i t x *
        lpsRegLap ρ ε hε b hb i t x) volume :=
      (lps_regR12_transport_memLp ρ ε hε b hb ht i).integrable_mul
        (lps_regR12_lap_memLp ρ ε hε b hb t ht i)
    have i1' : Integrable (fun x => -(lpsRegLap ρ ε hε b hb i t x ^ 2)) volume := i1.neg
    rw [← integral_neg, ← integral_add i1' i2]
    congr 1; funext x
    simp only [lpsRegR]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end

end ESS.LPS
