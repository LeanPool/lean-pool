/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegTransport
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Increment
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedMomentum

/-!
# The time derivative of the regularized velocity on a time slice

At a positive time the regularized momentum right-hand side is the Laplacian minus the transport
term minus the pressure gradient. The pressure gradient is bounded by the transport term in `L²`
(`lem:lps-regularized-Hk-start`, the pressure equation), so the time derivative has `L²` norm squared
at most `3 ‖∇²U_ε‖² + C ‖∇U_ε‖₂³ ‖∇²U_ε‖₂` on each slice.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The weak form of the pressure equation of the regularized solution at a positive time
(`thm:regularised` of the CKN manuscript, (R4)). -/
theorem lps_regR12_pressure_weak {t : ℝ} (ht : 0 < t) (ψ : Vec3 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, lpsRegP ρ ε hε b hb (x, t) * spatialLaplacian ψ x) =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (lpsRegV ρ ε hε b hb (x, t) i *
        lpsRegU ρ ε hε b hb (x, t) j) * mixedSecond ψ i j x := by
  have h := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hP, -⟩ := h
  obtain ⟨-, -, hw⟩ := hP t ht
  exact hw ψ hψ hψc

/-- The pressure gradient of the regularized solution is bounded in `L²` by the transport term
(`thm:regularised` of the CKN manuscript, (R4)). -/
theorem lps_regR12_pressure_gradient_sq_le {t : ℝ} (ht : 0 < t) :
    (∑ i : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) ≤
      ∑ i : Fin 3, ∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2 := by
  have hJ := lps_regR12Velocity_slice_isInJ ρ ε hε b hb t ht.le
  obtain ⟨hVs, hVw⟩ := lps_regR12_V_smooth_memLp ρ ε hε b hb ht.le
  have hUs := lps_regR12_slice_smooth ρ ε hε b hb t ht.le
  have hdiv : ∀ x : Vec3, ∑ j : Fin 3,
      spatialDeriv (fun y => lpsRegV ρ ε hε b hb (y, t) j) j x = 0 :=
    CKN.Leray.regUniformMollifiedVelocity_divergence_eq_zero ρ ε hε (lpsRegU ρ ε hε b hb) t hJ
  have hcb : ∀ i : Fin 3, (fun x => ∑ j : Fin 3, spatialDeriv
      (fun y => lpsRegV ρ ε hε b hb (y, t) j * lpsRegU ρ ε hε b hb (y, t) i) j x) =
      lpsRegTransport ρ ε hε b hb i t := by
    intro i
    funext x
    exact (lps_transport_divergence (fun y => lpsRegV ρ ε hε b hb (y, t))
      (fun y => lpsRegU ρ ε hε b hb (y, t)) hVs hUs hdiv i x).symm
  have hP := lps_regR12Pressure_slice_contDiff ρ ε hε b hb t ht
  have hPw := lps_regR12Pressure_all_word_memLp_slice ρ ε hε b hb t ht
  have key := lps_pressure_gradient_sq_le
    (P := fun x => lpsRegP ρ ε hε b hb (x, t))
    (F := fun i j x => lpsRegV ρ ε hε b hb (x, t) i * lpsRegU ρ ε hε b hb (x, t) j)
    hP (fun i j => (hVs i).mul (hUs j)) (hPw []) (fun k => hPw [k]) (fun k => hPw [k, k])
    (fun i => by rw [hcb i]; exact lps_regR12_transport_memLp ρ ε hε b hb ht.le i)
    (fun i => by rw [hcb i]; exact lps_regR12_transport_deriv_memLp ρ ε hε b hb ht.le i i)
    (fun ψ hψ hψc => lps_regR12_pressure_weak ρ ε hε b hb ht ψ hψ hψc)
  have hx : ∀ (i : Fin 3) (x : Vec3), (∑ j : Fin 3, spatialDeriv
      (fun y => lpsRegV ρ ε hε b hb (y, t) j * lpsRegU ρ ε hε b hb (y, t) i) j x) =
      lpsRegTransport ρ ε hε b hb i t x := fun i x => congrFun (hcb i) x
  simpa only [hx] using key

/-- The square of a sum of three real numbers is at most three times the sum of the squares. -/
theorem lps_sq_sum_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The transport term of the regularized momentum equation has `L²` norm squared at most
`27 S³ ‖∇U_ε‖₂³ ‖∇²U_ε‖₂` summed over components (`prop:lps-local-strong`). -/
theorem lps_regR12_transport_sq_sum_le {t : ℝ} (ht : 0 ≤ t) :
    (∑ i : Fin 3, ∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) ≤
      27 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
        lpsRegGradEnergy ρ ε hε b hb t ^ (3 / 2 : ℝ) *
        lpsRegHessEnergy ρ ε hε b hb t ^ (1 / 2 : ℝ)) := by
  set C0 := gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
        lpsRegGradEnergy ρ ε hε b hb t ^ (3 / 2 : ℝ) *
        lpsRegHessEnergy ρ ε hε b hb t ^ (1 / 2 : ℝ) with hC0
  have hi (i : Fin 3) : (∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) ≤ 9 * C0 := by
    have hT (k : Fin 3) : Integrable (fun x => lpsRegTransportTerm ρ ε hε b hb k i t x ^ 2) volume :=
      (lps_regR12_transportTerm_memLp ρ ε hε b hb ht k i).integrable_sq
    calc (∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2)
        ≤ ∫ x, 3 * ∑ k : Fin 3, lpsRegTransportTerm ρ ε hε b hb k i t x ^ 2 := by
          refine integral_mono ((lps_regR12_transport_memLp ρ ε hε b hb ht i).integrable_sq)
            ((integrable_finsetSum _ fun k _ => hT k).const_mul 3) fun x => ?_
          simp only [lpsRegTransport, Fin.sum_univ_three]
          exact lps_sq_sum_three_le _ _ _
      _ = 3 * ∑ k : Fin 3, ∫ x, lpsRegTransportTerm ρ ε hε b hb k i t x ^ 2 := by
          rw [integral_const_mul, integral_finsetSum _ fun k _ => hT k]
      _ ≤ 3 * ∑ k : Fin 3, C0 := by
          gcongr with k
          exact lps_regR12_transportTerm_sq_le ρ ε hε b hb ht k i
      _ = 9 * C0 := by simp; ring
  calc (∑ i : Fin 3, ∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2)
      ≤ ∑ i : Fin 3, 9 * C0 := Finset.sum_le_sum fun i _ => hi i
    _ = 27 * C0 := by simp; ring

/-- On a positive-time slice, the time derivative of the regularized velocity is square integrable
with `∑ᵢ ‖∂ₜ Uᵢ‖₂² ≤ 3 ‖∇²U_ε‖₂² + 162 S³ ‖∇U_ε‖₂³ ‖∇²U_ε‖₂` (`prop:lps-local-strong`). -/
theorem lps_regR12_Q_slice {t : ℝ} (ht : 0 < t) :
    (∀ i : Fin 3, MemLp (fun x => lpsRegQ ρ ε hε b hb (x, t) i) 2 volume) ∧
    (∑ i : Fin 3, ∫ x, lpsRegQ ρ ε hε b hb (x, t) i ^ 2) ≤
      3 * lpsRegHessEnergy ρ ε hε b hb t +
        162 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
          lpsRegGradEnergy ρ ε hε b hb t ^ (3 / 2 : ℝ) *
          lpsRegHessEnergy ρ ε hε b hb t ^ (1 / 2 : ℝ)) := by
  have hPw := lps_regR12Pressure_all_word_memLp_slice ρ ε hε b hb t ht
  have hA (i : Fin 3) : MemLp (lpsRegLap ρ ε hε b hb i t) 2 volume :=
    lps_regR12_lap_memLp ρ ε hε b hb t ht.le i
  have hB (i : Fin 3) : MemLp (lpsRegTransport ρ ε hε b hb i t) 2 volume :=
    lps_regR12_transport_memLp ρ ε hε b hb ht.le i
  have hC (i : Fin 3) :
      MemLp (spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i) 2 volume := hPw [i]
  have hQ (i : Fin 3) : (fun x => lpsRegQ ρ ε hε b hb (x, t) i) =
      fun x => lpsRegLap ρ ε hε b hb i t x - lpsRegTransport ρ ε hε b hb i t x -
        spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x := by
    funext x
    exact lps_regR12_Q_eq ρ ε hε b hb x t i
  have hQmem (i : Fin 3) : MemLp (fun x => lpsRegQ ρ ε hε b hb (x, t) i) 2 volume := by
    rw [hQ i]; exact ((hA i).sub (hB i)).sub (hC i)
  refine ⟨hQmem, ?_⟩
  have hpress := lps_regR12_pressure_gradient_sq_le ρ ε hε b hb ht
  have htrans := lps_regR12_transport_sq_sum_le ρ ε hε b hb ht.le
  have hlap := lps_regR12_lap_sq_eq_hess ρ ε hε b hb ht.le
  have hi (i : Fin 3) : (∫ x, lpsRegQ ρ ε hε b hb (x, t) i ^ 2) ≤
      3 * ((∫ x, lpsRegLap ρ ε hε b hb i t x ^ 2) +
        (∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) +
        ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) := by
    have hAB : Integrable (fun x => lpsRegLap ρ ε hε b hb i t x ^ 2 +
        lpsRegTransport ρ ε hε b hb i t x ^ 2) volume :=
      (hA i).integrable_sq.add (hB i).integrable_sq
    have hABC : Integrable (fun x => lpsRegLap ρ ε hε b hb i t x ^ 2 +
        lpsRegTransport ρ ε hε b hb i t x ^ 2 +
        spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) volume :=
      hAB.add (hC i).integrable_sq
    have hint : (∫ x, 3 * (lpsRegLap ρ ε hε b hb i t x ^ 2 +
        lpsRegTransport ρ ε hε b hb i t x ^ 2 +
        spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2)) =
        3 * ((∫ x, lpsRegLap ρ ε hε b hb i t x ^ 2) +
        (∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) +
        ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) := by
      rw [integral_const_mul, integral_add hAB (hC i).integrable_sq,
        integral_add (hA i).integrable_sq (hB i).integrable_sq]
    rw [← hint]
    refine integral_mono (hQmem i).integrable_sq (hABC.const_mul 3) fun x => ?_
    have := lps_sq_sum_three_le (lpsRegLap ρ ε hε b hb i t x)
      (-lpsRegTransport ρ ε hε b hb i t x) (-spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x)
    have hx : lpsRegQ ρ ε hε b hb (x, t) i = lpsRegLap ρ ε hε b hb i t x +
        -lpsRegTransport ρ ε hε b hb i t x +
        -spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x := by
      rw [lps_regR12_Q_eq]; unfold lpsRegLap; ring
    simp only [hx, neg_sq] at this ⊢
    exact this
  calc (∑ i : Fin 3, ∫ x, lpsRegQ ρ ε hε b hb (x, t) i ^ 2)
      ≤ ∑ i : Fin 3, 3 * ((∫ x, lpsRegLap ρ ε hε b hb i t x ^ 2) +
        (∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) +
        ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 3 * ((∑ i : Fin 3, ∫ x, lpsRegLap ρ ε hε b hb i t x ^ 2) +
        (∑ i : Fin 3, ∫ x, lpsRegTransport ρ ε hε b hb i t x ^ 2) +
        ∑ i : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegP ρ ε hε b hb (y, t)) i x ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by
        rw [hlap]
        linarith only [hpress, htrans]

end

end ESS.LPS

end
