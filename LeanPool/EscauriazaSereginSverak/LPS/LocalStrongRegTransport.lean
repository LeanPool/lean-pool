/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegProduct
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegPressure
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1TransportBound

/-!
# The `L²` size of the regularized transport term

Every slice of the transport term `(J_ε U_ε · ∇) U_ε` of the regularized velocity has square
integrable derivatives, and its `L²` norm is bounded by `S^{3/2} ‖∇U_ε‖₂^{3/2} ‖∇²U_ε‖₂^{1/2}`
(`prop:lps-local-strong`, the uniform time derivative bound).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The product of two smooth functions with all ordered derivatives square integrable is square
integrable, and so is its first derivative. -/
theorem lps_smooth_mul_deriv_memLp {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf' : ∀ α, MemLp (wordDeriv α f) 2 volume)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hg' : ∀ α, MemLp (wordDeriv α g) 2 volume) :
    MemLp (fun x => f x * g x) 2 volume ∧
      ∀ k, MemLp (spatialDeriv (fun x => f x * g x) k) 2 volume := by
  refine ⟨(lps_smooth_mul_memLp_two_norm_le hf (hf' []) (fun k => hf' [k]) hg (hg' [])
    (fun k => hg' [k])).1, fun k => ?_⟩
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f k) := contDiff_spatialDeriv_smooth hf k
  have hgd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g k) := contDiff_spatialDeriv_smooth hg k
  have h1 := (lps_smooth_mul_memLp_two_norm_le hfd (hf' [k]) (fun l => hf' [k, l]) hg (hg' [])
    (fun l => hg' [l])).1
  have h2 := (lps_smooth_mul_memLp_two_norm_le hf (hf' []) (fun l => hf' [l]) hgd (hg' [k])
    (fun l => hg' [k, l])).1
  have heq : spatialDeriv (fun x => f x * g x) k =
      fun x => spatialDeriv f k x * g x + f x * spatialDeriv g k x := by
    funext x
    exact spatialDeriv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x) k
  rw [heq]
  exact h1.add h2

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The `L²` size of one summand of the regularized transport term
(`prop:lps-local-strong`). -/
theorem lps_regR12_transportTerm_sq_le {t : ℝ} (ht : 0 ≤ t) (k i : Fin 3) :
    (∫ x, lpsRegTransportTerm ρ ε hε b hb k i t x ^ 2) ≤
      gagliardoNirenbergSobolevConstant.toReal ^ (3 : ℕ) *
        lpsRegGradEnergy ρ ε hε b hb t ^ (3 / 2 : ℝ) *
        lpsRegHessEnergy ρ ε hε b hb t ^ (1 / 2 : ℝ) := by
  obtain ⟨hVs, hVw⟩ := lps_regR12_V_smooth_memLp ρ ε hε b hb ht
  have hUs := lps_regR12_slice_smooth ρ ε hε b hb t ht
  have hUw := lps_regR12_slice_memLp ρ ε hε b hb t ht
  have hy0 : 0 ≤ lpsRegGradEnergy ρ ε hε b hb t :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => sq_nonneg _
  have hh0 : 0 ≤ lpsRegHessEnergy ρ ε hε b hb t :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
      integral_nonneg fun x => sq_nonneg _
  have hmain := lps_smooth_mul_sq_integral_le (V := fun x => lpsRegV ρ ε hε b hb (x, t) k)
    (d := spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k)
    (hVs k) (hVw k []) (fun l => hVw k [l])
    (contDiff_spatialDeriv_smooth (hUs i) k) (hUw i [k]) (fun l => hUw i [k, l])
    hy0 hh0 ?_ ?_ ?_
  · exact hmain
  · calc (∑ l : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegV ρ ε hε b hb (y, t) k) l x ^ 2)
        ≤ ∑ l : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) k) l x ^ 2 :=
          Finset.sum_le_sum fun l _ => lps_regR12_V_grad_contraction ρ ε hε b hb ht k l
      _ ≤ lpsRegGradEnergy ρ ε hε b hb t :=
          Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∫ x,
            spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i') j x ^ 2)
            (fun i' _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
            (Finset.mem_univ k)
  · calc (∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x ^ 2)
        ≤ ∑ j : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2 :=
          Finset.single_le_sum (f := fun j : Fin 3 => ∫ x,
            spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2)
            (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ lpsRegGradEnergy ρ ε hε b hb t :=
          Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∫ x,
            spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i') j x ^ 2)
            (fun i' _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
            (Finset.mem_univ i)
  · calc (∑ l : Fin 3, ∫ x, spatialDeriv (spatialDeriv
          (fun y => lpsRegU ρ ε hε b hb (y, t) i) k) l x ^ 2)
        ≤ ∑ k' : Fin 3, ∑ l : Fin 3, ∫ x, spatialDeriv (spatialDeriv
            (fun y => lpsRegU ρ ε hε b hb (y, t) i) k') l x ^ 2 :=
          Finset.single_le_sum (f := fun k' : Fin 3 => ∑ l : Fin 3, ∫ x, spatialDeriv (spatialDeriv
            (fun y => lpsRegU ρ ε hε b hb (y, t) i) k') l x ^ 2)
            (fun k' _ => Finset.sum_nonneg fun l _ => integral_nonneg fun x => sq_nonneg _)
            (Finset.mem_univ k)
      _ ≤ lpsRegHessEnergy ρ ε hε b hb t :=
          Finset.single_le_sum (f := fun i' : Fin 3 => ∑ k' : Fin 3, ∑ l : Fin 3, ∫ x,
            spatialDeriv (spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i') k') l x ^ 2)
            (fun i' _ => Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun l _ =>
              integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)

/-- The transport term of the regularized momentum equation and its first derivatives are square
integrable (`prop:lps-local-strong`). -/
theorem lps_regR12_transport_deriv_memLp {t : ℝ} (ht : 0 ≤ t) (i k : Fin 3) :
    MemLp (spatialDeriv (lpsRegTransport ρ ε hε b hb i t) k) 2 volume := by
  obtain ⟨hVs, hVw⟩ := lps_regR12_V_smooth_memLp ρ ε hε b hb ht
  have hUs := lps_regR12_slice_smooth ρ ε hε b hb t ht
  have hUw := lps_regR12_slice_memLp ρ ε hε b hb t ht
  have hterm (j : Fin 3) :
      MemLp (spatialDeriv (lpsRegTransportTerm ρ ε hε b hb j i t) k) 2 volume :=
    (lps_smooth_mul_deriv_memLp (hVs j) (hVw j) (contDiff_spatialDeriv_smooth (hUs i) j)
      (fun α => hUw i (j :: α))).2 k
  have hsm (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (lpsRegTransportTerm ρ ε hε b hb j i t) :=
    (hVs j).mul (contDiff_spatialDeriv_smooth (hUs i) j)
  have heq : spatialDeriv (lpsRegTransport ρ ε hε b hb i t) k =
      fun x => ∑ j : Fin 3, spatialDeriv (lpsRegTransportTerm ρ ε hε b hb j i t) k x := by
    have := localDivCurlSmooth_wordDeriv_sum [k] (f := fun j x => lpsRegTransportTerm ρ ε hε b
      hb j i t x) hsm
    exact this
  rw [heq]
  exact memLp_finsetSum _ fun j _ => hterm j

end

end ESS.LPS

end
