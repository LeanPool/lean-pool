/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Comparison.MollifySlice

/-!
# Barrier Support

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN

noncomputable section
namespace CIV

theorem posPart_sub_barrier_eq_zero_of_norm_ge {m : ℕ} {M σ K τ₀ τ Minf : ℝ} (hσ : 0 < σ) (hK :
    0 ≤ K)
    (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {v : Vec m → ℝ} (hv : ∀ x, |v x| ≤ Minf) (x : Vec m)
    (hx : Minf / σ ≤ ‖x‖) :
    max (v x - barrier m M σ K τ₀ (x, τ)) 0 = 0 := by
  have hvx : v x ≤ |v x| := le_abs_self (v x)
  have h_absv : |v x| ≤ Minf := hv x
  have h_Minf : Minf ≤ σ * ‖x‖ := by
    calc
      Minf = (Minf / σ) * σ := by field_simp
      _ ≤ ‖x‖ * σ := mul_le_mul_of_nonneg_right hx (le_of_lt hσ)
      _ = σ * ‖x‖ := mul_comm _ _
  have h_barrier : M + σ * ‖x‖ ≤ barrier m M σ K τ₀ (x, τ) :=
    le_barrier M K τ₀ τ x (le_of_lt hσ) hK hτ
  have h_nonpos : v x - barrier m M σ K τ₀ (x, τ) ≤ 0 := by
    have hle : v x ≤ barrier m M σ K τ₀ (x, τ) :=
      calc
        v x ≤ |v x| := hvx
        _ ≤ Minf := h_absv
        _ ≤ σ * ‖x‖ := h_Minf
        _ ≤ M + σ * ‖x‖ := by nlinarith only [hM]
        _ ≤ barrier m M σ K τ₀ (x, τ) := h_barrier
    exact sub_nonpos.mpr hle
  rw [max_eq_right h_nonpos]

theorem posPart_mollifySlice_sub_barrier_eq_zero {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (h_meas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (h_bdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) (x : Vec m) (hx : Minf / σ ≤ ‖x‖) :
    max (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ)) 0 = 0 := by
  have h_abs_mollify : |mollifySlice m ε q (x, τ)| ≤ Minf :=
    abs_mollifySlice_le hε h_meas h_bdd x
  have h_abs : mollifySlice m ε q (x, τ) ≤ |mollifySlice m ε q (x, τ)| := le_abs_self _
  have h_Minf : Minf ≤ σ * ‖x‖ := by
    calc
      Minf = (Minf / σ) * σ := by field_simp
      _ ≤ ‖x‖ * σ := mul_le_mul_of_nonneg_right hx (le_of_lt hσ)
      _ = σ * ‖x‖ := mul_comm _ _
  have h_barrier : M + σ * ‖x‖ ≤ barrier m M σ K τ₀ (x, τ) :=
    le_barrier M K τ₀ τ x (le_of_lt hσ) hK hτ
  have h_nonpos : mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ) ≤ 0 := by
    have hle : mollifySlice m ε q (x, τ) ≤ barrier m M σ K τ₀ (x, τ) :=
      calc
        mollifySlice m ε q (x, τ) ≤ |mollifySlice m ε q (x, τ)| := h_abs
        _ ≤ Minf := h_abs_mollify
        _ ≤ σ * ‖x‖ := h_Minf
        _ ≤ M + σ * ‖x‖ := by nlinarith only [hM]
        _ ≤ barrier m M σ K τ₀ (x, τ) := h_barrier
    exact sub_nonpos.mpr hle
  rw [max_eq_right h_nonpos]

theorem posPart_sq_le_of_le {a b : ℝ} (h : a ≤ b) : (max (a - b) 0) ^ 2 = 0 := by
  have h_sub : a - b ≤ 0 := sub_nonpos.mpr h
  rw [max_eq_right h_sub]
  norm_num

end CIV
