/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceTrilinear

/-!
# Relative Cancellation

The advective cross terms reduce to the relative convection form for a
finite Serrin pair. The proof uses only the integrable products
`|u||v||Du|`, `|u|²|Du|`, and `|v||u||Du|` (`lem:lps-comparison`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_mixed_prod_memLp {f g : Vec3 → ℝ} {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hrecip : p⁻¹ + q⁻¹ = r⁻¹)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    MemLp (fun x => f x * g x) (ENNReal.ofReal r) volume := by
  have _ : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q)
      (ENNReal.ofReal r) := serrin_holder_ofReal3 hp hq hr hrecip
  exact hf.mul hg

/-- The advective cross terms reduce to the relative convection form for a
finite Serrin pair. The proof uses only the integrable products
`|u||v||Du|`, `|u|²|Du|`, and `|v||u||Du|` (`lem:lps-comparison`). -/
theorem lps_slice_relative_cancellation
    {s : ℝ} (hs : 3 < s)
    {u v : Vec3 → Vec3} {Du Dv : Vec3 → Fin 3 → Vec3}
    (hu : SerrinSlice u Du)
    (huS : MemLp u (ENNReal.ofReal s) volume)
    (huQ : MemLp u (ENNReal.ofReal (2 * s / (s - 2))) volume)
    (hv : SerrinSlice v Dv)
    (hvQ : MemLp v (ENNReal.ofReal (2 * s / (s - 2))) volume) :
    (∫ x : Vec3,
      (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3,
        (v x j - u x j) * (Dv x k j - Du x k j)) = 0 := by
  let q : ℝ := 2 * s / (s - 2)
  let r₁ : ℝ := 2 * s / (s + 2)
  let r₂ : ℝ := s / (s - 1)
  have hs0 : 0 < s := by linarith only [hs]
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hs1 : 0 < s - 1 := by linarith only [hs]
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hr₁0 : 0 < r₁ := by dsimp [r₁]; positivity
  have hr₂0 : 0 < r₂ := by dsimp [r₂]; positivity
  have hq_ge_one : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hs2]
    nlinarith only [hs]
  have hs_ge_one : 1 ≤ s := by linarith only [hs]
  have lps_ofReal_two_eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hsq : s⁻¹ + q⁻¹ = (2 : ℝ)⁻¹ := by
    dsimp [q]
    field_simp
    ring
  have hr₁q : r₁⁻¹ + q⁻¹ = 1 := by
    dsimp [r₁, q]
    field_simp
    ring
  have hr₂s : r₂⁻¹ + s⁻¹ = 1 := by
    dsimp [r₂]
    field_simp
    ring
  have hUq : MemLp u (ENNReal.ofReal q) volume := by
    simpa only [q] using huQ
  have hVq : MemLp v (ENNReal.ofReal q) volume := by
    simpa only [q] using hvQ
  have hU2 : MemLp u (ENNReal.ofReal 2) volume := by
    rw [← lps_ofReal_two_eq]
    exact hu.mem2
  have hDu2 : MemLp Du (ENNReal.ofReal 2) volume := by
    rw [← lps_ofReal_two_eq]
    exact hu.grad2
  have hDv2 : MemLp Dv (ENNReal.ofReal 2) volume := by
    rw [← lps_ofReal_two_eq]
    exact hv.grad2
  have huu (j k : Fin 3) :
      MemLp (fun x => u x j * u x k) (ENNReal.ofReal 2) volume := by
    exact lps_mixed_prod_memLp hs0 hq0 (by norm_num) hsq
      (huS.eval j) (hUq.eval k)
  have huv (j k : Fin 3) :
      MemLp (fun x => u x j * v x k) (ENNReal.ofReal 2) volume := by
    exact lps_mixed_prod_memLp hs0 hq0 (by norm_num) hsq
      (huS.eval j) (hVq.eval k)
  have hvu (j k : Fin 3) :
      MemLp (fun x => v x j * u x k) (ENNReal.ofReal 2) volume := by
    exact lps_mixed_prod_memLp hq0 hs0 (by norm_num) (by simpa [add_comm] using hsq)
      (hVq.eval j) (huS.eval k)
  have huu2 (j k : Fin 3) : MemLp (fun x => u x j * u x k) 2 volume := by
    rw [lps_ofReal_two_eq]
    exact huu j k
  have huv2 (j k : Fin 3) : MemLp (fun x => u x j * v x k) 2 volume := by
    rw [lps_ofReal_two_eq]
    exact huv j k
  have hvu2 (j k : Fin 3) : MemLp (fun x => v x j * u x k) 2 volume := by
    rw [lps_ofReal_two_eq]
    exact hvu j k
  have _ : ENNReal.HolderTriple (ENNReal.ofReal r₁) (ENNReal.ofReal q) 1 :=
    serrin_holder_ofReal hr₁0 hq0 hr₁q
  have hT1 := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace
    hv.mem2 hv.grad2 hv.grad hu.mem2 hu.grad2 hu.grad
    (r := ENNReal.ofReal r₁) (s := ENNReal.ofReal q)
    (serrin_one_le_ofReal hq_ge_one) (by simp) huv2
    (fun j k => lps_mixed_prod_memLp hs0 (by norm_num) hr₁0
      (by dsimp [r₁]; field_simp; ring) (huS.eval j) ((hDv2.eval k).eval j))
    (fun k => hUq.eval k)
  have hT3 := serrin_trilinear_vanish hu.mem2 hu.grad2 hu.grad hu.trace
    hu.mem2 hu.grad2 hu.grad hu.mem2 hu.grad2 hu.grad
    (r := ENNReal.ofReal r₁) (s := ENNReal.ofReal q)
    (serrin_one_le_ofReal hq_ge_one) (by simp) huu2
    (fun j k => lps_mixed_prod_memLp hs0 (by norm_num) hr₁0
      (by dsimp [r₁]; field_simp; ring) (huS.eval j) ((hDu2.eval k).eval j))
    (fun k => hUq.eval k)
  have _ : ENNReal.HolderTriple (ENNReal.ofReal r₂) (ENNReal.ofReal s) 1 :=
    serrin_holder_ofReal hr₂0 hs0 hr₂s
  have hT2 := serrin_trilinear_vanish hv.mem2 hv.grad2 hv.grad hv.trace
    hu.mem2 hu.grad2 hu.grad hu.mem2 hu.grad2 hu.grad
    (r := ENNReal.ofReal r₂) (s := ENNReal.ofReal s)
    (serrin_one_le_ofReal hs_ge_one) (by simp) hvu2
    (fun j k => lps_mixed_prod_memLp hq0 (by norm_num) hr₂0
      (by dsimp [r₂, q]; field_simp; ring) (hVq.eval j) ((hDu2.eval k).eval j))
    (fun k => huS.eval k)
  have hmon {F : Vec3 → ℝ} (hF : MemLp F 2 volume)
      {G : Vec3 → Fin 3 → Vec3} (hG : MemLp G 2 volume)
      (k j : Fin 3) : Integrable (fun x => F x * G x k j) volume :=
    hF.integrable_mul (q := 2) ((hG.eval k).eval j)
  have hsum2 (F : Fin 3 → Fin 3 → Vec3 → ℝ)
      (hF : ∀ k j, Integrable (F k j) volume) :
      Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3, F k j x) volume :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hF k j
  have hX1 : Integrable (fun x =>
      ∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) volume := by
    refine (hsum2 (fun k j x => v x j * u x k * Dv x k j)
      fun k j => hmon (hvu2 j k) hv.grad2 k j).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hX2 : Integrable (fun x =>
      ∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) volume := by
    refine (hsum2 (fun k j x => u x j * v x k * Du x k j)
      fun k j => hmon (huv2 j k) hu.grad2 k j).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hY : Integrable (fun x =>
      ∑ k : Fin 3, u x k * ∑ j : Fin 3,
        (v x j - u x j) * (Dv x k j - Du x k j)) volume := by
    refine (hsum2 (fun k j x =>
      v x j * u x k * Dv x k j - v x j * u x k * Du x k j -
        u x j * u x k * Dv x k j + u x j * u x k * Du x k j)
      fun k j => (((hmon (hvu2 j k) hv.grad2 k j).sub
          (hmon (hvu2 j k) hu.grad2 k j)).sub
          (hmon (huu2 j k) hv.grad2 k j)).add
          (hmon (huu2 j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hpt : (fun x =>
      (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3,
        (v x j - u x j) * (Dv x k j - Du x k j)) =
    fun x =>
      (∑ k : Fin 3, ∑ j : Fin 3,
        u x j * (Dv x k j * u x k + v x k * Du x k j)) +
      (1 / 2 : ℝ) *
        (∑ k : Fin 3, ∑ j : Fin 3,
          v x j * (Du x k j * u x k + u x k * Du x k j)) -
      (1 / 2 : ℝ) *
        ∑ k : Fin 3, ∑ j : Fin 3,
          u x j * (Du x k j * u x k + u x k * Du x k j) := by
    funext x
    simp only [Fin.sum_univ_three]
    ring
  have hT1i : Integrable (fun x =>
      ∑ k : Fin 3, ∑ j : Fin 3,
        u x j * (Dv x k j * u x k + v x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x =>
      u x j * u x k * Dv x k j + u x j * v x k * Du x k j)
      fun k j => (hmon (huu2 j k) hv.grad2 k j).add
        (hmon (huv2 j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2i : Integrable (fun x =>
      ∑ k : Fin 3, ∑ j : Fin 3,
        v x j * (Du x k j * u x k + u x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x =>
      v x j * u x k * Du x k j + v x j * u x k * Du x k j)
      fun k j => (hmon (hvu2 j k) hu.grad2 k j).add
        (hmon (hvu2 j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hT3i : Integrable (fun x =>
      ∑ k : Fin 3, ∑ j : Fin 3,
        u x j * (Du x k j * u x k + u x k * Du x k j)) volume := by
    refine (hsum2 (fun k j x =>
      u x j * u x k * Du x k j + u x j * u x k * Du x k j)
      fun k j => (hmon (huu2 j k) hu.grad2 k j).add
        (hmon (huu2 j k) hu.grad2 k j)).congr
      (Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hdiff : (∫ x : Vec3,
      (∑ k : Fin 3, u x k * ∑ j : Fin 3, v x j * Dv x k j) +
      (∑ k : Fin 3, v x k * ∑ j : Fin 3, u x j * Du x k j) -
      ∑ k : Fin 3, u x k * ∑ j : Fin 3,
        (v x j - u x j) * (Dv x k j - Du x k j)) = 0 := by
    have hT2h : Integrable (fun x => (1 / 2 : ℝ) *
        ∑ k : Fin 3, ∑ j : Fin 3,
          v x j * (Du x k j * u x k + u x k * Du x k j)) volume :=
      hT2i.const_mul _
    have hT3h : Integrable (fun x => (1 / 2 : ℝ) *
        ∑ k : Fin 3, ∑ j : Fin 3,
          u x j * (Du x k j * u x k + u x k * Du x k j)) volume :=
      hT3i.const_mul _
    have hT12 : Integrable (fun x =>
        (∑ k : Fin 3, ∑ j : Fin 3,
          u x j * (Dv x k j * u x k + v x k * Du x k j)) +
        (1 / 2 : ℝ) * ∑ k : Fin 3, ∑ j : Fin 3,
          v x j * (Du x k j * u x k + u x k * Du x k j)) volume :=
      hT1i.add hT2h
    rw [hpt, integral_sub hT12 hT3h, integral_add hT1i hT2h,
      integral_const_mul, integral_const_mul, hT1, hT2, hT3]
    ring
  exact hdiff

end ESS

end
