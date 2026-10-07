/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergySlab

/-!
# The energy inequality for a kernel convolution of a weak heat solution

For a weak solution of `∂ₜ w - Δw = div H + f` with initial trace `w₀`, and a
smooth compact kernel `k`, the primitive `W = k ⋆ w` from
`CKN.vlConvT_ae_eq_prim` satisfies, for every `t ∈ [a, τ]`,
`‖W(t)‖² + ∫ₐᵗ ‖∇(k ⋆ w)‖² ≤ ‖k ⋆ w₀‖² + ∫ₐᵗ (‖k ⋆ H‖² + ‖k ⋆ w‖² + ‖k ⋆ f‖²)`.
It is the energy identity of the pointwise time primitive, integrated in
space, with the whole-space integration by parts and Young's inequality
(`lem:localized-vorticity-energy` of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

variable {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ} {w₀ : Vec3 → ℝ}

theorem vlSource_stronglyMeasurable (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) :
    StronglyMeasurable (fun p : Vec3 × ℝ => vlSource k w H f p.1 p.2) := by
  unfold vlSource
  refine (StronglyMeasurable.add ?_ ?_).add
    (vlConvT_stronglyMeasurable hk.continuous sol.f_meas)
  · exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      vlConvT_stronglyMeasurable ((hk.deriv j).deriv j).continuous sol.w_meas
  · exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      vlConvT_stronglyMeasurable (hk.deriv j).continuous (sol.H_meas j)

theorem vlSource_memLp (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ}
    (hk : IsVlKernel k) :
    MemLp (fun p : Vec3 × ℝ => vlSource k w H f p.1 p.2) 2
      (volume.restrict (vlSlab a τ)) := by
  unfold vlSource
  refine (MemLp.add ?_ ?_).add (vlConvT_memLp hk sol.f_meas sol.f_L2)
  · exact memLp_finsetSum _ fun j _ =>
      vlConvT_memLp ((hk.deriv j).deriv j) sol.w_meas sol.w_L2
  · exact memLp_finsetSum _ fun j _ =>
      vlConvT_memLp (hk.deriv j) (sol.H_meas j) (sol.H_L2 j)

/-- The slice identity: whole-space integration by parts of the pairing of
`k ⋆ w` with the convolved source. -/
theorem vlSource_slice_pairing {k : Vec3 → ℝ} (hk : IsVlKernel k) {s : ℝ}
    (hws : MemLp (fun y => w (y, s)) 2 volume)
    (hHs : ∀ j, MemLp (fun y => H j (y, s)) 2 volume)
    (hfs : MemLp (fun y => f (y, s)) 2 volume) :
    ∫ x, vlConvT k w x s * vlSource k w H f x s =
      -(∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) -
        (∑ j : Fin 3, ∫ x, vlConvT (vlDeriv k j) w x s * vlConvT k (H j) x s) +
        (∫ x, vlConvT k w x s * vlConvT k f x s) := by
  have hC := vlConv_memLp hk hws
  have hA : ∀ j, Integrable (fun x => vlConvT k w x s *
      vlConvT (vlDeriv (vlDeriv k j) j) w x s) volume := fun j =>
    hC.integrable_mul (vlConv_memLp ((hk.deriv j).deriv j) hws)
  have hB : ∀ j, Integrable (fun x => vlConvT k w x s *
      vlConvT (vlDeriv k j) (H j) x s) volume := fun j =>
    hC.integrable_mul (vlConv_memLp (hk.deriv j) (hHs j))
  have hE : Integrable (fun x => vlConvT k w x s * vlConvT k f x s) volume :=
    hC.integrable_mul (vlConv_memLp hk hfs)
  have hexpand : ∫ x, vlConvT k w x s * vlSource k w H f x s =
      (∑ j : Fin 3, ∫ x, vlConvT k w x s * vlConvT (vlDeriv (vlDeriv k j) j) w x s) +
        (∑ j : Fin 3, ∫ x, vlConvT k w x s * vlConvT (vlDeriv k j) (H j) x s) +
        (∫ x, vlConvT k w x s * vlConvT k f x s) := by
    have hsumA : Integrable (fun x => ∑ j : Fin 3, vlConvT k w x s *
        vlConvT (vlDeriv (vlDeriv k j) j) w x s) volume :=
      integrable_finsetSum _ fun j _ => hA j
    have hsumB : Integrable (fun x => ∑ j : Fin 3, vlConvT k w x s *
        vlConvT (vlDeriv k j) (H j) x s) volume :=
      integrable_finsetSum _ fun j _ => hB j
    have hAB : Integrable (fun x => (∑ j : Fin 3, vlConvT k w x s *
        vlConvT (vlDeriv (vlDeriv k j) j) w x s) + ∑ j : Fin 3, vlConvT k w x s *
        vlConvT (vlDeriv k j) (H j) x s) volume := hsumA.add hsumB
    rw [← integral_finsetSum _ fun j _ => hA j, ← integral_finsetSum _ fun j _ => hB j,
      ← integral_add hsumA hsumB, ← integral_add hAB hE]
    congr 1
    funext x
    simp only [vlSource, mul_add, Finset.mul_sum]
  have hIBPA : ∀ j : Fin 3, ∫ x, vlConvT k w x s * vlConvT (vlDeriv (vlDeriv k j) j) w x s =
      -∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2 := by
    intro j
    have h := vlConv_integral_mul_deriv hk (hk.deriv j) hws hws j
    simp only [vlConvT]
    rw [h]
    congr 2
    funext x
    ring
  have hIBPB : ∀ j : Fin 3, ∫ x, vlConvT k w x s * vlConvT (vlDeriv k j) (H j) x s =
      -∫ x, vlConvT (vlDeriv k j) w x s * vlConvT k (H j) x s := by
    intro j
    exact vlConv_integral_mul_deriv hk hk hws (hHs j) j
  rw [hexpand]
  simp_rw [hIBPA, hIBPB]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  ring

/-- Young's inequality for the slice pairing. -/
theorem vlSource_slice_pairing_le {k : Vec3 → ℝ} (hk : IsVlKernel k) {s : ℝ}
    (hws : MemLp (fun y => w (y, s)) 2 volume)
    (hHs : ∀ j, MemLp (fun y => H j (y, s)) 2 volume)
    (hfs : MemLp (fun y => f (y, s)) 2 volume) :
    2 * (∫ x, vlConvT k w x s * vlSource k w H f x s) ≤
      -(∑ j : Fin 3, ∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) +
        ((∑ j : Fin 3, ∫ x, (vlConvT k (H j) x s) ^ 2) + (∫ x, (vlConvT k w x s) ^ 2) +
          (∫ x, (vlConvT k f x s) ^ 2)) := by
  rw [vlSource_slice_pairing hk hws hHs hfs]
  have hD : ∀ j, MemLp (fun x => vlConvT (vlDeriv k j) w x s) 2 volume := fun j =>
    vlConv_memLp (hk.deriv j) hws
  have hKH : ∀ j, MemLp (fun x => vlConvT k (H j) x s) 2 volume := fun j =>
    vlConv_memLp hk (hHs j)
  have hC : MemLp (fun x => vlConvT k w x s) 2 volume := vlConv_memLp hk hws
  have hF : MemLp (fun x => vlConvT k f x s) 2 volume := vlConv_memLp hk hfs
  have hcross : ∀ j : Fin 3, -(2 * ∫ x, vlConvT (vlDeriv k j) w x s * vlConvT k (H j) x s) ≤
      (∫ x, (vlConvT (vlDeriv k j) w x s) ^ 2) + (∫ x, (vlConvT k (H j) x s) ^ 2) := by
    intro j
    rw [← integral_add (hD j).integrable_sq (hKH j).integrable_sq, ← integral_const_mul,
      ← integral_neg]
    refine integral_mono ((((hD j).integrable_mul (hKH j)).const_mul 2).neg)
      ((hD j).integrable_sq.add (hKH j).integrable_sq) (fun x => ?_)
    nlinarith only [sq_nonneg (vlConvT (vlDeriv k j) w x s + vlConvT k (H j) x s)]
  have hcross' : 2 * (∫ x, vlConvT k w x s * vlConvT k f x s) ≤
      (∫ x, (vlConvT k w x s) ^ 2) + (∫ x, (vlConvT k f x s) ^ 2) := by
    rw [← integral_add hC.integrable_sq hF.integrable_sq, ← integral_const_mul]
    refine integral_mono ((hC.integrable_mul hF).const_mul 2)
      (hC.integrable_sq.add hF.integrable_sq) (fun x => ?_)
    nlinarith only [sq_nonneg (vlConvT k w x s - vlConvT k f x s)]
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hcross j
  rw [Finset.sum_add_distrib] at hsum
  have hneg : ∑ j : Fin 3, -(2 * ∫ x, vlConvT (vlDeriv k j) w x s * vlConvT k (H j) x s) =
      -(2 * ∑ j : Fin 3, ∫ x, vlConvT (vlDeriv k j) w x s * vlConvT k (H j) x s) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hneg] at hsum
  linarith only [hsum, hcross']

end CKN

end
