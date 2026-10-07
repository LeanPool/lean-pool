/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Product rule for the coordinate directional derivative

`axisDeriv` is the directional derivative along a coordinate axis on a spatial slice.
This file establishes the Leibniz product rule for `axisDeriv`, its smoothness
counterpart, and a `Finset`-indexed sum-of-products corollary used in the
convective-term estimates of the inductive derivative bounds behind
`thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The Leibniz product rule for `axisDeriv`: differentiating a product along a
coordinate axis splits into the derivative of the first factor times the second,
plus the first times the derivative of the second. -/
theorem axisDeriv_mul {F G : Vec3 → ℝ} {x : Vec3} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Fin 3) :
    axisDeriv k (fun y => F y * G y) x = axisDeriv k F x * G x + F x * axisDeriv k G x := by
  unfold axisDeriv
  rw [fderiv_fun_mul hF hG]
  simp [smul_eq_mul]
  ring

/-- `axisDeriv_mul` with `ContDiffOn ℝ ⊤` hypotheses on an open set, matching the
regularity used in the interior analyticity argument. -/
theorem axisDeriv_mul_of_contDiffOn {F G : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F s) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (k : Fin 3)
    {x : Vec3} (hx : x ∈ s) :
    axisDeriv k (fun y => F y * G y) x = axisDeriv k F x * G x + F x * axisDeriv k G x := by
  have hF_diff : DifferentiableAt ℝ F x :=
    (hF.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hG_diff : DifferentiableAt ℝ G x :=
    (hG.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  exact axisDeriv_mul hF_diff hG_diff k

/-- `ContDiffOn` is preserved under pointwise products of real-valued functions. -/
theorem contDiffOn_mul_of_contDiffOn {F G : Vec3 → ℝ} {s : Set Vec3}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F s) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F y * G y) s := by
  exact ContDiffOn.mul hF hG

/-- `Finset`-indexed sum-of-products corollary of the Leibniz rule, matching the
convective term `∑_j g_j(x) ∂_j h(x)` that appears when differentiating the
momentum equation in the inductive derivative estimates behind
`thm:analytic:interior`. -/
theorem axisDeriv_sum_mul_of_contDiffOn {ι : Type*} (u : Finset ι)
    {F G : ι → Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hF : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (F i) s)
    (hG : ∀ i ∈ u, ContDiffOn ℝ (⊤ : ℕ∞) (G i) s) (k : Fin 3) {x : Vec3} (hx : x ∈ s) :
    axisDeriv k (fun y => ∑ i ∈ u, F i y * G i y) x
      = ∑ i ∈ u, (axisDeriv k (F i) x * G i x + F i x * axisDeriv k (G i) x) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      simp [axisDeriv]
  | insert a u ha ih =>
      have hFa : ContDiffOn ℝ (⊤ : ℕ∞) (F a) s := hF a (Finset.mem_insert_self a u)
      have hGa : ContDiffOn ℝ (⊤ : ℕ∞) (G a) s := hG a (Finset.mem_insert_self a u)
      have h_diff_a : axisDeriv k (fun y => F a y * G a y) x =
          axisDeriv k (F a) x * G a x + F a x * axisDeriv k (G a) x :=
        axisDeriv_mul_of_contDiffOn hs hFa hGa k hx
      have h_diff_Fa : DifferentiableAt ℝ (F a) x :=
        (hF a (Finset.mem_insert_self a u)).contDiffAt (hs.mem_nhds hx) |>.differentiableAt
          (by norm_num)
      have h_diff_Ga : DifferentiableAt ℝ (G a) x :=
        (hG a (Finset.mem_insert_self a u)).contDiffAt (hs.mem_nhds hx) |>.differentiableAt
          (by norm_num)
      have h_diff_prod_a : DifferentiableAt ℝ (fun y => F a y * G a y) x :=
        DifferentiableAt.mul h_diff_Fa h_diff_Ga
      have h_diff_sum : DifferentiableAt ℝ (fun y => ∑ i ∈ u, F i y * G i y) x := by
        have h := DifferentiableAt.sum fun i hi => by
          have hFi : DifferentiableAt ℝ (F i) x :=
            (hF i (Finset.mem_insert_of_mem hi)).contDiffAt (hs.mem_nhds hx) |>.differentiableAt
              (by norm_num)
          have hGi : DifferentiableAt ℝ (G i) x :=
            (hG i (Finset.mem_insert_of_mem hi)).contDiffAt (hs.mem_nhds hx) |>.differentiableAt
              (by norm_num)
          exact DifferentiableAt.mul hFi hGi
        convert h using 1
        ext y
        simp
      simp only [Finset.sum_insert ha]
      have h_add : axisDeriv k (fun y => F a y * G a y + ∑ i ∈ u, F i y * G i y) x =
          axisDeriv k (fun y => F a y * G a y) x +
          axisDeriv k (fun y => ∑ i ∈ u, F i y * G i y) x := by
        unfold axisDeriv
        rw [fderiv_fun_add h_diff_prod_a h_diff_sum, add_apply]
      rw [h_add, h_diff_a, ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
        (fun i hi => hG i (Finset.mem_insert_of_mem hi))]

end CIV
