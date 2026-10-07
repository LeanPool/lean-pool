/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.IteratedDerivBridge

/-!
# Multi Partial Linearity

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem axisDeriv_add {F G : Vec3 → ℝ} {x : Vec3} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Fin 3) :
    axisDeriv k (fun y => F y + G y) x = axisDeriv k F x + axisDeriv k G x := by
  unfold axisDeriv
  rw [fderiv_fun_add hF hG]
  simp

theorem axisDeriv_const_smul {F : Vec3 → ℝ} {x : Vec3} (hF : DifferentiableAt ℝ F x)
    (c : ℝ) (k : Fin 3) :
    axisDeriv k (fun y => c * F y) x = c * axisDeriv k F x := by
  have h_eq : (fun y : Vec3 => c * F y) = (fun y => c • F y) := by
    ext y; exact (smul_eq_mul (α := ℝ) _ _).symm
  rw [h_eq]
  unfold axisDeriv
  rw [fderiv_fun_const_smul hF c]
  simp [smul_eq_mul]

theorem multiPartial_add {h₁ h₂ : ParabolicPoint → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (t : ℝ) (hG₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h₁ (x, t)) s)
    (hG₂ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h₂ (x, t)) s)
    (α : Fin 3 → ℕ) {x : Vec3} (hx : x ∈ s) :
    multiPartial (fun z => h₁ z + h₂ z) α (x, t)
      = multiPartial h₁ α (x, t) + multiPartial h₂ α (x, t) := by
  set l := List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
    ++ List.replicate (α 2) (2 : Fin 3) with hl
  have h_multi_eq (h : ParabolicPoint → ℝ) :
      (fun (x' : Vec3) => multiPartial h α (x', t)) =
      List.foldr axisDeriv (fun (x' : Vec3) => h (x', t)) l := by
    simpa [l, List.foldr_append, foldr_axisDeriv_replicate] using multiPartial_slice h α t
  have h_add_eq_on : Set.EqOn
      (List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l)
      (fun y => List.foldr axisDeriv (fun z => h₁ (z, t)) l y +
                List.foldr axisDeriv (fun z => h₂ (z, t)) l y) s := by
    induction l with
    | nil =>
        intro x' _; rfl
    | cons j l' ih =>
        intro x' hx'
        have h_eq_on : Set.EqOn
            (List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l')
            (fun y => List.foldr axisDeriv (fun z => h₁ (z, t)) l' y +
                      List.foldr axisDeriv (fun z => h₂ (z, t)) l' y) s := ih
        have h_eq_on_deriv : Set.EqOn
            (axisDeriv j (List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l'))
            (axisDeriv j (fun y => List.foldr axisDeriv (fun z => h₁ (z, t)) l' y +
                                     List.foldr axisDeriv (fun z => h₂ (z, t)) l' y)) s :=
          axisDeriv_congr_on s hs _ _ j h_eq_on
        have hF_diff : DifferentiableAt ℝ (List.foldr axisDeriv (fun z => h₁ (z, t)) l') x' := by
          have h_cont := contDiffOn_foldr_axisDeriv s hs (fun x' : Vec3 => h₁ (x', t)) hG₁ l'
          have h_cont_at : ContDiffAt ℝ (⊤ : ℕ∞)
              (List.foldr axisDeriv (fun z => h₁ (z, t)) l') x' :=
            h_cont.contDiffAt (IsOpen.mem_nhds hs hx')
          exact h_cont_at.differentiableAt (by simp)
        have hG_diff : DifferentiableAt ℝ (List.foldr axisDeriv (fun z => h₂ (z, t)) l') x' := by
          have h_cont := contDiffOn_foldr_axisDeriv s hs (fun x' : Vec3 => h₂ (x', t)) hG₂ l'
          have h_cont_at : ContDiffAt ℝ (⊤ : ℕ∞)
              (List.foldr axisDeriv (fun z => h₂ (z, t)) l') x' :=
            h_cont.contDiffAt (IsOpen.mem_nhds hs hx')
          exact h_cont_at.differentiableAt (by simp)
        have h_eq_at_x' : axisDeriv j (List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l') x'
            = axisDeriv j (List.foldr axisDeriv (fun z => h₁ (z, t)) l') x'
              + axisDeriv j (List.foldr axisDeriv (fun z => h₂ (z, t)) l') x' := by
          calc
            axisDeriv j (List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l') x'
                = axisDeriv j (fun y => List.foldr axisDeriv (fun z => h₁ (z, t)) l' y +
                                         List.foldr axisDeriv (fun z => h₂ (z, t)) l' y) x' :=
              h_eq_on_deriv hx'
            _ = axisDeriv j (List.foldr axisDeriv (fun z => h₁ (z, t)) l') x'
                + axisDeriv j (List.foldr axisDeriv (fun z => h₂ (z, t)) l') x' :=
              axisDeriv_add hF_diff hG_diff j
        simpa [List.foldr] using h_eq_at_x'
  calc
    multiPartial (fun z => h₁ z + h₂ z) α (x, t)
        = (fun (x' : Vec3) => multiPartial (fun z => h₁ z + h₂ z) α (x', t)) x := rfl
    _ = List.foldr axisDeriv (fun (x' : Vec3) => (fun z => h₁ z + h₂ z) (x', t)) l x := by
      rw [h_multi_eq (fun z => h₁ z + h₂ z)]
    _ = List.foldr axisDeriv (fun y => h₁ (y, t) + h₂ (y, t)) l x := rfl
    _ = (fun y => List.foldr axisDeriv (fun z => h₁ (z, t)) l y +
                 List.foldr axisDeriv (fun z => h₂ (z, t)) l y) x := by
      rw [h_add_eq_on hx]
    _ = List.foldr axisDeriv (fun z => h₁ (z, t)) l x +
        List.foldr axisDeriv (fun z => h₂ (z, t)) l x := rfl
    _ = multiPartial h₁ α (x, t) + multiPartial h₂ α (x, t) := by
      rw [(congrFun (h_multi_eq h₁) x).symm, (congrFun (h_multi_eq h₂) x).symm]

theorem multiPartial_const_smul {h : ParabolicPoint → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) s)
    (α : Fin 3 → ℕ) (c : ℝ) {x : Vec3} (hx : x ∈ s) :
    multiPartial (fun z => c * h z) α (x, t) = c * multiPartial h α (x, t) := by
  set l := List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
    ++ List.replicate (α 2) (2 : Fin 3) with hl
  have h_multi_eq (h' : ParabolicPoint → ℝ) :
      (fun (x' : Vec3) => multiPartial h' α (x', t)) =
      List.foldr axisDeriv (fun (x' : Vec3) => h' (x', t)) l := by
    simpa [l, List.foldr_append, foldr_axisDeriv_replicate] using multiPartial_slice h' α t
  have h_smul_eq_on : Set.EqOn
      (List.foldr axisDeriv (fun y => c * h (y, t)) l)
      (fun y => c * List.foldr axisDeriv (fun z => h (z, t)) l y) s := by
    induction l with
    | nil =>
        intro x' _; rfl
    | cons j l' ih =>
        intro x' hx'
        have h_eq_on : Set.EqOn
            (List.foldr axisDeriv (fun y => c * h (y, t)) l')
            (fun y => c * List.foldr axisDeriv (fun z => h (z, t)) l' y) s := ih
        have h_eq_on_deriv : Set.EqOn
            (axisDeriv j (List.foldr axisDeriv (fun y => c * h (y, t)) l'))
            (axisDeriv j (fun y => c * List.foldr axisDeriv (fun z => h (z, t)) l' y)) s :=
          axisDeriv_congr_on s hs _ _ j h_eq_on
        have h_diff : DifferentiableAt ℝ (List.foldr axisDeriv (fun z => h (z, t)) l') x' := by
          have h_cont := contDiffOn_foldr_axisDeriv s hs (fun x' : Vec3 => h (x', t)) hG l'
          have h_cont_at : ContDiffAt ℝ (⊤ : ℕ∞)
              (List.foldr axisDeriv (fun z => h (z, t)) l') x' :=
            h_cont.contDiffAt (IsOpen.mem_nhds hs hx')
          exact h_cont_at.differentiableAt (by simp)
        have h_eq_at_x' : axisDeriv j (List.foldr axisDeriv (fun y => c * h (y, t)) l') x'
            = c * axisDeriv j (List.foldr axisDeriv (fun z => h (z, t)) l') x' := by
          calc
            axisDeriv j (List.foldr axisDeriv (fun y => c * h (y, t)) l') x'
                = axisDeriv j (fun y => c * List.foldr axisDeriv (fun z => h (z, t)) l' y) x' :=
              h_eq_on_deriv hx'
            _ = c * axisDeriv j (List.foldr axisDeriv (fun z => h (z, t)) l') x' :=
              axisDeriv_const_smul h_diff c j
        simpa [List.foldr] using h_eq_at_x'
  calc
    multiPartial (fun z => c * h z) α (x, t)
        = (fun (x' : Vec3) => multiPartial (fun z => c * h z) α (x', t)) x := rfl
    _ = List.foldr axisDeriv (fun (x' : Vec3) => (fun z => c * h z) (x', t)) l x := by
      rw [h_multi_eq (fun z => c * h z)]
    _ = List.foldr axisDeriv (fun y => c * h (y, t)) l x := rfl
    _ = (fun y => c * List.foldr axisDeriv (fun z => h (z, t)) l y) x := by
      rw [h_smul_eq_on hx]
    _ = c * List.foldr axisDeriv (fun z => h (z, t)) l x := rfl
    _ = c * multiPartial h α (x, t) := by
      rw [← congrFun (h_multi_eq h) x]

end CIV
