/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.IteratedDerivBridge

/-! ### The order-shift composition law for `multiPartial`/`axisDeriv`

One further coordinate derivative of a multi-index derivative on a time slice
is again a multi-index derivative, at the multi-index incremented by the new
direction — the bookkeeping step needed to differentiate the momentum equation's
`multiPartial`-language form (`CIV.laplacian_eq_of_isClassicalSolutionOn`) one
further time for the inductive derivative estimates behind
`thm:analytic:interior` (Kahane 1969). -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem contDiffOn_multiPartial_slice {h : ParabolicPoint → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) s) (α : Fin 3 → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => multiPartial h α (x, t)) s := by
  rw [multiPartial_slice h α t]
  have h_eq : List.foldr axisDeriv (fun x : Vec3 => h (x, t))
      (List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
        ++ List.replicate (α 2) (2 : Fin 3))
      = (axisDeriv 0)^[α 0] ((axisDeriv 1)^[α 1] ((axisDeriv 2)^[α 2]
        (fun x : Vec3 => h (x, t)))) := by
    simp [foldr_axisDeriv_replicate, List.foldr_append]
  rw [← h_eq]
  exact contDiffOn_foldr_axisDeriv s hs (fun x : Vec3 => h (x, t)) hG _

theorem axisDeriv_multiPartial_slice_eq {h : ParabolicPoint → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) s)
    (α : Fin 3 → ℕ) (k : Fin 3) {x : Vec3} (hx : x ∈ s) :
    axisDeriv k (fun y : Vec3 => multiPartial h α (y, t)) x
      = multiPartial h (α + Pi.single k 1) (x, t) := by
  let l : List (Fin 3) := List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
    ++ List.replicate (α 2) (2 : Fin 3)
  have h_fun_eq : (fun y : Vec3 => multiPartial h α (y, t)) =
      List.foldr axisDeriv (fun x : Vec3 => h (x, t)) l := by
    rw [multiPartial_slice h α t]
    simp [l, foldr_axisDeriv_replicate, List.foldr_append]
  let β : Fin 3 → ℕ := fun i => α i + (if i = k then 1 else 0)
  have hβ_eq : β = α + Pi.single k 1 := by
    ext i; simp [β, Pi.single_apply]
  have h_target_eq : multiPartial h β (x, t) =
      List.foldr axisDeriv (fun x : Vec3 => h (x, t))
        (List.replicate (β 0) (0 : Fin 3)
        ++ List.replicate (β 1) (1 : Fin 3)
        ++ List.replicate (β 2) (2 : Fin 3)) x := by
    have h_slice := congrFun (multiPartial_slice h β t) x
    simpa [foldr_axisDeriv_replicate, List.foldr_append] using h_slice
  let l' : List (Fin 3) := List.replicate (β 0) (0 : Fin 3)
    ++ List.replicate (β 1) (1 : Fin 3)
    ++ List.replicate (β 2) (2 : Fin 3)
  have h_perm : (k :: l).Perm l' := by
    rw [List.perm_iff_count]
    intro c
    fin_cases c <;> fin_cases k <;>
      dsimp [l, l', β] <;>
      simp [List.count_append, List.count_replicate]
  have h_eq_on := eqOn_foldr_axisDeriv_of_perm s hs (fun x : Vec3 => h (x, t)) hG h_perm
  calc
    axisDeriv k (fun y : Vec3 => multiPartial h α (y, t)) x
        = axisDeriv k (List.foldr axisDeriv (fun x : Vec3 => h (x, t)) l) x := by rw [h_fun_eq]
    _ = List.foldr axisDeriv (fun x : Vec3 => h (x, t)) (k :: l) x := rfl
    _ = List.foldr axisDeriv (fun x : Vec3 => h (x, t)) l' x := h_eq_on hx
    _ = multiPartial h β (x, t) := by rw [h_target_eq]
    _ = multiPartial h (α + Pi.single k 1) (x, t) := by rw [hβ_eq]

theorem axisDeriv_axisDeriv_multiPartial_slice_eq {h : ParabolicPoint → ℝ} {s : Set Vec3}
    (hs : IsOpen s) (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) s)
    (α : Fin 3 → ℕ) (k l : Fin 3) {x : Vec3} (hx : x ∈ s) :
    axisDeriv k (fun y : Vec3 => axisDeriv l (fun z : Vec3 => multiPartial h α (z, t)) y) x
      = multiPartial h (α + Pi.single k 1 + Pi.single l 1) (x, t) := by
  set G : Vec3 → ℝ := fun y : Vec3 => multiPartial h α (y, t) with hGdef
  have h_inner_eq_on : Set.EqOn (axisDeriv l G)
      (fun y : Vec3 => multiPartial h (α + Pi.single l 1) (y, t)) s := by
    intro y hy
    rw [hGdef]
    exact axisDeriv_multiPartial_slice_eq hs t hG α l hy
  have h_outer_eq_on : Set.EqOn (axisDeriv k (axisDeriv l G))
      (axisDeriv k (fun y : Vec3 => multiPartial h (α + Pi.single l 1) (y, t))) s :=
    axisDeriv_congr_on s hs _ _ k h_inner_eq_on
  have h_at_x := h_outer_eq_on hx
  rw [h_at_x]
  rw [axisDeriv_multiPartial_slice_eq hs t hG (α + Pi.single l 1) k hx]
  congr 1
  ext i
  simp [Pi.add_apply, Pi.single_apply, add_comm, add_left_comm]

theorem axisDeriv_axisDeriv_multiPartial_slice_eq_single {h : ParabolicPoint → ℝ} {s : Set Vec3}
    (hs : IsOpen s) (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) s)
    (α : Fin 3 → ℕ) (k : Fin 3) {x : Vec3} (hx : x ∈ s) :
    axisDeriv k (fun y : Vec3 => axisDeriv k (fun z : Vec3 => multiPartial h α (z, t)) y) x
      = multiPartial h (α + Pi.single k 2) (x, t) := by
  set G : Vec3 → ℝ := fun y : Vec3 => multiPartial h α (y, t) with hGdef
  have h_inner_eq_on : Set.EqOn (axisDeriv k G)
      (fun y : Vec3 => multiPartial h (α + Pi.single k 1) (y, t)) s := by
    intro y hy
    rw [hGdef]
    exact axisDeriv_multiPartial_slice_eq hs t hG α k hy
  have h_outer_eq_on : Set.EqOn (axisDeriv k (axisDeriv k G))
      (axisDeriv k (fun y : Vec3 => multiPartial h (α + Pi.single k 1) (y, t))) s :=
    axisDeriv_congr_on s hs _ _ k h_inner_eq_on
  have h_at_x := h_outer_eq_on hx
  rw [h_at_x]
  rw [axisDeriv_multiPartial_slice_eq hs t hG (α + Pi.single k 1) k hx]
  have h_add_eq : (α + Pi.single k 1) + Pi.single k 1 = α + Pi.single k 2 := by
    ext i; simp [Pi.single_apply]; split <;> omega
  rw [h_add_eq]

end CIV
