/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! ### Symmetry of iterated coordinate directional derivatives -/

public section

open Set Filter
open scoped Topology ContDiff
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- Iterating `axisDeriv` preserves `ContDiffOn ℝ ∞` on an open set. -/
theorem contDiffOn_foldr_axisDeriv (s : Set Vec3) (hs : IsOpen s) (G : Vec3 → ℝ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (l : List (Fin 3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (List.foldr axisDeriv G l) s := by
  induction l with
  | nil => exact hG
  | cons j l ih =>
    -- ih : ContDiffOn ℝ ∞ (List.foldr axisDeriv G l) s
    have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (List.foldr axisDeriv G l)) s :=
      ih.fderiv_of_isOpen (m := (⊤ : ℕ∞)) hs (by simp)
    have h_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun (_ : Vec3) => basisVec j) s :=
      contDiffOn_const
    have h_deriv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => fderiv ℝ (List.foldr axisDeriv G l) x (basisVec j)) s :=
      h_fderiv.clm_apply h_const
    -- axisDeriv j (List.foldr axisDeriv G l) is definitionally equal to the above
    exact h_deriv

/-- Symmetry of two consecutive `axisDeriv` applications on an open set.

Uses the symmetry of the second derivative (`second_derivative_symmetric_of_eventually`). -/
theorem axisDeriv_axisDeriv_symm (s : Set Vec3) (hs : IsOpen s) (G : Vec3 → ℝ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (a b : Fin 3) (x : Vec3) (hx : x ∈ s) :
    axisDeriv a (axisDeriv b G) x = axisDeriv b (axisDeriv a G) x := by
  have hG_at : ContDiffAt ℝ (⊤ : ℕ∞) G x :=
    hG.contDiffAt (IsOpen.mem_nhds hs hx)
  -- Use the symmetry of the second derivative for ℝ
  -- second_derivative_symmetric_of_eventually requires:
  -- ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y  and  HasFDerivAt f' f'' x
  have h_event : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y := by
    have h_cont_diff_on : ContDiffOn ℝ (⊤ : ℕ∞) G (s) := hG
    -- On an open set, ContDiffOn implies HasFDerivAt at each point
    apply Filter.eventually_of_mem (IsOpen.mem_nhds hs hx)
    intro y hy
    have h_diff : DifferentiableAt ℝ G y := by
      have : ContDiffAt ℝ (⊤ : ℕ∞) G y :=
        hG.contDiffAt (IsOpen.mem_nhds hs hy)
      exact this.differentiableAt (by simp)
    exact h_diff.hasFDerivAt
  have h_fderiv_at : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x := by
    have h_fderiv_cont : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ G) x :=
      hG_at.fderiv_right (by simp)
    exact h_fderiv_cont.differentiableAt (by simp) |>.hasFDerivAt
  have h_symm := second_derivative_symmetric_of_eventually h_event h_fderiv_at (basisVec a)
    (basisVec b)
  -- h_symm : fderiv ℝ (fderiv ℝ G) x (basisVec a) (basisVec b) = fderiv ℝ (fderiv ℝ G) x
  -- (basisVec b) (basisVec a)
  have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ G) x :=
    h_fderiv_at.differentiableAt
  have h_fderiv_eq_b : fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec b)) x
      = (fderiv ℝ (fderiv ℝ G) x).flip (basisVec b) := by
    have := fderiv_clm_apply h_fderiv_diff (differentiableAt_const (basisVec b))
    simpa [fderiv_const] using this
  have h_fderiv_eq_a : fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec a)) x
      = (fderiv ℝ (fderiv ℝ G) x).flip (basisVec a) := by
    have := fderiv_clm_apply h_fderiv_diff (differentiableAt_const (basisVec a))
    simpa [fderiv_const] using this
  have h1 : axisDeriv a (axisDeriv b G) x = fderiv ℝ (fderiv ℝ G) x (basisVec a) (basisVec b) := by
    calc
      axisDeriv a (axisDeriv b G) x
          = fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec b)) x (basisVec a) := rfl
      _ = ((fderiv ℝ (fderiv ℝ G) x).flip (basisVec b)) (basisVec a) := by rw [h_fderiv_eq_b]
      _ = fderiv ℝ (fderiv ℝ G) x (basisVec a) (basisVec b) := rfl
  have h2 : axisDeriv b (axisDeriv a G) x = fderiv ℝ (fderiv ℝ G) x (basisVec b) (basisVec a) := by
    calc
      axisDeriv b (axisDeriv a G) x
          = fderiv ℝ (fun y : Vec3 => fderiv ℝ G y (basisVec a)) x (basisVec b) := rfl
      _ = ((fderiv ℝ (fderiv ℝ G) x).flip (basisVec a)) (basisVec b) := by rw [h_fderiv_eq_a]
      _ = fderiv ℝ (fderiv ℝ G) x (basisVec b) (basisVec a) := rfl
  rw [h1, h2]
  exact h_symm

/-- If two functions agree on an open set `s` and both are `ContDiffOn ℝ ∞` there,
then their `axisDeriv` also agree on `s`. -/
theorem axisDeriv_congr_on (s : Set Vec3) (hs : IsOpen s) (F G : Vec3 → ℝ)
    (a : Fin 3) (h : Set.EqOn F G s) :
    Set.EqOn (axisDeriv a F) (axisDeriv a G) s := by
  intro x hx
  have h_event : F =ᶠ[𝓝 x] G := by
    apply Filter.eventually_of_mem (IsOpen.mem_nhds hs hx)
    intro y hy
    exact h hy
  have h_fderiv_eq : fderiv ℝ F x = fderiv ℝ G x :=
    Filter.EventuallyEq.fderiv_eq h_event
  simp [axisDeriv, h_fderiv_eq]

/-- Iterated `axisDeriv` does not depend on the order of the directions. -/
theorem eqOn_foldr_axisDeriv_of_perm (s : Set Vec3) (hs : IsOpen s) (G : Vec3 → ℝ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) {l l' : List (Fin 3)} (hperm : l.Perm l') :
    Set.EqOn (List.foldr axisDeriv G l) (List.foldr axisDeriv G l') s := by
  induction hperm with
  | nil =>
      intro x hx
      rfl
  | cons a hperm ih =>
      rename_i l₁ l₂
      have hF : ContDiffOn ℝ (⊤ : ℕ∞) (List.foldr axisDeriv G l₁) s :=
        contDiffOn_foldr_axisDeriv s hs G hG l₁
      have hG' : ContDiffOn ℝ (⊤ : ℕ∞) (List.foldr axisDeriv G l₂) s :=
        contDiffOn_foldr_axisDeriv s hs G hG l₂
      intro x hx
      have h_ax_eq : axisDeriv a (List.foldr axisDeriv G l₁) x =
          axisDeriv a (List.foldr axisDeriv G l₂) x :=
        axisDeriv_congr_on s hs _ _ a ih hx
      simpa [List.foldr] using h_ax_eq
  | swap a b =>
      rename_i l
      intro x hx
      have hF : ContDiffOn ℝ (⊤ : ℕ∞) (List.foldr axisDeriv G l) s :=
        contDiffOn_foldr_axisDeriv s hs G hG l
      have h_symm := axisDeriv_axisDeriv_symm s hs (List.foldr axisDeriv G l) hF a b x hx
      -- h_symm : axisDeriv a (axisDeriv b (foldr ... l)) x = axisDeriv b (axisDeriv a
      -- (foldr ... l)) x
      -- The goal is the reverse: axisDeriv b (axisDeriv a ...) x = axisDeriv a (axisDeriv b ...) x
      -- This is because Set.EqOn swaps the arguments in the swap case
      simpa [List.foldr] using h_symm.symm
  | trans hperm1 hperm2 ih1 ih2 =>
      intro x hx
      rw [ih1 hx, ih2 hx]

end CIV
