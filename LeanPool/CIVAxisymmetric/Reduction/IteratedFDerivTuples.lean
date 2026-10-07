/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Iterated FDeriv Tuples

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open scoped Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- On an open set, the `n`-th iterated Fréchet derivative evaluated at a tuple of coordinate
basis vectors agrees with the corresponding iteration of `axisDeriv` in the order the tuple
lists them. -/
theorem eqOn_iteratedFDeriv_basis (s : Set Vec3) (hs : IsOpen s) (G : Vec3 → ℝ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (n : ℕ) (v : Fin n → Fin 3) :
    Set.EqOn (fun x => iteratedFDeriv ℝ n G x (fun i => basisVec (v i)))
      (List.foldr axisDeriv G (List.ofFn v)) s := by
  induction n with
  | zero =>
      intro x _
      simp [List.ofFn_zero, List.foldr_nil]
  | succ n ih =>
      intro x hx
      have hG_at : ContDiffAt ℝ (⊤ : ℕ∞) G x := hG.contDiffAt (IsOpen.mem_nhds hs hx)
      have hDiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n G) x :=
        hG_at.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
      have hEq : (fun y : Vec3 => iteratedFDeriv ℝ n G y (fun i : Fin n => basisVec (v i.succ)))
          =ᶠ[𝓝 x] (List.foldr axisDeriv G (List.ofFn (fun i : Fin n => v i.succ))) :=
        Filter.eventually_of_mem (IsOpen.mem_nhds hs hx)
          (fun y hy => ih (fun i : Fin n => v i.succ) hy)
      have hFd : fderiv ℝ
            (fun y : Vec3 => iteratedFDeriv ℝ n G y (fun i : Fin n => basisVec (v i.succ))) x
          = fderiv ℝ (List.foldr axisDeriv G (List.ofFn (fun i : Fin n => v i.succ))) x :=
        Filter.EventuallyEq.fderiv_eq hEq
      have hFlip : fderiv ℝ
            (fun y : Vec3 => iteratedFDeriv ℝ n G y (fun i : Fin n => basisVec (v i.succ))) x
          = (fderiv ℝ (iteratedFDeriv ℝ n G) x).flipMultilinear
              (fun i : Fin n => basisVec (v i.succ)) :=
        fderiv_continuousMultilinear_apply_const hDiff (fun i : Fin n => basisVec (v i.succ))
      change iteratedFDeriv ℝ (n + 1) G x (fun i => basisVec (v i)) =
        List.foldr axisDeriv G (List.ofFn v) x
      rw [iteratedFDeriv_succ_apply_left, show List.ofFn v = v 0 :: List.ofFn
        (fun i : Fin n => v i.succ) from List.ofFn_succ, List.foldr_cons]
      change fderiv ℝ (iteratedFDeriv ℝ n G) x (basisVec (v 0))
          (fun i : Fin n => basisVec (v i.succ)) =
        fderiv ℝ (List.foldr axisDeriv G (List.ofFn (fun i : Fin n => v i.succ))) x
          (basisVec (v 0))
      rw [← hFd, hFlip]
      rfl

end CIV
