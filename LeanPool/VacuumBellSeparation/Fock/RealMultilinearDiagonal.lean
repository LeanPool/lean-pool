/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Real diagonal determination of symmetric continuous multilinear maps

Differentiate the identically zero diagonal. Permutation symmetry makes
all n directional terms equal, and characteristic zero cancels n.
Currying then reduces the number of variables. This proves the full
diagonal determination theorem without assuming polarization or density.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock.RealPolarization

variable {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Invariance of a multilinear map under permutations of its input coordinates. -/
def MultilinearPermutationInvariant {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) G) : Prop :=
  ∀ (e : Equiv.Perm (Fin n)) (v : Fin n → H), M (v ∘ e) = M v

theorem symmetric_multilinear_update_diagonal {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) G)
    (hM : MultilinearPermutationInvariant M) (x y : H) (i : Fin (n + 1)) :
    M (Function.update (fun _ => x) i y) = M (Function.update (fun _ => x) 0 y) := by
  have h := hM (Equiv.swap 0 i) (Function.update (fun _ => x) 0 y)
  have heq : Function.update (fun _ : Fin (n + 1) => x) 0 y ∘ Equiv.swap 0 i =
      Function.update (fun _ : Fin (n + 1) => x) i y := by
    rw [Function.update_comp_equiv]
    simp only [Equiv.symm_swap, Equiv.swap_apply_left, Function.comp_def]
  exact (congrArg M heq).symm.trans h

theorem symmetric_multilinear_first_diagonal_zero {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) G)
    (hM : MultilinearPermutationInvariant M) (hdiag : ∀ x, M (fun _ => x) = 0)
    (x y : H) : M (Fin.cons y (fun _ : Fin n => x)) = 0 := by
  let D : H →L[ℝ] (Fin (n + 1) → H) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ H)
  have hder := (M.hasFDerivAt (D x)).comp x D.hasFDerivAt
  have hfun : M ∘ D = fun _ => (0 : G) := funext fun z => hdiag z
  rw [hfun] at hder
  have hzero := hder.unique (hasFDerivAt_const (0 : G) x)
  have hsum := congrArg (fun L : H →L[ℝ] G => L y) hzero
  change M.linearDeriv (fun _ => x) (fun _ => y) = 0 at hsum
  rw [ContinuousMultilinearMap.linearDeriv_apply] at hsum
  simp only [symmetric_multilinear_update_diagonal M hM x y,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  have hsmul : ((n + 1 : ℕ) : ℝ) • M (Function.update (fun _ => x) 0 y) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hsum
  have hz : M (Function.update (fun _ => x) 0 y) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)
  convert hz using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem symmetric_multilinear_curryLeft {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => H) G)
    (hM : MultilinearPermutationInvariant M) (x : H) :
    MultilinearPermutationInvariant (M.curryLeft x) := by
  intro e v
  let E : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, e)
  have h := hM E (Fin.cons x v)
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
  convert h using 1
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [E]
  · simp [E, Function.comp_def]

/-- Genuine polarization consequence for every finite degree, including zero. -/
theorem symmetric_multilinear_eq_zero_of_diagonal (n : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) G)
    (hM : MultilinearPermutationInvariant M) (hdiag : ∀ x, M (fun _ => x) = 0) : M = 0 := by
  induction n with
  | zero =>
      apply ContinuousMultilinearMap.ext
      intro v
      have hv : v = fun _ : Fin 0 => (0 : H) := Subsingleton.elim _ _
      simpa only [hv, zero_apply] using hdiag 0
  | succ n ih =>
      apply ContinuousMultilinearMap.ext
      intro v
      have hc : M.curryLeft (v 0) = 0 := ih (M.curryLeft (v 0))
        (symmetric_multilinear_curryLeft M hM (v 0))
        (fun x => symmetric_multilinear_first_diagonal_zero M hM hdiag x (v 0))
      have he := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) G =>
        L (Fin.tail v)) hc
      simpa only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail,
        zero_apply] using he

end VacuumBellSeparation.Fock.RealPolarization
