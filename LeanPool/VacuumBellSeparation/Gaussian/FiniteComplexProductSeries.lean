/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteProductSeries
public import Mathlib.Analysis.Complex.Basic

/-!
# Absolute finite-product Fubini for complex series

The index consists of all occupation tuples. Absolute convergence is
proved from the finite product of the norm series before any rearrangement.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem summable_norm_fin_complex_product (m : ℕ) (f : Fin m → ℕ → ℂ)
    (hf : ∀ j, Summable (fun n => ‖f j n‖)) :
    Summable (fun k : Fin m → ℕ => ‖∏ j, f j (k j)‖) := by
  simpa only [norm_prod] using
    (hasSum_fin_product_nonneg m (fun j n => ‖f j n‖) (fun j => ∑' n, ‖f j n‖)
      (fun j n => norm_nonneg _) (fun j => (hf j).hasSum)).summable

theorem hasSum_fin_complex_product (m : ℕ) (f : Fin m → ℕ → ℂ) (s : Fin m → ℂ)
    (hf : ∀ j, Summable (fun n => ‖f j n‖)) (hs : ∀ j, HasSum (f j) (s j)) :
    HasSum (fun k : Fin m → ℕ => ∏ j, f j (k j)) (∏ j, s j) := by
  classical
  induction m with
  | zero =>
    let : Fintype (Fin 0 → ℕ) := Fintype.ofSubsingleton (fun i => Fin.elim0 i)
    simp
  | succ m ih =>
    have htail : HasSum (fun k : Fin m → ℕ => ∏ j, f j.succ (k j))
        (∏ j : Fin m, s j.succ) :=
      ih (fun j => f j.succ) (fun j => s j.succ)
        (fun j => hf j.succ) (fun j => hs j.succ)
    have habs : Summable (fun k : Fin m → ℕ => ‖∏ j, f j.succ (k j)‖) :=
      summable_norm_fin_complex_product m (fun j => f j.succ) (fun j => hf j.succ)
    have hsum : HasSum (fun k : ℕ × (Fin m → ℕ) =>
        f 0 k.1 * ∏ j, f j.succ (k.2 j)) (s 0 * ∏ j : Fin m, s j.succ) := by
      have hprod := (summable_mul_of_summable_norm (R := ℂ) (hf 0) habs).hasSum
      have heq := tsum_mul_tsum_of_summable_norm (R := ℂ) (hf 0) habs
      rw [(hs 0).tsum_eq, htail.tsum_eq] at heq
      exact heq.symm ▸ hprod
    apply (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hsum

end VacuumBellSeparation.Gaussian
