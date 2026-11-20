/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.Ratpoints.Spec.Sturm

import Mathlib.FieldTheory.IsRealClosed.Real
import LeanPool.Ratpoints.Mathlib.FieldTheory.Perfect
import TauCeti.Algebra.Polynomial.Sturm.GCD
import TauCeti.Algebra.Polynomial.Sturm.OneSided
import TauCeti.Algebra.Polynomial.Sturm.Variation

/-!
# Root counting for the Ratpoints Sturm specification

Tau Ceti counts roots with one-sided sign variations. For a squarefree polynomial, variation
immediately to the right of an endpoint equals variation at the endpoint itself. At a simple
root the polynomial's right-hand sign agrees with the derivative, so the first two entries
contribute no change.

* `Ratpoints.sturmTheorem` proves the root count used for interval pruning.
-/

public section

namespace Ratpoints

open Polynomial SignType Set TauCeti.Sturm

private theorem squarefree_sturmSeq_alternating {p : ℝ[X]} (hp : Squarefree p) :
    IsAlternating (sturmSeq p p.derivative) := by
  apply (IsSignedRemainderSeq.sturmSeq p p.derivative).isAlternating
  intro q hq x hqx
  obtain ⟨hdiv, hdiv'⟩ := TauCeti.getLast?_sturmSeq_dvd hq
  exact (hp.eval_ne_zero_or_eval_derivative_ne_zero x).elim
    (fun h => h (eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hqx))
    (fun h => h (eval_eq_zero_of_dvd_of_eval_eq_zero hdiv' hqx))

private theorem signRight_eq_sign_derivative_of_simple_root {p : ℝ[X]} {a : ℝ}
    (ha : p.IsRoot a) (hd : p.derivative.eval a ≠ 0) :
    p.derivSignRight a = sign (p.derivative.eval a) := by
  have hm := derivative_rootMultiplicity_of_root ha
  rw [rootMultiplicity_eq_zero hd] at hm
  have hpos := (rootMultiplicity_pos (show p ≠ 0 from fun h => hd (by simp [h]))).mpr ha
  have hone : p.rootMultiplicity a = 1 := by omega
  simp [derivSignRight_def, hone]

private theorem signVariationsRight_sturmSeq_eq_at {p : ℝ[X]} (hp : Squarefree p) (a : ℝ) :
    signVariationsRight (sturmSeq p p.derivative) a =
      signVariationsAt (sturmSeq p p.derivative) a := by
  let cs := sturmSeq p p.derivative
  have halt : IsAlternating cs := squarefree_sturmSeq_alternating hp
  obtain ⟨u, hau, hu⟩ := cs.exists_signs_right a
  obtain ⟨x, hax, hxu⟩ := exists_between hau
  have hs (q : ℝ[X]) (hq : q ∈ cs) := hu q hq x ⟨hax, hxu⟩
  have hn (q : ℝ[X]) (hq : q ∈ cs) :=
    eval_ne_zero_of_sign_eq_derivSignRight (halt.nonzero q hq) (hs q hq)
  have ha (q : ℝ[X]) (hq : q ∈ cs) (hq0 : q.eval a ≠ 0) :=
    (hs q hq).trans (derivSignRight_eq_sign_eval q hq0)
  change signVariationsRight cs a = signVariationsAt cs a
  rw [← signVariationsAt_eq_right hs]
  by_cases hpa : p.IsRoot a
  · have hd : p.derivative.eval a ≠ 0 :=
      (hp.eval_ne_zero_or_eval_derivative_ne_zero a).resolve_left (fun h => h hpa)
    have hcs : cs = p :: sturmSeq p.derivative (-p % p.derivative) := sturmSeq_cons hp.ne_zero
    have hd0 : p.derivative ≠ 0 := fun h => hd (by simp [h])
    have hmem : p.derivative ∈ cs := by rw [hcs, sturmSeq_cons hd0]; simp
    have hpx : sign (p.eval x) = sign (p.derivative.eval a) :=
      (hs p (by rw [hcs]; simp)).trans (signRight_eq_sign_derivative_of_simple_root hpa hd)
    have hdx : sign (p.derivative.eval x) = sign (p.derivative.eval a) := ha _ hmem hd
    have hpx0 := hn p (by rw [hcs]; simp)
    have hdx0 := hn p.derivative hmem
    change signVariationsAt (sturmSeq p p.derivative) x =
      signVariationsAt (sturmSeq p p.derivative) a
    rw [signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero hpx0 hdx0, hpx, hdx,
      signVariationsAt_sturmSeq_eq_of_eval_eq_zero hpa, ite_eq_left rfl, add_zero]
    rw [hcs] at halt hn ha
    exact halt.tail.signVariationsAt_eq x a
      (fun q hq => hn q (List.mem_cons_of_mem _ hq))
      (fun q hq => by rw [sturmSeq_cons hd0] at hq; cases hq; exact hd)
      (fun q hq => ha q (List.mem_cons_of_mem _ hq))
  · apply halt.signVariationsAt_eq x a hn _ ha
    intro q hq
    have heq : q = p := by simpa [cs, sturmSeq_cons hp.ne_zero] using hq.symm
    exact heq ▸ hpa

/-- The squarefree root count used in Ratpoints, from Tau Ceti's one-sided Sturm theorem. -/
theorem sturmTheorem : SturmTheorem := by
  classical
  intro p hp a b hab
  have hn := card_roots_toFinset_Ioc (R := ℝ) hp.ne_zero hab
  have hsame := card_roots_toFinset_Ioc (R := ℝ) hp.ne_zero (le_refl b)
  rw [Finset.filter_false_of_mem (fun x _ hx => (not_lt_of_ge hx.2) hx.1)] at hsame
  simp only [Finset.card_empty, Nat.cast_zero] at hsame
  have hset : {x | a < x ∧ x ≤ b ∧ p.IsRoot x} =
      (↑(p.roots.toFinset.filter fun x => a < x ∧ x ≤ b) : Set ℝ) := by
    ext x
    simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset,
      mem_roots hp.ne_zero]
    tauto
  rw [hset, ncard_coe_finset]
  rw [signVariationsRight_sturmSeq_eq_at hp a] at hn
  rw [signVariationsRight_sturmSeq_eq_at hp b] at hsame
  simp only [signVariationsAt_def] at hn hsame
  omega

end Ratpoints
