/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.PeierlsModel
public import LeanPool.HubbardMoments.Torus
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

/-!
# The doubled Peierls phase

Two electrons of opposite spin on a finite simple graph `G`, hopping with modulus `t` and
Peierls phases `A` (`HubbardMoments.pairHopping`). At second order in `t/U`, the effective
Hamiltonian on the doublon states `D_R` (`HubbardMoments.doublonSecondOrder`) is:

* `pairHopping_isHermitian`: the model is Hermitian when `A` is antisymmetric;
* `pairHopping_doublon`: no single hop connects two doublons, so the first-order term vanishes;
* `doublonSecondOrder_adj`: a doublon hops to a neighbouring site with amplitude
  `t_d e^{2 i A(R', R)}`, `t_d = 2t²/U`: twice the phase of one electron;
* `doublonSecondOrder_of_not_adj`: it does not hop further at this order;
* `doublonSecondOrder_self`: its energy shift is `2 z t²/U` (`z` the degree of `R`), for every
  antisymmetric `A`;
* `doublonSecondOrder_self_torus`: `8 t²/U` on the `L × L` torus, `L ≥ 3`.

The two virtual paths from `D_R` to `D_{R'}` (up electron first, or down electron first) use
the same bond twice, so each carries the phase `e^{2 i A(R', R)}` and they add.

## Not covered

Higher orders in `t/U`, several doublons, and the derivation of the second-order formula
itself (standard degenerate perturbation theory).
-/

public section

namespace HubbardMoments

open Finset SimpleGraph Complex

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (t : ℝ) (A : V → V → ℝ)

omit [Fintype V] in
/-- With antisymmetric phases, `A(x, y) = -A(y, x)`, the two-electron hopping operator is
Hermitian. -/
theorem pairHopping_isHermitian (hA : ∀ x y, G.Adj x y → A y x = -A x y) :
    (pairHopping G t A).IsHermitian := by
  ext p q
  have e₁ : (q.2 = p.2 ∧ G.Adj p.1 q.1) ↔ (p.2 = q.2 ∧ G.Adj q.1 p.1) :=
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have e₂ : (q.1 = p.1 ∧ G.Adj p.2 q.2) ↔ (p.1 = q.1 ∧ G.Adj q.2 p.2) :=
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  simp only [Matrix.conjTranspose_apply, pairHopping, star_add, e₁, e₂]
  congr 1 <;> split_ifs with h
  all_goals first | exact star_zero _ | rw [star_peierlsAmplitude, hA _ _ h.2]

omit [Fintype V] in
/-- One hop never takes a doublon to a doublon: the first-order term `P H P` vanishes on the
doublon states. -/
theorem pairHopping_doublon (R' R : V) : pairHopping G t A (R', R') (R, R) = 0 := by
  have h : ¬ (R' = R ∧ G.Adj R R') := fun h => G.ne_of_adj h.2 h.1.symm
  simp only [pairHopping, h, ↓reduceIte, add_zero]

/-- **The doubled Peierls phase.** For adjacent sites `R`, `R'`, the second-order amplitude for
the doublon to hop from `R` to `R'` is `t_d e^{2 i A(R', R)}` with `t_d = 2t²/U`. -/
theorem doublonSecondOrder_adj {R R' : V} (h : G.Adj R R') (U : ℝ) :
    doublonSecondOrder (pairHopping G t A) U R' R =
      2 * (t : ℂ) ^ 2 / U * exp (2 * A R' R * I) := by
  have hne : R ≠ R' := G.ne_of_adj h
  unfold doublonSecondOrder
  rw [sum_eq_add (R', R) (R, R') (by simp [hne.symm])]
  · simp only [pairHopping, peierlsAmplitude, hne.symm, h, and_true, ↓reduceIte,
      zero_add, add_zero, false_and]
    rw [show (2 * A R' R * I : ℂ) = A R' R * I + A R' R * I by ring, exp_add]
    ring
  · rintro ⟨x, y⟩ - ⟨h₁, h₂⟩
    simp only [pairHopping]
    split_ifs <;> simp_all
  · intro hm
    exact absurd (by simp [hne.symm]) hm
  · intro hm
    exact absurd (by simp [hne]) hm

/-- **The doublon hops only to nearest neighbours** at second order: for distinct,
non-adjacent `R`, `R'` the amplitude vanishes. -/
theorem doublonSecondOrder_of_not_adj {R R' : V} (hne : R ≠ R') (h : ¬ G.Adj R R') (U : ℝ) :
    doublonSecondOrder (pairHopping G t A) U R' R = 0 := by
  unfold doublonSecondOrder
  rw [sum_eq_zero, zero_div]
  rintro ⟨x, y⟩ -
  simp only [pairHopping]
  split_ifs <;> simp_all

omit [Fintype V] [DecidableEq V] in
/-- With antisymmetric phases, a hop followed by its reverse carries no phase. -/
theorem hop_mul_reverse {x y : V} (hA : A y x = -A x y) :
    peierlsAmplitude t (A x y) * peierlsAmplitude t (A y x) = (t : ℂ) ^ 2 := by
  rw [peierlsAmplitude, peierlsAmplitude, hA, mul_mul_mul_comm, ← exp_add,
    show (A x y : ℂ) * I + ((-A x y : ℝ) : ℂ) * I = 0 by push_cast; ring, exp_zero]
  ring

omit [DecidableEq V] in
theorem sum_ite_adj (c : ℂ) (R : V) : (∑ x, if G.Adj R x then c else 0) = G.degree R * c := by
  rw [← sum_filter, sum_const, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree,
    nsmul_eq_mul]

/-- **The on-site shift is flux-blind.** With antisymmetric phases, the second-order energy
shift of a doublon on site `R` is `2 z t²/U`, `z` the degree of `R`, whatever `A` is: each of
the `2z` virtual hops returns along the same bond and its phases cancel. -/
theorem doublonSecondOrder_self (U : ℝ) (R : V) (hA : ∀ x, G.Adj R x → A x R = -A R x) :
    doublonSecondOrder (pairHopping G t A) U R R = 2 * G.degree R * (t : ℂ) ^ 2 / U := by
  have key : ∀ m : V × V, pairHopping G t A (R, R) m * pairHopping G t A m (R, R) =
      (if m.2 = R ∧ G.Adj R m.1 then (t : ℂ) ^ 2 else 0) +
        (if m.1 = R ∧ G.Adj R m.2 then (t : ℂ) ^ 2 else 0) := by
    rintro ⟨x, y⟩
    have hRR : ¬ G.Adj R R := G.irrefl
    by_cases hy : y = R <;> by_cases hx : x = R
    · subst y x
      simp only [pairHopping, hRR, and_false, ↓reduceIte, add_zero, mul_zero]
    · subst y
      have hx' : R ≠ x := Ne.symm hx
      by_cases hadj : G.Adj R x
      · simp only [pairHopping, hadj, hadj.symm, hx, hx', and_true, false_and, ↓reduceIte,
          add_zero]
        exact hop_mul_reverse t A (hA x hadj)
      · have hadj' : ¬ G.Adj x R := fun h => hadj h.symm
        simp only [pairHopping, hadj, hadj', hx, hx', and_false, false_and, ↓reduceIte,
          add_zero, mul_zero]
    · subst x
      have hy' : R ≠ y := Ne.symm hy
      by_cases hadj : G.Adj R y
      · simp only [pairHopping, hadj, hadj.symm, hy, hy', and_true, false_and, ↓reduceIte,
          zero_add]
        exact hop_mul_reverse t A (hA y hadj)
      · have hadj' : ¬ G.Adj y R := fun h => hadj h.symm
        simp only [pairHopping, hadj, hadj', hy, hy', and_false, false_and, ↓reduceIte,
          add_zero, mul_zero]
    · have hx' : R ≠ x := Ne.symm hx
      have hy' : R ≠ y := Ne.symm hy
      simp only [pairHopping, hx, hy, hx', hy', false_and, ↓reduceIte, add_zero, mul_zero]
  unfold doublonSecondOrder
  rw [sum_congr rfl (fun m _ => key m), sum_subset (subset_univ _), sum_add_distrib,
    Fintype.sum_prod_type, Fintype.sum_prod_type_right (f := fun m : V × V =>
      if m.1 = R ∧ G.Adj R m.2 then (t : ℂ) ^ 2 else 0)]
  · simp only [ite_and, sum_ite_eq', mem_univ, ↓reduceIte, sum_ite_adj]
    ring
  · rintro ⟨x, y⟩ - hm
    have hxy : x = y := by simpa using hm
    subst hxy
    have hRR : ¬ G.Adj R R := G.irrefl
    by_cases hx : x = R
    · subst x
      simp only [hRR, and_false, ↓reduceIte, add_zero]
    · simp only [hx, false_and, ↓reduceIte, add_zero]

/-- On the `L × L` torus (`L ≥ 3`, degree 4) the doublon's second-order energy shift is
`8 t²/U`. -/
theorem doublonSecondOrder_self_torus {L : ℕ} (hL : 3 ≤ L) (t : ℝ)
    (A : Fin L × Fin L → Fin L × Fin L → ℝ) (U : ℝ) (R : Fin L × Fin L)
    (hA : ∀ x, (torus L).Adj R x → A x R = -A R x) :
    doublonSecondOrder (pairHopping (torus L) t A) U R R = 8 * (t : ℂ) ^ 2 / U := by
  rw [doublonSecondOrder_self _ _ _ U R hA]
  have h4 : ∀ z : ℕ, z = 4 → 2 * (z : ℂ) * (t : ℂ) ^ 2 / U = 8 * (t : ℂ) ^ 2 / U := by
    rintro z rfl
    push_cast
    ring
  exact h4 _ (torus_isRegularOfDegree_of_fintype L hL R)

end HubbardMoments
