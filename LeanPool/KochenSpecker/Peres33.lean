/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

/- Lean Pool adapted the imports and replaced the case-split certificate. -/
module

public import LeanPool.KochenSpecker.Checker
public import LeanPool.KochenSpecker.Valuation
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Dimension three: Peres's 33 rays

Peres (*Two simple proofs of the Kochen-Specker theorem*, J. Phys. A 24 (1991) L175) gave 33 rays
in `ℝ³`: the coordinate permutations and sign changes of `(0, 0, 1)`, `(0, 1, 1)`, `(0, 1, √2)`
and `(1, 1, √2)`, one vector per ray. Coordinates are kept exactly, as pairs `(a, b)` of integers
meaning `a + b √2`, so orthogonality is an integer computation.

They have 72 orthogonal pairs and 16 orthogonal triads (`sys`, checked by `pair_orth` and
`triad_orth`), and no colouring: `check_ok` runs a case-split certificate through
`KochenSpecker.Checker` in the kernel. Unit propagation and branching on active clauses generate
the tree.

`not_isValuation_three` turns this into the theorem in `𝕜³` for every `RCLike 𝕜` (so for `ℝ³`
and `ℂ³`): a valuation would colour the normalised rays, since each orthogonal triad is an
orthonormal basis (exactly one `true`) and each orthogonal pair extends to one (at most one
`true`).
-/

@[expose] public section

open Module

namespace KochenSpecker.Peres

-- Exact ray data from the upstream scripts/peres33.py
/-- Peres's 33 rays, coordinates `(a, b)` meaning `a + b √2`. -/
def rays : List (Fin 3 → ℤ × ℤ) := [
  ![(0, 0), (0, 0), (1, 0)],
  ![(0, 0), (1, 0), (0, 0)],
  ![(1, 0), (0, 0), (0, 0)],
  ![(0, 0), (1, 0), (1, 0)],
  ![(0, 0), (1, 0), (-1, 0)],
  ![(1, 0), (0, 0), (1, 0)],
  ![(1, 0), (0, 0), (-1, 0)],
  ![(1, 0), (1, 0), (0, 0)],
  ![(1, 0), (-1, 0), (0, 0)],
  ![(0, 0), (1, 0), (0, 1)],
  ![(0, 0), (1, 0), (0, -1)],
  ![(0, 0), (0, 1), (1, 0)],
  ![(0, 0), (0, 1), (-1, 0)],
  ![(1, 0), (0, 0), (0, 1)],
  ![(1, 0), (0, 0), (0, -1)],
  ![(1, 0), (0, 1), (0, 0)],
  ![(1, 0), (0, -1), (0, 0)],
  ![(0, 1), (0, 0), (1, 0)],
  ![(0, 1), (0, 0), (-1, 0)],
  ![(0, 1), (1, 0), (0, 0)],
  ![(0, 1), (-1, 0), (0, 0)],
  ![(1, 0), (1, 0), (0, 1)],
  ![(1, 0), (1, 0), (0, -1)],
  ![(1, 0), (-1, 0), (0, 1)],
  ![(1, 0), (-1, 0), (0, -1)],
  ![(1, 0), (0, 1), (1, 0)],
  ![(1, 0), (0, 1), (-1, 0)],
  ![(1, 0), (0, -1), (1, 0)],
  ![(1, 0), (0, -1), (-1, 0)],
  ![(0, 1), (1, 0), (1, 0)],
  ![(0, 1), (1, 0), (-1, 0)],
  ![(0, 1), (-1, 0), (1, 0)],
  ![(0, 1), (-1, 0), (-1, 0)]
]

/-- The orthogonal pairs and triads of `rays`, by index. -/
def sys : Constraints where
  pairs := [(0, 1), (0, 2), (0, 7), (0, 8), (0, 15), (0, 16), (0, 19), (0, 20), (1, 2), (1, 5), (1,
    6), (1, 13), (1, 14), (1, 17), (1, 18), (2, 3), (2, 4), (2, 9), (2, 10), (2, 11), (2, 12), (3,
    4), (3, 30), (3, 31), (4, 29), (4, 32), (5, 6), (5, 26), (5, 28), (6, 25), (6, 27), (7, 8), (7,
    23), (7, 24), (8, 21), (8, 22), (9, 12), (9, 26), (9, 27), (10, 11), (10, 25), (10, 28), (11,
    22), (11, 23), (12, 21), (12, 24), (13, 18), (13, 30), (13, 32), (14, 17), (14, 29), (14, 31),
    (15, 20), (15, 31), (15, 32), (16, 19), (16, 29), (16, 30), (17, 22), (17, 24), (18, 21), (18,
    23), (19, 27), (19, 28), (20, 25), (20, 26), (21, 22), (23, 24), (25, 27), (26, 28), (29, 32),
    (30, 31)]
  triads := [(0, 1, 2), (0, 7, 8), (0, 15, 20), (0, 16, 19), (1, 5, 6), (1, 13, 18), (1, 14, 17),
    (2, 3, 4), (2, 9, 12), (2, 10, 11), (3, 30, 31), (4, 29, 32), (5, 26, 28), (6, 25, 27), (7, 23,
    24), (8, 21, 22)]

/-- A case-split refutation of every colouring of `sys`, with branches chosen by
unit propagation and the number of remaining literals in active clauses. -/
def cert : Refutation :=
  (.branch 2 (.branch 1 .close (.branch 9 .close (.branch 10 .close (.branch 4 .close (.branch 0
    .close (.branch 3 .close (.branch 12 .close (.branch 11 .close (.branch 31 (.branch 15 .close
    (.branch 14 .close (.branch 20 (.branch 17 (.branch 24 .close (.branch 30 .close (.branch 26
    .close (.branch 22 .close (.branch 25 .close (.branch 19 (.branch 27 .close (.branch 28 .close
    (.branch 5 (.branch 6 .close .close) .close))) (.branch 16 (.branch 29 .close (.branch 32
    (.branch 13 .close (.branch 18 (.branch 21 .close (.branch 23 .close (.branch 8 (.branch 7
    .close .close) .close))) .close)) .close)) .close))))))) .close) .close))) (.branch 30 (.branch
    13 .close (.branch 18 (.branch 21 .close (.branch 23 .close (.branch 16 .close (.branch 19
    (.branch 28 .close (.branch 27 .close (.branch 17 (.branch 24 .close (.branch 14 .close (.branch
    22 .close (.branch 7 (.branch 8 .close .close) .close)))) (.branch 14 (.branch 29 .close
    (.branch 32 (.branch 15 .close (.branch 20 (.branch 26 .close (.branch 25 .close (.branch 6
    (.branch 5 .close .close) .close))) .close)) .close)) .close)))) .close)))) .close))
    .close)))))))))) (.branch 1 (.branch 6 .close (.branch 5 .close (.branch 0 .close (.branch 18
    .close (.branch 14 .close (.branch 13 .close (.branch 17 .close (.branch 28 (.branch 26 .close
    (.branch 10 .close (.branch 19 .close (.branch 16 (.branch 29 .close (.branch 30 .close (.branch
    11 (.branch 23 .close (.branch 22 .close (.branch 12 (.branch 9 .close (.branch 24 .close
    (.branch 7 (.branch 21 .close (.branch 8 .close .close)) .close))) (.branch 9 (.branch 27 .close
    (.branch 25 (.branch 20 .close (.branch 15 (.branch 31 .close (.branch 32 .close (.branch 3
    (.branch 4 .close .close) .close))) .close)) .close)) .close)))) .close))) .close)))) (.branch
    26 (.branch 9 .close (.branch 12 (.branch 20 .close (.branch 21 .close (.branch 15 (.branch 24
    .close (.branch 32 .close (.branch 31 .close (.branch 16 (.branch 29 .close (.branch 30 .close
    (.branch 4 (.branch 19 .close (.branch 3 .close .close)) .close))) (.branch 19 (.branch 27
    .close (.branch 25 (.branch 10 .close (.branch 11 (.branch 22 .close (.branch 8 (.branch 7
    .close (.branch 23 .close .close)) .close)) .close)) .close)) .close))))) .close))) .close))
    .close))))))))) (.branch 0 (.branch 8 .close (.branch 7 .close (.branch 20 .close (.branch 16
    .close (.branch 15 .close (.branch 19 .close (.branch 22 (.branch 21 .close (.branch 11 .close
    (.branch 17 .close (.branch 10 (.branch 14 (.branch 25 .close (.branch 28 .close (.branch 31
    .close (.branch 29 .close (.branch 9 (.branch 12 .close (.branch 26 .close (.branch 27 .close
    (.branch 6 (.branch 5 .close .close) .close)))) (.branch 12 (.branch 24 .close (.branch 23
    (.branch 18 .close (.branch 13 (.branch 30 .close (.branch 32 .close (.branch 3 (.branch 4
    .close .close) .close))) .close)) .close)) .close)))))) .close) .close)))) (.branch 21 (.branch
    18 .close (.branch 12 .close (.branch 13 (.branch 9 (.branch 30 .close (.branch 26 .close
    (.branch 27 .close (.branch 32 .close (.branch 3 (.branch 4 .close (.branch 31 .close (.branch
    29 (.branch 14 .close (.branch 17 (.branch 24 .close (.branch 23 (.branch 11 .close (.branch 10
    (.branch 28 .close (.branch 5 (.branch 25 .close (.branch 6 .close .close)) .close)) .close))
    .close)) .close)) .close))) (.branch 31 (.branch 14 .close (.branch 4 (.branch 29 .close
    (.branch 17 (.branch 24 .close (.branch 23 (.branch 11 .close (.branch 10 (.branch 28 .close
    (.branch 25 .close (.branch 6 (.branch 5 .close .close) .close))) .close)) .close)) .close))
    .close)) .close)))))) .close) .close))) .close)))))))) .close)))

/-- The `n`-th ray. -/
def ray (n : ℕ) : Fin 3 → ℤ × ℤ := rays.getD n (fun _ => (0, 0))

/-- The inner product of two rays, as `(a, b)` meaning `a + b √2`. -/
def ipZ (x y : Fin 3 → ℤ × ℤ) : ℤ × ℤ :=
  ((x 0).1 * (y 0).1 + 2 * (x 0).2 * (y 0).2 + (x 1).1 * (y 1).1 + 2 * (x 1).2 * (y 1).2 +
      (x 2).1 * (y 2).1 + 2 * (x 2).2 * (y 2).2,
    (x 0).1 * (y 0).2 + (x 0).2 * (y 0).1 + (x 1).1 * (y 1).2 + (x 1).2 * (y 1).1 +
      (x 2).1 * (y 2).2 + (x 2).2 * (y 2).1)

theorem rays_length : rays.length = 33 := by decide

/-- Every listed pair is orthogonal. -/
theorem pair_orth : ∀ p ∈ sys.pairs, ipZ (ray p.1) (ray p.2) = (0, 0) := by decide

/-- Every listed triad is pairwise orthogonal. -/
theorem triad_orth : ∀ t ∈ sys.triads, ipZ (ray t.1) (ray t.2.1) = (0, 0) ∧
    ipZ (ray t.1) (ray t.2.2) = (0, 0) ∧ ipZ (ray t.2.1) (ray t.2.2) = (0, 0) := by decide

/-- Each ray has squared length a positive integer: `ipZ r r = (m, 0)` with `0 < m`. -/
theorem self_pos : ∀ n < 33, (ipZ (ray n) (ray n)).2 = 0 ∧ 0 < (ipZ (ray n) (ray n)).1 := by
  decide

/-- **No colouring of Peres's rays**, checked by the kernel. -/
theorem check_ok : refutes sys [] cert = true := by decide

theorem pair_lt : ∀ p ∈ sys.pairs, p.1 < 33 ∧ p.2 < 33 := by decide

theorem triad_lt : ∀ t ∈ sys.triads, t.1 < 33 ∧ t.2.1 < 33 ∧ t.2.2 < 33 := by decide

/-! ### From rays to unit vectors of `𝕜³` -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `a + b √2`. -/
noncomputable def toR (z : ℤ × ℤ) : ℝ := z.1 + z.2 * √2

/-- A ray as a vector of `𝕜³`. -/
noncomputable def vec (x : Fin 3 → ℤ × ℤ) : EuclideanSpace 𝕜 (Fin 3) :=
  WithLp.toLp 2 (fun k => ((toR (x k) : ℝ) : 𝕜))

theorem inner_vec (x y : Fin 3 → ℤ × ℤ) :
    inner 𝕜 (vec (𝕜 := 𝕜) x) (vec y) = (((ipZ x y).1 + (ipZ x y).2 * √2 : ℝ) : 𝕜) := by
  have h2 : ((√2 : ℝ) : 𝕜) ^ 2 = 2 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : 𝕜)) (Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num))
  simp only [vec, PiLp.inner_apply, RCLike.inner_apply', RCLike.conj_ofReal,
    Fin.sum_univ_three, toR, ipZ]
  push_cast
  linear_combination
    (((x 0).2 : 𝕜) * (y 0).2 + ((x 1).2 : 𝕜) * (y 1).2 + ((x 2).2 : 𝕜) * (y 2).2) * h2

theorem inner_vec_eq_zero {x y : Fin 3 → ℤ × ℤ} (h : ipZ x y = (0, 0)) :
    inner 𝕜 (vec (𝕜 := 𝕜) x) (vec y) = 0 := by
  rw [inner_vec, h]
  simp

theorem vec_ne_zero {n : ℕ} (hn : n < 33) : vec (𝕜 := 𝕜) (ray n) ≠ 0 := by
  intro h0
  have h := inner_vec (𝕜 := 𝕜) (ray n) (ray n)
  rw [h0, inner_zero_left, (self_pos n hn).1] at h
  have hm := (self_pos n hn).2
  have : ((((ipZ (ray n) (ray n)).1 : ℝ)) : 𝕜) ≠ 0 := by
    rw [RCLike.ofReal_ne_zero]
    exact_mod_cast hm.ne'
  apply this
  rw [h]
  simp

/-- The `n`-th ray, normalised. -/
noncomputable def unit (n : ℕ) : EuclideanSpace 𝕜 (Fin 3) :=
  (‖vec (𝕜 := 𝕜) (ray n)‖⁻¹ : 𝕜) • vec (ray n)

theorem norm_unit {n : ℕ} (hn : n < 33) : ‖unit (𝕜 := 𝕜) n‖ = 1 :=
  norm_smul_inv_norm (vec_ne_zero hn)

theorem inner_unit_eq_zero {m n : ℕ} (h : ipZ (ray m) (ray n) = (0, 0)) :
    inner 𝕜 (unit (𝕜 := 𝕜) m) (unit n) = 0 := by
  simp [unit, inner_smul_left, inner_smul_right, inner_vec_eq_zero h]

theorem inner_unit_self {n : ℕ} (hn : n < 33) : inner 𝕜 (unit (𝕜 := 𝕜) n) (unit n) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_unit hn]
  simp

/-! ### A valuation colours the rays -/

/-- Exactly one of three values is `true`. -/
theorem exactlyOne_of_existsUnique {α : Type*} {g : Fin 3 → α} {w : α → Bool}
    (h : ∃! i, w (g i) = true) :
    (w (g 0) && !w (g 1) && !w (g 2)) || (!w (g 0) && w (g 1) && !w (g 2)) ||
      (!w (g 0) && !w (g 1) && w (g 2)) = true := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j, w (g j) = true ↔ j = i := fun j => ⟨hu j, fun e => e ▸ hi⟩
  have e0 := key 0
  have e1 := key 1
  have e2 := key 2
  generalize w (g 0) = a at e0 ⊢
  generalize w (g 1) = b at e1 ⊢
  generalize w (g 2) = c at e2 ⊢
  revert e0 e1 e2
  fin_cases i <;> revert a b c <;> decide

/-- A valuation of `𝕜³` colours Peres's system. -/
theorem colours_of_isValuation {v : EuclideanSpace 𝕜 (Fin 3) → Bool}
    (hv : IsValuation 𝕜 3 v) : Colours sys (fun n => v (unit n)) := by
  have hE : finrank 𝕜 (EuclideanSpace 𝕜 (Fin 3)) = 1 + 2 := by simp
  refine ⟨fun p hp => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, h2⟩ := pair_lt p hp
    exact hv.not_both (n := 1) hE (norm_unit h1) (norm_unit h2)
      (inner_unit_eq_zero (pair_orth p hp))
  · obtain ⟨h1, h2, h3⟩ := triad_lt t ht
    obtain ⟨o12, o13, o23⟩ := triad_orth t ht
    have hf : Orthonormal 𝕜 ![unit (𝕜 := 𝕜) t.1, unit t.2.1, unit t.2.2] := by
      rw [orthonormal_iff_ite]
      have s12 := inner_eq_zero_symm.1 (inner_unit_eq_zero (𝕜 := 𝕜) o12)
      have s13 := inner_eq_zero_symm.1 (inner_unit_eq_zero (𝕜 := 𝕜) o13)
      have s23 := inner_eq_zero_symm.1 (inner_unit_eq_zero (𝕜 := 𝕜) o23)
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [norm_unit h1, norm_unit h2, norm_unit h3, inner_unit_eq_zero o12,
          inner_unit_eq_zero o13, inner_unit_eq_zero o23, s12, s13, s23]
    simpa using exactlyOne_of_existsUnique (hv.existsUnique_of_orthonormal (by simp) hf)

/-- **The Kochen–Specker theorem in `𝕜³`.** -/
theorem not_isValuation_three (v : EuclideanSpace 𝕜 (Fin 3) → Bool) : ¬ IsValuation 𝕜 3 v :=
  fun hv => no_colouring_of_refutes sys cert check_ok ⟨_, colours_of_isValuation hv⟩

end KochenSpecker.Peres
