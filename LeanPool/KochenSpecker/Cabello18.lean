/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

/- Lean Pool adapted the import path for the valuation module. -/
module

public import LeanPool.KochenSpecker.Valuation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dimension four: Cabello's 18 vectors, by parity

Cabello, Estebaranz and García-Alcaine (*Bell-Kochen-Specker theorem: A proof with 18 vectors*,
Phys. Lett. A 212 (1996) 183) gave 18 vectors in `ℝ⁴`, with integer coordinates, forming 9
orthogonal bases in which every vector appears exactly twice. A valuation would make each basis
contribute exactly one `true`, nine in all, while each `true` vector is counted twice, an even
number. This proof uses no computer search.

The parity argument is `no_assignment`; `not_isValuation_four` turns it into the theorem in `𝕜⁴`
for every `RCLike 𝕜`. The combinatorial core was first written for the author's csd-lean4
(`Empirical/QM/Contextuality/KS18.lean`); this is a standalone version.
-/

@[expose] public section

open Module

namespace KochenSpecker.Cabello

/-- The 18 vectors. -/
def vecs : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0], ![0, 1, 0, 0], ![1, 0, 1, 0],
    ![1, 0, -1, 0], ![1, -1, 1, -1], ![1, -1, -1, 1], ![0, 0, 1, 1], ![1, 1, 1, 1],
    ![0, 1, 0, -1], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0], ![1, 1, -1, 1],
    ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- The 9 bases, as four vector indices each. -/
def bases : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3], ![0, 4, 5, 6], ![2, 7, 8, 9], ![6, 7, 10, 11], ![1, 4, 12, 13],
    ![8, 10, 13, 14], ![3, 9, 15, 16], ![5, 11, 15, 17], ![12, 14, 16, 17]]

/-- The integer dot product. -/
def dot (x y : Fin 4 → ℤ) : ℤ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

theorem bases_orth : ∀ B : Fin 9, ∀ i j : Fin 4, i ≠ j →
    dot (vecs (bases B i)) (vecs (bases B j)) = 0 := by decide

theorem dot_self_pos : ∀ n : Fin 18, 0 < dot (vecs n) (vecs n) := by decide

/-- Every vector appears in exactly two of the 36 basis slots. -/
theorem appears_twice : ∀ n : Fin 18,
    (Finset.univ.filter (fun p : Fin 9 × Fin 4 => bases p.1 p.2 = n)).card = 2 := by decide

/-- **The parity argument.** No assignment gives exactly one `true` in each of the 9 bases. -/
theorem no_assignment (c : Fin 18 → Bool)
    (h : ∀ B, (Finset.univ.filter (fun i : Fin 4 => c (bases B i) = true)).card = 1) : False := by
  set S := Finset.univ.filter (fun p : Fin 9 × Fin 4 => c (bases p.1 p.2) = true)
  set T := Finset.univ.filter (fun n : Fin 18 => c n = true)
  -- Basis by basis, the `true` slots number nine.
  have h9 : S.card = 9 := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp only [← Finset.card_filter, h]
    simp
  -- Vector by vector, each `true` vector fills two slots.
  have h2 : S.card = 2 * T.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin 9 × Fin 4 => bases p.1 p.2) (t := T)
      (fun p hp => by simpa [S, T] using hp)]
    rw [Finset.sum_congr rfl (g := fun _ => 2) (fun n hn => ?_), Finset.sum_const, smul_eq_mul,
      mul_comm]
    have hn' : c n = true := by simpa [T] using hn
    rw [← appears_twice n]
    congr 1
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hp
    rw [hp]
    exact hn'
  omega

/-! ### From the vectors to unit vectors of `𝕜⁴` -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A vector of `𝕜⁴` with integer coordinates. -/
def vec (x : Fin 4 → ℤ) : EuclideanSpace 𝕜 (Fin 4) := WithLp.toLp 2 (fun k => ((x k : ℤ) : 𝕜))

theorem inner_vec (x y : Fin 4 → ℤ) : inner 𝕜 (vec (𝕜 := 𝕜) x) (vec y) = ((dot x y : ℤ) : 𝕜) := by
  simp only [vec, PiLp.inner_apply, RCLike.inner_apply', map_intCast, Fin.sum_univ_four, dot]
  push_cast
  ring

theorem vec_ne_zero (n : Fin 18) : vec (𝕜 := 𝕜) (vecs n) ≠ 0 := by
  intro h0
  have h := inner_vec (𝕜 := 𝕜) (vecs n) (vecs n)
  rw [h0, inner_zero_left] at h
  have : ((dot (vecs n) (vecs n) : ℤ) : 𝕜) ≠ 0 := by exact_mod_cast (dot_self_pos n).ne'
  exact this h.symm

/-- The `n`-th vector, normalised. -/
noncomputable def unit (n : Fin 18) : EuclideanSpace 𝕜 (Fin 4) :=
  (‖vec (𝕜 := 𝕜) (vecs n)‖⁻¹ : 𝕜) • vec (vecs n)

theorem norm_unit (n : Fin 18) : ‖unit (𝕜 := 𝕜) n‖ = 1 := norm_smul_inv_norm (vec_ne_zero n)

/-- Each of the 9 bases, normalised, is orthonormal. -/
theorem orthonormal_basis (B : Fin 9) : Orthonormal 𝕜 (fun i => unit (𝕜 := 𝕜) (bases B i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  split_ifs with hij
  · subst hij
    rw [inner_self_eq_norm_sq_to_K, norm_unit]
    simp
  · simp [unit, inner_smul_left, inner_smul_right, inner_vec, bases_orth B i j hij]

/-- **The Kochen–Specker theorem in `𝕜⁴`**, by Cabello's parity argument. -/
theorem not_isValuation_four (v : EuclideanSpace 𝕜 (Fin 4) → Bool) : ¬ IsValuation 𝕜 4 v := by
  intro hv
  refine no_assignment (fun n => v (unit n)) (fun B => ?_)
  obtain ⟨i, hi, hu⟩ := hv.existsUnique_of_orthonormal (by simp) (orthonormal_basis B)
  rw [Finset.card_eq_one]
  exact ⟨i, by ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]; exact ⟨hu j, fun e => e ▸ hi⟩⟩

end KochenSpecker.Cabello
