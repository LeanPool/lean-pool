/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

/- Lean Pool adapted the import paths and clarified the theorem attribution. -/
module

public import LeanPool.KochenSpecker.Peres33
public import LeanPool.KochenSpecker.Cabello18

/-!
# The Kochen–Specker theorem

Kochen and Specker’s original obstruction (Theorem 1 of *The Problem of Hidden Variables in
Quantum Mechanics*) constructs a finite partial Boolean algebra of subspaces of `ℝ³`
with no homomorphism to the two-element Boolean algebra.

This development proves a vector-valuation formulation over `ℝ` and `ℂ` in every finite
dimension `d ≥ 3`: no Boolean map on vectors marks exactly one vector of each orthonormal basis.

* Dimension three is `Peres.not_isValuation_three` (Peres's 33 rays, a kernel-checked case split).
* `IsValuation.exists_subspace` restricts a valuation in dimension `d + 1` to the orthogonal
  complement of a unit vector where it is `false`; so `NoValuation.of_le` carries the theorem
  from dimension three to every larger dimension, for every inner product space, not only `𝕜ᵈ`.
* `kochen_specker_of_four_le` proves the case `d ≥ 4` a second way, from Cabello's 18 vectors by
  a parity count, with no computer search.
-/

@[expose] public section

open Module

namespace KochenSpecker

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

/-- No inner product space of dimension three carries a valuation. -/
theorem noValuation_three : NoValuation.{u} 𝕜 3 := by
  intro E _ _ hE v hv
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
  set φ := ((stdOrthonormalBasis 𝕜 E).reindex (finCongr hE)).repr
  exact Peres.not_isValuation_three _ (hv.map φ)

/-- No inner product space of dimension four carries a valuation (Cabello's parity argument). -/
theorem noValuation_four : NoValuation.{u} 𝕜 4 := by
  intro E _ _ hE v hv
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
  set φ := ((stdOrthonormalBasis 𝕜 E).reindex (finCongr hE)).repr
  exact Cabello.not_isValuation_four _ (hv.map φ)

/-- The vector-valuation obstruction in every inner product space of dimension `d ≥ 3`
over `ℝ` or `ℂ` (any `RCLike 𝕜`). -/
theorem not_isValuation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {d : ℕ}
    (hd : 3 ≤ d) (hE : finrank 𝕜 E = d) (v : E → Bool) : ¬ IsValuation 𝕜 d v :=
  noValuation_three.of_le (by norm_num) hd E hE v

/-- The vector-valuation formulation of the Kochen–Specker theorem in `𝕜ᵈ`. For `d ≥ 3`
and `𝕜 = ℝ` or `ℂ`, every Boolean map fails to mark exactly one vector in some
orthonormal basis. -/
theorem kochen_specker {d : ℕ} (hd : 3 ≤ d) :
    ¬ ∃ v : EuclideanSpace 𝕜 (Fin d) → Bool,
      ∀ b : OrthonormalBasis (Fin d) 𝕜 (EuclideanSpace 𝕜 (Fin d)), ∃! i, v (b i) = true :=
  fun ⟨v, hv⟩ => not_isValuation hd (by simp) v hv

/-- The case `d ≥ 4` of `kochen_specker`, proved from Cabello's 18 vectors by a parity count,
independently of Peres's rays and of any computer-generated certificate. -/
theorem kochen_specker_of_four_le {d : ℕ} (hd : 4 ≤ d) :
    ¬ ∃ v : EuclideanSpace 𝕜 (Fin d) → Bool,
      ∀ b : OrthonormalBasis (Fin d) 𝕜 (EuclideanSpace 𝕜 (Fin d)), ∃! i, v (b i) = true :=
  fun ⟨v, hv⟩ => noValuation_four.of_le (by norm_num) hd _ (by simp) v hv

end KochenSpecker
