/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus

/-!
# A finite grid net on the literal three-torus

The entropy step of `prop:particle-flow` quotes the Lipschitz entropy bound of
[HasselblattKatok02, Proposition 2.5.5]; the formalisation proves it through an *elementary
packing bound on `T³`*: a self-map whose iterates are Lipschitz with a
linearly growing constant admits dynamical covers of polynomially growing cardinality.  The
combinatorial half of that bound is the statement that the `N`-grid

```
  {(k₀/N, k₁/N, k₂/N) : 0 ≤ kⱼ < N}
```

is a `1/(2N)`-net of `Torus 3 = Fin 3 → UnitAddCircle` of cardinality at most `N³`.  This module
proves exactly that; `FastDynamo/Analysis/EntropyCriterion.lean` feeds it into Mathlib's
`Dynamics.coverEntropy`.

The three-torus carries the `Pi` (supremum) metric, so the net property is proved one coordinate
at a time and glued with `dist_pi_le_iff`.  In one coordinate the distance on `UnitAddCircle` is
the distance of a difference of representatives to the nearest integer,
`FastDynamo.LatticePeriodic.dist_unitAddCircle_coe` of
`FastDynamo/Analysis/LiteralThreeTorus.lean`, and the nearest grid point is obtained from `round`.

## Main declarations

* `torusGridPoint`, `torusGrid` — the grid and its indexing by `Fin 3 → Fin N`;
* `card_torusGrid_le` — the cardinality bound `#(torusGrid N) ≤ N ^ 3`;
* `exists_mem_torusGrid_dist_le` — the net property `∃ g ∈ torusGrid N, dist x g ≤ 1 / (2 * N)`.

Nothing here depends on the flow, on a velocity field, or on any measure; only the metric
structure of `Torus 3` is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The grid -/

/-- The grid point of `Torus 3` with coordinates `k j / N`, for a multi-index
`k : Fin 3 → Fin N`. -/
def torusGridPoint (N : ℕ) (k : Fin 3 → Fin N) : Torus 3 :=
  fun j => ((((k j : ℕ) : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)

open scoped Classical in
/-- The `N`-grid of the literal three-torus: the image of `Fin 3 → Fin N` under
`torusGridPoint N`.  It is the finite net used for the packing bound behind the entropy step of
`prop:particle-flow`. -/
def torusGrid (N : ℕ) : Finset (Torus 3) :=
  Finset.image (torusGridPoint N) Finset.univ

/-- Every grid point belongs to the grid. -/
theorem torusGridPoint_mem_torusGrid {N : ℕ} (k : Fin 3 → Fin N) :
    torusGridPoint N k ∈ torusGrid N := by
  classical
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ k, rfl⟩

/-- The `N`-grid has at most `N ^ 3` points. -/
theorem card_torusGrid_le (N : ℕ) : (torusGrid N).card ≤ N ^ 3 := by
  classical
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ]

/-! ## The net property -/

/-- One coordinate of the net property: every class on the unit circle is within `1 / (2 * N)`
of one of the `N` classes `k / N`, `0 ≤ k < N`.  The witness is `round (u * N)` reduced
modulo `N`. -/
theorem exists_dist_div_natCast_le {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ∃ k : Fin N,
      dist ((u : UnitAddCircle)) ((((k : ℕ) : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)
        ≤ 1 / (2 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set m : ℤ := round (u * N) with hm
  have hnn : 0 ≤ m % (N : ℤ) := Int.emod_nonneg m (by exact_mod_cast hN.ne')
  have hlt : (m % (N : ℤ)).toNat < N := by
    have h2 : m % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hN)
    omega
  refine ⟨⟨(m % (N : ℤ)).toNat, hlt⟩, ?_⟩
  have hk : ((((m % (N : ℤ)).toNat : ℕ) : ℝ)) = ((m % (N : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnn)
  have hsplit : (N : ℝ) * ((m / (N : ℤ) : ℤ) : ℝ) + ((m % (N : ℤ) : ℤ) : ℝ) = (m : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.mul_ediv_add_emod m (N : ℤ))
  have hq : ((m % (N : ℤ) : ℤ) : ℝ) / (N : ℝ)
      = (m : ℝ) / (N : ℝ) + (((-(m / (N : ℤ)) : ℤ) : ℝ)) := by
    push_cast
    field_simp
    linarith [hsplit]
  change dist ((u : UnitAddCircle))
      ((((((m % (N : ℤ)).toNat : ℕ) : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) ≤ 1 / (2 * N)
  rw [hk, hq]
  have hcoe : ((((m : ℝ) / (N : ℝ) + (((-(m / (N : ℤ)) : ℤ) : ℝ)) : ℝ)) : UnitAddCircle)
      = (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) :=
    LatticePeriodic.unitAddCircle_coe_add_intCast ((m : ℝ) / (N : ℝ)) (-(m / (N : ℤ) : ℤ))
  rw [hcoe]
  refine (dist_unitAddCircle_coe_le_abs_sub u ((m : ℝ) / (N : ℝ))).trans ?_
  have h1 : u - (m : ℝ) / (N : ℝ) = (u * (N : ℝ) - (m : ℝ)) / (N : ℝ) := by field_simp
  rw [h1, abs_div, abs_of_pos hN']
  have h2 : |u * (N : ℝ) - (m : ℝ)| ≤ 1 / 2 := by
    simpa [hm] using abs_sub_round (u * (N : ℝ))
  rw [div_le_div_iff₀ hN' (by positivity)]
  nlinarith [h2, hN']

/-- **The net property of the grid.**  For `N ≥ 1` every point of the literal three-torus lies
within `1 / (2 * N)` of a grid point, for the supremum metric of `Torus 3`.  This is the
elementary packing bound behind the entropy step of `prop:particle-flow`. -/
theorem exists_mem_torusGrid_dist_le {N : ℕ} (hN : 0 < N) (x : Torus 3) :
    ∃ g ∈ torusGrid N, dist x g ≤ 1 / (2 * N) := by
  choose u hu using fun j : Fin 3 => QuotientAddGroup.mk_surjective (x j)
  choose k hk using fun j : Fin 3 => exists_dist_div_natCast_le hN (u j)
  refine ⟨torusGridPoint N k, torusGridPoint_mem_torusGrid k, ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro j
  rw [← hu j]
  exact hk j

end

end FastDynamo
