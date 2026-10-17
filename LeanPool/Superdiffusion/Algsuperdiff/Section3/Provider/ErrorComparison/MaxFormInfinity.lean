/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-!
# MaxFormInfinity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the multiscale cube-maximum form at the endpoint `q = infinity`

```
lambda^{-1}_{s,q}(square_m; a) <= max_{z in 3^n Z^d cap square_m}
  lambda^{-1}_{s,q}(z + square_n; a)
```

## The endpoint display

The endpoint form reads, for every triadic cube `Q`, every `n <= Q.scale` and
every `t > 0`,

```
lambda^{-1}_{t,infinity}(Q; a)
  <= max_{R in descendantsAtScale Q n} lambda^{-1}_{t,infinity}(R; a) ,
Lambda_{t,infinity}(Q; a)
  <= max_{R in descendantsAtScale Q n} Lambda_{t,infinity}(R; a) .
```

At `Q = square_m` and `n < m` the index set `descendantsAtScale (square_m) n` is
the manuscript's `{z + square_n : z in 3^n Z^d cap square_m}`, so these are
exactly the manuscript's displays read at `q = infinity`.

## Why the endpoint form is true where the finite-`q` form is false

Write `M_j(P) := max_{depth-j descendants R of P} |sigma_*^{-1}(R; a)|`.  At
`q = infinity` the gauge is itself a *supremum* `sup_j 3^{-2sj} M_j(P)`, and
suprema commute with the two-level decomposition: splitting the scale index at
`n` turns `sup_j` over `Q` into `max_R sup_i` over the depth-`n` descendants
`R`, with the deep half priced by the two-level identity below and the shallow
half priced by the one-cube subadditivity `e.subadda.nosymm` at scale `n`.

## The missing CoarseGraining ingredient, supplied here

```
maxDescendant(Q, l) = max_{R in descendantsAtScale Q n} maxDescendant(R, l)
   for  l <= n <= Q.scale .
```

CoarseGraining exposes only the one-level recursion `descendantsAtDepth_succ`
and the transitivity `mem_descendantsAtScale_trans`; the converse factorization
is CoarseGraining's `exists_descendant_ancestor_at_depth`, transported to the
scale indexing by `exists_mem_descendantsAtScale_of_mem_descendantsAtScale`
below.  No CoarseGraining structural gap was found.

## Main results

* `exists_mem_descendantsAtScale_of_mem_descendantsAtScale`: the scale-indexed
  two-level factorization of triadic descendants.
* `le_finsetSupReal`: every value of a function on a `Finset` lies below its
  `finsetSupReal`.
* `rpow_three_add`: the base-`3` real power splits over a sum of exponents.

## References

* ABK26, the definitions (2.22)--(2.23), including
  `e.coarse.grained.ellipticity.infty`, `e.subadda.nosymm`, `l.bad.event.lemma`,
  case `n < m`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

variable {d : ℕ}

/-! ## A `finsetSupReal` helper -/

/-- Every value of a function on a `Finset` is below its `finsetSupReal`. -/
theorem le_finsetSupReal {α : Type*} (s : Finset α) (f : α → ℝ) {x : α}
    (hx : x ∈ s) : f x ≤ Book.Ch02.finsetSupReal s f := by
  unfold Book.Ch02.finsetSupReal
  exact le_csSup ((Set.toFinite _).image f).bddAbove ⟨x, hx, rfl⟩

/-! ## The two-level descendant factorization -/

/-- **Two-level factorization of triadic descendants.**  If `l <= n <= Q.scale`
then every descendant of `Q` at scale `l` is a descendant at scale `l` of some
descendant of `Q` at scale `n`.

This is the converse direction of CoarseGraining's
`mem_descendantsAtScale_trans`, and is the scale-indexed form of
CoarseGraining's depth-indexed `exists_descendant_ancestor_at_depth`. -/
theorem exists_mem_descendantsAtScale_of_mem_descendantsAtScale
    {Q S : TriadicCube d} {n l : ℤ} (hn : n ≤ Q.scale) (hln : l ≤ n)
    (hS : S ∈ descendantsAtScale Q l) :
    ∃ R ∈ descendantsAtScale Q n, S ∈ descendantsAtScale R l := by
  have hl : l ≤ Q.scale := hln.trans hn
  have hsplit :
      Int.toNat (Q.scale - l) =
        Int.toNat (Q.scale - n) + Int.toNat (n - l) := by
    have h1 : (0 : ℤ) ≤ Q.scale - n := sub_nonneg.mpr hn
    have h2 : (0 : ℤ) ≤ n - l := sub_nonneg.mpr hln
    rw [show Q.scale - l = Q.scale - n + (n - l) by ring, Int.toNat_add h1 h2]
  rw [descendantsAtScale_eq_descendantsAtDepth Q hl, hsplit] at hS
  obtain ⟨U, hU, hSU⟩ :=
    exists_descendant_ancestor_at_depth (Int.toNat (Q.scale - n))
      (Int.toNat (n - l)) hS
  have hUmem : U ∈ descendantsAtScale Q n := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hn]
    exact hU
  refine ⟨U, hUmem, ?_⟩
  have hUscale : U.scale = n :=
    HCPolySupport.descendant_scale_eq_of_mem_descendantsAtScale hUmem
  have hlU : l ≤ U.scale := by
    rw [hUscale]
    exact hln
  rw [descendantsAtScale_eq_descendantsAtDepth U hlU, hUscale]
  exact hSU

/-! ## Real-power bookkeeping for the base `3` -/

/-- The two opposite triadic weights cancel. -/
theorem rpow_three_add (y z : ℝ) :
    Real.rpow (3 : ℝ) (y + z) = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) z :=
  Real.rpow_add (by norm_num) y z

end Algsuperdiff.Section3.Provider.ErrorComparison
