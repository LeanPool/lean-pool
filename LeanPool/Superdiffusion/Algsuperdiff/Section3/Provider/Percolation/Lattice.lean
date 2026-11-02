/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.BigOperators

/-!
# Lattice

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Lattice paths and triadic cubes for the ABK26 percolation estimates

This module sets up the purely combinatorial geometry underlying the appendix
percolation estimates of ABK26, Section `s.percolation.estimate`.

ABK26 defines a *path* in `ℤ^d` to be a finite sequence `x₀, …, x_N`
with `dist (xᵢ, xᵢ₊₁) ≤ 1`, and it uses the triadic cubes `□_k =
(-3^k/2, 3^k/2)^d`.

## Choice of metric

The paper's global convention is that `dist` is the *Euclidean* distance. Here
we use instead the **sup metric** `latDist`, i.e. `ℓ^∞`. This is a deliberate
strengthening, not a weakening:

* every Euclidean-adjacent pair of sites is sup-adjacent, so the class of paths
  used here *contains* the paper's class, and any upper bound proved here for
  the event "a long path of bad sites exists" bounds the paper's event as well;
* the finite-range independence hypotheses are quantified over pairs of site
  sets at distance greater than a threshold, and sup-separation is a *stronger*
  requirement than Euclidean separation, so the hypotheses assumed here hold
  whenever the paper's do.

Consequently the sup-metric statements proved downstream imply the Euclidean
statements of ABK26. A further benefit is that on `ℤ^d` the sup distance is
`ℕ`-valued, which keeps the whole development free of square roots.

## Main definitions

* `Algsuperdiff.Section3.Provider.Percolation.latDist`: the `ℕ`-valued sup
  distance on the lattice `Fin d → ℤ`.
* `Algsuperdiff.Section3.Provider.Percolation.cubeAt`: the lattice points of the
  triadic cube `z + □_k`.
* `Algsuperdiff.Section3.Provider.Percolation.IsLatticePath`: the path predicate
  of ABK26, in the sup metric.

## Main results

* `latDist_triangle`, `coord_le_latDist`: the metric A.
* `mem_cubeAt_iff`: cube membership in terms of `latDist`.
* `IsLatticePath.latDist_start_succ_le`: the sup distance to the starting site
  increases by at most one per step.
* `exists_first_exit`: a path ending outside a cube has a first exit index —
  the site there is outside the cube and every earlier site is inside.

## References

* ABK26, `s.percolation.estimate`, paths, cubes, the Euclidean convention for
  `dist`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

variable {d : ℕ}

/-! ### The sup metric on the lattice -/

/-- The sup distance between two sites of the lattice `ℤ^d`, valued in `ℕ`. -/
def latDist (x y : Fin d → ℤ) : ℕ :=
  Finset.univ.sup fun j => (x j - y j).natAbs

/-- Each coordinate difference is bounded by the sup distance. -/
theorem coord_le_latDist (x y : Fin d → ℤ) (j : Fin d) :
    (x j - y j).natAbs ≤ latDist x y :=
  Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ j)

/-- The sup distance is bounded by `r` exactly when every coordinate difference is. -/
theorem latDist_le_iff {x y : Fin d → ℤ} {r : ℕ} :
    latDist x y ≤ r ↔ ∀ j, (x j - y j).natAbs ≤ r :=
  ⟨fun h j => le_trans (coord_le_latDist x y j) h, fun h => Finset.sup_le fun j _ => h j⟩

@[simp]
theorem latDist_self (x : Fin d → ℤ) : latDist x x = 0 :=
  Nat.le_zero.mp (Finset.sup_le fun j _ => by simp)

/-- The sup distance is symmetric. -/
theorem latDist_comm (x y : Fin d → ℤ) : latDist x y = latDist y x :=
  Finset.sup_congr rfl fun j _ => by rw [← Int.natAbs_neg, neg_sub]

/-- The triangle inequality for the sup distance. -/
theorem latDist_triangle (x y z : Fin d → ℤ) :
    latDist x z ≤ latDist x y + latDist y z := by
  refine Finset.sup_le fun j _ => ?_
  have hsplit : x j - z j = (x j - y j) + (y j - z j) :=
    (sub_add_sub_cancel (x j) (y j) (z j)).symm
  calc (x j - z j).natAbs
      ≤ (x j - y j).natAbs + (y j - z j).natAbs := by
        rw [hsplit]; exact Int.natAbs_add_le _ _
    _ ≤ latDist x y + latDist y z :=
        Nat.add_le_add (coord_le_latDist x y j) (coord_le_latDist y z j)

/-! ### Triadic cubes -/

/-- The lattice points of the triadic cube `z + □_k` of ABK26: `x` lies in it
exactly when `2 * |x j - z j| < 3 ^ k` in every coordinate `j`. -/
def cubeAt (k : ℕ) (z : Fin d → ℤ) : Set (Fin d → ℤ) :=
  {x | ∀ j, 2 * (x j - z j).natAbs < 3 ^ k}

theorem three_pow_pos (k : ℕ) : 0 < (3 : ℕ) ^ k := Nat.pow_pos (by omega)

/-- Membership in a triadic cube expressed through the sup distance. -/
theorem mem_cubeAt_iff {k : ℕ} {z x : Fin d → ℤ} :
    x ∈ cubeAt k z ↔ 2 * latDist z x < 3 ^ k := by
  have hpos := three_pow_pos k
  constructor
  · intro hx
    have hsup : latDist z x ≤ (3 ^ k - 1) / 2 :=
      Finset.sup_le fun j _ => by have := hx j; omega
    omega
  · intro hx j
    have hj := coord_le_latDist z x j
    omega

/-- A cube contains its own centre. -/
theorem self_mem_cubeAt (k : ℕ) (z : Fin d → ℤ) : z ∈ cubeAt k z := by
  have hpos := three_pow_pos k
  rw [mem_cubeAt_iff, latDist_self]
  omega

/-! ### Lattice paths -/

/-- ABK26: `x 0, …, x N` is a path when consecutive sites are at distance at
most one; here in the sup metric (see the module docstring). -/
def IsLatticePath (x : ℕ → Fin d → ℤ) (N : ℕ) : Prop :=
  ∀ i, i < N → latDist (x i) (x (i + 1)) ≤ 1

/-! ### Truncation at the first exit from a cube -/

/-- If a path ends outside the cube `z + □_k`, it has a first exit index `M`: the
site `x M` lies outside the cube and every earlier site lies inside. -/
theorem exists_first_exit {x : ℕ → Fin d → ℤ} {N k : ℕ} {z : Fin d → ℤ}
    (hout : x N ∉ cubeAt k z) :
    ∃ M, M ≤ N ∧ x M ∉ cubeAt k z ∧ ∀ i, i < M → x i ∈ cubeAt k z := by
  classical
  have hex : ∃ M, x M ∉ cubeAt k z := ⟨N, hout⟩
  refine ⟨Nat.find hex, Nat.find_le hout, Nat.find_spec hex, fun i hi => ?_⟩
  simpa using Nat.find_min hex hi



end Algsuperdiff.Section3.Provider.Percolation
