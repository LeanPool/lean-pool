/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.GetD
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Lattice
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Lattice

/-!
# LatticeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Two readings of a crossing of the annulus `□_k → □_{k+1}^c`

A crossing of the lattice annulus is written in two ways in this development.

* As a **function** `x : ℕ → Fin d → ℤ` together with a length `N`, with
  consecutive sites at sup distance at most one (`IsLatticePath`), starting in
  the cube `□_k` and ending outside `□_{k+1}`.  This is the reading of the
  source: a step may stay put, so a site may be repeated.
* As a **list** `Γ : List (Fin d → ℤ)` of strictly adjacent sites with the same
  endpoint conditions (`IsPathFrom k`).  This is the reading of the percolation
  path estimate.

The two readings describe the same crossings once the count attached to a
crossing is a count of *distinct sites*: deleting the repetitions of a
functional crossing changes neither its endpoints nor its set of sites.  This
file proves that equivalence, and records the geometric consequence that a
crossing visits at least `3 ^ k + 2` distinct sites.

## Main definitions

* `pathSites N x` — the set of sites visited by `x` on `{0, …, N}`.

## Main results

* `exists_isPathFrom_of_isLatticePath`, `exists_isLatticePath_of_isPathFrom` —
  the two directions of the translation, each preserving the set of sites.
* `exists_crossing_iff` — the resulting equivalence for any property of the set
  of sites.

## References

* ABK26, the percolation estimate for bad cubes.
-/

namespace Algsuperdiff.Section5.Percolation

open Algsuperdiff.Section3.Provider.Percolation

variable {d : ℕ}

/-! ## 1. The two lattices agree -/

/-- The two sup distances on the lattice are the same function. -/
theorem siteDist_eq_latDist (x y : Site d) : siteDist x y = latDist x y := rfl

/-- Membership in the centred cube agrees with membership in the cube at the
origin. -/
theorem inCube_iff_mem_cubeAt {k : ℕ} {x : Site d} :
    inCube k x ↔ x ∈ cubeAt k (0 : Site d) := by
  simp [inCube, cubeAt]

/-! ## 2. The sites of a functional crossing -/

/-- The set of sites visited by `x` on `{0, …, N}`. -/
def pathSites (N : ℕ) (x : ℕ → Site d) : Finset (Site d) :=
  (Finset.range (N + 1)).image x

theorem mem_pathSites {N : ℕ} {x : ℕ → Site d} {z : Site d} :
    z ∈ pathSites N x ↔ ∃ i ≤ N, x i = z := by
  simp [pathSites, Nat.lt_succ_iff]

/-! ## 3. From a functional crossing to a list crossing -/

theorem exists_isPathFrom_of_isLatticePath {k N : ℕ} {x : ℕ → Site d}
    (hpath : IsLatticePath x N) (h0 : x 0 ∈ cubeAt k (0 : Site d))
    (hN : x N ∉ cubeAt (k + 1) (0 : Site d)) :
    ∃ Γ : List (Site d), IsPathFrom k Γ ∧ Γ.toFinset = pathSites N x := by
  classical
  set f : Fin (N + 1) → Site d := fun i => x i with hf
  have hweak : IsWeakPath (List.ofFn f) := by
    refine List.isChain_ofFn.mpr ?_
    intro i hi
    exact hpath i (by omega)
  have hne : List.ofFn f ≠ [] := by simp
  have hhead : (List.ofFn f).head? = some (x 0) := by
    rw [List.ofFn_succ]
    rfl
  have hlast : (List.ofFn f).getLast? = some (x N) := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne, List.getLast_ofFn_succ]
    rfl
  have htoFinset : (List.ofFn f).toFinset = pathSites N x := by
    ext z
    simp only [List.mem_toFinset, List.mem_ofFn, mem_pathSites, hf]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, rfl⟩
  obtain ⟨Delta, hDelta, hDeltaFinset⟩ :=
    exists_isPathFrom_of_isWeakPath hweak hhead hlast
      (inCube_iff_mem_cubeAt.mpr h0) (fun h => hN (inCube_iff_mem_cubeAt.mp h))
  exact ⟨Delta, hDelta, by rw [hDeltaFinset, htoFinset]⟩

/-! ## 4. From a list crossing to a functional crossing -/

theorem exists_isLatticePath_of_isPathFrom {k : ℕ} {Γ : List (Site d)}
    (hΓ : IsPathFrom k Γ) :
    ∃ (N : ℕ) (x : ℕ → Site d), IsLatticePath x N ∧
      x 0 ∈ cubeAt k (0 : Site d) ∧ x N ∉ cubeAt (k + 1) (0 : Site d) ∧
        pathSites N x = Γ.toFinset := by
  classical
  cases Γ with
  | nil => exact absurd hΓ not_false
  | cons z zs =>
      obtain ⟨hpath, hz, hlast⟩ := hΓ
      refine ⟨zs.length, fun i => (z :: zs).getD i z, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hi1 : i + 1 < (z :: zs).length := by simp; omega
        have hi0 : i < (z :: zs).length := by omega
        change latDist ((z :: zs).getD i z) ((z :: zs).getD (i + 1) z) ≤ 1
        rw [List.getD_eq_getElem _ _ hi0, List.getD_eq_getElem _ _ hi1]
        have := hpath.getElem i hi1
        change latDist _ _ ≤ 1
        rw [← siteDist_eq_latDist]
        exact le_of_eq this
      · change (z :: zs).getD 0 z ∈ cubeAt k (0 : Site d)
        rw [List.getD_cons_zero]
        exact inCube_iff_mem_cubeAt.mp hz
      · change (z :: zs).getD zs.length z ∉ cubeAt (k + 1) (0 : Site d)
        have hlen : zs.length < (z :: zs).length := by simp
        rw [List.getD_eq_getElem _ _ hlen]
        have hgl : (z :: zs).getLast (List.cons_ne_nil z zs) = (z :: zs)[zs.length] := by
          rw [List.getLast_eq_getElem]
          simp
        intro hmem
        exact hlast (inCube_iff_mem_cubeAt.mpr (by rw [hgl]; exact hmem))
      · ext w
        rw [mem_pathSites, List.mem_toFinset, List.mem_iff_getElem]
        constructor
        · rintro ⟨i, hi, rfl⟩
          have hi' : i < (z :: zs).length := by simp; omega
          exact ⟨i, hi', (List.getD_eq_getElem _ _ hi').symm⟩
        · rintro ⟨i, hi, rfl⟩
          have hi' : i ≤ zs.length := by simp at hi; omega
          exact ⟨i, hi', List.getD_eq_getElem _ _ hi⟩

/-- **The two readings of a crossing agree**, for any property of the set of
sites visited. -/
theorem exists_crossing_iff (k : ℕ) (P : Finset (Site d) → Prop) :
    (∃ (N : ℕ) (x : ℕ → Site d), IsLatticePath x N ∧
        x 0 ∈ cubeAt k (0 : Site d) ∧ x N ∉ cubeAt (k + 1) (0 : Site d) ∧
          P (pathSites N x)) ↔
      ∃ Γ : List (Site d), IsPathFrom k Γ ∧ P Γ.toFinset := by
  constructor
  · rintro ⟨N, x, hpath, h0, hN, hP⟩
    obtain ⟨Γ, hΓ, hfinset⟩ := exists_isPathFrom_of_isLatticePath hpath h0 hN
    exact ⟨Γ, hΓ, by rw [hfinset]; exact hP⟩
  · rintro ⟨Γ, hΓ, hP⟩
    obtain ⟨N, x, hpath, h0, hN, hfinset⟩ := exists_isLatticePath_of_isPathFrom hΓ
    exact ⟨N, x, hpath, h0, hN, by rw [hfinset]; exact hP⟩

end Algsuperdiff.Section5.Percolation
