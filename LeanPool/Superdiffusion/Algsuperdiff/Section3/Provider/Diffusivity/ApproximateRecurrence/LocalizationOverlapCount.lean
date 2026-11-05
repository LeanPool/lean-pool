/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationCubeFamily

/-!
# LocalizationOverlapCount

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the bounded-overlap count for the meso windows

Source displays in ABK26:

* `e.nablaw.oscillations` (label; display) is stated at a mesh point `z in 3^n
  Zd cap cu_K` and involves the *outer window* `z + cu_{m-h}`, of side
  `3^{m-h}`, which is much larger than the mesh spacing `3^n`;
* `e.lower.bound.oscillations` (label; display) averages the resulting quantity
  over the whole mesh `z in 3^n Zd cap cu_K`.

Because the window scale `m - h` exceeds the mesh scale `n`, the windows
`z + cu_{m-h}` attached to distinct mesh points **overlap**.  The tiling identity
`cubeAverage_originCube_eq_mesoGridAverage` of `LocalizationGrid` is a partition
statement about the scale-`n` *tiles* `z + cu_n` and says nothing about the
windows.  This module supplies the missing combinatorial input: the exact
multiplicity of the overlapping window family.

## What is proved

Write `N = m - h - n` for the gap, so the window at the site `z` is
`z + cu_{n+N} = openCubeAtScale z (n + N)`, and let `I` be any finite family of
scale-`n` triadic cubes, each contributing the window based at its own site
`z = triadicCubeShift R`.

* `card_filter_mem_openCubeAtScale_le` -- **the overlap count.**  For every point
  `x`, the number of members of `I` whose window contains `x` is at most
  `(3^N)^d`.  The proof is one-dimensional and exact: a window contains `x` iff
  the cube's `i`-th index lies in an open real interval of length exactly `3^N`,
  and such an interval contains at most `3^N` integers.
* `sum_indicator_openCubeAtScale_le` -- the same statement as a pointwise bound
  on the sum of the window indicators, which is the form the integral transfer
  consumes.  Since it is stated at an arbitrary finite family of scale-`n`
  cubes, it applies verbatim to the meso grid and to the interior meso grid of
  `LocalizationGrid`, whose members all have scale `n` by construction.

## Divergences from the printed statement

* The count below is proved for any finite family of cubes of a common scale,
  so it covers `mesoCubeGrid`, `interiorMesoCubeGrid` and any subfamily of
  either.
* **The count is not clipped to `cu_K`.**  The bound `(3^N)^d` is the full
  lattice multiplicity; restricting the family to `cu_K` can only decrease it.
  It is also the exact multiplicity, since `(3^N)^d` scale-`n` cubes can have
  windows sharing a common point, so the volume-normalized transfer constant
  produced from it (module `LocalizationOverlapTransfer`) cannot be improved by
  sharpening the count.  That sharpness is a remark about the lattice, not a
  theorem of this module.
* **Nothing here is an average.**  This module is pure counting; the passage from
  the count to a normalized average, including the interior-grid deficit, is the
  separate module `LocalizationOverlapTransfer`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The one-dimensional interval of admissible indices -/

/-- The right endpoint of the open interval of admissible `i`-th indices: a cube
of scale `n` and `i`-th index `k` has its window `z + cu_{n+N}` containing `x`
in the `i`-th coordinate exactly when `k` lies in
`(overlapWindowArg x n N i - 3^N, overlapWindowArg x n N i)`. -/
noncomputable def overlapWindowArg (x : Vec d) (n : ℤ) (N : ℕ) (i : Fin d) : ℝ :=
  x i / (3 : ℝ) ^ n + (3 : ℝ) ^ N / 2

/-- The integer box containing every admissible `i`-th index. -/
noncomputable def overlapIndexBox (x : Vec d) (n : ℤ) (N : ℕ) (i : Fin d) :
    Finset ℤ :=
  Finset.Icc (⌊overlapWindowArg x n N i⌋ - ((3 ^ N : ℕ) : ℤ) + 1)
    (⌈overlapWindowArg x n N i⌉ - 1)

/-- An open real interval of length exactly `3^N` contains at most `3^N`
integers. -/
private theorem card_overlapIndexBox_le (x : Vec d) (n : ℤ) (N : ℕ) (i : Fin d) :
    (overlapIndexBox x n N i).card ≤ 3 ^ N := by
  have hceil : ⌈overlapWindowArg x n N i⌉ ≤ ⌊overlapWindowArg x n N i⌋ + 1 :=
    Int.ceil_le_floor_add_one _
  rw [overlapIndexBox, Int.card_Icc]
  exact Int.toNat_le.mpr (by linarith)

/-- A cube of scale `n` whose window contains `x` has each index in the box. -/
private theorem index_mem_overlapIndexBox {n : ℤ} {N : ℕ} {R : TriadicCube d}
    (hR : R.scale = n) {x : Vec d}
    (hx : x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))) (i : Fin d) :
    R.index i ∈ overlapIndexBox x n N i := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := Corrector.zpow_three_pos n
  have habs := (Corrector.mem_openCubeAtScale_iff _ _ _).mp hx i
  have hshift : triadicCubeShift R i = (R.index i : ℝ) * (3 : ℝ) ^ n := by
    simp [triadicCubeShift, cubeScaleFactor, hR]
  have hsplit : (3 : ℝ) ^ (n + (N : ℤ)) = (3 : ℝ) ^ n * (3 : ℝ) ^ N := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hshift, hsplit] at habs
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hupper : ((R.index i : ℤ) : ℝ) < overlapWindowArg x n N i := by
    have hkey : overlapWindowArg x n N i - ((R.index i : ℤ) : ℝ) =
        (x i + (3 : ℝ) ^ n * (3 : ℝ) ^ N / 2 - (R.index i : ℝ) * (3 : ℝ) ^ n) /
          (3 : ℝ) ^ n := by
      rw [overlapWindowArg]
      field_simp
    have hnum : (0 : ℝ) <
        x i + (3 : ℝ) ^ n * (3 : ℝ) ^ N / 2 - (R.index i : ℝ) * (3 : ℝ) ^ n := by
      linarith
    have hpos := div_pos hnum h3n
    rw [← hkey] at hpos
    linarith
  have hlower : overlapWindowArg x n N i - ((3 ^ N : ℕ) : ℝ) < ((R.index i : ℤ) : ℝ) := by
    have hkey : ((R.index i : ℤ) : ℝ) -
        (overlapWindowArg x n N i - ((3 ^ N : ℕ) : ℝ)) =
        ((R.index i : ℝ) * (3 : ℝ) ^ n - x i + (3 : ℝ) ^ n * (3 : ℝ) ^ N / 2) /
          (3 : ℝ) ^ n := by
      rw [overlapWindowArg]
      push_cast
      field_simp
      ring
    have hnum : (0 : ℝ) <
        (R.index i : ℝ) * (3 : ℝ) ^ n - x i + (3 : ℝ) ^ n * (3 : ℝ) ^ N / 2 := by
      linarith
    have hpos := div_pos hnum h3n
    rw [← hkey] at hpos
    linarith
  rw [overlapIndexBox, Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · have h := Int.floor_lt.mpr hlower
    rw [Int.floor_sub_natCast] at h
    exact Int.lt_iff_add_one_le.mp h
  · have h := Int.lt_iff_add_one_le.mp (Int.lt_ceil.mpr hupper)
    linarith

/-! ## The overlap count -/

open scoped Classical in
/-- **The bounded-overlap count for the meso windows.**

For a finite family `I` of triadic cubes all of scale `n`, and for the windows
`z + cu_{n+N}` based at the sites `z = triadicCubeShift R`, every point of
space lies in at most `(3^N)^d` of the windows.  This is the multiplicity that
the manuscript's passage from `e.nablaw.in.L.eight` to
`e.lower.bound.oscillations` needs and does not state.

: the caller supplies `hI`, the common-scale property of the family; it is
discharged for the development's grids by `scale_eq_of_mem_mesoCubeGrid`. -/
theorem card_filter_mem_openCubeAtScale_le (x : Vec d) (n : ℤ) (N : ℕ)
    {I : Finset (TriadicCube d)} (hI : ∀ R ∈ I, R.scale = n) :
    (I.filter fun R => x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))).card ≤
      (3 ^ N) ^ d := by
  classical
  have hmap : ∀ R ∈ I.filter
      (fun R => x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))),
      R.index ∈ Fintype.piFinset (overlapIndexBox x n N) := by
    intro R hR
    obtain ⟨hRI, hRx⟩ := Finset.mem_filter.mp hR
    exact Fintype.mem_piFinset.mpr fun i => index_mem_overlapIndexBox (hI R hRI) hRx i
  have hinj : Set.InjOn (fun R : TriadicCube d => R.index)
      ↑(I.filter fun R => x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))) := by
    intro R hR S hS hidx
    have hRI := (Finset.mem_filter.mp (Finset.mem_coe.mp hR)).1
    have hSI := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).1
    have hRs : R.scale = n := hI R hRI
    have hSs : S.scale = n := hI S hSI
    cases R with
    | mk s1 i1 => cases S with
      | mk s2 i2 => simp_all
  calc (I.filter fun R => x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ))).card
      ≤ (Fintype.piFinset (overlapIndexBox x n N)).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = ∏ i : Fin d, (overlapIndexBox x n N i).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, 3 ^ N :=
        Finset.prod_le_prod fun i _ => card_overlapIndexBox_le x n N i
    _ = (3 ^ N) ^ d := by simp

/-- **The overlap count in indicator form.**  This is the shape the integral
transfer consumes: the sum of the window indicators is bounded by the pure
multiplicity `(3^N)^d`, uniformly in the point.

: the caller supplies `hI`, as in `card_filter_mem_openCubeAtScale_le`. -/
theorem sum_indicator_openCubeAtScale_le (x : Vec d) (n : ℤ) (N : ℕ)
    {I : Finset (TriadicCube d)} (hI : ∀ R ∈ I, R.scale = n) :
    ∑ R ∈ I, Set.indicator (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)))
        (fun _ => (1 : ℝ)) x ≤ ((3 : ℝ) ^ N) ^ d := by
  classical
  have hrw : ∀ R : TriadicCube d,
      Set.indicator (openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)))
        (fun _ => (1 : ℝ)) x =
        if x ∈ openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) then (1 : ℝ) else 0 :=
    fun R => Set.indicator_apply _ _ _
  rw [Finset.sum_congr rfl fun R _ => hrw R, Finset.sum_boole]
  have hcast := (Nat.cast_le (α := ℝ)).mpr (card_filter_mem_openCubeAtScale_le x n N hI)
  push_cast at hcast ⊢
  exact hcast

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
