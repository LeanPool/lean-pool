/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.PartitionCovering

/-!
# BoundaryDistance

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-sided boundary distance of a Whitney layer

This module proves the assertion ABK26 records without proof — "the cubes in
`𝒲(□_m, n)` lie at distance roughly `3^{m-n}` from the boundary `∂□_m`" — and
the two consequences its proof of `l.bad.clusters.geometry` draws from it:

* **the two-sided estimate**, in the form the consumers need: `3^{m-n} < 3^m/2
  - ‖cubeCenter □‖` for every `□ ∈ 𝒲(□_m,n)`
  (`three_zpow_lt_boundaryMargin_cubeCenter_of_mem_whitneyLayer`) and `3^m/2 -
  ‖x‖ ≤ 3·3^{m-n}` for every `x` in a layer-`n` cube
  (`boundaryMargin_le_of_mem_whitneyLayer`).  Here `3^m/2 - ‖x‖` is the `ℓ^∞`
  distance from `x` to `∂□_m`, since `□_m` is the centred cube of side `3^m`.
* **the layer separation constant** `c = 2/3`, *dimension-free* as computes it:
  cubes two or more layers apart have centres more than `(2/3)·3^{m-n}` apart
  (`two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers`).
* **the adjacency clause of the manuscript's first proof paragraph**: two
  *touching* Whitney cubes lie in equal or neighbouring layers
  (`whitneyLayer_index_close_of_cubeTouch`).  Following consequence 2 this
  needs **no** percolation input and **no** largeness of `k₀` — only `h_n ≥ 1`.

## Why the lower half is stated at the centre only

The consumer `two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers` pairs the lower
half at the centre of the *shallower* cube against the upper half at the centre
of the *deeper* one, so the centre-only lower bound suffices; it is also the
form for which the index arithmetic is exact.

## Provider hypotheses

Both halves are proved for an **abstract** depth profile `hn : ℕ → ℕ`; no
monotonicity, no gap bound and no dimension hypothesis is used.  The adjacency
clause adds only `1 ≤ hn n` for the two layers involved (consequence 3: `k₀ ≥
1`).  Layer indices are automatically `≥ 1` because `whitneyLayer m hn 0 = ∅`.

## References

* ABK26, `sss.whitney.partition`; `l.bad.clusters.geometry`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## Elementary cube arithmetic -/

theorem cubeRadius_eq_zpow_div_two (Q : TriadicCube d) :
    HCPolySupport.cubeRadius Q = (3 : ℝ) ^ Q.scale / 2 := by
  simp only [HCPolySupport.cubeRadius, cubeScaleFactor]
  ring

theorem cubeCenter_mem_cubeSet (Q : TriadicCube d) : cubeCenter Q ∈ cubeSet Q := by
  intro i
  have hpos : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [cubeCenter]
  constructor <;> nlinarith [hpos]

/-- The `ℓ^∞` characterization of `CubeTouch` at the centres. -/
theorem cubeTouch_iff_dist_cubeCenter_le {Q R : TriadicCube d} :
    CubeTouch Q R ↔ dist (cubeCenter Q) (cubeCenter R) ≤
      HCPolySupport.cubeRadius Q + HCPolySupport.cubeRadius R := by
  rw [cubeTouch_iff, dist_pi_le_iff
    (add_nonneg (HCPolySupport.cubeRadius_nonneg Q) (HCPolySupport.cubeRadius_nonneg R))]
  exact ⟨fun h i => by simpa only [Real.dist_eq] using h i,
    fun h i => by simpa only [Real.dist_eq] using h i⟩

theorem norm_cubeCenter_sub_le_of_cubeTouch {Q R : TriadicCube d} (h : CubeTouch Q R) :
    ‖cubeCenter Q - cubeCenter R‖ ≤
      HCPolySupport.cubeRadius Q + HCPolySupport.cubeRadius R := by
  have h' := cubeTouch_iff_dist_cubeCenter_le.mp h
  rwa [dist_eq_norm] at h'

/-! ## Structure of a layer cube -/

theorem one_le_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) : 1 ≤ n :=
  (mem_whitneyLayer_iff.mp hQ).1

/-- The **interior cube** of a layer-`n` Whitney cube: the depth-`n`
non-boundary-touching descendant of `□_m` produced by the recursion. -/
theorem exists_interiorCube_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    ∃ C ∈ descendantsAtDepth (originCube d m) n,
      ¬ TouchesBoundary m C ∧ Q ∈ descendantsAtDepth C (hn n) := by
  obtain ⟨hn1, A, hA, _, C, hCA, hCnt, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  refine ⟨C, ?_, hCnt, hQC⟩
  have hCA' : C ∈ descendantsAtDepth A 1 := by
    simpa only [HCPolySupport.descendantsAtDepth_one] using hCA
  simpa only [show n - 1 + 1 = n from by omega] using
    HCPolySupport.mem_descendantsAtDepth_add hA hCA'

/-- The **boundary ancestor** of a layer-`n` Whitney cube: the depth-`(n-1)`
descendant of `□_m` that still touches `∂□_m`. -/
theorem exists_boundaryAncestor_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    ∃ A : TriadicCube d, A.scale = m - ((n - 1 : ℕ) : ℤ) ∧ TouchesBoundary m A ∧
      cubeSet Q ⊆ cubeSet A := by
  obtain ⟨_, A, hA, hAt, C, hCA, _, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  refine ⟨A, ?_, hAt, (cubeSet_subset_of_mem_descendantsAtDepth hQC).trans
    (cubeSet_subset_of_mem_childCubes hCA)⟩
  have h := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hA
  simpa only [originCube] using h

/-- Distinct layers of a nondecreasing profile sit at distinct scales, so a
Whitney cube determines its layer index. -/
theorem whitneyLayer_index_unique {m : ℤ} {hn : ℕ → ℕ} (hmono : Monotone hn) {n n' : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) (hQ' : Q ∈ whitneyLayer m hn n') :
    n = n' := by
  have h1 := scale_eq_of_mem_whitneyLayer hQ
  have h2 := scale_eq_of_mem_whitneyLayer hQ'
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · have hh := hmono hlt.le
    omega
  · exact heq
  · have hh := hmono hgt.le
    omega

/-! ## Additivity of the extreme index -/

/-- `E_{t+s} = 3^s E_t + E_s`: subdividing `s` further generations rescales the
extreme index and adds the extreme index of the new depth. -/
theorem extremeIdx_add (t s : ℕ) :
    extremeIdx (t + s) = 3 ^ s * extremeIdx t + extremeIdx s := by
  have h1 := two_mul_extremeIdx_add_one (t + s)
  have h2 := two_mul_extremeIdx_add_one t
  have h3 := two_mul_extremeIdx_add_one s
  have h4 : (3 : ℤ) ^ (t + s) = 3 ^ t * 3 ^ s := pow_add 3 t s
  have key : 2 * extremeIdx (t + s) = 2 * (3 ^ s * extremeIdx t + extremeIdx s) := by
    linear_combination h1 - (3 : ℤ) ^ s * h2 - h3 + h4
  omega

/-! ## The two-sided boundary distance -/

/-- **, the index bound.**  A layer-`n` Whitney cube has every index coordinate at
most `E_{n+h_n} - 3^{h_n}`: it is a depth-`h_n` descendant of a non-touching
depth-`n` cube, whose index is at most `E_n - 1`. -/
theorem abs_index_le_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) (j : Fin d) :
    |Q.index j| ≤ extremeIdx (n + hn n) - 3 ^ hn n := by
  obtain ⟨C, hC, hCnt, hQC⟩ := exists_interiorCube_of_mem_whitneyLayer hQ
  have hCidx := abs_le.mp (abs_index_le_extremeIdx_sub_one hC hCnt j)
  have hQidx := abs_le.mp (abs_index_sub_le_of_mem_descendantsAtDepth hQC j)
  have hp : (0 : ℤ) < 3 ^ hn n := pow_pos (by norm_num) _
  have hup : (3 : ℤ) ^ hn n * C.index j ≤ 3 ^ hn n * (extremeIdx n - 1) :=
    mul_le_mul_of_nonneg_left hCidx.2 hp.le
  have hlo : (3 : ℤ) ^ hn n * (-(extremeIdx n - 1)) ≤ 3 ^ hn n * C.index j :=
    mul_le_mul_of_nonneg_left hCidx.1 hp.le
  have hE := extremeIdx_add n (hn n)
  rw [abs_le]
  constructor <;> nlinarith [hQidx.1, hQidx.2, hup, hlo, hE]

/-- **, the lower half**, at the centre: a layer-`n` Whitney cube has its centre at
`ℓ^∞` distance strictly more than `3^{m-n}` from `∂□_m`. -/
theorem three_zpow_lt_boundaryMargin_cubeCenter_of_mem_whitneyLayer {m : ℤ}
    {hn : ℕ → ℕ} {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    (3 : ℝ) ^ (m - (n : ℤ)) < (3 : ℝ) ^ m / 2 - ‖cubeCenter Q‖ := by
  have hn1 := one_le_of_mem_whitneyLayer hQ
  set L : ℕ := n + hn n with hL
  have hscale : Q.scale = m - (L : ℤ) := by
    have h := scale_eq_of_mem_whitneyLayer hQ
    rw [hL]
    push_cast
    omega
  have hEL := extremeIdx_mul_zpow m L
  have hposL : (0 : ℝ) < (3 : ℝ) ^ (m - (L : ℤ)) := zpow_pos (by norm_num) _
  have hsplit : (3 : ℝ) ^ (hn n : ℤ) * (3 : ℝ) ^ (m - (L : ℤ)) = (3 : ℝ) ^ (m - (n : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    rw [hL]
    push_cast
    ring
  have hbound : ∀ j : Fin d, |cubeCenter Q j| ≤
      (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ (m - (L : ℤ)) / 2 - (3 : ℝ) ^ (m - (n : ℤ)) := by
    intro j
    have hidx := abs_index_le_of_mem_whitneyLayer hQ j
    have hidxR : |((Q.index j : ℤ) : ℝ)| ≤
        ((extremeIdx L : ℤ) : ℝ) - ((3 : ℤ) ^ hn n : ℤ) := by
      have h : ((|Q.index j| : ℤ) : ℝ) ≤ (((extremeIdx L - 3 ^ hn n : ℤ)) : ℝ) := by
        exact_mod_cast hidx
      rw [Int.cast_abs] at h
      push_cast at h ⊢
      linarith
    have hcen : |cubeCenter Q j| = |((Q.index j : ℤ) : ℝ)| * (3 : ℝ) ^ (m - (L : ℤ)) := by
      simp only [cubeCenter, cubeScaleFactor, hscale, abs_mul]
      rw [abs_of_pos hposL]
    have hmul : |((Q.index j : ℤ) : ℝ)| * (3 : ℝ) ^ (m - (L : ℤ)) ≤
        (((extremeIdx L : ℤ) : ℝ) - ((3 : ℤ) ^ hn n : ℤ)) * (3 : ℝ) ^ (m - (L : ℤ)) :=
      mul_le_mul_of_nonneg_right hidxR hposL.le
    have hpow : (((3 : ℤ) ^ hn n : ℤ) : ℝ) = (3 : ℝ) ^ (hn n : ℤ) := by
      push_cast
      rw [zpow_natCast]
    rw [hcen]
    rw [hpow] at hmul
    nlinarith [hmul, hEL, hsplit]
  have hposn : (0 : ℝ) < (3 : ℝ) ^ (m - (n : ℤ)) := zpow_pos (by norm_num) _
  have hle : (3 : ℝ) ^ (m - (n : ℤ)) ≤ (3 : ℝ) ^ (m - (1 : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hm1 : (3 : ℝ) ^ (m - (1 : ℤ)) = (3 : ℝ) ^ m / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have hnorm : ‖cubeCenter Q‖ <
      (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ (m - (n : ℤ)) := by
    refine (pi_norm_lt_iff (by nlinarith [hposn, hle, hm1] :
      (0 : ℝ) < (3 : ℝ) ^ m / 2 - (3 : ℝ) ^ (m - (n : ℤ)))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have := hbound j
    linarith [hposL]
  linarith [hnorm]

/-- **, the upper half**: every point of a layer-`n` Whitney cube is within
`3·3^{m-n}` of `∂□_m` in the `ℓ^∞` sense, because the cube sits inside a
boundary-touching cube of size `3^{m-n+1}`. -/
theorem boundaryMargin_le_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) {x : Vec d} (hx : x ∈ cubeSet Q) :
    (3 : ℝ) ^ m / 2 - ‖x‖ ≤ 3 * (3 : ℝ) ^ (m - (n : ℤ)) := by
  have hn1 := one_le_of_mem_whitneyLayer hQ
  obtain ⟨A, hAscale, hAt, hQA⟩ := exists_boundaryAncestor_of_mem_whitneyLayer hQ
  have h := boundaryMargin_le_of_touchesBoundary hAscale (hQA hx) hAt
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hcast] at h
  have hz : (3 : ℝ) ^ (m - ((n : ℤ) - 1)) = 3 * (3 : ℝ) ^ (m - (n : ℤ)) := by
    rw [show m - ((n : ℤ) - 1) = (m - (n : ℤ)) + 1 from by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rwa [hz] at h

/-! ## Layer separation and adjacency -/

/-- **The layer-separation constant `c = 2/3`**: Whitney cubes two or more layers
apart have centres more than `(2/3)·3^{m-n}` apart in the `ℓ^∞` sense.  The
constant is dimension-free. -/
theorem two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers {m : ℤ} {hn : ℕ → ℕ}
    {n n' : ℕ} (hnn' : n + 2 ≤ n') {Q R : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) (hR : R ∈ whitneyLayer m hn n') :
    (2 / 3 : ℝ) * (3 : ℝ) ^ (m - (n : ℤ)) < ‖cubeCenter Q - cubeCenter R‖ := by
  have hlow := three_zpow_lt_boundaryMargin_cubeCenter_of_mem_whitneyLayer hQ
  have hup := boundaryMargin_le_of_mem_whitneyLayer hR (cubeCenter_mem_cubeSet R)
  have hshrink : (3 : ℝ) ^ (m - (n' : ℤ)) ≤ (3 : ℝ) ^ (m - (n : ℤ) - 2) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hnine : (3 : ℝ) ^ (m - (n : ℤ) - 2) = (3 : ℝ) ^ (m - (n : ℤ)) / 9 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have htri : ‖cubeCenter R‖ - ‖cubeCenter Q‖ ≤ ‖cubeCenter Q - cubeCenter R‖ := by
    rw [← norm_neg (cubeCenter Q - cubeCenter R), neg_sub]
    exact norm_sub_norm_le _ _
  rw [hnine] at hshrink
  linarith [hlow, hup, hshrink, htri]

/-- **The adjacency clause**: two *touching* Whitney cubes lie in equal or
neighbouring layers.  Per consequence 2 this uses no percolation input and no
largeness of `k₀`; only `h_n ≥ 1` enters. -/
theorem whitneyLayer_index_close_of_cubeTouch {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) {n n' : ℕ} {Q R : TriadicCube d}
    (hQ : Q ∈ whitneyLayer m hn n) (hR : R ∈ whitneyLayer m hn n')
    (htouch : CubeTouch Q R) : n ≤ n' + 1 ∧ n' ≤ n + 1 := by
  have key : ∀ {a a' : ℕ} {U V : TriadicCube d}, U ∈ whitneyLayer (d := d) m hn a →
      V ∈ whitneyLayer (d := d) m hn a' → CubeTouch U V → a + 2 ≤ a' → False := by
    intro a a' U V hU hV hUV hlt
    have hsep := two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers hlt hU hV
    have hle := norm_cubeCenter_sub_le_of_cubeTouch hUV
    have hUscale := scale_eq_of_mem_whitneyLayer hU
    have hVscale := scale_eq_of_mem_whitneyLayer hV
    have hUr : HCPolySupport.cubeRadius U ≤ (3 : ℝ) ^ (m - (a : ℤ) - 1) / 2 := by
      rw [cubeRadius_eq_zpow_div_two, hUscale]
      have := zpow_le_zpow_right₀ (a := (3 : ℝ)) (by norm_num)
        (show m - (a : ℤ) - (hn a : ℤ) ≤ m - (a : ℤ) - 1 from by
          have := hn1 a
          omega)
      linarith
    have hVr : HCPolySupport.cubeRadius V ≤ (3 : ℝ) ^ (m - (a : ℤ) - 1) / 2 := by
      rw [cubeRadius_eq_zpow_div_two, hVscale]
      have := zpow_le_zpow_right₀ (a := (3 : ℝ)) (by norm_num)
        (show m - (a' : ℤ) - (hn a' : ℤ) ≤ m - (a : ℤ) - 1 from by
          have := hn1 a'
          omega)
      linarith
    have hthird : (3 : ℝ) ^ (m - (a : ℤ) - 1) = (3 : ℝ) ^ (m - (a : ℤ)) / 3 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [hthird] at hUr hVr
    have hposa : (0 : ℝ) < (3 : ℝ) ^ (m - (a : ℤ)) := zpow_pos (by norm_num) _
    linarith [hsep, hle, hUr, hVr, hposa]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    exact key hR hQ htouch.symm (by omega)
  · by_contra hcon
    exact key hQ hR htouch (by omega)

end

end Algsuperdiff.Section3.Provider.Whitney
