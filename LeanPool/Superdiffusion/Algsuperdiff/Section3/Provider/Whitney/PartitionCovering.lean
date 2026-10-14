/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BadSetDefinitions

/-!
# PartitionCovering

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `d.whitney.bad-set.definitions`, the partition contract: covering and boundary geometry

This module proves local versions of two clauses of ABK26's
`sss.whitney.partition` that the definition module `BadSetDefinitions` states
but does not prove:

* **the covering / partition property** (: "a Whitney-type partition of
  `□_m`"): the half-open realizations of the cubes of `𝒲(□_m)` are pairwise
  disjoint (`whitneyPartition_pairwiseDisjoint_cubeSet`) and their union is
  exactly the *open* root cube
  (`openCubeSet_originCube_eq_iUnion_whitneyPartition`), so every point of the
  open root lies in exactly one Whitney cube;
* **the geometric meaning of `TouchesBoundary`** claimed in the docstring of
  `BadSetDefinitions`: for a triadic descendant of `□_m`, failing the
  extreme-index test puts the *closed* cube --- which is the closed ball
  `closure_cubeSet_eq_closedBall` --- inside the open root
  (`closedBall_subset_openCubeSet_of_not_touchesBoundary`), and the test is
  controlled quantitatively by the `ℓ^∞` distance to `∂□_m`
  (`boundaryMargin_le_of_touchesBoundary` and its contrapositive
  `not_touchesBoundary_of_lt_boundaryMargin`).

## Why the *open* root cube

`Homogenization.cubeSet` is the half-open realization `∏ᵢ [·, ·)`; this is the
realization for which triadic subdivision is an exact partition.  The
manuscript's termination clause says that **no** element of `𝒲(□_m)` touches
`∂□_m`, so no Whitney cube can contain a point of `∂□_m`, while the half-open
`cubeSet (originCube d m)` does contain its own "lower" faces.  The exact
identity is therefore with `openCubeSet (originCube d m)`, and this is the
honest reading of "partition of `□_m`" here; it is also the form the simplicial
refinement `iUnion_carrier_simplexPartition` composes with.  Stronger still:
the manuscript's root cube is *literally open* — defines `□_m:= (−½·3^m,
½·3^m)^d` — so the open form is not merely forced by the termination clause, it
is the printed carrier itself.

## Provider hypotheses

* The covering needs `[NeZero d]`.  This is not a convenience: for `d = 0` no
  cube satisfies `TouchesBoundary` (the predicate is an `∃ i : Fin 0`), so every
  `whitneyLayer` is empty while `openCubeSet (originCube 0 m)` is the whole
  one-point space.  `[NeZero d]` is the standing dimension hypothesis of the
  manuscript, and it enters exactly once, through
  `touchesBoundary_originCube` — the seed `□_m` of the recursion.
* Pairwise disjointness needs **no** hypothesis on the depth profile `hn`: it
  is proved from the exit-depth structure of `whitneyLayer` alone.  (The
  variant `SimplexPartition.disjoint_cubeSet_of_mem_whitneyPartition` is now a
  delegation to the theorem here, likewise hypothesis-free —.)
* The covering needs no hypothesis on `hn` either.

## References

* ABK26, `sss.whitney.partition` (the construction, its termination clause, and
  `e.W.n.def`).
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## Boundary-index arithmetic -/

/-- The extreme index of a depth-`t` descendant sits exactly one half-cube inside
`∂□_m`: `E_t · 3^{m-t} + 3^{m-t}/2 = 3^m/2`. -/
theorem extremeIdx_mul_zpow (m : ℤ) (t : ℕ) :
    ((extremeIdx t : ℤ) : ℝ) * (3 : ℝ) ^ (m - (t : ℤ)) +
        (3 : ℝ) ^ (m - (t : ℤ)) / 2 =
      (3 : ℝ) ^ m / 2 := by
  have h : (2 : ℝ) * ((extremeIdx t : ℤ) : ℝ) + 1 = (3 : ℝ) ^ (t : ℤ) := by
    have hidx := two_mul_extremeIdx_add_one t
    have hcast : ((2 * extremeIdx t + 1 : ℤ) : ℝ) = (((3 : ℤ) ^ t : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hidx
    push_cast at hcast
    rw [show ((3 : ℝ) ^ (t : ℤ)) = (3 : ℝ) ^ (t : ℕ) from zpow_natCast 3 t]
    linarith [hcast]
  have hsplit : (3 : ℝ) ^ (t : ℤ) * (3 : ℝ) ^ (m - (t : ℤ)) = (3 : ℝ) ^ m := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  linear_combination ((3 : ℝ) ^ (m - (t : ℤ)) / 2) * h + (1 / 2 : ℝ) * hsplit

/-- A non-touching depth-`t` descendant of `□_m` has *strictly* sub-extreme index
in every coordinate. -/
theorem abs_index_le_extremeIdx_sub_one {m : ℤ} {t : ℕ} {C : TriadicCube d}
    (hCmem : C ∈ descendantsAtDepth (originCube d m) t)
    (hCnt : ¬ TouchesBoundary m C) (j : Fin d) :
    |C.index j| ≤ extremeIdx t - 1 := by
  have hCscale : C.scale = m - (t : ℤ) := by
    have h := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hCmem
    simpa only [originCube] using h
  have hle := abs_index_le_extremeIdx hCmem j
  rcases lt_or_eq_of_le hle with hlt | heq
  · omega
  · refine absurd ⟨j, ?_⟩ hCnt
    rw [hCscale, rootExtreme_sub_natCast]
    rcases abs_cases (C.index j) with ⟨hv, _⟩ | ⟨hv, _⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **`□_m` touches its own boundary**: the seed of the Whitney recursion.  This
is the single place where the dimension hypothesis enters. -/
theorem touchesBoundary_originCube [NeZero d] (m : ℤ) :
    TouchesBoundary m (originCube d m) := by
  refine ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, Or.inl ?_⟩
  have h : rootExtreme m ((originCube d m).scale) = extremeIdx 0 := by
    have hs : ((originCube d m).scale) = m - ((0 : ℕ) : ℤ) := by simp [originCube]
    rw [hs, rootExtreme_sub_natCast]
  rw [h]
  simp [originCube, extremeIdx]

/-! ## Closed cubes, open cubes and the frontier of `□_m` -/

/-- Coordinatewise membership in the closed realization of a triadic cube. -/
theorem mem_closedBall_cubeCenter_iff {Q : TriadicCube d} {x : Vec d} :
    x ∈ Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) ↔
      ∀ i, ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ x i ∧
        x i ≤ ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
  have hlo : ∀ i : Fin d, cubeCenter Q i - HCPolySupport.cubeRadius Q =
      ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro i
    simp only [cubeCenter, HCPolySupport.cubeRadius]
    ring
  have hhi : ∀ i : Fin d, cubeCenter Q i + HCPolySupport.cubeRadius Q =
      ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro i
    simp only [cubeCenter, HCPolySupport.cubeRadius]
    ring
  rw [closedBall_cubeCenter_eq_pi_Icc]
  constructor
  · intro hx i
    have hi := Set.mem_Icc.mp (hx i (Set.mem_univ i))
    exact ⟨hlo i ▸ hi.1, hhi i ▸ hi.2⟩
  · intro hx i _
    rw [Set.mem_Icc, hlo i, hhi i]
    exact hx i

/-- The closure of a half-open triadic cube is its closed realization. -/
theorem closure_cubeSet_eq_closedBall (Q : TriadicCube d) :
    closure (cubeSet Q) = Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) := by
  refine Set.Subset.antisymm
    (closure_minimal (cubeSet_subset_closedBall Q) Metric.isClosed_closedBall) ?_
  rw [← closure_ball (cubeCenter Q) (ne_of_gt (HCPolySupport.cubeRadius_pos Q))]
  refine closure_mono ?_
  rw [ball_cubeCenter_eq_openCubeSet]
  exact fun x hx i => ⟨(hx i).1.le, (hx i).2⟩

/-! ## The geometric characterization of `TouchesBoundary` -/

/-- A non-touching descendant of `□_m` has its **closed** cube strictly inside
the open root cube. -/
theorem closedBall_subset_openCubeSet_of_not_touchesBoundary {m : ℤ} {t : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtDepth (originCube d m) t)
    (hQnt : ¬ TouchesBoundary m Q) :
    Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) ⊆
      openCubeSet (originCube d m) := by
  have hQscale : Q.scale = m - (t : ℤ) := by
    have h := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hQ
    simpa only [originCube] using h
  have hspos : (0 : ℝ) < (3 : ℝ) ^ (m - (t : ℤ)) := zpow_pos (by norm_num) _
  have hE := extremeIdx_mul_zpow m t
  intro x hx
  rw [mem_closedBall_cubeCenter_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hidx := abs_index_le_extremeIdx_sub_one hQ hQnt i
  have hup : Q.index i ≤ extremeIdx t - 1 := (le_abs_self (Q.index i)).trans hidx
  have hlo : -(extremeIdx t - 1) ≤ Q.index i := (neg_le_neg hidx).trans (neg_abs_le (Q.index i))
  have hupR : ((Q.index i : ℤ) : ℝ) ≤ ((extremeIdx t : ℤ) : ℝ) - 1 := by
    have : ((Q.index i : ℤ) : ℝ) ≤ (((extremeIdx t - 1 : ℤ)) : ℝ) := by exact_mod_cast hup
    push_cast at this
    linarith
  have hloR : -((extremeIdx t : ℤ) : ℝ) + 1 ≤ ((Q.index i : ℤ) : ℝ) := by
    have : ((-(extremeIdx t - 1) : ℤ) : ℝ) ≤ ((Q.index i : ℤ) : ℝ) := by exact_mod_cast hlo
    push_cast at this
    linarith
  have hxi := hx i
  rw [cubeScaleFactor, hQscale] at hxi
  have hexpLo : ((Q.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) =
      ((Q.index i : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) - (3 : ℝ) ^ (m - (t : ℤ)) / 2 := by ring
  have hexpHi : ((Q.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) =
      ((Q.index i : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) + (3 : ℝ) ^ (m - (t : ℤ)) / 2 := by ring
  rw [hexpLo] at hxi
  rw [hexpHi] at hxi
  have hmulUp : ((Q.index i : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) ≤
      (((extremeIdx t : ℤ) : ℝ) - 1) * (3 : ℝ) ^ (m - (t : ℤ)) :=
    mul_le_mul_of_nonneg_right hupR hspos.le
  have hmulLo : (-((extremeIdx t : ℤ) : ℝ) + 1) * (3 : ℝ) ^ (m - (t : ℤ)) ≤
      ((Q.index i : ℝ)) * (3 : ℝ) ^ (m - (t : ℤ)) :=
    mul_le_mul_of_nonneg_right hloR hspos.le
  constructor <;> nlinarith [hxi.1, hxi.2, hmulUp, hmulLo, hE, hspos]

/-! ## Every Whitney cube lies in the open root cube -/

/-- **The termination clause, geometrically**: a Whitney cube does not meet `∂□_m`;
its closed realization sits inside the open root cube. -/
theorem closedBall_subset_openCubeSet_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) ⊆
      openCubeSet (originCube d m) :=
  closedBall_subset_openCubeSet_of_not_touchesBoundary
    (mem_descendantsAtDepth_of_mem_whitneyLayer hQ)
    (not_touchesBoundary_of_mem_whitneyLayer hQ)

theorem cubeSet_subset_openCubeSet_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    cubeSet Q ⊆ openCubeSet (originCube d m) :=
  (cubeSet_subset_closedBall Q).trans (closedBall_subset_openCubeSet_of_mem_whitneyLayer hQ)

theorem cubeSet_subset_openCubeSet_of_mem_whitneyPartition {m : ℤ} {hn : ℕ → ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyPartition m hn) :
    cubeSet Q ⊆ openCubeSet (originCube d m) := by
  obtain ⟨n, hQn⟩ := hQ
  exact cubeSet_subset_openCubeSet_of_mem_whitneyLayer hQn

/-! ## The boundary margin of a touching ancestor -/

private theorem exists_nat_zpow_sub_lt (m : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (3 : ℝ) ^ (m - (n : ℤ)) < ε := by
  have hpowm : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hpowm)
    (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  calc
    (3 : ℝ) ^ (m - (n : ℤ)) = (3 : ℝ) ^ m * (1 / 3 : ℝ) ^ n := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      simp [div_eq_mul_inv]
    _ < (3 : ℝ) ^ m * (ε / (3 : ℝ) ^ m) := mul_lt_mul_of_pos_left hn hpowm
    _ = ε := by field_simp

/-- **The boundary-margin estimate** (one-sided half): a boundary-touching cube
of size `3^{m-n}` containing `x` forces `x` to be within `3^{m-n}` of `∂□_m` in
the `ℓ^∞` sense. -/
theorem boundaryMargin_le_of_touchesBoundary {m : ℤ} {n : ℕ} {A : TriadicCube d}
    (hAscale : A.scale = m - (n : ℤ)) {x : Vec d} (hxA : x ∈ cubeSet A)
    (hAt : TouchesBoundary m A) :
    (3 : ℝ) ^ m / 2 - ‖x‖ ≤ (3 : ℝ) ^ (m - (n : ℤ)) := by
  have hE := extremeIdx_mul_zpow m n
  obtain ⟨i, hi⟩ := hAt
  rw [hAscale, rootExtreme_sub_natCast] at hi
  have hxi : (((A.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (n : ℤ)) ≤ x i) ∧
      (x i < ((A.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (n : ℤ))) := by
    simpa only [cubeSet, cubeScaleFactor, hAscale, Set.mem_ofPred_eq] using hxA i
  have hnorm : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  rcases hi with h | h
  · have hcast : ((A.index i : ℤ) : ℝ) = ((extremeIdx n : ℤ) : ℝ) := by exact_mod_cast h
    have hexp : ((A.index i : ℝ) - (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (n : ℤ)) =
        ((extremeIdx n : ℤ) : ℝ) * (3 : ℝ) ^ (m - (n : ℤ)) - (3 : ℝ) ^ (m - (n : ℤ)) / 2 := by
      rw [hcast]; ring
    rw [hexp] at hxi
    have hxle : x i ≤ |x i| := le_abs_self (x i)
    linarith [hxi.1]
  · have hcast : ((A.index i : ℤ) : ℝ) = -((extremeIdx n : ℤ) : ℝ) := by exact_mod_cast h
    have hexp : ((A.index i : ℝ) + (1 / 2 : ℝ)) * (3 : ℝ) ^ (m - (n : ℤ)) =
        -(((extremeIdx n : ℤ) : ℝ) * (3 : ℝ) ^ (m - (n : ℤ))) + (3 : ℝ) ^ (m - (n : ℤ)) / 2 := by
      rw [hcast]; ring
    rw [hexp] at hxi
    have hxle : -x i ≤ |x i| := neg_le_abs (x i)
    linarith [hxi.2]

/-- Contrapositive of the margin estimate: a cube much smaller than the distance
from `x` to `∂□_m` cannot touch `∂□_m`. -/
theorem not_touchesBoundary_of_lt_boundaryMargin {m : ℤ} {n : ℕ} {A : TriadicCube d}
    (hAscale : A.scale = m - (n : ℤ)) {x : Vec d} (hxA : x ∈ cubeSet A)
    (hsmall : (3 : ℝ) ^ (m - (n : ℤ)) < (3 : ℝ) ^ m / 2 - ‖x‖) :
    ¬ TouchesBoundary m A := fun hAt =>
  absurd (boundaryMargin_le_of_touchesBoundary hAscale hxA hAt) (not_le.mpr hsmall)

/-! ## The covering -/

/-- **Every point of the open root cube exits the boundary recursion at a finite
layer.**  This is the constructive content of the covering clause. -/
theorem exists_mem_whitneyLayer_of_mem_openCubeSet [NeZero d] (m : ℤ) (hn : ℕ → ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    ∃ n : ℕ, ∃ Q ∈ whitneyLayer m hn n, x ∈ cubeSet Q := by
  classical
  have hxroot : x ∈ cubeSet (originCube d m) := fun i => ⟨(hx i).1.le, (hx i).2⟩
  have hnorm : ‖x‖ < (3 : ℝ) ^ m / 2 := by
    have hx' := mem_openCubeSet_originCube_iff.mp hx
    refine (pi_norm_lt_iff (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [(hx' i).1], by linarith [(hx' i).2]⟩
  obtain ⟨N, hN⟩ := exists_nat_zpow_sub_lt m (by linarith : (0 : ℝ) < (3 : ℝ) ^ m / 2 - ‖x‖)
  obtain ⟨D, hD, hxD⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet N hxroot
  have hDscale : D.scale = m - (N : ℤ) := by
    have h := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hD
    simpa only [originCube] using h
  have hDnt : ¬ TouchesBoundary m D :=
    not_touchesBoundary_of_lt_boundaryMargin hDscale hxD hN
  obtain ⟨n, ⟨C, hC, hxC, hCnt⟩, hnmin⟩ :
      ∃ n : ℕ, (∃ C ∈ descendantsAtDepth (originCube d m) n,
          x ∈ cubeSet C ∧ ¬ TouchesBoundary m C) ∧
        ∀ k, k < n → ¬ ∃ C ∈ descendantsAtDepth (originCube d m) k,
          x ∈ cubeSet C ∧ ¬ TouchesBoundary m C := by
    have hex : ∃ k : ℕ, ∃ C ∈ descendantsAtDepth (originCube d m) k,
        x ∈ cubeSet C ∧ ¬ TouchesBoundary m C := ⟨N, D, hD, hxD, hDnt⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, HCPolySupport.descendantsAtDepth_zero, Finset.mem_singleton] at hC
    exact hCnt (hC ▸ touchesBoundary_originCube m)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hCsucc : C ∈ descendantsAtDepth (originCube d m) ((n - 1) + 1) := by
    simpa only [show n - 1 + 1 = n from by omega] using hC
  obtain ⟨A, hA, hCA⟩ := HCPolySupport.mem_descendantsAtDepth_succ_iff.mp hCsucc
  have hxA : x ∈ cubeSet A := cubeSet_subset_of_mem_childCubes hCA hxC
  have hAt : TouchesBoundary m A := by
    by_contra hAnt
    exact hnmin (n - 1) (by omega) ⟨A, hA, hxA, hAnt⟩
  obtain ⟨Q, hQC, hxQ⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet (hn n) hxC
  exact ⟨n, Q, mem_whitneyLayer_iff.mpr ⟨hn1, A, hA, hAt, C, hCA, hCnt, hQC⟩, hxQ⟩

/-- **`𝒲(□_m)` covers `□_m`**: the half-open Whitney cubes tile the open root cube
exactly. -/
theorem openCubeSet_originCube_eq_iUnion_whitneyPartition [NeZero d] (m : ℤ) (hn : ℕ → ℕ) :
    openCubeSet (originCube d m) =
      ⋃ Q ∈ whitneyPartition (d := d) m hn, cubeSet Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, Q, hQ, hxQ⟩ := exists_mem_whitneyLayer_of_mem_openCubeSet m hn hx
    exact Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨⟨n, hQ⟩, hxQ⟩⟩
  · intro hx
    obtain ⟨Q, hQ, hxQ⟩ := by simpa only [Set.mem_iUnion] using hx
    exact cubeSet_subset_openCubeSet_of_mem_whitneyPartition hQ hxQ

/-! ## Pairwise disjointness -/

/-- The exit cube of a layer-`n` Whitney cube: the depth-`n` non-touching
ancestor produced by the recursion. -/
private theorem exists_exitCube_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    ∃ C ∈ descendantsAtDepth (originCube d m) n,
      ¬ TouchesBoundary m C ∧ cubeSet Q ⊆ cubeSet C := by
  obtain ⟨hn1, A, hA, _, C, hCA, hCnt, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  refine ⟨C, ?_, hCnt, cubeSet_subset_of_mem_descendantsAtDepth hQC⟩
  have hCA' : C ∈ descendantsAtDepth A 1 := by
    simpa only [HCPolySupport.descendantsAtDepth_one] using hCA
  simpa only [show n - 1 + 1 = n from by omega] using HCPolySupport.mem_descendantsAtDepth_add hA
    hCA'

/-- The touching ancestor of a layer-`n` Whitney cube at depth `n - 1`. -/
private theorem exists_touchingAncestor_of_mem_whitneyLayer {m : ℤ} {hn : ℕ → ℕ} {n : ℕ}
    {Q : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) :
    ∃ A ∈ descendantsAtDepth (originCube d m) (n - 1),
      TouchesBoundary m A ∧ cubeSet Q ⊆ cubeSet A := by
  obtain ⟨_, A, hA, hAt, C, hCA, _, hQC⟩ := mem_whitneyLayer_iff.mp hQ
  exact ⟨A, hA, hAt, (cubeSet_subset_of_mem_descendantsAtDepth hQC).trans
    (cubeSet_subset_of_mem_childCubes hCA)⟩

/-- Two triadic descendants of `□_m` sharing a point, the first not deeper than
the second, are nested. -/
theorem mem_descendantsAtDepth_of_mem_cubeSet_inter {m : ℤ} {p q : ℕ}
    {U V : TriadicCube d} (hU : U ∈ descendantsAtDepth (originCube d m) p)
    (hV : V ∈ descendantsAtDepth (originCube d m) q) (hpq : p ≤ q)
    {x : Vec d} (hxU : x ∈ cubeSet U) (hxV : x ∈ cubeSet V) :
    V ∈ descendantsAtDepth U (q - p) := by
  have hV' : V ∈ descendantsAtDepth (originCube d m) (p + (q - p)) := by
    simpa only [show p + (q - p) = q from by omega] using hV
  obtain ⟨W, hW, hVW⟩ := exists_descendant_ancestor_at_depth p (q - p) hV'
  have hxW : x ∈ cubeSet W := cubeSet_subset_of_mem_descendantsAtDepth hVW hxV
  have hWU : W = U := by
    by_contra hne
    exact (pairwiseDisjoint_descendantsAtDepth (originCube d m) p (Finset.mem_coe.mpr hW)
      (Finset.mem_coe.mpr hU) hne).le_bot ⟨hxW, hxU⟩
  exact hWU ▸ hVW

/-- Whitney cubes of strictly different layers cannot share a point: the exit
cube of the shallower layer would be a non-touching ancestor of the touching
ancestor of the deeper layer. -/
private theorem not_mem_cubeSet_inter_of_lt {m : ℤ} {hn : ℕ → ℕ} {n n' : ℕ}
    {Q R : TriadicCube d} (hQ : Q ∈ whitneyLayer m hn n) (hR : R ∈ whitneyLayer m hn n')
    (hlt : n < n') {x : Vec d} (hxQ : x ∈ cubeSet Q) (hxR : x ∈ cubeSet R) : False := by
  obtain ⟨C, hC, hCnt, hQC⟩ := exists_exitCube_of_mem_whitneyLayer hQ
  obtain ⟨A', hA', hA't, hRA'⟩ := exists_touchingAncestor_of_mem_whitneyLayer hR
  have hCscale : C.scale = m - (n : ℤ) := by
    have h := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hC
    simpa only [originCube] using h
  have hnest : A' ∈ descendantsAtDepth C ((n' - 1) - n) :=
    mem_descendantsAtDepth_of_mem_cubeSet_inter hC hA' (by omega) (hQC hxQ) (hRA' hxR)
  exact hCnt (touchesBoundary_of_mem_descendantsAtDepth hCscale hnest hA't)

/-- **Whitney cubes containing a common point coincide.**  No hypothesis on the
depth profile `hn` is needed. -/
theorem eq_of_mem_cubeSet_of_mem_whitneyPartition {m : ℤ} {hn : ℕ → ℕ}
    {Q R : TriadicCube d} (hQ : Q ∈ whitneyPartition m hn) (hR : R ∈ whitneyPartition m hn)
    {x : Vec d} (hxQ : x ∈ cubeSet Q) (hxR : x ∈ cubeSet R) : Q = R := by
  obtain ⟨n, hQn⟩ := hQ
  obtain ⟨n', hRn'⟩ := hR
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd hxR (fun h => not_mem_cubeSet_inter_of_lt hQn hRn' hlt hxQ h)
  · subst heq
    by_contra hne
    exact (pairwiseDisjoint_descendantsAtDepth (originCube d m) (n + hn n)
      (Finset.mem_coe.mpr (mem_descendantsAtDepth_of_mem_whitneyLayer hQn))
      (Finset.mem_coe.mpr (mem_descendantsAtDepth_of_mem_whitneyLayer hRn'))
      hne).le_bot ⟨hxQ, hxR⟩
  · exact absurd hxQ (fun h => not_mem_cubeSet_inter_of_lt hRn' hQn hgt hxR h)

/-- **`𝒲(□_m)` is pairwise disjoint**. -/
theorem whitneyPartition_pairwiseDisjoint_cubeSet (m : ℤ) (hn : ℕ → ℕ) :
    (whitneyPartition (d := d) m hn).PairwiseDisjoint cubeSet := by
  intro Q hQ R hR hQR
  refine Set.disjoint_left.mpr ?_
  intro x hxQ hxR
  exact hQR (eq_of_mem_cubeSet_of_mem_whitneyPartition hQ hR hxQ hxR)

end

end Algsuperdiff.Section3.Provider.Whitney
