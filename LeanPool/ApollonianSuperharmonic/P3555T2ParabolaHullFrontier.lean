/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.P3555T2ParabolaSupporting
public import Mathlib.Analysis.Convex.Topology
public import LeanPool.ApollonianSuperharmonic.P3381T1AffineTriangleMap
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P3555T2ParabolaHullFrontier]

/-!
# P3555T2ParabolaHullFrontier

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParabolaHullConstruction

private theorem seg_rep (a b x : Real × Real) (hx : x ∈ segment Real a b) :
      ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = (1-t) • a + t • b := by
  classical
  rw [segment_eq_image_lineMap] at hx
  rcases hx with ⟨t, ht, htx⟩
  refine ⟨t, ht, ?_⟩
  rw [← htx]
  simp [AffineMap.lineMap_apply_module]

private theorem det_affine (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (i : Fin (n + 3)) (a b : Real ×
    Real) (t : Real) :
      P3381T1TriangleDeterminant ![q i, q (i+1), (1-t) • a + t • b] =
        (1-t) * P3381T1TriangleDeterminant ![q i, q (i+1), a] +
          t * P3381T1TriangleDeterminant ![q i, q (i+1), b] := by
  classical
  simp [P3381T1TriangleDeterminant, Prod.smul_fst, Prod.smul_snd]
  ring

private theorem det_zero_left (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (i : Fin (n + 3)) :
      P3381T1TriangleDeterminant ![q i, q (i+1), q i] = 0 := by
  classical
  simp [P3381T1TriangleDeterminant]

private theorem det_zero_right (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (i : Fin (n + 3)) :
      P3381T1TriangleDeterminant ![q i, q (i+1), q (i+1)] = 0 := by
  classical
  simp [P3381T1TriangleDeterminant]

private theorem endpoint_det_nonneg (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hsupport : ∀ (i j : Fin (n
    + 3)), j ≠ i → j ≠ i + 1 → 0 < P3381T1TriangleDeterminant ![q i, q (i + 1), q j])
    (det_zero_left : ∀ (i : Fin (n + 3)), P3381T1TriangleDeterminant ![q i, q (i + 1), q i] =
    0) (det_zero_right : ∀ (i : Fin (n + 3)), P3381T1TriangleDeterminant ![q i, q (i + 1), q (i
    + 1)] = 0) (i k : Fin (n + 3)) :
      0 ≤ P3381T1TriangleDeterminant ![q i, q (i+1), q k] := by
  classical
  by_cases h : k = i ∨ k = i+1
  · rcases h with h | h
    · subst k
      simp [det_zero_left]
    · subst k
      simp [det_zero_right]
  · exact (hsupport i k (by tauto) (by tauto)).le

private theorem no_two_cycle (n : ℕ) (i : Fin (n + 3)) : i + 1 + 1 ≠ i := by
  classical
  intro h
  by_cases hi : i = Fin.last (n + 2)
  · have h1 : (i+1).val = 0 := by simp [hi]
    have h2 : (i+1+1).val = 1 := by
      have hlast : i+1 = (0 : Fin (n+3)) := by
        apply Fin.ext
        simp [hi]
      simp [hlast]
    have hv := congrArg Fin.val h
    rw [h2] at hv
    simp [hi] at hv
  · have h1 : (i+1).val = i.val + 1 := by simp [Fin.val_add_one, hi]
    by_cases hi1 : i+1 = Fin.last (n+2)
    · have h2 : (i+1+1).val = 0 := by simp [hi1]
      have hv := congrArg Fin.val h
      rw [h2] at hv
      have hi1v : (i+1).val = n+2 := by simp [hi1]
      omega
    · have h2 : (i+1+1).val = i.val + 2 := by
        simp [Fin.val_add_one, hi, hi1]
      have hv := congrArg Fin.val h
      rw [h2] at hv
      omega

private noncomputable abbrev M (n : ℕ) : Real := by
  classical
  let M : Real := (n+2 : Nat)
  exact M

private noncomputable abbrev kmax (n : ℕ) : Fin (n+3) := by
  classical
  let kmax : Fin (n+3) := Fin.last (n+2)
  exact kmax

private theorem hqzero (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q i = ((↑(↑i
    : ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) : q (0 : Fin (n+3)) = (0,0) := by
  classical
  rw [hq]; simp

private theorem hqmax (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q i = ((↑(↑i :
    ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) : q (kmax n) = ((M n),(M n)^2) := by
  classical
  let M : Real := (n+2 : Nat)
  let kmax : Fin (n+3) := Fin.last (n+2)
  change (q kmax = (M,M^2))
  rw [hq]
  simp [kmax, M]

private noncomputable abbrev L (n : ℕ) (j : Fin (n + 2)) (x : Real) : Real := by
  classical
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  exact L j x

private noncomputable abbrev D (n : ℕ) : Set (Real × Real) := by
  classical
  let M : Real := (n+2 : Nat)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  exact D

private theorem hvertex (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q i = ((↑(↑i
    : ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) : ∀ k : Fin (n+3), q k ∈ (D n) := by
  classical
  let M : Real := (n+2 : Nat)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  change (∀ k : Fin (n+3), q k ∈ D)
  intro k
  rw [hq k]
  have hkM : k.val ≤ n+2 := by omega
  have hkM' : (k.val : Real) ≤ M := by
    dsimp [M]
    exact_mod_cast hkM
  refine ⟨Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · change (k.val : Real) ≤ M
    exact hkM'
  · change (k.val : Real)^2 ≤ M * (k.val : Real)
    nlinarith [mul_nonneg (show 0 ≤ (k.val : Real) by positivity)
      (sub_nonneg.mpr hkM')]
  · intro j
    have hkcase : k.val ≤ j.val ∨ j.val < k.val := by omega
    have hprod : 0 ≤ ((k.val : Real)-(j.val : Real)) *
        ((k.val : Real)-(j.val : Real)-1) := by
      rcases hkcase with hk | hk
      · have hk' : (k.val : Real) ≤ (j.val : Real) := by exact_mod_cast hk
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hk') (by linarith)
      · have hk' : (j.val : Real)+1 ≤ (k.val : Real) := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
        have hk'' : (j.val : Real) ≤ (k.val : Real) := by linarith
        exact mul_nonneg (sub_nonneg.mpr hk'') (by linarith)
    dsimp [L]
    nlinarith [hprod]

private theorem hDconv (n : ℕ) (seg_rep : ∀ (a b x : ℝ × ℝ), x ∈ segment ℝ a b → ∃ t ∈ Set.Icc (0
    : ℝ) 1, x = (1 - t) • a + t • b) : Convex Real (D n) := by
  classical
  let M : Real := (n+2 : Nat)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  change (Convex Real D)
  rw [convex_iff_segment_subset]
  intro a ha b hb z hz
  obtain ⟨t, ht, hzt⟩ := seg_rep a b z hz
  rw [hzt]
  rcases ha with ⟨ha0, haM, haU, haL⟩
  rcases hb with ⟨hb0, hbM, hbU, hbL⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hlin (j : Fin (n+2)) :
      L j ((1-t)*a.1+t*b.1) = (1-t)*L j a.1+t*L j b.1 := by
    dsimp [L]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 ≤ (1-t)*a.1+t*b.1
    nlinarith [mul_nonneg ht1 ha0, mul_nonneg ht0 hb0]
  · change (1-t)*a.1+t*b.1 ≤ M
    nlinarith [mul_nonneg ht1 (sub_nonneg.mpr haM),
      mul_nonneg ht0 (sub_nonneg.mpr hbM)]
  · change (1-t)*a.2+t*b.2 ≤ M*((1-t)*a.1+t*b.1)
    nlinarith [mul_nonneg ht1 (sub_nonneg.mpr haU),
      mul_nonneg ht0 (sub_nonneg.mpr hbU)]
  · intro j
    change L j ((1-t)*a.1+t*b.1) ≤ (1-t)*a.2+t*b.2
    rw [hlin]
    nlinarith [mul_nonneg ht1 (sub_nonneg.mpr (haL j)),
      mul_nonneg ht0 (sub_nonneg.mpr (hbL j))]

private theorem hKD (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hvertex : ∀ (k : Fin (n + 3)), q k ∈ (D
    n)) (hDconv : Convex ℝ (D n)) : convexHull Real (Set.range q) ⊆ (D n) := by
  classical
  let M : Real := (n+2 : Nat)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  change (∀ (k : Fin (n + 3)), q k ∈ D) at hvertex
  change (Convex ℝ D) at hDconv
  change (convexHull Real (Set.range q) ⊆ D)
  apply convexHull_min
  · rintro z ⟨k, rfl⟩
    exact hvertex k
  · exact hDconv

private theorem choose_interval (n : ℕ) (x : Real) (hx0 : 0 ≤ x) (hxM : x ≤ (M n)) :
      ∃ j : Fin (n+2), (j.val : Real) ≤ x ∧ x ≤ (j.val : Real)+1 := by
  classical
  let M : Real := (n+2 : Nat)
  change x ≤ M at hxM
  let r := min ⌊x⌋₊ (n+1)
  have hfloor : (⌊x⌋₊ : Real) ≤ x := Nat.floor_le hx0
  have hr_le : r ≤ n+1 := Nat.min_le_right _ _
  have hr_cast : (r : Real) ≤ x := by
    exact (Nat.cast_le.mpr (Nat.min_le_left _ _)).trans hfloor
  have hx_lt : x < (⌊x⌋₊ : Real)+1 := Nat.lt_floor_add_one x
  have hr_lt : x ≤ (r : Real)+1 := by
    by_cases hcap : ⌊x⌋₊ ≤ n+1
    · have hr : r = ⌊x⌋₊ := Nat.min_eq_left hcap
      rw [hr]
      exact hx_lt.le
    · have hfloorM : ⌊x⌋₊ = n+2 := by
        have hfloor_le : ⌊x⌋₊ ≤ n+2 := by
          apply Nat.floor_le_of_le
          simpa [M] using hxM
        omega
      have hx_eq : x = M := by
        have hfcast : (n : Real)+2 ≤ x := by
          simpa [Nat.cast_add] using
            (show (↑(n+2) : Real) ≤ x by rw [← hfloorM]; exact hfloor)
        exact le_antisymm (by simpa [M] using hxM) (by simpa [M] using hfcast)
      have hr : r = n+1 := by simp [r, hfloorM]
      rw [hx_eq, hr]
      change (↑(n+2) : Real) ≤ (↑(n+1) : Real)+1
      exact_mod_cast (show n+2 ≤ n+1+1 by omega)
  refine ⟨⟨r, by omega⟩, ?_, ?_⟩
  · exact hr_cast
  · exact hr_lt

private theorem segment_combo_mem (a b : Real × Real) (t : Real)
      (ht : t ∈ Set.Icc (0 : Real) 1) :
      (1-t) • a + t • b ∈ segment Real a b := by
  classical
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module]

private theorem qmem (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (i : Fin (n + 3)) : q i ∈ convexHull Real
    (Set.range q) := by
  classical
  exact subset_convexHull Real _ (Set.mem_range_self i)

private theorem segment_memK (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (qmem : ∀ (i : Fin (n + 3)), q i ∈
    (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range q)) (a b : Fin (n + 3)) :
      segment Real (q a) (q b) ⊆ convexHull Real (Set.range q) := by
  classical
  intro z hz
  exact (convex_convexHull Real (Set.range q)).segment_subset (qmem a) (qmem b) hz

private theorem hDK (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q i = ((↑(↑i :
    ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) (hqzero : q 0 = (0, 0)) (hqmax : q (kmax n) = ((M n), (M n) ^
    2)) (choose_interval : ∀ (x : ℝ), 0 ≤ x → x ≤ (M n) → ∃ (j : Fin (n + 2)), (↑(↑j : ℕ) : ℝ) ≤
    x ∧ x ≤ (↑(↑j : ℕ) : ℝ) + 1) (segment_combo_mem : ∀ (a b : ℝ × ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 - t) • a + t • b ∈ segment ℝ a b) (qmem : ∀ (i : Fin (n + 3)), q i ∈ (convexHull ℝ : Set
    (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range q)) (segment_memK : ∀ (a b : Fin (n + 3)), segment ℝ (q a)
    (q b) ⊆ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range q)) : (D n) ⊆ convexHull Real
    (Set.range q) := by
  classical
  let M : Real := (n+2 : Nat)
  let kmax : Fin (n+3) := Fin.last (n+2)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  change (q kmax = (M, M ^ 2)) at hqmax
  change (∀ (x : ℝ), 0 ≤ x → x ≤ M → ∃ (j : Fin (n + 2)), (↑(↑j : ℕ) : ℝ) ≤ x ∧ x ≤ (↑(↑j : ℕ) :
      ℝ) + 1) at choose_interval
  change (D ⊆ convexHull Real (Set.range q))
  intro z hz
  rcases hz with ⟨hx0, hxM, hyU, hyL⟩
  by_cases hxzero : z.1 = 0
  · have hlow := hyL (⟨0, by omega⟩ : Fin (n+2))
    have hylo : 0 ≤ z.2 := by simpa [L, hxzero] using hlow
    have hyhi : z.2 ≤ 0 := by simpa [hxzero] using hyU
    have hz : z = q (0 : Fin (n+3)) := by
      apply Prod.ext
      · rw [hxzero, hqzero]
      · rw [hqzero]
        exact le_antisymm hyhi hylo
    rw [hz]
    exact qmem 0
  by_cases hxmax : z.1 = M
  · let jt : Fin (n+2) := ⟨n+1, by omega⟩
    have hlow := hyL jt
    have hline : L jt M = M^2 := by
      dsimp [L, jt, M]
      push_cast
      ring
    have hylo : M^2 ≤ z.2 := by simpa [hxmax, hline] using hlow
    have hyhi : z.2 ≤ M^2 := by rw [hxmax] at hyU; nlinarith [hyU]
    have hz : z = q kmax := by
      apply Prod.ext
      · rw [hxmax, hqmax]
      · rw [hqmax]
        exact le_antisymm hyhi hylo
    rw [hz]
    exact qmem kmax
  have hxpos : 0 < z.1 := by
    apply lt_of_le_of_ne hx0
    intro h
    exact hxzero h.symm
  have hxlt : z.1 < M := lt_of_le_of_ne hxM hxmax
  obtain ⟨j, hjx, hxj⟩ := choose_interval z.1 hx0 hxM
  let jj : Fin (n+3) := ⟨j.val, by omega⟩
  let jn : Fin (n+3) := jj+1
  have hjne : jj ≠ Fin.last (n+2) := by
    intro h
    have hv := congrArg Fin.val h
    simp [jj] at hv
    omega
  have hval : jn.val = j.val+1 := by
    simp [jn, Fin.val_add_one, hjne, jj]
  let t : Real := z.1 - (j.val : Real)
  have ht : t ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [t]
      exact sub_nonneg.mpr hjx
    · dsimp [t]
      have hxj' : z.1 ≤ (j.val : Real)+1 := hxj
      linarith
  let lower : Real × Real := (1-t) • q jj + t • q jn
  have hlower : lower = (z.1, L j z.1) := by
    apply Prod.ext
    · dsimp [lower, t]
      rw [hq jj, hq jn]
      simp only []
      have hval' : (jn.val : Real) = (j.val : Real)+1 := by exact_mod_cast hval
      rw [hval']
      ring
    · dsimp [lower, t]
      rw [hq jj, hq jn]
      simp only []
      have hval' : (jn.val : Real) = (j.val : Real)+1 := by exact_mod_cast hval
      rw [hval']
      dsimp [L]
      ring
  have hMpos : 0 < M := by dsimp [M]; positivity
  let s : Real := z.1 / M
  have hs : s ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [s]
      exact div_nonneg hx0 hMpos.le
    · dsimp [s]
      exact (div_le_one hMpos).2 (by simpa [M] using hxM)
  let upper : Real × Real := (1-s) • q (0:Fin (n+3)) + s • q kmax
  have hupper : upper = (z.1, M*z.1) := by
    apply Prod.ext
    · dsimp [upper, s]
      rw [hqzero, hqmax]
      simp only []
      field_simp [ne_of_gt hMpos]
      ring
    · dsimp [upper, s]
      rw [hqzero, hqmax]
      simp only []
      field_simp [ne_of_gt hMpos]
      ring
  have hlower_mem : lower ∈ convexHull Real (Set.range q) :=
    segment_memK jj jn (segment_combo_mem (q jj) (q jn) t ht)
  have hupper_mem : upper ∈ convexHull Real (Set.range q) :=
    segment_memK (0:Fin (n+3)) kmax (segment_combo_mem
      (q (0:Fin (n+3))) (q kmax) s hs)
  have hy_bounds : L j z.1 ≤ z.2 ∧ z.2 ≤ M*z.1 := ⟨hyL j, hyU⟩
  let A : Real := (j.val : Real) * (M - (j.val : Real))
  let B : Real := ((j.val : Real)+1) * (M - (j.val : Real)-1)
  have hJplus : (j.val : Real)+1 ≤ M := by
    have hc : ((j.val+1 : Nat) : Real) ≤ ((n+2 : Nat) : Real) := by
      exact_mod_cast (show j.val+1 ≤ n+2 by omega)
    simpa [M, Nat.cast_add] using hc
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (by linarith [hJplus])
  have hfactor : M*z.1 - L j z.1 = (1-t)*A+t*B := by
    dsimp [A, B, L, t]
    ring
  have hgap : L j z.1 < M*z.1 := by
    by_cases hj0 : j.val = 0
    · have hJ : (j.val : Real) = 0 := by exact_mod_cast hj0
      have htEq : t = z.1 := by dsimp [t]; rw [hJ]; ring
      have hAeq : A = 0 := by dsimp [A]; rw [hJ]; ring
      have hBpos : 0 < B := by
        dsimp [B]
        rw [hJ]
        nlinarith [show 2 ≤ M by dsimp [M]; exact_mod_cast (show 2 ≤ n+2 by omega)]
      rw [← sub_pos, hfactor, htEq, hAeq]
      simpa using mul_pos hxpos hBpos
    · have hJpos : 0 < (j.val : Real) := by
        exact_mod_cast (Nat.pos_of_ne_zero hj0)
      have hApos : 0 < A := by
        dsimp [A]
        exact mul_pos hJpos (by linarith [hJplus])
      by_cases htlt : t < 1
      · rw [← sub_pos, hfactor]
        exact add_pos_of_pos_of_nonneg
          (mul_pos (sub_pos.mpr htlt) hApos) (mul_nonneg ht.1 hB)
      · have htEq : t = 1 := le_antisymm ht.2 (le_of_not_gt htlt)
        have hxEq : z.1 = (j.val : Real)+1 := by
          dsimp [t] at htEq
          linarith
        have hJstrict : (j.val : Real)+1 < M := by linarith [hxEq, hxlt]
        have hBpos : 0 < B := by
          dsimp [B]
          exact mul_pos (by linarith [hJpos]) (by linarith [hJstrict])
        rw [← sub_pos, hfactor, htEq]
        simpa using hBpos
  let u : Real := (z.2 - L j z.1) / (M*z.1 - L j z.1)
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [u]
      exact div_nonneg (sub_nonneg.mpr hy_bounds.1) (le_of_lt (sub_pos.mpr hgap))
    · dsimp [u]
      apply (div_le_iff₀ (sub_pos.mpr hgap)).2
      nlinarith [hy_bounds.2]
  have hzline : z = (1-u) • lower + u • upper := by
    apply Prod.ext
    · rw [hlower, hupper]
      simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
      ring
    · rw [hlower, hupper]
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      dsimp [u]
      field_simp [ne_of_gt (sub_pos.mpr hgap)]
      ring
  rw [hzline]
  exact (convex_convexHull Real (Set.range q)).segment_subset hlower_mem hupper_mem
    (segment_combo_mem lower upper u hu)

private theorem hHullEq (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hKD : (convexHull ℝ : Set (ℝ × ℝ) →
    Set (ℝ × ℝ)) (Set.range q) ⊆ (D n)) (hDK : (D n) ⊆ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ))
    (Set.range q)) : convexHull Real (Set.range q) = (D n) := by
  classical
  let M : Real := (n+2 : Nat)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  change ((convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range q) ⊆ D) at hKD
  change (D ⊆ (convexHull ℝ : Set (ℝ × ℝ) → Set (ℝ × ℝ)) (Set.range q)) at hDK
  change (convexHull Real (Set.range q) = D)
  exact Set.Subset.antisymm hKD hDK

private theorem lowerEdge (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q i =
    ((↑(↑i : ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) (segment_combo_mem : ∀ (a b : ℝ × ℝ), ∀ t ∈ Set.Icc
    (0 : ℝ) 1, (1 - t) • a + t • b ∈ segment ℝ a b) (j : Fin (n + 2)) (x : Real)
      (hx0 : (j.val : Real) ≤ x) (hx1 : x ≤ (j.val : Real) + 1) :
      (x, (L n) j x) ∈ segment Real (q ⟨j.val, by omega⟩)
        (q ((⟨j.val, by omega⟩ : Fin (n+3))+1)) := by
  classical
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  change ((x, L j x) ∈ segment Real (q ⟨j.val, by omega⟩)
        (q ((⟨j.val, by omega⟩ : Fin (n+3))+1)))
  let jj : Fin (n+3) := ⟨j.val, by omega⟩
  let jn : Fin (n+3) := jj+1
  have hjne : jj ≠ Fin.last (n+2) := by
    intro h
    have hv := congrArg Fin.val h
    simp [jj] at hv
    omega
  have hval : jn.val = j.val+1 := by simp [jn, Fin.val_add_one, hjne, jj]
  let t : Real := x-(j.val:Real)
  have ht : t ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [t]
      exact sub_nonneg.mpr hx0
    · dsimp [t]
      linarith [hx1]
  have hpoint : (x,L j x) = (1-t) • q jj+t • q jn := by
    apply Prod.ext
    · dsimp [t]
      rw [hq jj,hq jn]
      simp only []
      have hval' : (jn.val:Real)=(j.val:Real)+1 := by exact_mod_cast hval
      rw [hval']
      ring
    · dsimp [t]
      rw [hq jj,hq jn]
      simp only []
      have hval' : (jn.val:Real)=(j.val:Real)+1 := by exact_mod_cast hval
      rw [hval']
      dsimp [L]
      ring
  rw [hpoint]
  exact segment_combo_mem (q jj) (q jn) t ht

private theorem upperEdge (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hqzero : q 0 = (0, 0)) (hqmax : q
    (kmax n) = ((M n), (M n) ^ 2)) (segment_combo_mem : ∀ (a b : ℝ × ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 - t) • a + t • b ∈ segment ℝ a b) (x : Real) (hx0 : 0 ≤ x) (hxM : x ≤ (M n)) :
      (x, (M n)*x) ∈ segment Real (q (0 : Fin (n+3))) (q (kmax n)) := by
  classical
  let M : Real := (n+2 : Nat)
  let kmax : Fin (n+3) := Fin.last (n+2)
  change (q kmax = (M, M ^ 2)) at hqmax
  change ((x, M*x) ∈ segment Real (q (0 : Fin (n+3))) (q kmax))
  have hMpos : 0 < M := by dsimp [M]; positivity
  let s : Real := x/M
  have hs : s ∈ Set.Icc (0 : Real) 1 := by
    constructor
    · dsimp [s]
      exact div_nonneg hx0 hMpos.le
    · dsimp [s]
      exact (div_le_one hMpos).2 hxM
  have hpoint : (x, M*x) = (1-s) • q (0 : Fin (n+3)) + s • q kmax := by
    apply Prod.ext
    · dsimp [s]
      rw [hqzero,hqmax]
      simp only []
      field_simp [ne_of_gt hMpos]
      ring
    · dsimp [s]
      rw [hqzero,hqmax]
      simp only []
      field_simp [ne_of_gt hMpos]
      ring
  rw [hpoint]
  exact segment_combo_mem (q (0 : Fin (n+3))) (q kmax) s hs

private theorem edgeLowerEquation (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (hq : ∀ (i : Fin (n + 3)), q
    i = ((↑(↑i : ℕ) : ℝ), (↑(↑i : ℕ) : ℝ) ^ 2)) (seg_rep : ∀ (a b x : ℝ × ℝ), x ∈ segment ℝ a b →
    ∃ t ∈ Set.Icc (0 : ℝ) 1, x = (1 - t) • a + t • b) (i : Fin (n + 3)) (hi : i ≠ (kmax n)) (z :
    Real × Real)
      (hz : z ∈ segment Real (q i) (q (i + 1))) :
      ∃ j : Fin (n+2), (L n) j z.1 = z.2 := by
  classical
  let kmax : Fin (n+3) := Fin.last (n+2)
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  change (∃ j : Fin (n+2), L j z.1 = z.2)
  have hival : i.val ≤ n+1 := by
    by_contra hn
    have : i.val = n+2 := by omega
    apply hi
    apply Fin.ext
    simpa [kmax] using this
  let j : Fin (n+2) := ⟨i.val, by omega⟩
  have hnext : (i+1).val = i.val+1 := by
    simp [Fin.val_add_one, hi]
  have hnextR : ((i+1).val : Real) = (i.val : Real)+1 := by exact_mod_cast hnext
  obtain ⟨t, ht, hzt⟩ := seg_rep (q i) (q (i+1)) z hz
  refine ⟨j, ?_⟩
  rw [hzt, hq i, hq (i+1)]
  simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul]
  have hjval : (j.val : Real) = (i.val : Real) := by rfl
  rw [hnextR, hjval]
  dsimp [L]
  ring

private theorem edgeUpperEquation (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) (seg_rep : ∀ (a b x : ℝ × ℝ),
    x ∈ segment ℝ a b → ∃ t ∈ Set.Icc (0 : ℝ) 1, x = (1 - t) • a + t • b) (hqzero : q 0 = (0, 0))
    (hqmax : q (kmax n) = ((M n), (M n) ^ 2)) (z : Real × Real)
      (hz : z ∈ segment Real (q (kmax n)) (q ((kmax n) + 1))) :
      z.2 = (M n)*z.1 := by
  classical
  let M : Real := (n+2 : Nat)
  let kmax : Fin (n+3) := Fin.last (n+2)
  change (q kmax = (M, M ^ 2)) at hqmax
  change (z.2 = M*z.1)
  have hwrap : kmax+1 = (0 : Fin (n+3)) := by
    apply Fin.ext
    simp [kmax]
  obtain ⟨t, ht, hzt⟩ := seg_rep (q kmax) (q (kmax+1)) z hz
  rw [hzt, hqmax, hwrap, hqzero]
  simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul]
  ring

private theorem hcompact (n : ℕ) (q : Fin (n + 3) → ℝ × ℝ) : IsCompact ((convexHull ℝ : Set (ℝ ×
    ℝ) → Set (ℝ × ℝ)) (Set.range q)) := by
  classical
  exact (Set.finite_range q).isCompact_convexHull Real

end ParabolaHullConstruction

namespace ParabolaHullInterior

private theorem hshared :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
        : ℕ))), ∀ (t : ℝ), ((1-t) * P3381T1TriangleDeterminant ![q i, q (i+1), q j] = 0) → (t *
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)] = 0) → (j ≠ i ∧ j ≠ i+1 → 0 <
        P3381T1TriangleDeterminant ![q i, q (i+1), q j]) → (j+1 ≠ i ∧ j+1 ≠ i+1 → 0 <
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)]) → (j = i ∨ j = i+1) ∨ (j+1 = i ∨
        j+1 = i+1) := by
  classical
  intro n q i j t hleftzero hrightzero hleftstrict hrightstrict
  by_cases hj : j = i ∨ j = i+1
  · exact Or.inl hj
  · right
    by_contra hj'
    have hp₁ := hleftstrict ⟨by tauto, by tauto⟩
    have hp₂ := hrightstrict ⟨by tauto, by tauto⟩
    have htone : 1-t = 0 := (mul_eq_zero.mp hleftzero).resolve_right hp₁.ne'
    have htzero : t = 0 := (mul_eq_zero.mp hrightzero).resolve_right hp₂.ne'
    linarith

private theorem hnotboth :
    ∀ (n : Nat),
      ∀ (q : Fin (n + 3) → Real × Real),
        (∀ (i : Fin (n + 3)), i + 1 + 1 ≠ i) →
          ∀ (i : Fin (n + (3 : ℕ))),
            ∀ (j : Fin (n + (3 : ℕ))),
              i ≠ j →
                ∀ (x : ℝ × ℝ),
                  ∀ (t : ℝ),
                    x = ((1 : ℝ) - t) • q j + t • q (j + (1 : Fin (n + (3 : ℕ)))) →
                      ((1 : ℝ) - t) *
                            P3381T1TriangleDeterminant
                            ![q i, q (i + (1 : Fin (n + (3 : ℕ)))), q j] +
                            t *
                            P3381T1TriangleDeterminant
                            ![q i, q (i + (1 : Fin (n + (3 : ℕ)))),
                            q (j + (1 : Fin (n + (3 : ℕ))))] =
                          (0 : ℝ) →
                        P3381T1TriangleDeterminant
                            ![q i, q (i + (1 : Fin (n + (3 : ℕ)))),
                            ((1 : ℝ) - t) • q j + t • q (j + (1 : Fin (n + (3 : ℕ))))] =
                            ((1 : ℝ) - t) *
                            P3381T1TriangleDeterminant
                            ![q i, q (i + (1 : Fin (n + (3 : ℕ)))), q j] +
                            t *
                            P3381T1TriangleDeterminant
                            ![q i, q (i + (1 : Fin (n + (3 : ℕ)))),
                            q (j + (1 : Fin (n + (3 : ℕ))))] →
                          0 ≤ (1 - t) * P3381T1TriangleDeterminant ![q i, q (i + 1), q j] →
                            0 ≤
                            t * P3381T1TriangleDeterminant ![q i, q (i + 1), q (j + 1)] →
                            (1 - t) * P3381T1TriangleDeterminant ![q i, q (i + 1), q j] =
                            0 →
                            t * P3381T1TriangleDeterminant ![q i, q (i + 1), q (j + 1)] =
                            0 →
                            (j ≠ i ∧ j ≠ i + 1 →
                            0 < P3381T1TriangleDeterminant ![q i, q (i + 1), q j]) →
                            (j + 1 ≠ i ∧ j + 1 ≠ i + 1 →
                            0 < P3381T1TriangleDeterminant ![q i, q (i + 1), q (j + 1)]) →
                            (j = i ∨ j = i + 1) ∨ j + 1 = i ∨ j + 1 = i + 1 →
                            ¬((j = i ∨ j = i + 1) ∧ (j + 1 = i ∨ j + 1 = i + 1)) := by
  classical
  intro n q no_two_cycle i j hij x t hxt hz hcomb hleft hright hleftzero hrightzero hleftstrict
      hrightstrict hshared
  rintro ⟨hj, hj'⟩
  rcases hj with hj | hj <;> rcases hj' with hj' | hj'
  · subst j
    have hne : i+1 ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      by_cases hi : i = Fin.last (n+2)
      · simp [hi] at hv
      · have hv' : (i+1).val = i.val+1 := by simp [Fin.val_add_one, hi]
        rw [hv'] at hv
        omega
    exact hne hj'
  · subst j
    exact hij (add_right_cancel hj')
  · subst j
    exact no_two_cycle i hj'
  · exact hij (add_right_cancel hj'.symm)

private theorem hxend :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), ∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n + (3
        : ℕ))), ∀ (x : ℝ × ℝ), ∀ (t : ℝ), (x = ((1 : ℝ) - t) • q j + t • q (j + (1 : Fin (n + (3
        : ℕ))))) → ((1-t) * P3381T1TriangleDeterminant ![q i, q (i+1), q j] = 0) → (t *
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)] = 0) → (j ≠ i ∧ j ≠ i+1 → 0 <
        P3381T1TriangleDeterminant ![q i, q (i+1), q j]) → (j+1 ≠ i ∧ j+1 ≠ i+1 → 0 <
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)]) → ((j = i ∨ j = i+1) ∨ (j+1 = i ∨
        j+1 = i+1)) → (¬ ((j = i ∨ j = i+1) ∧ (j+1 = i ∨ j+1 = i+1))) → x = q j ∧ (j = i ∨ j =
        i+1) ∨
      x = q (j+1) ∧ (j+1 = i ∨ j+1 = i+1) := by
  classical
  intro n q i j x t hxt hleftzero hrightzero hleftstrict hrightstrict hshared hnotboth
  rcases hshared with hj | hj'
  · have hj' : ¬ (j+1 = i ∨ j+1 = i+1) := fun h => hnotboth ⟨hj,h⟩
    have hp := hrightstrict ⟨by tauto, by tauto⟩
    have ht0 : t = 0 := (mul_eq_zero.mp hrightzero).resolve_right hp.ne'
    left
    refine ⟨?_, hj⟩
    rw [hxt, ht0]
    simp
  · have hj : ¬ (j = i ∨ j = i+1) := by
      intro h
      exact hnotboth ⟨h,hj'⟩
    have hp := hleftstrict ⟨by tauto, by tauto⟩
    have ht1 : 1-t = 0 := (mul_eq_zero.mp hleftzero).resolve_right hp.ne'
    right
    refine ⟨?_, hj'⟩
    rw [hxt]
    have : t = 1 := by linarith
    rw [this]
    simp

private theorem hUopen :
    let U : Set (Real × Real) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < 1}
    IsOpen U := by
  classical
  intro U
  have hEq : U = {z | 0 < z.1} ∩ {z | 0 < z.2} ∩ {z | z.1+z.2 < 1} := by
    ext z
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨⟨h1,h2⟩,h3⟩
    · rintro ⟨⟨h1,h2⟩,h3⟩
      exact ⟨h1,h2,h3⟩
  rw [hEq]
  exact ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const)

private theorem hUsub :
    let p : Fin 3 → Real × Real := ![(0,0),(1,0),(0,1)]
    let w (z : Real × Real) : Fin 3 → Real := ![1-z.1-z.2,z.1,z.2]
    (∀ (z : Real × Real), (∑ i, w z i) = 1) → (∀ (z : Real × Real), (∑ i, w z i • p i) = z) →
    let U : Set (Real × Real) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < 1}
    U ⊆ convexHull Real (Set.range p) := by
  classical
  intro p w hw_sum hp_sum U z hz
  apply mem_convexHull_of_exists_fintype (w z) p
  · intro i
    fin_cases i
    · dsimp [w]
      linarith [hz.2.2]
    · dsimp [w]
      exact hz.1.le
    · dsimp [w]
      exact hz.2.1.le
  · exact hw_sum z
  · intro i
    exact Set.mem_range_self i
  · exact hp_sum z

private theorem hImageSub :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real),
    let f : Fin 3 → Fin (n+3) := fun i => ⟨i.val, by omega⟩
    let p : Fin 3 → Real × Real := ![(0,0),(1,0),(0,1)]
    ∀ (H : ℝ × ℝ ≃ₜ ℝ × ℝ), (∀ (w : Fin (3 : ℕ) → ℝ), ∑ i : Fin (3 : ℕ), w i = (1 : ℝ) → (H : ℝ ×
        ℝ → ℝ × ℝ) (∑ i : Fin (3 : ℕ), w i • p i) = ∑ i : Fin (3 : ℕ), w i • (q ∘ f) i) →
    let w (z : Real × Real) : Fin 3 → Real := ![1-z.1-z.2,z.1,z.2]
    (∀ (z : Real × Real), (∑ i, w z i) = 1) → (∀ (z : Real × Real), (∑ i, w z i • p i) = z) →
    let U : Set (Real × Real) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < 1}
    (Set.range (q ∘ f) ⊆ Set.range q) → H '' U ⊆ convexHull Real (Set.range q) := by
  classical
  intro n q f p H hH w hw_sum hp_sum U target_subset
  rintro y ⟨z, hz, rfl⟩
  have hHz : H z = ∑ i, w z i • (q ∘ f) i := by
    calc
      H z = H (∑ i, w z i • p i) := congrArg H (hp_sum z).symm
      _ = ∑ i, w z i • (q ∘ f) i := hH (w z) (hw_sum z)
  rw [hHz]
  apply mem_convexHull_of_exists_fintype (w z) (q ∘ f)
  · intro i
    fin_cases i
    · dsimp [w]
      linarith [hz.2.2]
    · dsimp [w]
      exact hz.1.le
    · dsimp [w]
      exact hz.2.1.le
  · exact hw_sum z
  · intro i
    exact target_subset (Set.mem_range_self i)
  · rfl

private theorem hOopen :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let O : Set (Real × Real) :=
      {z | 0 < z.1 ∧ z.1 < M ∧ z.2 < M*z.1 ∧ ∀ j : Fin (n+2), L j z.1 < z.2}
    IsOpen O := by
  classical
  intro n M L O
  have hlow : IsOpen (⋂ j : Fin (n+2), {z : Real × Real | L j z.1 < z.2}) :=
    isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_snd
  have hEq : O = {z | 0 < z.1} ∩
      ({z | z.1 < M} ∩ ({z | z.2 < M*z.1} ∩
        ⋂ j : Fin (n+2), {z : Real × Real | L j z.1 < z.2})) := by
    ext z
    simp [O]
  rw [hEq]
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_snd (by fun_prop)).inter hlow))

private theorem noLeftInterior :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    (∀ (z : Real × Real), (z ∈ interior D) → ∃ e : Real, 0 < e ∧ Metric.ball z e ⊆ D) → ∀ (z :
        Real × Real), (z ∈ interior D) → z.1 ≠ 0 := by
  classical
  intro n M L D ballAt z hz heq
  obtain ⟨e,he,hball⟩ := ballAt z hz
  let w : Real × Real := (z.1-e/2,z.2)
  have hwball : w ∈ Metric.ball z e := by
    change dist w z < e
    simp [w, Prod.dist_eq, Real.dist_eq,
      abs_of_pos (show 0 < e/2 by linarith)]
    linarith
  have hwD := hball hwball
  rcases hwD with ⟨hw0,_,_,_⟩
  dsimp [w] at hw0
  rw [heq] at hw0
  linarith

private theorem noRightInterior :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    (∀ (z : Real × Real), (z ∈ interior D) → ∃ e : Real, 0 < e ∧ Metric.ball z e ⊆ D) → ∀ (z :
        Real × Real), (z ∈ interior D) → z.1 ≠ M := by
  classical
  intro n M L D ballAt z hz heq
  obtain ⟨e,he,hball⟩ := ballAt z hz
  let w : Real × Real := (z.1+e/2,z.2)
  have hwball : w ∈ Metric.ball z e := by
    change dist w z < e
    simp [w, Prod.dist_eq, Real.dist_eq,
      abs_of_pos (show 0 < e/2 by linarith)]
    linarith
  have hwD := hball hwball
  rcases hwD with ⟨_,hwM,_,_⟩
  dsimp [w] at hwM
  rw [heq] at hwM
  linarith

private theorem noUpperInterior :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    (∀ (z : Real × Real), (z ∈ interior D) → ∃ e : Real, 0 < e ∧ Metric.ball z e ⊆ D) → ∀ (z :
        Real × Real), (z ∈ interior D) → (z.2 = M*z.1) → False := by
  classical
  intro n M L D ballAt z hz heq
  obtain ⟨e,he,hball⟩ := ballAt z hz
  let w : Real × Real := (z.1,z.2+e/2)
  have hwball : w ∈ Metric.ball z e := by
    change dist w z < e
    simp [w, Prod.dist_eq, Real.dist_eq,
      abs_of_pos (show 0 < e/2 by linarith)]
    linarith
  have hwD := hball hwball
  rcases hwD with ⟨_,_,hwU,_⟩
  dsimp [w] at hwU
  rw [heq] at hwU
  linarith

private theorem noLowerInterior :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    (∀ (z : Real × Real), (z ∈ interior D) → ∃ e : Real, 0 < e ∧ Metric.ball z e ⊆ D) → ∀ (z :
        Real × Real), (z ∈ interior D) → ∀ (j : Fin (n+2)), (L j z.1 = z.2) → False := by
  classical
  intro n M L D ballAt z hz j heq
  obtain ⟨e,he,hball⟩ := ballAt z hz
  let w : Real × Real := (z.1,z.2-e/2)
  have hwball : w ∈ Metric.ball z e := by
    change dist w z < e
    simp [w, Prod.dist_eq, Real.dist_eq,
      abs_of_pos (show 0 < e/2 by linarith)]
    linarith
  have hwD := hball hwball
  have hwL := hwD.2.2.2 j
  dsimp [w] at hwL
  rw [heq] at hwL
  linarith

private theorem interiorStrict :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    let O : Set (Real × Real) :=
      {z | 0 < z.1 ∧ z.1 < M ∧ z.2 < M*z.1 ∧ ∀ j : Fin (n+2), L j z.1 < z.2}
    (∀ (z : Real × Real), (z ∈ interior D) → z.1 ≠ 0) → (∀ (z : Real × Real), (z ∈ interior D) →
        z.1 ≠ M) → (∀ (z : Real × Real), (z ∈ interior D) → (z.2 = M*z.1) → False) → (∀ (z : Real
        × Real), (z ∈ interior D) → ∀ (j : Fin (n+2)), (L j z.1 = z.2) → False) → ∀ (z : Real ×
        Real), (z ∈ interior D) → z ∈ O := by
  classical
  intro n M L D O noLeftInterior noRightInterior noUpperInterior noLowerInterior z hz
  have hzD : z ∈ D := interior_subset hz
  rcases hzD with ⟨hz0,hzM,hzU,hzL⟩
  have h0 : 0 < z.1 := by
    apply lt_of_le_of_ne hz0
    intro h
    exact noLeftInterior z hz h.symm
  have hM : z.1 < M := by
    apply lt_of_le_of_ne hzM
    exact noRightInterior z hz
  have hU : z.2 < M*z.1 := by
    apply lt_of_le_of_ne hzU
    intro h
    exact noUpperInterior z hz h
  have hL : ∀ j : Fin (n+2), L j z.1 < z.2 := by
    intro j
    apply lt_of_le_of_ne (hzL j)
    intro h
    exact noLowerInterior z hz j h
  exact ⟨h0,hM,hU,hL⟩

private theorem heqcases :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let O : Set (Real × Real) :=
      {z | 0 < z.1 ∧ z.1 < M ∧ z.2 < M*z.1 ∧ ∀ j : Fin (n+2), L j z.1 < z.2}
    ∀ (x : ℝ × ℝ), (x ∉ O) → ((0 : ℝ) ≤ x.1) → (x.1 ≤ M) → (x.2 ≤ M * x.1) → (∀ (j : Fin (n + (2
        : ℕ))), L j x.1 ≤ x.2) → x.1 = 0 ∨ x.1 = M ∨ x.2 = M*x.1 ∨
      ∃ j : Fin (n+2), L j x.1 = x.2 := by
  classical
  intro n M L O x hnotO hx0 hxM hxU hxL
  by_cases h0 : x.1 = 0
  · exact Or.inl h0
  by_cases hM : x.1 = M
  · exact Or.inr (Or.inl hM)
  by_cases hU : x.2 = M*x.1
  · exact Or.inr (Or.inr (Or.inl hU))
  by_cases hL : ∃ j : Fin (n+2), L j x.1 = x.2
  · exact Or.inr (Or.inr (Or.inr hL))
  have h0' : x.1 ≠ 0 := h0
  have hM' : x.1 ≠ M := hM
  have hU' : x.2 ≠ M*x.1 := hU
  have hstrict0 : 0 < x.1 := lt_of_le_of_ne hx0 (Ne.symm h0')
  have hstrictM : x.1 < M := lt_of_le_of_ne hxM hM'
  have hstrictU : x.2 < M*x.1 := lt_of_le_of_ne hxU hU'
  have hstrictL : ∀ j : Fin (n+2), L j x.1 < x.2 := by
    intro j
    apply lt_of_le_of_ne (hxL j)
    intro heq
    exact hL ⟨j, heq⟩
  exact (hnotO ⟨hstrict0,hstrictM,hstrictU,hstrictL⟩).elim

private theorem hjlower :
    ∀ (n : Nat),
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    ∀ (x : ℝ × ℝ), ((0 : ℝ) ≤ x.1) → (∀ (j : Fin (n + (2 : ℕ))), L j x.1 ≤ x.2) → ∀ (j : Fin (n +
        (2 : ℕ))), (L j x.1 = x.2) → (j.val : Real) ≤ x.1 := by
  classical
  intro n L x hx0 hxL j hxlower
  by_cases hj0 : j.val = 0
  · have : (j.val : Real) = 0 := by exact_mod_cast hj0
    rw [this]
    exact hx0
  · let jm : Fin (n+2) := ⟨j.val-1, by omega⟩
    have hprev : jm.val+1=j.val := by dsimp [jm]; omega
    have hprevR : (jm.val:Real)+1=(j.val:Real) := by exact_mod_cast hprev
    have hineq := hxL jm
    rw [← hxlower] at hineq
    dsimp [L] at hineq
    rw [hprevR] at hineq
    nlinarith [hineq]

private theorem hjupper :
    ∀ (n : Nat),
    let M : Real := (n+2 : Nat)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    ∀ (x : ℝ × ℝ), (x.1 ≤ M) → (∀ (j : Fin (n + (2 : ℕ))), L j x.1 ≤ x.2) → ∀ (j : Fin (n + (2 :
        ℕ))), (L j x.1 = x.2) → x.1 ≤ (j.val : Real)+1 := by
  classical
  intro n M L x hxM hxL j hxlower
  by_cases hjlast : j.val = n+1
  · have : (j.val : Real)+1 = M := by
      dsimp [M]
      exact_mod_cast congrArg Nat.succ hjlast
    rw [this]
    exact hxM
  · let jn : Fin (n+2) := ⟨j.val+1, by omega⟩
    have hnext : jn.val=j.val+1 := by rfl
    have hnextR : (jn.val:Real)=(j.val:Real)+1 := by exact_mod_cast hnext
    have hineq := hxL jn
    rw [← hxlower] at hineq
    dsimp [L] at hineq
    rw [hnextR] at hineq
    nlinarith [hineq]

private theorem hnotintK :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real),
    let M : Real := (n+2 : Nat)
    let kmax : Fin (n+3) := Fin.last (n+2)
    let L (j : Fin (n+2)) (x : Real) : Real :=
      (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
    let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
      ∀ j : Fin (n+2), L j z.1 ≤ z.2}
    (∀ (i : Fin (n+3)), (i ≠ kmax) → ∀ (z : Real × Real), (z ∈ segment Real (q i) (q (i+1))) → ∃
        j : Fin (n+2), L j z.1 = z.2) → (∀ (z : Real × Real), (z ∈ segment Real (q kmax) (q
        (kmax+1))) → z.2 = M*z.1) → (∀ (z : Real × Real), (z ∈ interior D) → (z.2 = M*z.1) →
        False) → (∀ (z : Real × Real), (z ∈ interior D) → ∀ (j : Fin (n+2)), (L j z.1 = z.2) →
        False) → ∀ (x : ℝ × ℝ), ∀ (i : Fin (n + (3 : ℕ))), (x ∈ segment ℝ (q i) (q (i + (1 : Fin
        (n + (3 : ℕ)))))) → (interior (convexHull Real (Set.range q)) = interior D) → x ∉
        interior (convexHull Real (Set.range q)) := by
  classical
  intro n q M kmax L D edgeLowerEquation edgeUpperEquation noUpperInterior noLowerInterior x i
      hxi hIntEq hxint
  have hxintD : x ∈ interior D := by simpa [hIntEq] using hxint
  by_cases hi : i = kmax
  · subst i
    have heq := edgeUpperEquation x hxi
    exact noUpperInterior x hxintD heq
  · obtain ⟨j,heq⟩ := edgeLowerEquation i hi x hxi
    exact noLowerInterior x hxintD j heq

end ParabolaHullInterior

namespace ParabolaHullEdges

private theorem edge_intersections :
    ∀ (n : Nat), ∀ (q : Fin (n + 3) → Real × Real), (∀ (i : Fin (n + (3 : ℕ))), ∀ (j : Fin (n +
        (3 : ℕ))), j ≠ i → j ≠ i + (1 : Fin (n + (3 : ℕ))) → (0 : ℝ) <
        P3381T1TriangleDeterminant ![q i, q (i + (1 : Fin (n + (3 : ℕ)))), q j]) → (∀ (a : Real
        × Real), ∀ (b : Real × Real), ∀ (x : Real × Real), (x ∈ segment Real a b) → ∃ t : Real, t
        ∈ Set.Icc 0 1 ∧ x = (1-t) • a + t • b) → (∀ (i : Fin (n + 3)), ∀ (a : Real × Real), ∀ (b
            : Real × Real), ∀ (t : Real), P3381T1TriangleDeterminant ![q i, q (i+1), (1-t) • a + t
        • b] = (1-t) * P3381T1TriangleDeterminant ![q i, q (i+1), a] + t *
        P3381T1TriangleDeterminant ![q i, q (i+1), b]) → (∀ (i : Fin (n + 3)),
            P3381T1TriangleDeterminant ![q i, q (i+1), q i] = 0) → (∀ (i : Fin (n + 3)),
            P3381T1TriangleDeterminant ![q i, q (i+1), q (i+1)] = 0) → (∀ (i : Fin (n + 3)), ∀
            (k : Fin (n + 3)), 0 ≤ P3381T1TriangleDeterminant ![q i, q (i+1), q k]) → (∀ (i :
            Fin (n +
        3)), i + 1 + 1 ≠ i) → ∀ i j : Fin (n + 3), i ≠ j →
      segment Real (q i) (q (i + 1)) ∩ segment Real (q j) (q (j + 1)) =
        {x | (x = q i ∨ x = q (i + 1)) ∧
          (x = q j ∨ x = q (j + 1))} := by
  classical
  intro n q hsupport seg_rep det_affine det_zero_left det_zero_right endpoint_det_nonneg
      no_two_cycle i j hij
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨hxi, hxj⟩
    obtain ⟨s, hs, hxs⟩ := seg_rep (q i) (q (i+1)) x hxi
    obtain ⟨t, ht, hxt⟩ := seg_rep (q j) (q (j+1)) x hxj
    have hz : P3381T1TriangleDeterminant ![q i, q (i+1), x] = 0 := by
      rw [hxs]
      rw [det_affine i (q i) (q (i+1)) s, det_zero_left, det_zero_right]
      ring
    have hcomb := det_affine i (q j) (q (j+1)) t
    rw [hxt] at hz
    rw [hcomb] at hz
    have hleft : 0 ≤ (1-t) *
        P3381T1TriangleDeterminant ![q i, q (i+1), q j] :=
      mul_nonneg (sub_nonneg.mpr ht.2) (endpoint_det_nonneg i j)
    have hright : 0 ≤ t *
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)] :=
      mul_nonneg ht.1 (endpoint_det_nonneg i (j+1))
    have hleftzero : (1-t) *
        P3381T1TriangleDeterminant ![q i, q (i+1), q j] = 0 := by
      nlinarith [hz]
    have hrightzero : t *
        P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)] = 0 := by
      nlinarith [hz]
    have hleftstrict : j ≠ i ∧ j ≠ i+1 →
        0 < P3381T1TriangleDeterminant ![q i, q (i+1), q j] := by
      intro h
      exact hsupport i j h.1 h.2
    have hrightstrict : j+1 ≠ i ∧ j+1 ≠ i+1 →
        0 < P3381T1TriangleDeterminant ![q i, q (i+1), q (j+1)] := by
      intro h
      exact hsupport i (j+1) h.1 h.2
    have hshared : (j = i ∨ j = i+1) ∨ (j+1 = i ∨ j+1 = i+1) := ParabolaHullInterior.hshared n
        q i j t hleftzero hrightzero hleftstrict hrightstrict
    have hnotboth : ¬ ((j = i ∨ j = i+1) ∧ (j+1 = i ∨ j+1 = i+1)) :=
        ParabolaHullInterior.hnotboth n q no_two_cycle i j hij x t hxt hz hcomb hleft
        hright hleftzero hrightzero hleftstrict hrightstrict hshared
    have hxend : x = q j ∧ (j = i ∨ j = i+1) ∨
    x = q (j+1) ∧ (j+1 = i ∨ j+1 = i+1) := ParabolaHullInterior.hxend n q i j x t hxt hleftzero
        hrightzero hleftstrict hrightstrict hshared hnotboth
    rcases hxend with ⟨hxj, hji⟩ | ⟨hxj, hji⟩
    · rcases hji with hji | hji
      · subst j
        exact ⟨Or.inl hxj, Or.inl hxj⟩
      · subst j
        exact ⟨Or.inr hxj, Or.inl hxj⟩
    · rcases hji with hji | hji
      · subst i
        exact ⟨Or.inl hxj, Or.inr hxj⟩
      · have hj : j = i := add_right_cancel hji
        subst j
        exact ⟨Or.inr hxj, Or.inr hxj⟩
  · rintro ⟨hxij, hxji⟩
    refine ⟨?_, ?_⟩
    · rcases hxij with hx | hx
      · rw [hx]
        exact left_mem_segment Real (q i) (q (i+1))
      · rw [hx]
        exact right_mem_segment Real (q i) (q (i+1))
    · rcases hxji with hx | hx
      · rw [hx]
        exact left_mem_segment Real (q j) (q (j+1))
      · rw [hx]
        exact right_mem_segment Real (q j) (q (j+1))

end ParabolaHullEdges

theorem P3555T2ParabolaHullFrontier {n : Nat}
    (q : Fin (n + 3) → Real × Real)
    (hq : ∀ i, q i = ((i.val : Real), (i.val : Real) ^ 2)) :
    let K := convexHull Real (Set.range q)
    (∀ i j : Fin (n + 3), i ≠ j →
      segment Real (q i) (q (i + 1)) ∩ segment Real (q j) (q (j + 1)) =
        {x | (x = q i ∨ x = q (i + 1)) ∧
          (x = q j ∨ x = q (j + 1))}) ∧
    Convex Real K ∧ IsClosed K ∧ Bornology.IsBounded K ∧
    (interior K).Nonempty ∧
    frontier K = ⋃ i, segment Real (q i) (q (i + 1)) := by
-- BODY
  classical
  obtain ⟨hinjective, hnondegenerate, hsupport⟩ :=
    P3555T2ParabolaSupporting q hq
  have seg_rep (a b x : Real × Real) (hx : x ∈ segment Real a b) :
      ∃ t : Real, t ∈ Set.Icc 0 1 ∧ x = (1-t) • a + t • b := ParabolaHullConstruction.seg_rep a b
          x hx
  have det_affine (i : Fin (n + 3)) (a b : Real × Real) (t : Real) :
      P3381T1TriangleDeterminant ![q i, q (i+1), (1-t) • a + t • b] =
        (1-t) * P3381T1TriangleDeterminant ![q i, q (i+1), a] +
          t * P3381T1TriangleDeterminant ![q i, q (i+1), b] :=
              ParabolaHullConstruction.det_affine n q i a b t
  have det_zero_left (i : Fin (n + 3)) :
      P3381T1TriangleDeterminant ![q i, q (i+1), q i] = 0 :=
          ParabolaHullConstruction.det_zero_left n q i
  have det_zero_right (i : Fin (n + 3)) :
      P3381T1TriangleDeterminant ![q i, q (i+1), q (i+1)] = 0 :=
          ParabolaHullConstruction.det_zero_right n q i
  have endpoint_det_nonneg (i k : Fin (n + 3)) :
      0 ≤ P3381T1TriangleDeterminant ![q i, q (i+1), q k] :=
          ParabolaHullConstruction.endpoint_det_nonneg n q hsupport det_zero_left det_zero_right i k
  have no_two_cycle (i : Fin (n + 3)) : i + 1 + 1 ≠ i := ParabolaHullConstruction.no_two_cycle n i
  let M : Real := (n+2 : Nat)
  let kmax : Fin (n+3) := Fin.last (n+2)
  have hqzero : q (0 : Fin (n+3)) = (0,0) := ParabolaHullConstruction.hqzero n q hq
  have hqmax : q kmax = (M,M^2) := ParabolaHullConstruction.hqmax n q hq
  let L (j : Fin (n+2)) (x : Real) : Real :=
    (2 * (j.val : Real) + 1) * x - (j.val : Real) * ((j.val : Real) + 1)
  let D : Set (Real × Real) := {z | 0 ≤ z.1 ∧ z.1 ≤ M ∧ z.2 ≤ M*z.1 ∧
    ∀ j : Fin (n+2), L j z.1 ≤ z.2}
  have hvertex : ∀ k : Fin (n+3), q k ∈ D := ParabolaHullConstruction.hvertex n q hq
  have hDconv : Convex Real D := ParabolaHullConstruction.hDconv n seg_rep
  have hKD : convexHull Real (Set.range q) ⊆ D := ParabolaHullConstruction.hKD n q hvertex hDconv
  have choose_interval (x : Real) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
      ∃ j : Fin (n+2), (j.val : Real) ≤ x ∧ x ≤ (j.val : Real)+1 :=
          ParabolaHullConstruction.choose_interval n x hx0 hxM
  have segment_combo_mem (a b : Real × Real) (t : Real)
      (ht : t ∈ Set.Icc (0 : Real) 1) :
      (1-t) • a + t • b ∈ segment Real a b := ParabolaHullConstruction.segment_combo_mem a b t ht
  have qmem (i : Fin (n+3)) : q i ∈ convexHull Real (Set.range q) :=
      ParabolaHullConstruction.qmem n q i
  have segment_memK (a b : Fin (n+3)) :
      segment Real (q a) (q b) ⊆ convexHull Real (Set.range q) :=
          ParabolaHullConstruction.segment_memK n q qmem a b
  have hDK : D ⊆ convexHull Real (Set.range q) := ParabolaHullConstruction.hDK n q hq hqzero
      hqmax choose_interval segment_combo_mem qmem segment_memK
  have hHullEq : convexHull Real (Set.range q) = D := ParabolaHullConstruction.hHullEq n q hKD hDK
  have lowerEdge (j : Fin (n+2)) (x : Real)
      (hx0 : (j.val : Real) ≤ x) (hx1 : x ≤ (j.val : Real)+1) :
      (x, L j x) ∈ segment Real (q ⟨j.val, by omega⟩)
        (q ((⟨j.val, by omega⟩ : Fin (n+3))+1)) := ParabolaHullConstruction.lowerEdge n q hq
            segment_combo_mem j x hx0 hx1
  have upperEdge (x : Real) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
      (x, M*x) ∈ segment Real (q (0 : Fin (n+3))) (q kmax) := ParabolaHullConstruction.upperEdge
          n q hqzero hqmax segment_combo_mem x hx0 hxM
  have edgeLowerEquation (i : Fin (n+3)) (hi : i ≠ kmax) (z : Real × Real)
      (hz : z ∈ segment Real (q i) (q (i+1))) :
      ∃ j : Fin (n+2), L j z.1 = z.2 := ParabolaHullConstruction.edgeLowerEquation n q hq seg_rep
          i hi z hz
  have edgeUpperEquation (z : Real × Real)
      (hz : z ∈ segment Real (q kmax) (q (kmax+1))) :
      z.2 = M*z.1 := ParabolaHullConstruction.edgeUpperEquation n q seg_rep hqzero hqmax z hz
  have hcompact := ParabolaHullConstruction.hcompact n q
  have edge_intersections := ParabolaHullEdges.edge_intersections n q hsupport seg_rep
              det_affine det_zero_left det_zero_right endpoint_det_nonneg no_two_cycle
  refine ⟨edge_intersections, convex_convexHull Real _, hcompact.isClosed, hcompact.isBounded,
      ?_, ?_⟩
  · let f : Fin 3 → Fin (n+3) := fun i => ⟨i.val, by omega⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Fin.ext
      simpa [f] using congrArg Fin.val h
    have hdet : P3381T1TriangleDeterminant (q ∘ f) ≠ 0 := hnondegenerate f hf
    let p : Fin 3 → Real × Real := ![(0,0),(1,0),(0,1)]
    have hp : P3381T1TriangleDeterminant p ≠ 0 := by
      change ((1:Real)-0) * (1-0) - (0-0) * (0-0) ≠ 0
      norm_num
    obtain ⟨H, hH⟩ := P3381T1AffineTriangleMap p (q ∘ f) hp hdet
    let w (z : Real × Real) : Fin 3 → Real := ![1-z.1-z.2,z.1,z.2]
    have hw_sum (z : Real × Real) : (∑ i, w z i) = 1 := by
      rw [Fin.sum_univ_three]
      simp [w]
      ring
    have hp_sum (z : Real × Real) : (∑ i, w z i • p i) = z := by
      apply Prod.ext <;> simp [Fin.sum_univ_three, w, p]
    let U : Set (Real × Real) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < 1}
    have hUopen : IsOpen U := ParabolaHullInterior.hUopen
    have hUsub : U ⊆ convexHull Real (Set.range p) := ParabolaHullInterior.hUsub hw_sum hp_sum
    have target_subset : Set.range (q ∘ f) ⊆ Set.range q := by
      rintro x ⟨i, rfl⟩
      exact ⟨f i, rfl⟩
    have hImageSub : H '' U ⊆ convexHull Real (Set.range q) := ParabolaHullInterior.hImageSub n q
        H hH hw_sum hp_sum target_subset
    have hImageOpen : IsOpen (H '' U) := H.isOpenMap U hUopen
    let z₀ : Real × Real := (1/3,1/3)
    have hz₀ : z₀ ∈ U := by norm_num [U, z₀]
    refine ⟨H z₀, (hImageOpen.subset_interior_iff.mpr hImageSub) ?_⟩
    exact Set.mem_image_of_mem H hz₀
  · have hDclosed : IsClosed D := by
      rw [← hHullEq]
      exact hcompact.isClosed
    let O : Set (Real × Real) :=
      {z | 0 < z.1 ∧ z.1 < M ∧ z.2 < M*z.1 ∧ ∀ j : Fin (n+2), L j z.1 < z.2}
    have hOopen : IsOpen O := ParabolaHullInterior.hOopen n
    have hOsub : O ⊆ D := by
      intro z hz
      simp only [O, Set.mem_ofPred_eq] at hz
      rcases hz with ⟨hz0,hzM,hzU,hzL⟩
      exact ⟨hz0.le,hzM.le,hzU.le,fun j => (hzL j).le⟩
    have hOinter : O ⊆ interior D := hOopen.subset_interior_iff.mpr hOsub
    have ballAt (z : Real × Real) (hz : z ∈ interior D) :
        ∃ e : Real, 0 < e ∧ Metric.ball z e ⊆ D :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    have noLeftInterior (z : Real × Real) (hz : z ∈ interior D) : z.1 ≠ 0 :=
        ParabolaHullInterior.noLeftInterior n ballAt z hz
    have noRightInterior (z : Real × Real) (hz : z ∈ interior D) : z.1 ≠ M :=
        ParabolaHullInterior.noRightInterior n ballAt z hz
    have noUpperInterior (z : Real × Real) (hz : z ∈ interior D)
      (heq : z.2 = M*z.1) : False := ParabolaHullInterior.noUpperInterior n ballAt z hz heq
    have noLowerInterior (z : Real × Real) (hz : z ∈ interior D)
      (j : Fin (n+2)) (heq : L j z.1 = z.2) : False := ParabolaHullInterior.noLowerInterior n
          ballAt z hz j heq
    have interiorStrict (z : Real × Real) (hz : z ∈ interior D) : z ∈ O :=
        ParabolaHullInterior.interiorStrict n noLeftInterior noRightInterior noUpperInterior
        noLowerInterior z hz
    apply Set.ext
    intro x
    constructor
    · intro hx
      have hxDfront : x ∈ frontier D := by simpa [hHullEq] using hx
      rw [hDclosed.frontier_eq] at hxDfront
      rcases hxDfront with ⟨hxD,hnotint⟩
      have hnotO : x ∉ O := fun h => hnotint (hOinter h)
      rcases hxD with ⟨hx0,hxM,hxU,hxL⟩
      have heqcases : x.1 = 0 ∨ x.1 = M ∨ x.2 = M*x.1 ∨
      ∃ j : Fin (n+2), L j x.1 = x.2 := ParabolaHullInterior.heqcases n x hnotO hx0 hxM hxU hxL
      rcases heqcases with hxzero | hxmax | hxupper | ⟨j,hxlower⟩
      · have hylo : 0 ≤ x.2 := by
          have := hxL (⟨0, by omega⟩ : Fin (n+2))
          simpa [L,hxzero] using this
        have hyhi : x.2 ≤ 0 := by simpa [hxzero] using hxU
        have hxq : x = q (0 : Fin (n+3)) := by
          apply Prod.ext
          · rw [hxzero,hqzero]
          · rw [hqzero]
            exact le_antisymm hyhi hylo
        have hwrap : kmax+1 = (0 : Fin (n+3)) := by
          apply Fin.ext
          simp [kmax]
        refine Set.mem_iUnion.mpr ⟨kmax, ?_⟩
        rw [hwrap,hxq]
        exact right_mem_segment Real (q kmax) (q (0 : Fin (n+3)))
      · let jtop : Fin (n+2) := ⟨n+1, by omega⟩
        have hline : L jtop M = M^2 := by
          dsimp [L,jtop,M]
          push_cast
          ring
        have hylo : M^2 ≤ x.2 := by simpa [hxmax,hline] using hxL jtop
        have hyhi : x.2 ≤ M^2 := by rw [hxmax] at hxU; nlinarith [hxU]
        have hxq : x = q kmax := by
          apply Prod.ext
          · rw [hxmax,hqmax]
          · rw [hqmax]
            exact le_antisymm hyhi hylo
        have hwrap : kmax+1 = (0 : Fin (n+3)) := by
          apply Fin.ext
          simp [kmax]
        refine Set.mem_iUnion.mpr ⟨kmax, ?_⟩
        rw [hwrap,hxq]
        exact left_mem_segment Real (q kmax) (q (0 : Fin (n+3)))
      · have hedge := upperEdge x.1 hx0 hxM
        have hxline : x = (x.1,M*x.1) := Prod.ext rfl hxupper
        have hedge' : x ∈ segment Real (q (0 : Fin (n+3))) (q kmax) := by
          rw [hxline]
          exact hedge
        have hwrap : kmax+1 = (0 : Fin (n+3)) := by
          apply Fin.ext
          simp [kmax]
        refine Set.mem_iUnion.mpr ⟨kmax, ?_⟩
        rw [hwrap]
        simpa [segment_symm] using hedge'
      · have hjlower : (j.val : Real) ≤ x.1 := ParabolaHullInterior.hjlower n x hx0 hxL j hxlower
        have hjupper : x.1 ≤ (j.val : Real)+1 := ParabolaHullInterior.hjupper n x hxM hxL j hxlower
        let jj : Fin (n+3) := ⟨j.val, by omega⟩
        have hedge := lowerEdge j x.1 hjlower hjupper
        have hxline : x = (x.1,L j x.1) := Prod.ext rfl hxlower.symm
        refine Set.mem_iUnion.mpr ⟨jj, ?_⟩
        rw [hxline]
        simpa [jj] using hedge
    · intro hx
      obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
      have hxK : x ∈ convexHull Real (Set.range q) := segment_memK i (i+1) hxi
      have hIntEq : interior (convexHull Real (Set.range q)) = interior D :=
        congrArg interior hHullEq
      have hnotintK : x ∉ interior (convexHull Real (Set.range q)) :=
          ParabolaHullInterior.hnotintK n q edgeLowerEquation edgeUpperEquation noUpperInterior
          noLowerInterior x i hxi hIntEq
      rw [hcompact.isClosed.frontier_eq]
      exact ⟨hxK,hnotintK⟩

end ApollonianSuperharmonic

end
