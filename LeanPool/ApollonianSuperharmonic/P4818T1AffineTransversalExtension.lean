/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: P4818T1AffineTransversalExtension]

/-!
# P4818T1AffineTransversalExtension

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4818T1AffineTransversalExtension
    (H : Set GaussianInt) (a b : GaussianInt)
    (α β : GaussianInt →+ Int) (ca cb : Int) (f : IntegerLatticeFunction)
    (hrep : ∀ x : GaussianInt, ∃! p : GaussianInt × (Int × Int),
      p.1 ∈ H ∧ x = p.1 + p.2.1 • a + p.2.2 • b)
    (hcomm : α b = β a) :
    ∃ g : IntegerLatticeFunction,
      (∀ h, h ∈ H → g h = f h) ∧
      (∀ x, g (x + a) = g x + α x + ca) ∧
      (∀ x, g (x + b) = g x + β x + cb) ∧
      (∀ h, h ∈ H → ∀ m n : Int,
        g (h + m • a + n • b) = f h +
          m * (α h + ca) + (m * (m - 1) / 2) * α a +
          n * (β h + cb) + (n * (n - 1) / 2) * β b + m * n * β a) ∧
      (∀ g' : IntegerLatticeFunction,
        (∀ x, g' (x + a) = g' x + α x + ca) →
        (∀ x, g' (x + b) = g' x + β x + cb) →
        (∀ h, h ∈ H → g' h = f h) → g' = g) := by
-- BODY
  classical
  let B : Int → Int := fun t => t * (t - 1) / 2
  have hB (t : Int) : B (t + 1) = B t + t := by
    have he : (t + 1) * (t + 1 - 1) = t * (t - 1) + t * 2 := by ring
    dsimp [B]
    rw [he, Int.add_mul_ediv_right _ _ (by decide)]
  let E : GaussianInt → Int → Int → Int := fun h m n =>
    f h + m * (α h + ca) + B m * α a +
      n * (β h + cb) + B n * β b + m * n * β a
  have eA (h : GaussianInt) (m n : Int) :
      E h (m + 1) n = E h m n + α (h + m • a + n • b) + ca := by
    simp only [E, hB, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, hcomm]
    ring
  have eB (h : GaussianInt) (m n : Int) :
      E h m (n + 1) = E h m n + β (h + m • a + n • b) + cb := by
    simp only [E, hB, map_add, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id]
    ring
  let coord := fun x => Classical.choose (hrep x)
  have hc (x : GaussianInt) :
      (coord x).1 ∈ H ∧ x = (coord x).1 + (coord x).2.1 • a + (coord x).2.2 • b :=
    (Classical.choose_spec (hrep x)).1
  have cu (h : GaussianInt) (hh : h ∈ H) (m n : Int) :
      coord (h + m • a + n • b) = (h, m, n) := by
    exact ((Classical.choose_spec (hrep (h + m • a + n • b))).2
      (h, m, n) ⟨hh, rfl⟩).symm
  let g : IntegerLatticeFunction := fun x =>
    E (coord x).1 (coord x).2.1 (coord x).2.2
  have value (h : GaussianInt) (hh : h ∈ H) (m n : Int) :
      g (h + m • a + n • b) = E h m n := by
    dsimp [g]
    rw [cu h hh m n]
  have hH (h : GaussianInt) (hh : h ∈ H) : g h = f h := by
    have hval := value h hh 0 0
    simpa [E, B] using hval
  have ga (x : GaussianInt) : g (x + a) = g x + α x + ca := by
    obtain ⟨hh, hx⟩ := hc x
    let h := (coord x).1
    let m := (coord x).2.1
    let n := (coord x).2.2
    have he : x + a = h + (m + 1) • a + n • b := by
      rw [hx]
      simp only [h, m, n, add_zsmul, one_zsmul]
      abel
    rw [he, value h hh (m + 1) n, eA]
    rw [show h + m • a + n • b = x from hx.symm]
  have gb (x : GaussianInt) : g (x + b) = g x + β x + cb := by
    obtain ⟨hh, hx⟩ := hc x
    let h := (coord x).1
    let m := (coord x).2.1
    let n := (coord x).2.2
    have he : x + b = h + m • a + (n + 1) • b := by
      rw [hx]
      simp only [h, m, n, add_zsmul, one_zsmul]
      abel
    rw [he, value h hh m (n + 1), eB]
    rw [show h + m • a + n • b = x from hx.symm]
  refine ⟨g, hH, ga, gb, value, ?_⟩
  intro g' ga' gb' hH'
  let w : GaussianInt → Int := fun x => g' x - g x
  have wa (x : GaussianInt) : w (x + a) = w x := by
    dsimp [w]
    rw [ga', ga]
    ring
  have wb (x : GaussianInt) : w (x + b) = w x := by
    dsimp [w]
    rw [gb', gb]
    ring
  have periodic (d : GaussianInt) (hd : ∀ x, w (x + d) = w x)
      (m : Int) (x : GaussianInt) : w (x + m • d) = w x := by
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [add_zsmul, one_zsmul, ← add_assoc, hd, ih]
    | pred m ih =>
        have he : x + (-(m : Int) - 1) • d + d = x + (-(m : Int)) • d := by
          rw [sub_zsmul, one_zsmul]
          abel
        have h := hd (x + (-(m : Int) - 1) • d)
        rw [he, ih] at h
        exact h.symm
  funext x
  obtain ⟨p, ⟨hh, hx⟩, _⟩ := hrep x
  have hw : w x = 0 := by
    rw [hx, periodic b wb, periodic a wa]
    dsimp [w]
    rw [hH' p.1 hh, hH p.1 hh]
    ring
  exact sub_eq_zero.mp hw

end ApollonianSuperharmonic

end
