/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry

-- [TABLET NODE: P3913T1PeriodicPositionUnbounded]

/-!
# P3913T1PeriodicPositionUnbounded

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3913T1PeriodicPositionUnbounded {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) (F : Set ι) (hF : F.Finite) :
    ¬ Bornology.IsBounded (D.position '' Fᶜ) := by
-- BODY
  classical
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  have nonzero_period : ∃ u : P.lattice, u ≠ 0 := by
    by_contra hz
    have hallzero : ∀ u : P.lattice, u = 0 := by simpa using hz
    have hrep : ∀ z : GaussianInt, z ∈ P.latticeReps := by
      intro z
      obtain ⟨r, ⟨hr, hzr⟩, _⟩ := P.lattice_full_rank z
      have heq : z - r = 0 := congrArg Subtype.val (hallzero ⟨z - r, hzr⟩)
      simpa [sub_eq_zero.mp heq] using hr
    have hinj : Function.Injective (fun n : Nat => (n : GaussianInt)) := Nat.cast_injective
    have hfinite := P.latticeReps.finite_toSet.preimage hinj.injOn
    have hall : (fun n : Nat => (n : GaussianInt)) ⁻¹'
        (P.latticeReps : Set GaussianInt) = Set.univ := by
      ext n
      simp [hrep]
    rw [hall] at hfinite
    exact Set.infinite_univ hfinite
  obtain ⟨u, hu⟩ := nonzero_period
  let v := GaussianRealPoint (u : GaussianInt)
  have hv : v ≠ (0, 0) := by
    intro h
    apply hu
    apply Subtype.ext
    apply Zsqrtd.ext
    · have hr := congrArg Prod.fst h
      have hr' : (((u : GaussianInt).re : Int) : Real) = 0 := by
        simpa [v, GaussianRealPoint] using hr
      exact_mod_cast hr'
    · have hi := congrArg Prod.snd h
      have hi' : (((u : GaussianInt).im : Int) : Real) = 0 := by
        simpa [v, GaussianRealPoint] using hi
      exact_mod_cast hi'
  have coord : ∃ q : (Real × Real) → Real,
      q v ≠ 0 ∧
      (∀ x y, q (x + y) = q x + q y) ∧
      (∀ (n : Nat) x, q (n • x) = (n : Real) * q x) ∧
      ∀ x, |q x| ≤ ‖x‖ := by
    by_cases h : v.1 ≠ 0
    · exact ⟨Prod.fst, h, fun _ _ => rfl,
        by intros; simp, fun x => by simpa using norm_fst_le x⟩
    · have h' : v.2 ≠ 0 := by
        intro hzero
        exact hv (Prod.ext (not_ne_iff.mp h) hzero)
      exact ⟨Prod.snd, h', fun _ _ => rfl,
        by intros; simp, fun x => by simpa using norm_snd_le x⟩
  obtain ⟨q, hq, hadd, hsmul, hnorm⟩ := coord
  intro hb
  have hall : Bornology.IsBounded (Set.range D.position) := by
    apply ((hF.image D.position).isBounded.union hb).subset
    rintro x ⟨a, rfl⟩
    by_cases ha : a ∈ F
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  obtain ⟨B, _, hB⟩ := hall.exists_pos_norm_le
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  have hc : 0 < |q v| := abs_pos.mpr hq
  obtain ⟨n, hn⟩ := exists_nat_gt ((B + |q (D.position a)|) / |q v|)
  have hlarge : B + |q (D.position a)| < (n : Real) * |q v| :=
    (div_lt_iff₀ hc).mp hn
  have hpos : D.position (P.shift (n • u) a) = D.position a + n • v := by
    rw [D.position_periodic]
    congr 1
    ext <;> simp [v, GaussianRealPoint]
  have hrev : (n : Real) * |q v| ≤
      |q (D.position a) + (n : Real) * q v| + |q (D.position a)| := by
    calc
      (n : Real) * |q v| = |(n : Real) * q v| := by
        have hnabs : |(n : Real)| = (n : Real) := abs_of_nonneg (Nat.cast_nonneg n)
        rw [abs_mul, hnabs]
      _ = |(q (D.position a) + (n : Real) * q v) - q (D.position a)| := by
        congr 1
        ring
      _ ≤ _ := abs_sub _ _
  have hcoord : |q (D.position a) + (n : Real) * q v| ≤ B := by
    have hh := (hnorm (D.position (P.shift (n • u) a))).trans
      (hB _ (Set.mem_range_self _))
    simpa only [hpos, hadd, hsmul] using hh
  linarith

end ApollonianSuperharmonic

end
