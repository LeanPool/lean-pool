/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.CompletePrefix
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.Card

/-! Phase formulas for source prefix counts at coprime moduli. -/

@[expose] public section

namespace Shellsort

open scoped BigOperators

/-- Coprimality makes the source-chain position a bijective affine residue coordinate. -/
theorem coprime_affine_mod_eq_iff (h g s v w : ℕ) (hc : Nat.Coprime h g) :
    (s + h * v) % g = (s + h * w) % g ↔ v % g = w % g := by
  constructor
  · intro he
    exact Nat.ModEq.cancel_left_of_coprime hc.symm
      (Nat.ModEq.add_left_cancel' s he)
  · intro he
    exact (Nat.ModEq.mul_left h he).add_left s

/-- Each target residue has an actual source-chain phase; this is not an assumed phase. -/
theorem exists_coprime_source_phase (h g j s : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    ∃ a < g, (s + h * a) % g = j := by
  let f : Fin g → Fin g := fun a => ⟨(s + h * a.val) % g, Nat.mod_lt _ hg⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have he := congrArg Fin.val hab
    change (s + h * a.val) % g = (s + h * b.val) % g at he
    have he' := (coprime_affine_mod_eq_iff h g s a.val b.val hc).mp he
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using he'
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj ⟨j, hj⟩
  exact ⟨a.val, a.isLt, congrArg Fin.val ha⟩

/-- Identifies the original arithmetic-progression count with the simple residue count. -/
theorem sourcePrefixCount_eq_of_phase (h g j s a y : ℕ)
    (hc : Nat.Coprime h g) (ha : a < g) (hphase : (s + h * a) % g = j) :
    sourcePrefixCount h g j s y = residuePrefixCount g a y := by
  unfold sourcePrefixCount residuePrefixCount
  apply Finset.sum_congr rfl
  intro v _
  have he : (s + h * v) % g = j ↔ v % g = a := by
    rw [← hphase]
    simpa only [Nat.mod_eq_of_lt ha] using
      coprime_affine_mod_eq_iff h g s v a hc
  simp only [he]

/-- A single phase works for every prefix length of a fixed source-target pair. -/
theorem exists_sourcePrefixCount_phase (h g j s : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    ∃ a < g, ∀ y, sourcePrefixCount h g j s y = residuePrefixCount g a y := by
  obtain ⟨a, ha, hphase⟩ := exists_coprime_source_phase h g j s hg hc hj
  exact ⟨a, ha, fun y => sourcePrefixCount_eq_of_phase h g j s a y hc ha hphase⟩

/-- The residual of the actual source count has width g-1, uniformly over its prefix. -/
theorem source_residual_bounds_of_phase (h g j s a y : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (ha : a < g) (hphase : (s + h * a) % g = j) :
    -(a : ℤ) ≤ (g : ℤ) * sourcePrefixCount h g j s y - y ∧
      (g : ℤ) * sourcePrefixCount h g j s y - y ≤ (g : ℤ) - 1 - a := by
  rw [sourcePrefixCount_eq_of_phase h g j s a y hc ha hphase]
  exact counted_residual_bounds g a y hg ha

/-- The bounded interval exists without an externally supplied phase. -/
theorem exists_source_residual_interval (h g j s : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    ∃ a < g, ∀ y,
      -(a : ℤ) ≤ (g : ℤ) * sourcePrefixCount h g j s y - y ∧
      (g : ℤ) * sourcePrefixCount h g j s y - y ≤ (g : ℤ) - 1 - a := by
  obtain ⟨a, ha, hphase⟩ := exists_coprime_source_phase h g j s hg hc hj
  exact ⟨a, ha, fun y => source_residual_bounds_of_phase h g j s a y hg hc ha hphase⟩

/-- If the tagged key has source position y, its target residue selects phase y mod g. -/
theorem sourcePrefixCount_owner (h g s y b : ℕ) (hc : Nat.Coprime h g) :
    sourcePrefixCount h g ((s + h * y) % g) s b = residuePrefixCount g (y % g) b := by
  unfold sourcePrefixCount residuePrefixCount
  apply Finset.sum_congr rfl
  intro v _
  simp only [coprime_affine_mod_eq_iff h g s v y hc]

/-- The owner residual is exactly the lower endpoint of its phase interval. -/
theorem source_residual_owner (h g s y : ℕ) (hg : 0 < g) (hc : Nat.Coprime h g) :
    (g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s y - y = -(y % g : ℤ) := by
  rw [sourcePrefixCount_owner h g s y y hc,
    counted_residual_eq_phase g (y % g) y hg (Nat.mod_lt y hg),
    phaseResidual_owner]

/-- Fixing the owner's prefix can only decrease that source's residual. -/
theorem source_residual_owner_min (h g s y b : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) :
    (g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s y - y ≤
      (g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s b - b := by
  rw [source_residual_owner h g s y hg hc, sourcePrefixCount_owner h g s y b hc]
  exact (counted_residual_bounds g (y % g) b hg (Nat.mod_lt y hg)).1

/-- Replacing an arbitrary source prefix by the owner's prefix gives a one-sided,
uniformly bounded correction. This is the deterministic input to conditioning. -/
theorem source_residual_owner_correction_bounds (h g s y b : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) :
    -((g : ℤ) - 1) ≤
      ((g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s y - y) -
        ((g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s b - b) ∧
    ((g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s y - y) -
        ((g : ℤ) * sourcePrefixCount h g ((s + h * y) % g) s b - b) ≤ 0 := by
  rw [source_residual_owner h g s y hg hc, sourcePrefixCount_owner h g s y b hc]
  have hb := counted_residual_bounds g (y % g) b hg (Nat.mod_lt y hg)
  omega

/-- Two source residuals differ by at most the length of their common phase interval. -/
theorem source_residual_diff_bound (h g j s y z : ℕ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    |((g : ℤ) * sourcePrefixCount h g j s y - y) -
      ((g : ℤ) * sourcePrefixCount h g j s z - z)| ≤ (g : ℤ) - 1 := by
  obtain ⟨a, _, hb⟩ := exists_source_residual_interval h g j s hg hc hj
  have hy := hb y
  have hz := hb z
  rw [abs_le]
  omega

end Shellsort
