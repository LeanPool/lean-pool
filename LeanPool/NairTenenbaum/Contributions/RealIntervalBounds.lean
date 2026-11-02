/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # Integer endpoint bounds for the real short interval -/

@[expose] public section

namespace NairTenenbaum

/-- Rounding costs at most a factor two when the real interval length is at
least two; all points remain in the range needed for the height bound. -/
theorem shortInterval_endpoint_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x) :
    (⌊x⌋₊ : ℤ) ≤ (⌊x + y⌋₊ : ℤ) ∧
    y / 2 ≤ (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) ∧
    (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) ≤ 2 * y ∧
    ∀ t ∈ Finset.Ioc (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ), (t.natAbs : ℝ) ≤ 2 * x := by
  have hxy : 0 ≤ x + y := by linarith
  have hxa := Nat.floor_le hx
  have hax := Nat.lt_floor_add_one x
  have hxb := Nat.floor_le hxy
  have hbx := Nat.lt_floor_add_one (x + y)
  refine ⟨by exact_mod_cast Nat.floor_mono (by linarith : x ≤ x + y), by linarith, by linarith, ?_⟩
  intro t ht
  obtain ⟨hat, htb⟩ := Finset.mem_Ioc.mp ht
  have ht₀ : 0 ≤ t := (Int.natCast_nonneg _).trans hat.le
  have habs : (t.natAbs : ℤ) = t := by rw [Int.natCast_natAbs, abs_of_nonneg ht₀]
  have H : (t.natAbs : ℝ) ≤ (⌊x + y⌋₊ : ℝ) := by
    exact_mod_cast (show (t.natAbs : ℤ) ≤ (⌊x + y⌋₊ : ℤ) by simpa only [habs] using htb)
  linarith

/-- Natural and integer versions of the interval agree under the natural cast. -/
theorem shortInterval_natCast_image (x y : ℝ) :
    (shortInterval x y).image (fun n : ℕ => (n : ℤ)) = Finset.Ioc (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  ext t
  simp only [Finset.mem_image, shortInterval, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨ha, hb⟩, rfl⟩
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · rintro ⟨ha, hb⟩
    have ht : 0 ≤ t := (Int.natCast_nonneg _).trans ha.le
    refine ⟨t.toNat, ⟨?_, ?_⟩, Int.toNat_of_nonneg ht⟩
    · exact_mod_cast (show (⌊x⌋₊ : ℤ) < (t.toNat : ℤ) by
      simpa only [Int.toNat_of_nonneg ht] using ha)
    · exact_mod_cast (show (t.toNat : ℤ) ≤ (⌊x + y⌋₊ : ℤ) by
      simpa only [Int.toNat_of_nonneg ht] using hb)

end NairTenenbaum
