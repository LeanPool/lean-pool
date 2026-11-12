/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4818T1ClosedOverlaps
public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic

-- [TABLET NODE: P4818T1OverlapDifferences]

/-!
# P4818T1OverlapDifferences

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4818T1OverlapDifferences (K : DiamondParameter) :
    let k : Int := K.1
    let a : GaussianInt := ⟨0, -2 * k⟩
    let b : GaussianInt := ⟨k + 1, k⟩
    let c : GaussianInt := ⟨-k - 1, k⟩
    (∀ x, x ∈ DiamondVertexDomains K false →
      x + a ∈ DiamondVertexDomains K false →
      P4207T1DiamondFormula (x + a) - P4207T1DiamondFormula x =
        -k * x.re + (k - 1) * x.im - k * (k - 2)) ∧
    (∀ x, x ∈ DiamondVertexDomains K false →
      x + b ∈ DiamondVertexDomains K false →
      P4207T1DiamondFormula (x + b) - P4207T1DiamondFormula x =
        k * x.re + x.im + k * (k + 1) / 2) ∧
    (∀ x, x ∈ DiamondVertexDomains K false →
      x + c ∈ DiamondVertexDomains K false →
      P4207T1DiamondFormula (x + c) - P4207T1DiamondFormula x =
        -k * x.im - k * (k + 1) / 2) := by
-- BODY
  dsimp only
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -2 * k⟩
  let b : GaussianInt := ⟨k + 1, k⟩
  let c : GaussianInt := ⟨-k - 1, k⟩
  change _ ∧ _ ∧ _
  obtain ⟨_, hA, hB, hC⟩ := P4818T1ClosedOverlaps K
  have half (z : Int) : 2 * (z * (z - 1) / 2) = z * (z - 1) := by
    obtain ⟨q, hq⟩ := Int.even_mul_pred_self z
    omega
  have first (j : Int) (hj : 1 ≤ j) (hjk : j ≤ k) :
      P4207T1DiamondFormula ⟨k + 1 - j, k + j⟩ -
        P4207T1DiamondFormula ⟨-j, j⟩ = -k * j + j + k * (k + 1) / 2 := by
    have hs : (2 * -j) ^ 2 / 4 = j ^ 2 := by
      simpa using P4207T1FloorArithmetic.1 0 (-j)
    have ht : (1 + 2 * -j) ^ 2 / 4 = -j + j ^ 2 := by
      simpa using P4207T1FloorArithmetic.1 1 (-j)
    have hp : 0 ≤ k + 1 - j := by omega
    have hjp : 0 ≤ j := by omega
    simp only [P4207T1DiamondFormula, Int.natCast_natAbs, abs_neg,
      abs_of_nonneg hp, abs_of_nonneg hjp]
    have es : -j - j = 2 * -j := by ring
    have et : k + 1 - j - (k + j) = 1 + 2 * -j := by ring
    rw [es, et, hs, ht]
    have h1 := half (k + 1 - j)
    have h2 := half j
    have h3 := half (k + 1)
    have he : (k + 1) * (k + 1 - 1) = k * (k + 1) := by ring
    rw [he] at h3
    nlinarith
  have second (j : Int) (hj : 0 ≤ j) (hjk : j < k) :
      P4207T1DiamondFormula ⟨k - j, k + j⟩ -
        P4207T1DiamondFormula ⟨-1 - j, j⟩ =
        -k * (1 + j) + j + k * (k + 1) / 2 := by
    have hs : (-1 + 2 * -j) ^ 2 / 4 = j + j ^ 2 := by
      simpa using P4207T1FloorArithmetic.1 (-1) (-j)
    have ht : (2 * -j) ^ 2 / 4 = j ^ 2 := by
      simpa using P4207T1FloorArithmetic.1 0 (-j)
    have hp : 0 ≤ k - j := by omega
    have hn : -1 - j ≤ 0 := by omega
    simp only [P4207T1DiamondFormula, Int.natCast_natAbs,
      abs_of_nonneg hp, abs_of_nonpos hn]
    have es : -1 - j - j = -1 + 2 * -j := by ring
    have et : k - j - (k + j) = 2 * -j := by ring
    rw [es, et, hs, ht]
    have h1 := half (k - j)
    have h2 := half (-(-1 - j))
    have h3 := half (k + 1)
    have he : (k + 1) * (k + 1 - 1) = k * (k + 1) := by ring
    rw [he] at h3
    nlinarith
  have hb : ∀ x, x ∈ DiamondVertexDomains K false →
      x + b ∈ DiamondVertexDomains K false →
      P4207T1DiamondFormula (x + b) - P4207T1DiamondFormula x =
        k * x.re + x.im + k * (k + 1) / 2 := by
    intro x hx hxb
    rcases (hB x).mp ⟨hx, hxb⟩ with ⟨j, hj, hjk, rfl⟩ | ⟨j, hj, hjk, rfl⟩
    · have he : (⟨-j, j⟩ : GaussianInt) + b = ⟨k + 1 - j, k + j⟩ := by
        ext <;> simp [b] <;> ring
      rw [he]
      simpa only [neg_mul, mul_neg] using first j hj hjk
    · have he : (⟨-1 - j, j⟩ : GaussianInt) + b = ⟨k - j, k + j⟩ := by
        ext <;> simp [b] <;> ring
      rw [he]
      have h := second j hj hjk
      change _ = k * (-1 - j) + j + k * (k + 1) / 2
      linarith
  refine ⟨?_, hb, ?_⟩
  · intro x hx hxa
    obtain ⟨r, _, _, rfl⟩ := (hA x).mp ⟨hx, hxa⟩
    have he : (⟨r, 2 * k⟩ : GaussianInt) + a = ⟨r, 0⟩ := by
      ext <;> simp [a]
    rw [he]
    simp only [P4207T1DiamondFormula]
    have es : r - 2 * k = r + 2 * -k := by ring
    rw [sub_zero, es, P4207T1FloorArithmetic.1 r (-k)]
    ring
  · intro x hx hxc
    let R : GaussianInt → GaussianInt := fun z => ⟨-z.re, z.im⟩
    have hrmem : R x ∈ DiamondVertexDomains K false ∧
        R x + b ∈ DiamondVertexDomains K false := by
      apply (hB (R x)).mpr
      obtain ⟨j, hj, hjk, he | he⟩ := (hC x).mp ⟨hx, hxc⟩
      · right
        refine ⟨j - 1, by omega, by omega, ?_⟩
        rw [he]
        ext <;> simp [R]; ring
      · left
        exact ⟨j, hj, hjk, by rw [he]⟩
    have h := hb (R x) hrmem.1 hrmem.2
    have hR (z : GaussianInt) : P4207T1DiamondFormula (R z) =
        P4207T1DiamondFormula z - z.re * z.im :=
      P4207T1FloorArithmetic.2.2.2.2 z.re z.im
    have he : R (x + c) = R x + b := by
      ext <;> simp [R, c, b]; ring
    rw [← he, hR, hR] at h
    dsimp [R, c] at h ⊢
    have hhalf := half (k + 1)
    have heven : (k + 1) * (k + 1 - 1) = k * (k + 1) := by ring
    rw [heven] at hhalf
    nlinarith

end ApollonianSuperharmonic

end
