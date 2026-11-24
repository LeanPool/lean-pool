/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.GM12.Section2CirclePeriod

/-!
# Simplicity of a circle assembled from cyclic region paths

For Case 1 of XII (2.1), page 244, assemble the two-spoke paths of
the successive region visits into a closed curve. If distinct paths
have disjoint images after removing their final endpoints, and each
remaining parameterization is injective, the assembled curve is
injective. Represent every circle parameter in exactly one half-open
piece of the cyclic chain and compare those two representations.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07

/-- Every point of a concatenated cyclic chain has a representation
in one of its half-open parameter pieces, including its circle
parameter as well as its image value. -/
theorem concatLoop_point_representation
    {S : Type*} [TopologicalSpace S] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (z : Circle) :
    ∃ (i : Fin n) (t : unitInterval), t.val < 1 ∧
      z = Circle.exp (2 * Real.pi * ((i.val : ℝ) + t.val) / (n : ℝ)) ∧
      concatLoop hn γ hmatch z = γ i t := by
  obtain ⟨u, hu, huz⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let y := u * (n : ℝ)
  have hy0 : 0 ≤ y := mul_nonneg hu.1 hnpos.le
  have hyn : y < n := by
    dsimp only [y]
    have hu1 : u < 1 := by simpa only [zero_add] using hu.2
    exact mul_lt_of_lt_one_left hnpos hu1
  have hfloor0 : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
  have hfloorn : ⌊y⌋ < (n : ℤ) := by
    rw [Int.floor_lt]
    exact_mod_cast hyn
  let i : Fin n := ⟨⌊y⌋.toNat, by omega⟩
  let t : unitInterval := unitFract y
  have ht : t.val < 1 := Int.fract_lt_one y
  have hity : (i.val : ℝ) + t.val = y := by
    have hfloor : (i.val : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg hfloor0
    change ((i.val : ℤ) : ℝ) + Int.fract y = y
    rw [hfloor, Int.floor_add_fract]
  have hz : z = Circle.exp (2 * Real.pi * ((i.val : ℝ) + t.val) / (n : ℝ)) := by
    rw [hity]
    have heq : 2 * Real.pi * y / (n : ℝ) = 2 * Real.pi * u := by
      dsimp only [y]
      rw [← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt hnpos)]
    rw [heq]
    exact huz.symm
  refine ⟨i, t, ht, hz, ?_⟩
  rw [hz]
  exact concatLoop_exp_piece hn γ hmatch i t

/-- Half-open pieces with no repeated image point assemble to a
simple closed curve. This gives the simplicity step for the cyclic
region paths in XII (2.1), Case 1, page 244. -/
theorem concatLoop_injective_of_halfopen_pieces
    {S : Type*} [TopologicalSpace S] {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (hsep : ∀ (i j : Fin n) (s t : unitInterval), s.val < 1 → t.val < 1 →
      γ i s = γ j t → i = j ∧ s = t) :
    Function.Injective (concatLoop hn γ hmatch) := by
  intro z z' hzz
  obtain ⟨i, s, hs, hz, hγ⟩ := concatLoop_point_representation hn γ hmatch z
  obtain ⟨j, t, ht, hz', hγ'⟩ := concatLoop_point_representation hn γ hmatch z'
  rw [hγ, hγ'] at hzz
  obtain ⟨rfl, rfl⟩ := hsep i j s t hs ht hzz
  exact hz.trans hz'.symm

end GraphMinor.GM12
