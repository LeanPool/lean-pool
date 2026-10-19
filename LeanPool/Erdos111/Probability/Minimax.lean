/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# A finite minimax lemma

Let finitely many pure strategies `x` have payoffs `f i x` against finitely many
constraints `i`. If every nonnegative combination of the constraints is met by some
pure strategy, then one mixed strategy meets all the constraints at once. The proof
separates the convex hull of the payoff vectors from the closed lower orthant at `c`.
-/

@[expose] public section

namespace Erdos111

/-- If every nonnegative combination of the constraints `f i ≤ c i` is met by a pure
strategy, a single mixed strategy meets every constraint. -/
theorem exists_mixed_le {ι X : Type*} [Fintype ι] [Fintype X]
    (f : ι → X → ℝ) (c : ι → ℝ)
    (h : ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) → ∃ x, ∑ i, ρ i * f i x ≤ ∑ i, ρ i * c i) :
    ∃ p : X → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧ ∀ i, ∑ x, p x * f i x ≤ c i := by
  classical
  -- the mixed strategies, and their payoff vectors
  let P : Set (X → ℝ) := convexHull ℝ (Set.range fun x => Pi.single x 1)
  let M : Matrix ι X ℝ := Matrix.of fun i x => f i x
  let K : Set (ι → ℝ) := M.mulVecLin '' P
  have hP : P ⊆ {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨x, rfl⟩
      refine ⟨fun y => ?_, by simp⟩
      dsimp only
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    · rintro p ⟨hp0, hp1⟩ q ⟨hq0, hq1⟩ a b ha hb hab
      refine ⟨fun x => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hp0 x
        have := hq0 x
        positivity
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1, hab]
  by_cases hKO : (K ∩ Set.Iic c).Nonempty
  · obtain ⟨_, ⟨p, hp, rfl⟩, hpc⟩ := hKO
    refine ⟨p, (hP hp).1, (hP hp).2, fun i => ?_⟩
    have := hpc i
    rw [Matrix.mulVecLin_apply] at this
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using this
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hKO
  have hKv : Convex ℝ K := (convex_convexHull ℝ _).linear_image M.mulVecLin
  have hKc : IsCompact K := ((Set.finite_range _).isCompact_convexHull ℝ).image
    M.mulVecLin.continuous_of_finiteDimensional
  obtain ⟨φ, u, v, hφK, huv, hφO⟩ :=
    geometric_hahn_banach_compact_closed hKv hKc (convex_Iic c) isClosed_Iic hKO
  -- the separating functional in coordinates
  let ρ : ι → ℝ := fun i => -φ (Pi.single i 1)
  have hφ : ∀ z, φ z = -∑ i, ρ i * z i := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    simp only [map_sum, ρ, neg_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Pi.single i (z i) = z i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hc : v < φ c := hφO c (Set.mem_Iic.2 le_rfl)
  have hρ : ∀ i, 0 ≤ ρ i := by
    intro i
    by_contra hi
    have hpos : 0 < φ (Pi.single i 1) := by simp only [ρ] at hi; linarith
    set t := (φ c - v) / φ (Pi.single i 1)
    have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have hmem : c - t • Pi.single i 1 ∈ Set.Iic c := by
      intro j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
        rw [Pi.single_apply]; split_ifs <;> norm_num
      nlinarith
    have := hφO _ hmem
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  obtain ⟨x, hx⟩ := h ρ hρ
  have hxK : M.mulVecLin (Pi.single x 1) ∈ K :=
    ⟨_, subset_convexHull ℝ _ ⟨x, rfl⟩, rfl⟩
  have h1 := hφK _ hxK
  rw [hφ] at h1 hc
  have : ∀ i, (M.mulVecLin (Pi.single x 1) : ι → ℝ) i = f i x := by
    intro i
    rw [Matrix.mulVecLin_apply]
    simp [M, Matrix.mulVec_single]
  simp only [this] at h1
  linarith

end Erdos111
