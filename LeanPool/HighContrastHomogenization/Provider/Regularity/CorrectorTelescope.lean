/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LocalGradientTopology
public import LeanPool.HighContrastHomogenization.Support.Ambient.Euclidean

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorTelescope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local gradient telescopes

Summable scalar weak-error rows control finite telescopes of local gradient
classes.  The estimates are stated for normalized centered cubes and retain
the slope factor explicitly.
-/

open scoped BigOperators

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- The weak-error expression occurring in the finite-corrector slope
estimate. -/
@[expose]
def scalarIdentityCorrectedWeakError {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s : ℝ) (k : ℤ) : ℝ :=
  scalarIdentityWeakError a s k * (1 + scalarIdentityWeakError a s k)

/-- The corrected scalar weak error is nonnegative. -/
theorem scalarIdentityCorrectedWeakError_nonneg {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s : ℝ) (k : ℤ) :
    0 ≤ scalarIdentityCorrectedWeakError a s k := by
  exact mul_nonneg (scalarIdentityWeakError_nonneg a s k)
    (by linarith only [scalarIdentityWeakError_nonneg a s k])

@[expose]
public def intNatShiftEmbedding (n : ℤ) : ℕ ↪ ℤ where
  toFun j := n + (j : ℤ)
  inj' := by
    intro i j hij
    have hcast : (i : ℤ) = (j : ℤ) := Int.add_left_cancel hij
    exact_mod_cast hcast

/-- An infinite scalar good tail gives a summable sequence after reindexing
the integer scales by natural offsets. -/
theorem ScalarIdentityGoodTail.summable_nat_shift {d : ℕ} [NeZero d]
    {a : Book.Ch02.TriadicCoeffFamily d} {s δ : ℝ} {n : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) :
    Summable (fun j : ℕ => scalarIdentityWeakError a s (n + (j : ℤ))) := by
  apply summable_of_sum_range_le
  · intro j
    exact scalarIdentityWeakError_nonneg a s (n + (j : ℤ))
  · intro N
    let shift := intNatShiftEmbedding n
    have hsubset :
        (Finset.range N).map shift ⊆ Finset.Icc n (n + (N : ℤ)) := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
      have hjlt : j < N := Finset.mem_range.mp hj
      rw [Finset.mem_Icc]
      constructor
      · exact le_add_of_nonneg_right (Int.natCast_nonneg j)
      · simpa only [shift, intNatShiftEmbedding, add_comm] using!
          add_le_add_left (Int.ofNat_le.mpr (Nat.le_of_lt hjlt)) n
    calc
      (∑ j ∈ Finset.range N,
          scalarIdentityWeakError a s (n + (j : ℤ))) =
          ∑ k ∈ (Finset.range N).map shift,
            scalarIdentityWeakError a s k := by
              rw [Finset.sum_map]
              rfl
      _ ≤ ∑ k ∈ Finset.Icc n (n + (N : ℤ)),
          scalarIdentityWeakError a s k := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ =>
              scalarIdentityWeakError_nonneg a s k
      _ ≤ δ := h.interval (by omega)

/-- The quadratic correction of a summable good-tail row remains summable. -/
theorem ScalarIdentityGoodTail.summable_corrected_nat_shift
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n : ℤ} (h : ScalarIdentityGoodTail a s δ n) :
    Summable
      (fun j : ℕ => scalarIdentityCorrectedWeakError a s (n + (j : ℤ))) := by
  let E : ℕ → ℝ := fun j => scalarIdentityWeakError a s (n + (j : ℤ))
  have hsum : Summable E := by
    simpa only [E] using h.summable_nat_shift
  have hmajorant : Summable (fun j => (1 + δ) * E j) :=
    hsum.mul_left (1 + δ)
  apply hmajorant.of_nonneg_of_le
  · intro j
    exact scalarIdentityCorrectedWeakError_nonneg a s (n + (j : ℤ))
  · intro j
    have hE_nonneg : 0 ≤ E j :=
      scalarIdentityWeakError_nonneg a s (n + (j : ℤ))
    have hE_le : E j ≤ δ := by
      exact h.weakError_le (by omega)
    calc
      scalarIdentityCorrectedWeakError a s (n + (j : ℤ)) =
          E j * (1 + E j) := rfl
      _ ≤ E j * (1 + δ) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using add_le_add_left hE_le 1) hE_nonneg
      _ = (1 + δ) * E j := by ring

/-- Corrected weak errors on every finite natural-offset interval are bounded
by the good-tail budget. -/
theorem ScalarIdentityGoodTail.sum_Ico_corrected_nat_shift_le
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n : ℤ} (h : ScalarIdentityGoodTail a s δ n)
    (k m : ℕ) :
    (∑ j ∈ Finset.Ico k m,
      scalarIdentityCorrectedWeakError a s (n + (j : ℤ))) ≤
        (1 + δ) * δ := by
  let shift := intNatShiftEmbedding n
  have hδ : 0 ≤ δ :=
    (scalarIdentityWeakError_nonneg a s n).trans (h.weakError_le le_rfl)
  have hsubset :
      (Finset.Ico k m).map shift ⊆ Finset.Icc n (n + (m : ℤ)) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hz
    have hjlt : j < m := (Finset.mem_Ico.mp hj).2
    rw [Finset.mem_Icc]
    constructor
    · exact le_add_of_nonneg_right (Int.natCast_nonneg j)
    · simpa only [shift, intNatShiftEmbedding, add_comm] using!
        add_le_add_left (Int.ofNat_le.mpr (Nat.le_of_lt hjlt)) n
  have hraw :
      (∑ j ∈ Finset.Ico k m,
        scalarIdentityWeakError a s (n + (j : ℤ))) ≤ δ := by
    calc
      (∑ j ∈ Finset.Ico k m,
          scalarIdentityWeakError a s (n + (j : ℤ))) =
          ∑ z ∈ (Finset.Ico k m).map shift,
            scalarIdentityWeakError a s z := by
              rw [Finset.sum_map]
              rfl
      _ ≤ ∑ z ∈ Finset.Icc n (n + (m : ℤ)),
          scalarIdentityWeakError a s z := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun z _ _ =>
              scalarIdentityWeakError_nonneg a s z
      _ ≤ δ := h.interval (by omega)
  calc
    (∑ j ∈ Finset.Ico k m,
        scalarIdentityCorrectedWeakError a s (n + (j : ℤ))) ≤
        ∑ j ∈ Finset.Ico k m,
          (1 + δ) * scalarIdentityWeakError a s (n + (j : ℤ)) := by
            apply Finset.sum_le_sum
            intro j _
            have hE_nonneg :
                0 ≤ scalarIdentityWeakError a s (n + (j : ℤ)) :=
              scalarIdentityWeakError_nonneg a s (n + (j : ℤ))
            have hE_le : scalarIdentityWeakError a s (n + (j : ℤ)) ≤ δ :=
              h.weakError_le (by omega)
            calc
              scalarIdentityCorrectedWeakError a s (n + (j : ℤ)) =
                  scalarIdentityWeakError a s (n + (j : ℤ)) *
                    (1 + scalarIdentityWeakError a s (n + (j : ℤ))) := rfl
              _ ≤ scalarIdentityWeakError a s (n + (j : ℤ)) * (1 + δ) :=
                mul_le_mul_of_nonneg_left
                  (by simpa only [add_comm] using add_le_add_left hE_le 1)
                  hE_nonneg
              _ = (1 + δ) * scalarIdentityWeakError a s (n + (j : ℤ)) := by
                ring
    _ = (1 + δ) *
        (∑ j ∈ Finset.Ico k m,
          scalarIdentityWeakError a s (n + (j : ℤ))) := by
            rw [Finset.mul_sum]
    _ ≤ (1 + δ) * δ :=
      mul_le_mul_of_nonneg_left hraw (by linarith only [hδ])

/-- A bound on successive differences gives the corresponding finite
interval telescope. -/
theorem norm_sub_le_sum_Ico_of_successive_norm_le
    {E : Type*} [NormedAddCommGroup E] (g : ℕ → E) (ε : ℕ → ℝ)
    (C R : ℝ)
    (hstep : ∀ j, ‖g (j + 1) - g j‖ ≤ C * ε j * R)
    {k m : ℕ} (hkm : k ≤ m) :
    ‖g m - g k‖ ≤ C * (∑ j ∈ Finset.Ico k m, ε j) * R := by
  calc
    ‖g m - g k‖ = dist (g k) (g m) := by
      rw [dist_eq_norm, norm_sub_rev]
    _ ≤ ∑ j ∈ Finset.Ico k m, C * ε j * R := by
      apply dist_le_Ico_sum_of_dist_le hkm
      intro j _ _
      rw [dist_eq_norm, norm_sub_rev]
      exact hstep j
    _ = C * (∑ j ∈ Finset.Ico k m, ε j) * R := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Summable bounds on successive differences make a normed-group sequence
Cauchy. -/
theorem cauchySeq_of_summable_successive_norm_le
    {E : Type*} [NormedAddCommGroup E] (g : ℕ → E) (ε : ℕ → ℝ)
    (C R : ℝ) (hε : Summable ε)
    (hstep : ∀ j, ‖g (j + 1) - g j‖ ≤ C * ε j * R) :
    CauchySeq g := by
  apply cauchySeq_of_dist_le_of_summable (fun j => C * ε j * R)
  · intro j
    rw [dist_eq_norm, norm_sub_rev]
    exact hstep j
  · exact (hε.mul_left C).mul_right R

/-- Summable successive bounds make one local-gradient coordinate Cauchy. -/
theorem localGradientL2_cauchySeq_of_summable_successive_norm_le
    {d q : ℕ} (g : ℕ → LocalGradientL2 d q) (ε : ℕ → ℝ)
    (C : ℝ) (e : Vec d) (hε : Summable ε)
    (hstep : ∀ j,
      ‖g (j + 1) - g j‖ ≤ C * ε j * euclideanNorm e) :
    CauchySeq g :=
  cauchySeq_of_summable_successive_norm_le
    g ε C (euclideanNorm e) hε hstep

end

end HighContrast
end HCPolySupport
