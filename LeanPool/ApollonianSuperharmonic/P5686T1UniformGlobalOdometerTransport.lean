/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Tactic.LinearCombination
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends

-- [TABLET NODE: P5686T1UniformGlobalOdometerTransport]

/-!
# P5686T1UniformGlobalOdometerTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5686T1UniformGlobalOdometerTransport
    (s : BandPackingSymmetry) (g : IntegerLatticeFunction)
    (h : PartialOdometer) (hext : GlobalOdometerExtends g h) :
    ∃ g' : IntegerLatticeFunction,
      GlobalOdometerExtends g' (BandPackingSymmetryPartialOdometerAction s h) ∧
      ∀ x, FourNeighborLaplacian g' (BandPackingSymmetryVectorAction s x) =
        FourNeighborLaplacian g x := by
-- BODY
  classical
  induction s generalizing g h with
  | identity =>
      exact ⟨g, by simpa [BandPackingSymmetryPartialOdometerAction], by
        intro x; simp [BandPackingSymmetryVectorAction]⟩
  | shift w =>
      let g' : IntegerLatticeFunction := fun y =>
        g y + BandPackingShiftPotential w y
      refine ⟨g', ?_, ?_⟩
      · rcases hext with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        intro y hy
        simp only [BandPackingSymmetryPartialOdometerAction] at hy ⊢
        simp [g', hy, hc y hy]
        abel
      · intro x
        simp only [BandPackingSymmetryVectorAction]
        rcases w with ⟨A, B⟩
        rcases x with ⟨a, b⟩
        have tri_succ (n : ℤ) :
            (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n := by
          rcases Int.even_or_odd' n with ⟨k, hk | hk⟩ <;> subst n
          · rw [Int.ediv_eq_of_eq_mul_right (by norm_num)
                (show (2 * k + 1) * (2 * k + 1 - 1) =
                  2 * ((2 * k + 1) * k) by ring)]
            rw [Int.ediv_eq_of_eq_mul_right (by norm_num)
                (show (2 * k) * (2 * k - 1) =
                  2 * (k * (2 * k - 1)) by ring)]
            ring
          · rw [Int.ediv_eq_of_eq_mul_right (by norm_num)
                (show (2 * k + 1 + 1) * (2 * k + 1 + 1 - 1) =
                  2 * ((k + 1) * (2 * k + 1)) by ring)]
            rw [Int.ediv_eq_of_eq_mul_right (by norm_num)
                (show (2 * k + 1) * (2 * k + 1 - 1) =
                  2 * (k * (2 * k + 1)) by ring)]
            ring
        have tri_pred (n : ℤ) :
            (n - 1) * ((n - 1) - 1) / 2 =
              n * (n - 1) / 2 - (n - 1) := by
          have ht := tri_succ (n - 1)
          simp only [sub_add_cancel] at ht
          linarith
        have second_difference (n : ℤ) :
            (n + n ^ 2) / 2 + (2 - 3 * n + n ^ 2) / 2 -
                2 * ((-n + n ^ 2) / 2) = 1 := by
          have hs := tri_succ n
          have hp := tri_pred n
          ring_nf at hs hp ⊢
          linarith
        simp [g', FourNeighborLaplacian, BandPackingShiftPotential]
        ring_nf
        have reorder (n : ℤ) :
            2 - n * 3 + n ^ 2 = 2 - 3 * n + n ^ 2 := by
          ring
        rw [reorder a, reorder b]
        linear_combination A * second_difference a - A * second_difference b
  | negate =>
      let g' : IntegerLatticeFunction := fun y => g (-GaussianQuarterTurn y)
      refine ⟨g', ?_, ?_⟩
      · rcases hext with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        intro y hy
        simp only [BandPackingSymmetryPartialOdometerAction] at hy ⊢
        have hpre : -GaussianQuarterTurn y ∈ h.domain := by
          simp only [Finset.mem_image] at hy
          rcases hy with ⟨z, hz, rfl⟩
          have hinv : -GaussianQuarterTurn (GaussianQuarterTurn z) = z := by
            ext <;> simp [GaussianQuarterTurn]
          simpa [hinv] using hz
        simp [g', hy, hc _ hpre]
      · intro x
        rcases x with ⟨a, b⟩
        simp only [g', BandPackingSymmetryVectorAction, FourNeighborLaplacian]
        have hr : -GaussianQuarterTurn
            (GaussianQuarterTurn ⟨a, b⟩ + 1) = ⟨a, b - 1⟩ := by
          ext <;> simp [GaussianQuarterTurn]; ring
        have hl : -GaussianQuarterTurn
            (GaussianQuarterTurn ⟨a, b⟩ - 1) = ⟨a, b + 1⟩ := by
          ext <;> simp [GaussianQuarterTurn]; ring
        have hu : -GaussianQuarterTurn
            (GaussianQuarterTurn ⟨a, b⟩ + ⟨0, 1⟩) = ⟨a + 1, b⟩ := by
          ext <;> simp [GaussianQuarterTurn]
        have hd : -GaussianQuarterTurn
            (GaussianQuarterTurn ⟨a, b⟩ - ⟨0, 1⟩) = ⟨a - 1, b⟩ := by
          ext <;> simp [GaussianQuarterTurn]
        have hc : -GaussianQuarterTurn
            (GaussianQuarterTurn ⟨a, b⟩) = ⟨a, b⟩ := by
          ext <;> simp [GaussianQuarterTurn]
        have xr : (⟨a, b⟩ : GaussianInt) + 1 = ⟨a + 1, b⟩ := by
          ext <;> simp
        have xl : (⟨a, b⟩ : GaussianInt) - 1 = ⟨a - 1, b⟩ := by
          ext <;> simp
        have xu : (⟨a, b⟩ : GaussianInt) + ⟨0, 1⟩ = ⟨a, b + 1⟩ := by
          ext <;> simp
        have xd : (⟨a, b⟩ : GaussianInt) - ⟨0, 1⟩ = ⟨a, b - 1⟩ := by
          ext <;> simp
        rw [hr, hl, hu, hd, hc, xr, xl, xu, xd]
        ring
  | conjugate =>
      let g' : IntegerLatticeFunction := fun y => g (-GaussianReflection y)
      refine ⟨g', ?_, ?_⟩
      · rcases hext with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        intro y hy
        simp only [BandPackingSymmetryPartialOdometerAction] at hy ⊢
        have hpre : -GaussianReflection y ∈ h.domain := by
          simp only [Finset.mem_image] at hy
          rcases hy with ⟨z, hz, rfl⟩
          have hinv : -GaussianReflection (-GaussianReflection z) = z := by
            ext <;> simp [GaussianReflection]
          simpa [hinv] using hz
        simp [g', hy, hc _ hpre]
      · intro x
        rcases x with ⟨a, b⟩
        simp only [g', BandPackingSymmetryVectorAction, FourNeighborLaplacian]
        have hr : -GaussianReflection
            (-GaussianReflection ⟨a, b⟩ + 1) = ⟨a - 1, b⟩ := by
          ext <;> simp [GaussianReflection]; ring
        have hl : -GaussianReflection
            (-GaussianReflection ⟨a, b⟩ - 1) = ⟨a + 1, b⟩ := by
          ext <;> simp [GaussianReflection]; ring
        have hu : -GaussianReflection
            (-GaussianReflection ⟨a, b⟩ + ⟨0, 1⟩) = ⟨a, b + 1⟩ := by
          ext <;> simp [GaussianReflection]
        have hd : -GaussianReflection
            (-GaussianReflection ⟨a, b⟩ - ⟨0, 1⟩) = ⟨a, b - 1⟩ := by
          ext <;> simp [GaussianReflection]
        have hc : -GaussianReflection
            (-GaussianReflection ⟨a, b⟩) = ⟨a, b⟩ := by
          ext <;> simp [GaussianReflection]
        have xr : (⟨a, b⟩ : GaussianInt) + 1 = ⟨a + 1, b⟩ := by
          ext <;> simp
        have xl : (⟨a, b⟩ : GaussianInt) - 1 = ⟨a - 1, b⟩ := by
          ext <;> simp
        have xu : (⟨a, b⟩ : GaussianInt) + ⟨0, 1⟩ = ⟨a, b + 1⟩ := by
          ext <;> simp
        have xd : (⟨a, b⟩ : GaussianInt) - ⟨0, 1⟩ = ⟨a, b - 1⟩ := by
          ext <;> simp
        rw [hr, hl, hu, hd, hc, xr, xl, xu, xd]
        ring
  | comp a b iha ihb =>
      obtain ⟨gb, hgb, hlb⟩ := ihb g h hext
      obtain ⟨ga, hga, hla⟩ := iha gb
        (BandPackingSymmetryPartialOdometerAction b h)
        hgb
      refine ⟨ga, ?_, ?_⟩
      · simpa [BandPackingSymmetryPartialOdometerAction] using hga
      · intro x
        simpa [BandPackingSymmetryVectorAction] using
          (hla (BandPackingSymmetryVectorAction b x)).trans (hlb x)

end ApollonianSuperharmonic

end
