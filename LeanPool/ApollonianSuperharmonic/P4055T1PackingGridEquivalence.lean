/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction

-- [TABLET NODE: P4055T1PackingGridEquivalence]

/-!
# P4055T1PackingGridEquivalence

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4055T1PackingGridEquivalence (g : BandPackingSymmetry) :
    ∃ f : GaussianInt ≃ GaussianInt,
      (∀ z, f z = BandPackingSymmetryVectorAction g z) ∧
      (∀ a b : GaussianInt,
        (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
        (f b = f a + 1 ∨ f b = f a - 1 ∨
          f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩)) ∧
      (∀ a b : GaussianInt,
        (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
        (f.symm b = f.symm a + 1 ∨ f.symm b = f.symm a - 1 ∨
          f.symm b = f.symm a + ⟨0, 1⟩ ∨ f.symm b = f.symm a - ⟨0, 1⟩)) := by
-- BODY
  have steps : ∀ g (a b : GaussianInt),
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (BandPackingSymmetryVectorAction g b =
          BandPackingSymmetryVectorAction g a + 1 ∨
       BandPackingSymmetryVectorAction g b =
          BandPackingSymmetryVectorAction g a - 1 ∨
       BandPackingSymmetryVectorAction g b =
          BandPackingSymmetryVectorAction g a + ⟨0, 1⟩ ∨
       BandPackingSymmetryVectorAction g b =
          BandPackingSymmetryVectorAction g a - ⟨0, 1⟩) := by
    intro h
    induction h with
    | identity => intro a b q; simpa [BandPackingSymmetryVectorAction] using q
    | shift w => intro a b q; simpa [BandPackingSymmetryVectorAction] using q
    | negate =>
        intro a b q
        rcases q with q | q | q | q <;> subst b
        · right; right; left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
        · right; right; right; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
        · right; left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; omega
        · left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; omega
    | conjugate =>
        intro a b q
        rcases q with q | q | q | q <;> subst b
        · right; left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianReflection]; omega
        · left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianReflection]; omega
        · right; right; left; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianReflection]
        · right; right; right; apply Zsqrtd.ext <;>
            simp [BandPackingSymmetryVectorAction, GaussianReflection]
    | comp h k ih ihk =>
        intro a b q
        simpa [BandPackingSymmetryVectorAction] using
          ih _ _ (ihk a b q)
  let inverseMap : BandPackingSymmetry → GaussianInt → GaussianInt :=
    BandPackingSymmetry.rec (motive := fun _ => GaussianInt → GaussianInt)
      id (fun z => ⟨z.im, -z.re⟩) (fun z => ⟨-z.re, z.im⟩)
      (fun _ => id) (fun _ _ ih ihk => ihk ∘ ih)
  have inverseLeft : ∀ h z,
      inverseMap h (BandPackingSymmetryVectorAction h z) = z := by
    intro h
    induction h with
    | identity => intro z; unfold inverseMap; rfl
    | shift w => intro z; unfold inverseMap; rfl
    | negate => intro z; unfold inverseMap; apply Zsqrtd.ext <;> simp
        [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
    | conjugate => intro z; unfold inverseMap; apply Zsqrtd.ext <;> simp
        [BandPackingSymmetryVectorAction, GaussianReflection]
    | comp h k ih ihk =>
      intro z
      have map_comp : inverseMap (h.comp k) = inverseMap k ∘ inverseMap h := by rfl
      rw [map_comp]
      change inverseMap k (inverseMap h
        (BandPackingSymmetryVectorAction h
          (BandPackingSymmetryVectorAction k z))) = z
      rw [ih, ihk]
  have inverseRight : ∀ h z,
      BandPackingSymmetryVectorAction h (inverseMap h z) = z := by
    intro h
    induction h with
    | identity => intro z; unfold inverseMap; rfl
    | shift w => intro z; unfold inverseMap; rfl
    | negate => intro z; unfold inverseMap; apply Zsqrtd.ext <;> simp
        [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
    | conjugate => intro z; unfold inverseMap; apply Zsqrtd.ext <;> simp
        [BandPackingSymmetryVectorAction, GaussianReflection]
    | comp h k ih ihk =>
      intro z
      have map_comp : inverseMap (h.comp k) = inverseMap k ∘ inverseMap h := by rfl
      rw [map_comp]
      change BandPackingSymmetryVectorAction h
        (BandPackingSymmetryVectorAction k (inverseMap k (inverseMap h z))) = z
      rw [ihk, ih]
  have inverseSteps : ∀ (sym : BandPackingSymmetry) (a b : GaussianInt),
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (inverseMap sym b = inverseMap sym a + 1 ∨
       inverseMap sym b = inverseMap sym a - 1 ∨
       inverseMap sym b = inverseMap sym a + ⟨0, 1⟩ ∨
       inverseMap sym b = inverseMap sym a - ⟨0, 1⟩) := by
    intro sym
    induction sym with
    | identity => intro a b q; simpa [inverseMap] using q
    | shift w => intro a b q; simpa [inverseMap] using q
    | negate =>
        intro a b q
        rcases q with q | q | q | q <;> subst b
        · right; right; right; apply Zsqrtd.ext <;>
            simp [inverseMap]; omega
        · right; right; left; apply Zsqrtd.ext <;>
            simp [inverseMap]; omega
        · left; apply Zsqrtd.ext <;>
            simp [inverseMap]
        · right; left; apply Zsqrtd.ext <;>
            simp [inverseMap]
    | conjugate =>
        intro a b q
        rcases q with q | q | q | q <;> subst b
        · right; left; apply Zsqrtd.ext <;> simp [inverseMap]; omega
        · left; apply Zsqrtd.ext <;> simp [inverseMap]; omega
        · right; right; left; apply Zsqrtd.ext <;> simp [inverseMap]
        · right; right; right; apply Zsqrtd.ext <;> simp [inverseMap]
    | comp h k ih ihk =>
        intro a b q
        simpa [inverseMap, Function.comp_def] using ihk _ _ (ih a b q)
  let f : GaussianInt ≃ GaussianInt :=
    { toFun := BandPackingSymmetryVectorAction g
      invFun := inverseMap g
      left_inv := inverseLeft g
      right_inv := inverseRight g }
  exact ⟨f, fun _ => rfl, steps g, inverseSteps g⟩

end ApollonianSuperharmonic

end
