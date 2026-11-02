/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Choose

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation.Separation

/-- Finite product of cyclic groups containing the integer separation grid. -/
abbrev AuxiliaryGroup (d Q : ℕ) := Fin d → ZMod (4 * Q)

/-- Embed an integer grid point into the finite ambient separation group. -/
def gridToGroup {d Q : ℕ} (x : Grid d Q) : AuxiliaryGroup d Q :=
  fun i => (x i : ℕ)

/-- Embed an integer grid point into real coordinate space. -/
def gridToReal {d Q : ℕ} (x : Grid d Q) : Fin d → ℝ :=
  fun i => (x i : ℕ)

theorem gridToReal_injective {d Q : ℕ} :
    Function.Injective (gridToReal : Grid d Q → Fin d → ℝ) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((x i : ℕ) : ℝ) = ((y i : ℕ) : ℝ) at hi
  exact_mod_cast hi

theorem squaredNorm_gridToReal {d Q : ℕ} (x : Grid d Q) :
    squaredNorm (gridToReal x) = (gridSquaredNorm x : ℝ) := by
  simp [squaredNorm, gridToReal, gridSquaredNorm, Nat.cast_sum]

theorem dot_gridToReal {d Q : ℕ} (x y : Grid d Q) :
    dot (gridToReal x) (gridToReal y) = (gridDot x y : ℝ) := by
  simp [dot, gridToReal, gridDot, Nat.cast_sum]

theorem grid_group_collision_lift {d Q : ℕ} (t c u v : Grid d Q)
    (h : gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c) :
    ∀ i, ((c i : ℕ) : ℤ) =
      ((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ) := by
  intro i
  have hcast : (((c i : ℕ) : ℤ) : ZMod (4 * Q)) =
      ((((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) :
        ZMod (4 * Q)) := by
    simpa [gridToGroup, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (congrFun h i).symm
  have hmod : Int.ModEq (4 * (Q : ℤ)) ((c i : ℕ) : ℤ)
      (((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff _ _ (4 * Q)).mp
        (by simpa only [Int.cast_add, Int.cast_sub] using hcast)
  have hbound (x : Fin Q) : 0 ≤ ((x : ℕ) : ℤ) ∧ ((x : ℕ) : ℤ) < (Q : ℤ) := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast x.isLt
  exact grid_modular_collision (Q : ℤ) _ _ _ _
    (hbound (c i)) (hbound (t i)) (hbound (u i)) (hbound (v i)) hmod

theorem grid_sphere_slice_collision {d Q : ℕ} (t c u v : Grid d Q)
    (hsphere : gridSquaredNorm c = gridSquaredNorm t)
    (hslice : gridDot t u = gridDot t v) :
    gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c ↔
      u = v ∧ c = t := by
  constructor
  · intro h
    have hnorm : squaredNorm (gridToReal c) = squaredNorm (gridToReal t) := by
      simp only [squaredNorm_gridToReal, hsphere]
    have hdot : dot (gridToReal t) (gridToReal u) =
        dot (gridToReal t) (gridToReal v) := by
      simp only [dot_gridToReal, hslice]
    have hlift := grid_group_collision_lift t c u v h
    have hreal : ∀ i, gridToReal c i =
        gridToReal t i + gridToReal u i - gridToReal v i := by
      intro i
      dsimp [gridToReal]
      exact_mod_cast hlift i
    obtain ⟨huv, hct⟩ := sphere_slice_collision
      (gridToReal t) (gridToReal c) (gridToReal u) (gridToReal v) hnorm hdot hreal
    exact ⟨gridToReal_injective huv, gridToReal_injective hct⟩
  · rintro ⟨rfl, rfl⟩
    simp [sub_eq_add_neg, add_left_comm]

theorem indexed_grid_collision {S U : Type*} {d Q : ℕ}
    (tag : S → Grid d Q) (point : S → U → Grid d Q)
    (htag : Function.Injective tag)
    (hpoint : ∀ s, Function.Injective (point s))
    (hsphere : ∀ s s', gridSquaredNorm (tag s') = gridSquaredNorm (tag s))
    (hslice : ∀ s i j, gridDot (tag s) (point s i) = gridDot (tag s) (point s j)) :
    ∀ s s' i j,
      gridToGroup (point s i) + (gridToGroup (tag s) - gridToGroup (point s j)) =
        gridToGroup (tag s') ↔ s = s' ∧ i = j := by
  intro s s' i j
  rw [grid_sphere_slice_collision (tag s) (tag s') (point s i) (point s j)
    (hsphere s s') (hslice s i j)]
  constructor
  · rintro ⟨hij, hss⟩
    exact ⟨(htag hss).symm, hpoint s hij⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem exists_modular_separation {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ (tag : Fin K → AuxiliaryGroup d Q)
      (point : Fin K → Fin m → AuxiliaryGroup d Q),
      ∀ s s' i j,
        point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j := by
  classical
  obtain ⟨tags, htags, ⟨radius, hradius⟩, hslices⟩ := grid_tags_slices hK hm
  choose slice hsliceCard level hlevel using
    (fun t : ↥tags => hslices t.val t.property)
  let tagEnum : Fin K ≃ ↥tags := (Finset.equivFinOfCardEq htags).symm
  let sliceEnum (t : ↥tags) : Fin m ≃ ↥(slice t) :=
    (Finset.equivFinOfCardEq (hsliceCard t)).symm
  let tagGrid (s : Fin K) : Grid d Q := (tagEnum s).val
  let pointGrid (s : Fin K) (i : Fin m) : Grid d Q :=
    (sliceEnum (tagEnum s) i).val
  have htag : Function.Injective tagGrid := by
    intro s s' h
    apply tagEnum.injective
    exact Subtype.ext h
  have hpoint : ∀ s, Function.Injective (pointGrid s) := by
    intro s i j h
    apply (sliceEnum (tagEnum s)).injective
    exact Subtype.ext h
  have hsphere : ∀ s s', gridSquaredNorm (tagGrid s') = gridSquaredNorm (tagGrid s) := by
    intro s s'
    have hc := (hradius (tagEnum s').val (tagEnum s').property).trans
      (hradius (tagEnum s).val (tagEnum s).property).symm
    exact congrArg Fin.val hc
  have hslice : ∀ s i j,
      gridDot (tagGrid s) (pointGrid s i) = gridDot (tagGrid s) (pointGrid s j) := by
    intro s i j
    have hc := (hlevel (tagEnum s) (sliceEnum (tagEnum s) i).val
      (sliceEnum (tagEnum s) i).property).trans
      (hlevel (tagEnum s) (sliceEnum (tagEnum s) j).val
        (sliceEnum (tagEnum s) j).property).symm
    exact congrArg Fin.val hc
  exact ⟨fun s => gridToGroup (tagGrid s), fun s i => gridToGroup (pointGrid s i),
    indexed_grid_collision tagGrid pointGrid htag hpoint hsphere hslice⟩

theorem card_auxiliaryGroup (d Q : ℕ) [NeZero (4 * Q)] :
    Fintype.card (AuxiliaryGroup d Q) = (4 * Q) ^ d := by
  simp [AuxiliaryGroup, ZMod.card]

end MatrixMultiplication.Foundation.Separation

end MatrixMultiplicationAllFields
