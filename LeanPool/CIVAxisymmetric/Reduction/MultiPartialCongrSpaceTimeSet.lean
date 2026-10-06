/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Multi Partial Congr Space Time Set

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

private theorem spatialPartial_congr_of_eqOn_spaceTimeSet' {v u : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (h : ∀ w ∈ spaceTimeSet Ω I, v w = u w) {z : ParabolicPoint} (hz : z ∈ spaceTimeSet Ω I)
    (j : Fin 3) :
    spatialPartial v j z = spatialPartial u j z := by
  show fderiv ℝ (fun y : Vec3 => v (y, z.2)) z.1 (basisVec j)
    = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (basisVec j)
  have _ := hI.mem_nhds hz.2
  have hev : (fun y : Vec3 => v (y, z.2)) =ᶠ[nhds z.1] (fun y : Vec3 => u (y, z.2)) := by
    filter_upwards [hΩ.mem_nhds hz.1] with y hy using h (y, z.2) ⟨hy, hz.2⟩
  rw [hev.fderiv_eq]

theorem spatialPartial_iterate_congr_of_eqOn_spaceTimeSet {v u : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (h : Set.EqOn v u (spaceTimeSet Ω I)) (j : Fin 3) (n : ℕ) :
    Set.EqOn ((fun k => spatialPartial k j)^[n] v) ((fun k => spatialPartial k j)^[n] u)
      (spaceTimeSet Ω I) := by
  induction n with
  | zero => simpa [Set.EqOn] using h
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    intro z hz
    have ih_pointwise : ∀ w ∈ spaceTimeSet Ω I, ((fun k => spatialPartial k j)^[k] v) w =
        ((fun k => spatialPartial k j)^[k] u) w := ih
    exact spatialPartial_congr_of_eqOn_spaceTimeSet' hΩ hI ih_pointwise hz j

theorem multiPartial_congr_of_eqOn_spaceTimeSet {v u : ParabolicPoint → ℝ} {Ω : Set Vec3}
    {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (h : Set.EqOn v u (spaceTimeSet Ω I)) (α : Fin 3 → ℕ) :
    Set.EqOn (multiPartial v α) (multiPartial u α) (spaceTimeSet Ω I) := by
  have h2 : Set.EqOn ((fun k => spatialPartial k 2)^[α 2] v)
      ((fun k => spatialPartial k 2)^[α 2] u) (spaceTimeSet Ω I) :=
    spatialPartial_iterate_congr_of_eqOn_spaceTimeSet hΩ hI h 2 (α 2)
  have h1 : Set.EqOn ((fun k => spatialPartial k 1)^[α 1]
      ((fun k => spatialPartial k 2)^[α 2] v))
      ((fun k => spatialPartial k 1)^[α 1]
      ((fun k => spatialPartial k 2)^[α 2] u)) (spaceTimeSet Ω I) :=
    spatialPartial_iterate_congr_of_eqOn_spaceTimeSet hΩ hI h2 1 (α 1)
  have h0 : Set.EqOn ((fun k => spatialPartial k 0)^[α 0]
      ((fun k => spatialPartial k 1)^[α 1]
      ((fun k => spatialPartial k 2)^[α 2] v)))
      ((fun k => spatialPartial k 0)^[α 0]
      ((fun k => spatialPartial k 1)^[α 1]
      ((fun k => spatialPartial k 2)^[α 2] u))) (spaceTimeSet Ω I) :=
    spatialPartial_iterate_congr_of_eqOn_spaceTimeSet hΩ hI h1 0 (α 0)
  intro z hz
  simpa [multiPartial] using h0 hz

theorem sum_spatialPartial_congr_of_eqOn_spaceTimeSet {v u : Fin 3 → ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (h : ∀ k : Fin 3, Set.EqOn (v k) (u k) (spaceTimeSet Ω I)) {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet Ω I) :
    (∑ j : Fin 3, spatialPartial (v j) j z) = ∑ j : Fin 3, spatialPartial (u j) j z := by
  simp_rw [Finset.sum_congr rfl (fun j _ =>
    spatialPartial_congr_of_eqOn_spaceTimeSet' hΩ hI (h j) hz j)]

end CIV
