/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityBasic
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityCoulomb
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Smooth cell representatives and harmonicity

The explicit smooth representative associated to a nearest-nucleus cell.
-/

public section

open InnerProductSpace Laplacian Filter
open scoped Topology NNReal

namespace LiebThirring

/-- The explicit smooth representative associated to a nearest-nucleus cell. -/
@[expose] noncomputable def screenedCellPotential {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (k : Fin M) (x : Position) : ℝ :=
  ∑ p ∈ Finset.univ.erase k, (Z : ℝ) * ‖x - R p‖⁻¹

theorem contDiffAt_screenedCellPotential {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (screenedCellPotential Z R k) x := by
  classical
  apply ContDiffAt.sum
  intro p hp
  exact contDiffAt_const.mul (contDiffAt_inv_nuclear_distance (R p) x
    (ne_nucleus_of_mem_closedVoronoiCell R hR k p (Finset.mem_erase.mp hp).1 hx) n)

theorem screenedPotentialReal_eq_screenedCellPotential {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    screenedPotentialReal Z R x = screenedCellPotential Z R k x :=
  screenedPotentialReal_eq_on_closedVoronoiCell Z R hR k hx

theorem harmonicAt_inv_nuclear_distance (y x : Position) (hx : x ≠ y) :
    HarmonicAt (fun z : Position => ‖z - y‖⁻¹) x := by
  refine ⟨contDiffAt_inv_nuclear_distance y x hx 2, ?_⟩
  filter_upwards [isOpen_ne.mem_nhds hx] with z hz
  exact laplacian_inv_nuclear_distance y z hz

theorem harmonicAt_screenedCellPotential {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    HarmonicAt (screenedCellPotential Z R k) x := by
  classical
  have hterm (p : Fin M) (hp : p ∈ Finset.univ.erase k) :
      HarmonicAt (fun z => (Z : ℝ) * ‖z - R p‖⁻¹) x := by
    have hh := (harmonicAt_inv_nuclear_distance (R p) x
      (ne_nucleus_of_mem_closedVoronoiCell R hR k p (Finset.mem_erase.mp hp).1 hx)).const_smul (c
        := (Z : ℝ))
    have he : (Z : ℝ) • (fun z : Position => ‖z - R p‖⁻¹) =
        (fun z : Position => (Z : ℝ) * ‖z - R p‖⁻¹) := by
      ext z
      simp only [Pi.smul_apply, smul_eq_mul]
    rwa [he] at hh
  unfold screenedCellPotential
  generalize Finset.univ.erase k = s at hterm ⊢
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using harmonicAt_const (0 : ℝ)
  | @insert p s hp ih =>
    simp only [Finset.sum_insert hp]
    exact (hterm p (Finset.mem_insert_self p s)).add
      (ih (fun l hl => hterm l (Finset.mem_insert_of_mem hl)))

end LiebThirring

end
