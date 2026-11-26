/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Range

/-!
# Ordering finitely many meetings on an edge arc

In XII (4.5), page 252, subdivide an edge according to its finite
nonempty set of crossings. Pull these points back through an arc
parametrization and sort the resulting finite subset of the unit
interval. Because the endpoints are not crossings, all sorted
parameters lie strictly between zero and one.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A finite nonempty set of interior points of an edge arc has
strictly increasing parameters. These are the crossing parameters
used for the subdivision in XII (4.5), page 252. -/
theorem exists_ordered_arc_meeting_parameters {E X : Set ℂ} {a b : ℂ}
    (hE : IsLineWithEnds E a b) (hX : X.Finite) (hXne : X.Nonempty)
    (hXE : X ⊆ E) (haX : a ∉ X) (hbX : b ∉ X) :
    ∃ k : ℕ, 0 < k ∧ ∃ φ : unitInterval ≃ₜ E,
      (φ 0).val = a ∧ (φ 1).val = b ∧
      ∃ t : Fin k → unitInterval, StrictMono t ∧
        (∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1) ∧
        X = range (fun i => (φ (t i)).val) := by
  classical
  obtain ⟨φ, hφ0, hφ1⟩ := hE
  let Y : Set E := Subtype.val ⁻¹' X
  have hY : Y.Finite := hX.preimage Subtype.val_injective.injOn
  let T : Set unitInterval := φ ⁻¹' Y
  have hT : T.Finite := hY.preimage φ.injective.injOn
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    refine ⟨φ.symm ⟨x, hXE hx⟩, ?_⟩
    change (φ (φ.symm ⟨x, hXE hx⟩)).val ∈ X
    rw [φ.apply_symm_apply]
    exact hx
  let : Fintype T := hT.fintype
  let k := Fintype.card T
  let σ : Fin k ≃o T := Fintype.orderIsoFinOfCardEq _ rfl
  have hk : 0 < k := Fintype.card_pos_iff.mpr ⟨⟨hTne.choose, hTne.choose_spec⟩⟩
  let t : Fin k → unitInterval := fun i => (σ i).val
  have ht : StrictMono t := fun _ _ hij => σ.strictMono hij
  have ht01 : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1 := by
    intro i
    have hmem : (φ (t i)).val ∈ X := (σ i).property
    have hzero : (t i : ℝ) ≠ 0 := by
      intro h
      have heq : t i = 0 := Subtype.ext h
      rw [heq, hφ0] at hmem
      exact haX hmem
    have hone : (t i : ℝ) ≠ 1 := by
      intro h
      have heq : t i = 1 := Subtype.ext h
      rw [heq, hφ1] at hmem
      exact hbX hmem
    exact ⟨lt_of_le_of_ne (t i).property.1 (Ne.symm hzero),
      lt_of_le_of_ne (t i).property.2 hone⟩
  refine ⟨k, hk, φ, hφ0, hφ1, t, ht, ht01, ?_⟩
  apply Subset.antisymm
  · intro x hx
    let u : unitInterval := φ.symm ⟨x, hXE hx⟩
    have hu : u ∈ T := by
      change (φ (φ.symm ⟨x, hXE hx⟩)).val ∈ X
      rw [φ.apply_symm_apply]
      exact hx
    refine ⟨σ.symm ⟨u, hu⟩, ?_⟩
    change (φ (σ (σ.symm ⟨u, hu⟩)).val).val = x
    rw [σ.apply_symm_apply]
    change (φ (φ.symm ⟨x, hXE hx⟩)).val = x
    rw [φ.apply_symm_apply]
  · rintro x ⟨i, rfl⟩
    exact (σ i).property

end GraphMinor.GM12
