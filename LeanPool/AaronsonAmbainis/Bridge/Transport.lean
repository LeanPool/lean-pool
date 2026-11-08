/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import LeanPool.AaronsonAmbainis.Bridge.Basic

/-!
# `RowBound` on the index types `Fin n`

`RowBound` quantifies over all finite index types `ι : Type`; Theorem 1.7 of arXiv:2410.19062 is
about `[n]`. The statement restricted to the index types `Fin n` (`RowBoundFin`) already implies
`RowBound` (transport along `Fintype.equivFin`). So the generality of `RowBound` in the index type
asks for nothing beyond the `[n]` statement (`rowBound_iff_fin`).
-/

@[expose] public section

namespace AaronsonAmbainis.Bridge

open Finset

/-- `RowBound`, restricted to the index types `Fin n`. -/
def RowBoundFin : Prop :=
  ∀ (n d : ℕ) (f : Cube (Fin n) → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem chi_comp_equiv (e : ι ≃ κ) (S : Finset ι) (y : Cube κ) :
    chi S (fun i => y (e i)) = chi (S.map e.toEmbedding) y := by
  simp [chi, Finset.prod_map]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `HasDegreeLE` is invariant under relabelling the coordinates. -/
theorem hasDegreeLE_comp_equiv (e : ι ≃ κ) {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    HasDegreeLE (fun y : Cube κ => f (fun i => y (e i))) d := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => c (T.map e.symm.toEmbedding),
    fun T hT => hc _ (by rwa [Finset.card_map]), fun y => ?_⟩
  change f (fun i => y (e i)) = ∑ T : Finset κ, c (T.map e.symm.toEmbedding) * chi T y
  rw [hf]
  refine Fintype.sum_equiv e.finsetCongr _ _ (fun S => ?_)
  have h1 : (e.finsetCongr S).map e.symm.toEmbedding = S := e.finsetCongr.left_inv S
  rw [h1, chi_comp_equiv]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem diffSet_comp_equiv (e : ι ≃ κ) (x y : Cube ι) :
    diffSet (fun k => x (e.symm k)) (fun k => y (e.symm k))
      = (diffSet x y).map e.toEmbedding := by
  ext k
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro h
    exact ⟨e.symm k, h, e.apply_symm_apply k⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi

omit [DecidableEq ι] [DecidableEq κ] in
/-- The conclusion of `RowBound` transports along an equivalence of index types. -/
theorem rowBound_concl_transport (e : ι ≃ κ) (f : Cube ι → ℝ) (B : ℝ)
    (h : ∃ c : Cube κ → κ → ℝ,
      (∀ x y, |f (fun i => x (e i)) - f (fun i => y (e i))| ≤ ∑ k ∈ diffSet x y, c x k) ∧
      (∀ x, ∑ k, c x k ≤ B)) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧ (∀ x, ∑ i, c x i ≤ B) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨fun x i => c (fun k => x (e.symm k)) (e i), fun x y => ?_, fun x => ?_⟩
  · have h1 := hc1 (fun k => x (e.symm k)) (fun k => y (e.symm k))
    simp only [Equiv.symm_apply_apply] at h1
    rw [diffSet_comp_equiv, Finset.sum_map] at h1
    exact h1
  · have h2 := hc2 (fun k => x (e.symm k))
    rw [← Equiv.sum_comp e] at h2
    exact h2

/-- The `[n]` statement implies the statement for all finite index types. -/
theorem rowBound_of_fin (h : RowBoundFin) : RowBound := by
  intro ι _ _ d f hf hdeg
  refine rowBound_concl_transport (Fintype.equivFin ι) f _ ?_
  exact h (Fintype.card ι) d (fun y => f (fun i => y (Fintype.equivFin ι i)))
    (fun y => hf _) (hasDegreeLE_comp_equiv (Fintype.equivFin ι) hdeg)

theorem rowBoundFin_of_rowBound (h : RowBound) : RowBoundFin :=
  fun n d f hf hdeg => h (Fin n) d f hf hdeg

/-- `RowBound` is equivalent to its restriction to the index types `Fin n`. -/
theorem rowBound_iff_fin : RowBound ↔ RowBoundFin :=
  ⟨rowBoundFin_of_rowBound, rowBound_of_fin⟩

end AaronsonAmbainis.Bridge
