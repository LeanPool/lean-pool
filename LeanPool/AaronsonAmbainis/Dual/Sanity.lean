/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import LeanPool.AaronsonAmbainis.Dual.Cover
public import LeanPool.AaronsonAmbainis.Dual.RowAux
public import LeanPool.AaronsonAmbainis.MainTheorem

/-!
# Consistency checks for the statements of the duality part

Not used in the proof of the main theorem. These lemmas check that the propositions
`CoverDuality`, `PackingBound`, `RowBoundPM` of `RowDefs.lean` say what is intended:

* `packing_le_of_cover`      — weak duality, the easy converse of `Dual.exists_cover`;
* `cover_iff_packing`        — the packing hypothesis of `CoverDuality` is equivalent to its
                               conclusion;
* `empty_nonpos_of_packing`  — the side hypothesis `t ∅ ≤ 0` of `CoverDuality` follows from the
                               packing hypothesis;
* `packingBound_of_rowBoundPM`, `packingBound_iff_rowBoundPM` — `PackingBound ↔ RowBoundPM`;
* `rowBoundPM_of_rowBound`   — the row bound of Agarwal and Ben-David (`RowBound` in
                               `Statements.lean`: Theorem 1.7 of arXiv:2410.19062, constant `π²/4`
                               for values in `[0,1]`; a hypothesis, not proved in this project)
                               implies `RowBoundPM`, hence `PackingBound`: these two statements
                               are consequences of the published theorem.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Dual

open Finset

section Weak

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weak duality: a cover of mass at most `K` bounds the value of every fractional packing. -/
theorem packing_le_of_cover (t : Finset ι → ℝ) (K : ℝ) (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (haK : ∑ i, a i ≤ K) (hcov : ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hload : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) :
    ∑ S, κ S * t S ≤ K := by
  calc ∑ S, κ S * t S
      ≤ ∑ S, κ S * ∑ i ∈ S, a i :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hcov S) (hκ S)
    _ = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := sum_mul_sum_mem κ a
    _ ≤ ∑ i, a i * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hload i) (ha0 i)
    _ = ∑ i, a i := by simp
    _ ≤ K := haK

/-- The packing hypothesis of `CoverDuality` is equivalent to its conclusion. -/
theorem cover_iff_packing (t : Finset ι → ℝ) (K : ℝ) :
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) ↔
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i :=
  ⟨exists_cover t K, fun ⟨a, ha0, haK, hcov⟩ κ hκ hload =>
    packing_le_of_cover t K a ha0 haK hcov κ hκ hload⟩

/-- The side hypothesis `t ∅ ≤ 0` of `CoverDuality` follows from the packing hypothesis. -/
theorem empty_nonpos_of_packing (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) : t ∅ ≤ 0 := by
  obtain ⟨a, -, -, h⟩ := exists_cover t K hpack
  simpa using h ∅

end Weak

/-- The converse of `rowBoundPM_of_packing`: rows of cost at most `π² d²` bound every fractional
packing. -/
theorem packingBound_of_rowBoundPM : RowBoundPM → PackingBound := by
  intro hRB ι _ _ d f hf hdeg x κ hκ hload
  obtain ⟨a, ha0, haK, hacov⟩ := hRB ι d f hf hdeg
  refine packing_le_of_cover (fun S => |f x - f (flipSet x S)|) _ (a x) (ha0 x) (haK x)
    (fun S => ?_) κ hκ hload
  have h := hacov x (flipSet x S)
  rwa [diffSet_flipSet] at h

/-- `PackingBound` and `RowBoundPM` are equivalent. -/
theorem packingBound_iff_rowBoundPM : PackingBound ↔ RowBoundPM :=
  ⟨fun h => rowBoundPM_of_packing_of_cover h (fun _ _ _ t K _ _ hp => exists_cover t K hp),
    packingBound_of_rowBoundPM⟩

/-- The row bound of Agarwal and Ben-David (the hypothesis `RowBound`) implies `RowBoundPM`: it
gives rows of cost at most `π² d² / 2 ≤ π² d²` (`rows_of_rowBound`). -/
theorem rowBoundPM_of_rowBound : RowBound → RowBoundPM := by
  intro hRB ι _ _ d f hf hdeg
  obtain ⟨a, ha0, haK, hacov⟩ := rows_of_rowBound hRB d f hf hdeg
  have hp : (0 : ℝ) ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by positivity
  exact ⟨a, ha0, fun x => le_trans (haK x) (by linarith), hacov⟩

/-- Consequently `PackingBound` follows from the row bound of Agarwal and Ben-David (the
hypothesis `RowBound`). -/
theorem packingBound_of_rowBound : RowBound → PackingBound :=
  fun h => packingBound_of_rowBoundPM (rowBoundPM_of_rowBound h)

end Dual
end AaronsonAmbainis
