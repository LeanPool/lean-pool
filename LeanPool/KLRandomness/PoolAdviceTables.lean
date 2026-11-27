/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolAdvice
public import LeanPool.KLRandomness.PoolApproximationFunction

/-!
# Ordinary finite encodings of prefix tables

An arbitrary table on the finite type of depth-d binary prefixes has an
ordinary finite-list encoding for the pool checker. Thus choosing analytic
clopen and rational cylinder approximations only supplies finite advice; it
does not supply a membership oracle for an infinite set.
-/

@[expose] public section

namespace Klr.PoolAdvice

open MeasureTheory
open scoped symmDiff

/-- Every function on depth-d binary words has a finite list representation,
using the same ordinary word encodings as the pool checker. -/
theorem exists_list_table {β : Type*} (d : ℕ) (f : (Fin d → Bool) → β) (default : β) :
    ∃ L : List β, ∀ u : Fin d → Bool,
      L.getD (Encodable.encode (List.ofFn u)) default = f u := by
  classical
  let bound := (Finset.univ : Finset (Fin d → Bool)).sup
    (fun u => Encodable.encode (List.ofFn u)) + 1
  let value (n : ℕ) : β := f (fun i =>
    ((@Encodable.decode (List Bool) inferInstance n).getD []).getD i.val false)
  refine ⟨List.ofFn (fun n : Fin bound => value n.val), ?_⟩
  intro u
  have hu : Encodable.encode (List.ofFn u) < bound := by
    exact Nat.lt_succ_of_le (Finset.le_sup
      (f := fun u : Fin d → Bool => Encodable.encode (List.ofFn u)) (Finset.mem_univ u))
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hu, ↓reduceDIte,
    Option.getD_some]
  change value (Encodable.encode (List.ofFn u)) = f u
  dsimp only [value]
  rw [Encodable.encodek]
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem inputPrefix_eq_ofFn (Z : Cantor) (d : ℕ) :
    ScanRule.inputPrefix Z d = List.ofFn (PoolApproximation.bits d Z) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [ScanRule.inputPrefix, List.getElem_map, List.getElem_range,
      List.getElem_ofFn, PoolApproximation.bits]

/-- The list representation evaluates exactly to the original finite table
on every infinite sequence. -/
theorem exists_list_prefix_table {β : Type*} (d : ℕ)
    (f : (Fin d → Bool) → β) (default : β) :
    ∃ L : List β, ∀ Z : Cantor,
      L.getD (Encodable.encode (ScanRule.inputPrefix Z d)) default =
        PoolApproximation.eval f Z := by
  obtain ⟨L, hL⟩ := exists_list_table d f default
  refine ⟨L, fun Z => ?_⟩
  rw [inputPrefix_eq_ofFn]
  exact hL (PoolApproximation.bits d Z)

/-- All the finitely many clopen and rational tables can be encoded together
in one finite list, with a single common depth. -/
theorem exists_advice_tables (d D : ℕ)
    (H : Fin D → (Fin d → Bool) → Bool) (ψ : Fin D → (Fin d → Bool) → ℚ) :
    ∃ tables : List Table, ∀ i : Fin D, ∀ Z : Cantor,
      ((tables.getD i.val ([], [])).1).getD
          (Encodable.encode (ScanRule.inputPrefix Z d)) false = PoolApproximation.eval (H i) Z ∧
      ((tables.getD i.val ([], [])).2).getD
          (Encodable.encode (ScanRule.inputPrefix Z d)) 0 = PoolApproximation.eval (ψ i) Z := by
  classical
  choose LH hH using fun i => exists_list_prefix_table d (H i) false
  choose Lψ hψ using fun i => exists_list_prefix_table d (ψ i) 0
  refine ⟨List.ofFn (fun i : Fin D => (LH i, Lψ i)), ?_⟩
  intro i Z
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some]
  exact ⟨hH i Z, hψ i Z⟩

/-- A finite family of Borel high sets and bounded measurable limit functions
admits one fixed finite advice record, with no dependence on a future pool size. -/
theorem exists_approximating_advice (D z ℓ : ℕ) (δ γ : ℚ) (hδ : 0 < δ)
    (H : Fin D → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (g : Fin D → Cantor → ℝ) (hgm : ∀ i, Measurable (g i))
    (hg0 : ∀ i Z, 0 ≤ g i Z) (hg1 : ∀ i Z, g i Z ≤ 1) :
    ∃ A : Advice, A.positionBound = z ∧ A.protectedCount = ℓ ∧
      A.error = δ ∧ A.threshold = γ ∧ ∀ i : Fin D,
        fairCoin.real (highSet A i.val ∆ H i) < (δ : ℝ) ∧
        (∀ Z, 0 ≤ approx A i.val Z ∧ approx A i.val Z ≤ 1) ∧
        (∫ Z, |approx A i.val Z - g i Z| ∂fairCoin) < (δ : ℝ) := by
  classical
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨d, high, value, happrox⟩ :=
    PoolApproximation.exists_common_tables H hH g hgm hg0 hg1 hδr hδr
  obtain ⟨tables, htables⟩ := exists_advice_tables d D high value
  let A : Advice := ⟨z, ℓ, d, δ, γ, tables⟩
  have htake (Z : Cantor) : (ScanRule.inputPrefix Z d).take d =
      ScanRule.inputPrefix Z d := List.take_of_length_le (by simp)
  have hhigh (i : Fin D) : highSet A i.val = PoolApproximation.event (high i) := by
    ext Z
    change (((tables.getD i.val ([], [])).1).getD
      (Encodable.encode ((ScanRule.inputPrefix Z d).take d)) false = true) ↔ _
    rw [htake Z, (htables i Z).1]
    rfl
  have hvalue (i : Fin D) (Z : Cantor) : approx A i.val Z =
      ((PoolApproximation.eval (value i) Z : ℚ) : ℝ) := by
    change ((((tables.getD i.val ([], [])).2).getD
      (Encodable.encode ((ScanRule.inputPrefix Z d).take d)) 0 : ℚ) : ℝ) = _
    rw [htake Z, (htables i Z).2]
  refine ⟨A, rfl, rfl, rfl, rfl, fun i => ⟨?_, ?_, ?_⟩⟩
  · rw [hhigh i]
    exact (happrox i).1
  · intro Z
    rw [hvalue]
    exact_mod_cast (happrox i).2.1 (PoolApproximation.bits d Z)
  · simp_rw [hvalue]
    simpa only [Real.norm_eq_abs] using (happrox i).2.2

end Klr.PoolAdvice
