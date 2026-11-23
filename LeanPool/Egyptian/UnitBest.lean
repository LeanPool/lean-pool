/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Assembly
public import LeanPool.Egyptian.UnitComparison
import Mathlib.Data.List.GetD

/-! # The unit-fraction boundary, in both denominator conventions -/

@[expose] public section

namespace Egyptian

private theorem unit_best_aux (σ : Convention) (T m : ℕ) (hT : 0 < T) :
    let g := prefixTuple (fun i => unitIter T i + 1) m
    IsBest σ (unit T) m g ∧ ∀ ds, IsBest σ (unit T) m ds → ds = g := by
  let t := unitIter T
  let g := prefixTuple (fun i => t i + 1) m
  change IsBest σ (unit T) m g ∧ _
  have had : Admissible σ (unit T) m g := by
    rw [show g = unitDigits T m from (digits_eq_prefix T m).symm]
    obtain ⟨hl, hlower, horder, hsum⟩ := digits_data σ hT m
    have hresidual : 0 < unit (unitIter T m) :=
      one_div_pos.mpr (by exact_mod_cast unitIter_pos hT m)
    exact ⟨hl, fun d hd => by have := hlower d hd; omega, horder, by linarith⟩
  have compare (ds : List ℕ) (h : Admissible σ (unit T) m ds) :
      recipSum ds ≤ recipSum g ∧ (recipSum g ≤ recipSum ds → ds = g) := by
    obtain ⟨hl, hd, horder, hsmall⟩ := h
    let d (i : ℕ) := ds.getD i 2
    have repr : prefixTuple d m = ds := by
      rw [← hl]
      simpa only [d, List.take_length] using prefixTuple_getD ds 2 le_rfl
    have hdpos (i : ℕ) (hi : i < m) : 0 < d i := by
      have hj : i < ds.length := by omega
      have := hd ds[i] (List.getElem_mem hj)
      change 0 < ds.getD i 2
      rw [List.getD_eq_getElem _ _ hj]
      omega
    have hmono (i : ℕ) (hi : i+1 < m) : d i ≤ d (i+1) := by
      have hi' : i < ds.length := by omega
      have hj' : i+1 < ds.length := by omega
      have hh := List.pairwise_iff_getElem.mp horder i (i+1) hi' hj' (by omega)
      rw [show d i = ds[i] from List.getD_eq_getElem _ _ hi',
        show d (i+1) = ds[i+1] from List.getD_eq_getElem _ _ hj']
      exact Convention.rel_le hh
    have hs := real_prefix_sum d m
    rw [repr] at hs
    have hs' := real_prefix_sum (fun i => t i + 1) m
    change (recipSum g : ℝ) = _ at hs'
    simp only [Nat.cast_add, Nat.cast_one] at hs'
    change recipSum ds < 1 / (T : ℚ) at hsmall
    have smallR := (Rat.cast_lt (K := ℝ)).mpr hsmall
    have hcmp := unitFiniteComparison T m hT d hdpos hmono (hs ▸ (by simpa using smallR))
    refine ⟨?_, ?_⟩
    · have w := hcmp.1
      change _ ≤ ∑ i ∈ Finset.range m, 1 / ((t i : ℝ) + 1) at w
      rw [← hs, ← hs'] at w
      exact_mod_cast w
    · intro he
      have hr : (recipSum g : ℝ) ≤ (recipSum ds : ℝ) := by exact_mod_cast he
      rw [hs', hs] at hr
      have same := hcmp.2 hr
      rw [← repr]
      apply List.map_congr_left
      intro i hi
      exact same i (List.mem_range.mp hi)
  refine ⟨⟨had, fun ds h => (compare ds h).1⟩, ?_⟩
  intro ds h
  exact (compare ds h.1).2 (h.2 _ had)

/-- The paper's unit-fraction extremality lemma, at every length. -/
theorem uniqueUnitTails : UniqueUnitTails := by
  intro σ T m hT
  rw [greedyTuple_unit σ hT, digits_eq_prefix]
  exact unit_best_aux σ T m hT

end Egyptian
