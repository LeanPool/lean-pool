/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Assembly
public import LeanPool.Egyptian.UnitComparison

/-! # The unit-fraction boundary, in both denominator conventions -/

@[expose] public section

namespace Egyptian

private def entry (ds : List ℕ) (i : ℕ) := ds[i]?.getD 2

private theorem entry_of_lt {ds : List ℕ} {i : ℕ} (h : i < ds.length) :
    entry ds i = ds[i] := by simp [entry, h]

private theorem prefix_entry (ds : List ℕ) : prefixTuple (entry ds) ds.length = ds := by
  apply List.ext_getElem
  · simp [prefixTuple]
  · intro i hi hj
    simp [prefixTuple, entry_of_lt hj]

private theorem unit_best_aux (σ : Convention) (T m : ℕ) (hT : 0 < T) :
    let g := prefixTuple (fun i => unitIter T i + 1) m
    IsBest σ (unit T) m g ∧ ∀ ds, IsBest σ (unit T) m ds → ds = g := by
  let t := unitIter T
  let g := prefixTuple (fun i => t i + 1) m
  change IsBest σ (unit T) m g ∧ _
  have hpos (i : ℕ) : 0 < t i := unitIter_pos hT i
  have inc : StrictMono t := unitIter_strictMono hT
  have hsum : (recipSum g : ℝ) = 1 / (T : ℝ) - 1 / (t m : ℝ) := by
    rw [show g = prefixTuple (fun i => t i + 1) m from rfl, real_prefix_sum]
    simpa [t] using unitPrefixSum T m hT
  have had : Admissible σ (unit T) m g := by
    refine ⟨by simp [g, prefixTuple], ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      have := hpos i
      omega
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      have h := inc hij
      simp only [g, prefixTuple, List.getElem_map, List.getElem_range]
      cases σ with
      | weak => exact (Nat.succ_lt_succ h).le
      | strict => exact Nat.succ_lt_succ h
    · have less : (recipSum g : ℝ) < 1 / (T : ℝ) := by
        rw [hsum]
        exact sub_lt_self _ (one_div_pos.mpr (Nat.cast_pos.mpr (hpos m)))
      change recipSum g < 1 / (T : ℚ)
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa using less
  have compare (ds : List ℕ) (h : Admissible σ (unit T) m ds) :
      recipSum ds ≤ recipSum g ∧ (recipSum g ≤ recipSum ds → ds = g) := by
    obtain ⟨hl, hd, horder, hsmall⟩ := h
    let d := entry ds
    have repr : prefixTuple d m = ds := hl ▸ prefix_entry ds
    have hdpos (i : ℕ) (hi : i < m) : 0 < d i := by
      have hj : i < ds.length := by omega
      have := hd ds[i] (List.getElem_mem hj)
      simpa [d, entry_of_lt hj] using (show 0 < ds[i] by omega)
    have hmono (i : ℕ) (hi : i+1 < m) : d i ≤ d (i+1) := by
      have hi' : i < ds.length := by omega
      have hj' : i+1 < ds.length := by omega
      have hh := List.pairwise_iff_getElem.mp horder i (i+1) hi' hj' (by omega)
      rw [show d i = ds[i] from entry_of_lt hi', show d (i+1) = ds[i+1] from entry_of_lt hj']
      cases σ with
      | weak => exact hh
      | strict => exact Nat.le_of_lt hh
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

/-- The paper's unit-fraction extremality lemma, at every positive length. -/
theorem uniqueUnitTails : UniqueUnitTails := by
  intro σ T m hT _
  rw [greedyTuple_unit σ hT, digits_eq_prefix]
  exact unit_best_aux σ T m hT

end Egyptian
