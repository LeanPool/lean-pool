/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith


-- [TABLET NODE: P3832T1ChamberOverlap]

/-!
# P3832T1ChamberOverlap

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ChamberOverlap

private def sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set (Fin 3 → ℝ) := fun i j k =>
  {s | s j ≤ s i ∧ s k ≤ s j}
private abbrev SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
private def sectorI : SectorOrder → Fin 3 := fun o => o.1.1
private def sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
private def sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
private def sectorCh (o : SectorOrder) := sectorChamber (sectorI o) (sectorJ o) (sectorK o)

private theorem sectorIndexCover (o : SectorOrder) (n : Fin 3) :
    n = sectorI o ∨ n = sectorJ o ∨ n = sectorK o := by
  classical
  let t : Finset (Fin 3) := {sectorI o, sectorJ o, sectorK o}
  have hcard : t.card = Fintype.card (Fin 3) := by
    simp [t, sectorI, sectorJ, sectorK, o.2.1, o.2.2.1, o.2.2.2]
  have huniv := Finset.eq_univ_of_card t hcard
  have hn : n ∈ t := by rw [huniv]; simp
  simpa [t] using hn

private theorem sectorOrdersTie (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o') :
    o = o' ∨ s (sectorI o) = s (sectorJ o) ∨ s (sectorJ o) = s (sectorK o) := by
  classical
  by_cases heq : o = o'
  · exact Or.inl heq
  · by_cases ht : s (sectorI o) = s (sectorJ o)
    · exact Or.inr (Or.inl ht)
    · by_cases hb : s (sectorJ o) = s (sectorK o)
      · exact Or.inr (Or.inr hb)
      · have hji : s (sectorJ o) < s (sectorI o) :=
          lt_of_le_of_ne ho.1 (Ne.symm ht)
        have hkj : s (sectorK o) < s (sectorJ o) :=
          lt_of_le_of_ne ho.2 (Ne.symm hb)
        have hmax : s (sectorI o) = s (sectorI o') := by
          apply le_antisymm
          · rcases sectorIndexCover o' (sectorI o) with h | h | h
            · rw [h]
            · rw [h]; exact ho'.1
            · rw [h]; exact ho'.2.trans ho'.1
          · rcases sectorIndexCover o (sectorI o') with h | h | h
            · rw [h]
            · rw [h]; exact ho.1
            · rw [h]; exact ho.2.trans ho.1
        have hii' : sectorI o' = sectorI o := by
          rcases sectorIndexCover o (sectorI o') with h | h | h
          · exact h
          · have hx : s (sectorI o) = s (sectorJ o) := by
              rw [h] at hmax
              exact hmax
            exact False.elim ((ne_of_gt hji) hx)
          · have hx : s (sectorI o) = s (sectorK o) := by
              rw [h] at hmax
              exact hmax
            exact False.elim ((ne_of_gt (hkj.trans hji)) hx)
        have hj'ne : sectorJ o' ≠ sectorI o := by
          rw [← hii']; exact o'.2.1.symm
        have hj' : sectorJ o' = sectorJ o := by
          rcases sectorIndexCover o (sectorJ o') with h | h | h
          · exact False.elim (hj'ne h)
          · exact h
          · have hk'j : sectorK o' = sectorJ o := by
              rcases sectorIndexCover o (sectorK o') with hI | hJ | hK
              · have : sectorI o' = sectorK o' := hii'.trans hI.symm
                exact False.elim (o'.2.2.1 this)
              · exact hJ
              · have : sectorJ o' = sectorK o' := h.trans hK.symm
                exact False.elim (o'.2.2.2 this)
            have hbad : s (sectorJ o) ≤ s (sectorK o) := by
              simpa [h, hk'j] using ho'.2
            exact False.elim ((not_le_of_gt hkj) hbad)
        have hk'neI : sectorK o' ≠ sectorI o := by
          rw [← hii']; exact o'.2.2.1.symm
        have hk'neJ : sectorK o' ≠ sectorJ o := by
          rw [← hj']; exact o'.2.2.2.symm
        have hk' : sectorK o' = sectorK o := by
          rcases sectorIndexCover o (sectorK o') with h | h | h
          · exact False.elim (hk'neI h)
          · exact False.elim (hk'neJ h)
          · exact h
        left
        apply Subtype.ext
        change (sectorI o, (sectorJ o, sectorK o)) =
          (sectorI o', (sectorJ o', sectorK o'))
        exact Prod.ext hii'.symm (Prod.ext hj'.symm hk'.symm)

private theorem sectorOrderedBetaTop (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorI o) = s (sectorJ o)) :
    2 * (s (sectorJ o)-s (sectorK o))=
      2 * (s (sectorJ o')-s (sectorK o')) := by
  classical
  fin_cases o <;> fin_cases o'
  all_goals simp only [sectorCh,sectorChamber,sectorI,sectorJ,sectorK,
    Set.mem_ofPred_eq] at ho ho' ht
  all_goals dsimp only [sectorI, sectorJ, sectorK] at ho ho' ht ⊢
  all_goals linarith

private theorem sectorOrderedRBottom (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorJ o) = s (sectorK o)) :
    2 * (s (sectorJ o)-s (sectorK o)) + 3 * s (sectorK o)=
      2 * (s (sectorJ o')-s (sectorK o')) + 3 * s (sectorK o') := by
  classical
  let i := sectorI o
  let j := sectorJ o
  let k := sectorK o
  let i' := sectorI o'
  let j' := sectorJ o'
  let k' := sectorK o'
  have hij : s j ≤ s i := ho.1
  have hik : s k ≤ s j := ho.2
  have hi'j' : s j' ≤ s i' := ho'.1
  have hi'k' : s k' ≤ s j' := ho'.2
  have hmax : s i = s i' := by
    apply le_antisymm
    · rcases sectorIndexCover o' i with h | h | h
      · simp [i', h]
      · simpa [j', h] using hi'j'
      · simpa [k', j', h] using hi'k'.trans hi'j'
    · rcases sectorIndexCover o i' with h | h | h
      · simp [i, h]
      · simpa [j, h] using hij
      · simpa [k, j, h] using hik.trans hij
  have hminj : s j' = s k := by
    by_cases heq : s i = s k
    · have hiall : ∀ n, s n = s k := by
        intro n
        rcases sectorIndexCover o n with h | h | h
        · rw [h]; exact heq
        · rw [h]; exact ht
        · rw [h]
      exact hiall j'
    · have hlt : s k < s i := lt_of_le_of_ne (hik.trans hij) (Ne.symm heq)
      have hii' : i' = i := by
        rcases sectorIndexCover o i' with h | h | h
        · exact h
        · exfalso
          have heqik : s i = s k := by
            simpa only [i', h, ht] using hmax
          exact (ne_of_gt hlt) heqik
        · exfalso
          have heqik : s i = s k := by
            simpa only [i', h, ht] using hmax
          exact (ne_of_gt hlt) heqik
      have hj'ne : j' ≠ i := by rw [← hii']; exact o'.2.1.symm
      rcases sectorIndexCover o j' with h | h | h
      · exact False.elim (hj'ne h)
      · rw [h]; exact ht
      · rw [h]
  have hmink : s k' = s k := by
    by_cases heq : s i = s k
    · have hiall : ∀ n, s n = s k := by
        intro n
        rcases sectorIndexCover o n with h | h | h
        · rw [h]; exact heq
        · rw [h]; exact ht
        · rw [h]
      exact hiall k'
    · have hlt : s k < s i := lt_of_le_of_ne (hik.trans hij) (Ne.symm heq)
      have hii' : i' = i := by
        rcases sectorIndexCover o i' with h | h | h
        · exact h
        · exfalso
          have hx : s i = s k := by simpa only [i', h, ht] using hmax
          exact (ne_of_gt hlt) hx
        · exfalso
          have hx : s i = s k := by simpa only [i', h, ht] using hmax
          exact (ne_of_gt hlt) hx
      have hk'ne : k' ≠ i := by rw [← hii']; exact o'.2.2.1.symm
      rcases sectorIndexCover o k' with h | h | h
      · exact False.elim (hk'ne h)
      · rw [h]; exact ht
      · rw [h]
  rw [hminj, hmink, ht]

private theorem sectorBottomSameTop (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorJ o) = s (sectorK o)) :
    sectorI o = sectorI o' ∨
      (s (sectorI o) = s (sectorJ o) ∧ s (sectorJ o) = s (sectorK o)) := by
  classical
  have hmax : s (sectorI o) = s (sectorI o') := by
    apply le_antisymm
    · rcases sectorIndexCover o' (sectorI o) with h | h | h
      · rw [h]
      · rw [h]; exact ho'.1
      · rw [h]; exact ho'.2.trans ho'.1
    · rcases sectorIndexCover o (sectorI o') with h | h | h
      · rw [h]
      · rw [h]; exact ho.1
      · rw [h]; exact ho.2.trans ho.1
  by_cases heq : s (sectorI o) = s (sectorK o)
  · right
    constructor
    · exact heq.trans ht.symm
    · exact ht
  · left
    have hlt : s (sectorK o)<s (sectorI o) :=
      lt_of_le_of_ne (ho.2.trans ho.1) (Ne.symm heq)
    rcases sectorIndexCover o (sectorI o') with h | h | h
    · exact h.symm
    · have hx : s (sectorI o) = s (sectorJ o) := by
        rw [h] at hmax
        exact hmax
      exact False.elim ((ne_of_gt hlt) (hx.trans ht))
    · have hx : s (sectorI o) = s (sectorK o) := by
        rw [h] at hmax
        exact hmax
      exact False.elim ((ne_of_gt hlt) hx)

private theorem sectorTopTieOther (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorI o) = s (sectorJ o)) :
    s (sectorI o') = s (sectorJ o') := by
  classical
  by_cases heq : s (sectorI o) = s (sectorK o)
  · have hv (n : Fin 3) : s n = s (sectorI o) := by
      rcases sectorIndexCover o n with hI | hJ | hK
      · rw [hI]
      · rw [hJ, ht.symm]
      · rw [hK, heq]
    exact (hv (sectorI o')).trans (hv (sectorJ o')).symm
  · have hki : s (sectorK o)<s (sectorI o) := by
      apply lt_of_le_of_ne
      · exact ho.2.trans (le_of_eq ht.symm)
      · exact Ne.symm heq
    have hmax : s (sectorI o) = s (sectorI o') := by
      apply le_antisymm
      · rcases sectorIndexCover o' (sectorI o) with h | h | h
        · rw [h]
        · rw [h]; exact ho'.1
        · rw [h]; exact ho'.2.trans ho'.1
      · rcases sectorIndexCover o (sectorI o') with h | h | h
        · rw [h]
        · rw [h]; exact ho.1
        · rw [h]; exact ho.2.trans ho.1
    have hi'top : sectorI o'=sectorI o ∨ sectorI o'=sectorJ o := by
      rcases sectorIndexCover o (sectorI o') with hI | hJ | hK
      · exact Or.inl hI
      · exact Or.inr hJ
      · have hx : s (sectorI o) = s (sectorK o) := by
          rw [hK] at hmax
          exact hmax
        exact False.elim ((ne_of_gt hki) hx)
    rcases sectorIndexCover o (sectorJ o') with hI | hJ | hK
    · rw [hI, ← hmax]
    · rw [hJ, ← hmax, ht]
    · rcases hi'top with hi | hi
      · have hk'j : sectorK o'=sectorJ o := by
          rcases sectorIndexCover o (sectorK o') with hI | hJ | hK'
          · have : sectorI o'=sectorK o' := hi.trans hI.symm
            exact False.elim (o'.2.2.1 this)
          · exact hJ
          · have : sectorJ o'=sectorK o' := hK.trans hK'.symm
            exact False.elim (o'.2.2.2 this)
        have hbad : s (sectorJ o)≤s (sectorK o) := by
          simpa [hK, hk'j] using ho'.2
        rw [← ht] at hbad
        exact False.elim ((not_le_of_gt hki) hbad)
      · have hk'i : sectorK o'=sectorI o := by
          rcases sectorIndexCover o (sectorK o') with hI | hJ | hK'
          · exact hI
          · have : sectorI o'=sectorK o' := hi.trans hJ.symm
            exact False.elim (o'.2.2.1 this)
          · have : sectorJ o'=sectorK o' := hK.trans hK'.symm
            exact False.elim (o'.2.2.2 this)
        have hbad : s (sectorI o)≤s (sectorK o) := by
          simpa [hK, hk'i] using ho'.2
        exact False.elim ((not_le_of_gt hki) hbad)

private theorem sectorBottomTieOther (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorJ o) = s (sectorK o)) :
    s (sectorJ o') = s (sectorK o') := by
  classical
  rcases sectorBottomSameTop s o o' ho ho' ht with htop | hall
  · have hj'ne : sectorJ o' ≠ sectorI o := by
      rw [htop]; exact o'.2.1.symm
    have hk'ne : sectorK o' ≠ sectorI o := by
      rw [htop]; exact o'.2.2.1.symm
    have hv (n : Fin 3) (hn : n ≠ sectorI o) : s n = s (sectorJ o) := by
      rcases sectorIndexCover o n with hI | hJ | hK
      · exact False.elim (hn hI)
      · rw [hJ]
      · rw [hK, ht]
    exact (hv _ hj'ne).trans (hv _ hk'ne).symm
  · have hv (n : Fin 3) : s n = s (sectorK o) := by
      rcases sectorIndexCover o n with hI | hJ | hK
      · rw [hI, hall.1, hall.2]
      · rw [hJ, hall.2]
      · rw [hK]
    exact (hv (sectorJ o')).trans (hv (sectorK o')).symm

private theorem sectorTopPairClassify (s : (Fin 3 → ℝ)) (o o' : SectorOrder)
    (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
    (ht : s (sectorI o) = s (sectorJ o))
    (ht' : s (sectorI o') = s (sectorJ o')) :
    (sectorI o = sectorI o' ∧ sectorJ o = sectorJ o' ∧ sectorK o = sectorK o') ∨
    (sectorI o = sectorJ o' ∧ sectorJ o = sectorI o' ∧ sectorK o = sectorK o') ∨
    (s (sectorI o) = s (sectorJ o) ∧ s (sectorJ o) = s (sectorK o)) := by
  classical
  by_cases hall : s (sectorI o) = s (sectorK o)
  · right; right
    exact ⟨ht, ht.symm.trans hall⟩
  · have hki : s (sectorK o)<s (sectorI o) := by
      apply lt_of_le_of_ne
      · exact ho.2.trans (le_of_eq ht.symm)
      · exact Ne.symm hall
    have hmax : s (sectorI o) = s (sectorI o') := by
      apply le_antisymm
      · rcases sectorIndexCover o' (sectorI o) with h | h | h
        · rw [h]
        · rw [h]; exact ho'.1
        · rw [h]; exact ho'.2.trans ho'.1
      · rcases sectorIndexCover o (sectorI o') with h | h | h
        · rw [h]
        · rw [h]; exact ho.1
        · rw [h]; exact ho.2.trans ho.1
    have hi' : sectorI o'=sectorI o ∨ sectorI o'=sectorJ o := by
      rcases sectorIndexCover o (sectorI o') with hI | hJ | hK
      · exact Or.inl hI
      · exact Or.inr hJ
      · have hx : s (sectorI o) = s (sectorK o) := by
          rw [hK] at hmax
          exact hmax
        exact False.elim ((ne_of_gt hki) hx)
    rcases hi' with hi | hi
    · have hj' : sectorJ o'=sectorJ o := by
        rcases sectorIndexCover o (sectorJ o') with hI | hJ | hK
        · have : sectorI o'=sectorJ o' := hi.trans hI.symm
          exact False.elim (o'.2.1 this)
        · exact hJ
        · have hx : s (sectorI o') = s (sectorJ o') := ht'
          rw [hi, hK] at hx
          exact False.elim ((ne_of_gt hki) hx)
      have hk' : sectorK o'=sectorK o := by
        rcases sectorIndexCover o (sectorK o') with hI | hJ | hK
        · have : sectorI o'=sectorK o' := hi.trans hI.symm
          exact False.elim (o'.2.2.1 this)
        · have : sectorJ o'=sectorK o' := hj'.trans hJ.symm
          exact False.elim (o'.2.2.2 this)
        · exact hK
      left
      exact ⟨hi.symm,hj'.symm,hk'.symm⟩
    · have hj' : sectorJ o'=sectorI o := by
        rcases sectorIndexCover o (sectorJ o') with hI | hJ | hK
        · exact hI
        · have : sectorI o'=sectorJ o' := hi.trans hJ.symm
          exact False.elim (o'.2.1 this)
        · have hx : s (sectorI o') = s (sectorJ o') := ht'
          rw [hi, hK] at hx
          exact False.elim ((ne_of_gt hki) (ht.trans hx))
      have hk' : sectorK o'=sectorK o := by
        rcases sectorIndexCover o (sectorK o') with hI | hJ | hK
        · have : sectorJ o'=sectorK o' := hj'.trans hI.symm
          exact False.elim (o'.2.2.2 this)
        · have : sectorI o'=sectorK o' := hi.trans hJ.symm
          exact False.elim (o'.2.2.1 this)
        · exact hK
      right; left
      exact ⟨hj'.symm,hi.symm,hk'.symm⟩


end ChamberOverlap

open ChamberOverlap in
theorem P3832T1ChamberOverlap (x : Fin 3 → ℝ)
    (o o' : {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2})
    (ho : x o.1.2.1 ≤ x o.1.1 ∧ x o.1.2.2 ≤ x o.1.2.1)
    (ho' : x o'.1.2.1 ≤ x o'.1.1 ∧ x o'.1.2.2 ≤ x o'.1.2.1) :
    (o = o' ∨ x (o.1.1) = x (o.1.2.1) ∨ x (o.1.2.1) = x (o.1.2.2)) ∧
      (x (o.1.1) = x (o.1.2.1) →
        x (o'.1.1) = x (o'.1.2.1) ∧
        2 * (x (o.1.2.1) - x (o.1.2.2)) =
          2 * (x (o'.1.2.1) - x (o'.1.2.2)) ∧
        ((o.1.1 = o'.1.1 ∧ o.1.2.1 = o'.1.2.1 ∧ o.1.2.2 = o'.1.2.2) ∨
          (o.1.1 = o'.1.2.1 ∧ o.1.2.1 = o'.1.1 ∧ o.1.2.2 = o'.1.2.2) ∨
          (x (o.1.1) = x (o.1.2.1) ∧ x (o.1.2.1) = x (o.1.2.2)))) ∧
      (x (o.1.2.1) = x (o.1.2.2) →
        x (o'.1.2.1) = x (o'.1.2.2) ∧
        2 * (x (o.1.2.1) - x (o.1.2.2)) + 3 * x (o.1.2.2) =
          2 * (x (o'.1.2.1) - x (o'.1.2.2)) + 3 * x (o'.1.2.2) ∧
        (o.1.1 = o'.1.1 ∨
          (x (o.1.1) = x (o.1.2.1) ∧ x (o.1.2.1) = x (o.1.2.2)))) := by
-- BODY
  classical
  refine ⟨sectorOrdersTie x o o' ho ho', ?_, ?_⟩
  · intro ht
    have ht' := sectorTopTieOther x o o' ho ho' ht
    exact ⟨ht', sectorOrderedBetaTop x o o' ho ho' ht,
      sectorTopPairClassify x o o' ho ho' ht ht'⟩
  · intro ht
    exact ⟨sectorBottomTieOther x o o' ho ho' ht,
      sectorOrderedRBottom x o o' ho ho' ht,
      sectorBottomSameTop x o o' ho ho' ht⟩

end ApollonianSuperharmonic

end
