/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

/-!
# Counting disjoint finite families

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Disjoint sets contribute one chosen element each and another for a distinguished subfamily. -/
theorem Finset.card_biUnion_ge_card_add {V A : Type*} [DecidableEq A]
    (Z ends0 : Finset V) (parts : V → Finset A) (hendsSubZ : ends0 ⊆ Z)
    (hdisj : (↑Z : Set V).PairwiseDisjoint parts)
    (firstColor : (v : V) → v ∈ Z → A)
    (firstMem : ∀ v hv, firstColor v hv ∈ parts v)
    (extraColor : (v : V) → v ∈ ends0 → A)
    (extraMem : ∀ v hv, extraColor v hv ∈ (parts v).erase (firstColor v (hendsSubZ hv))) :
    Z.card + ends0.card ≤ (Z.biUnion parts).card := by
  classical
  let M := Z.biUnion parts
  let domain := Sum {v : V // v ∈ Z} {v : V // v ∈ ends0}
  let color : domain → A := fun q => match q with
    | Sum.inl v => firstColor v.1 v.2
    | Sum.inr v => extraColor v.1 v.2
  have hmap : ∀ q : domain, color q ∈ M := by
    intro q
    rcases q with q | q
    · apply Finset.mem_biUnion.mpr
      exact ⟨q.1, q.2, firstMem q.1 q.2⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨q.1, hendsSubZ q.2,
        Finset.mem_erase.mp (extraMem q.1 q.2) |>.2⟩
  have hinj : Function.Injective color := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj a.2 b.2 hn
        have hc : firstColor a.1 a.2 = firstColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd) (firstMem a.1 a.2)
          (by simpa only [hc] using firstMem b.1 b.2)
      cases Subtype.ext huv
      rfl
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj a.2 (hendsSubZ b.2) hn
        have hc : firstColor a.1 a.2 = extraColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd) (firstMem a.1 a.2)
          (by simpa only [hc] using Finset.mem_erase.mp (extraMem b.1 b.2) |>.2)
      have he := Finset.mem_erase.mp (extraMem b.1 b.2)
      exact False.elim (he.1 (by simpa [color, huv] using hab.symm))
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj (hendsSubZ a.2) b.2 hn
        have hc : extraColor a.1 a.2 = firstColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd)
          (Finset.mem_erase.mp (extraMem a.1 a.2) |>.2)
          (by simpa only [hc] using firstMem b.1 b.2)
      have he := Finset.mem_erase.mp (extraMem a.1 a.2)
      exact False.elim (he.1 (by simpa [color, huv] using hab))
    · have huv : a.1 = b.1 := by
        by_contra hn
        have hd := hdisj (hendsSubZ a.2) (hendsSubZ b.2) hn
        have hc : extraColor a.1 a.2 = extraColor b.1 b.2 := by
          simpa [color] using hab
        exact (Finset.disjoint_left.mp hd)
          (Finset.mem_erase.mp (extraMem a.1 a.2) |>.2)
          (by simpa only [hc] using Finset.mem_erase.mp (extraMem b.1 b.2) |>.2)
      cases Subtype.ext huv
      rfl
  let A : Finset domain :=
    Z.attach.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      ends0.attach.map ⟨Sum.inr, Sum.inr_injective⟩
  have hAdisj : Disjoint
      (Z.attach.map ⟨Sum.inl, Sum.inl_injective⟩)
      (ends0.attach.map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [Finset.mem_map] at hq1 hq2
    rcases hq1 with ⟨a, ha, rfl⟩
    rcases hq2 with ⟨b, hb, h⟩
    cases h
  have hAcard : A.card = Z.card + ends0.card := by
    dsimp [A]
    rw [Finset.card_union_of_disjoint hAdisj]
    simp
  have hle : A.card ≤ M.card := by
    apply Finset.card_le_card_of_injOn color
    · intro q hq
      exact hmap q
    · exact hinj.injOn
  exact hAcard ▸ hle

end GoldbergSeymour

end
