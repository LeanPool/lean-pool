/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Order.Antisymmetrization

/-!
# Direct finite semiorder representation

The order used here is the one introduced by Scott and Suppes (1958):
`x ≼ y` says that every predecessor of `x` is a predecessor of `y`, and
every successor of `y` is a successor of `x`.  Its antisymmetrization is
the paper's quotient by substitutability.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

section WeakOrder

variable {A : Type u} (P : A → A → Prop)

/-- The Scott--Suppes weak order associated with a strict preference. -/
def ScottWeakOrder (x y : A) : Prop :=
  (∀ z, P z x → P z y) ∧ (∀ z, P y z → P x z)

/-- Substitute alternatives have identical strict-preference profiles. -/
def PreferenceSubstitute (x y : A) : Prop :=
  (∀ z, P z x ↔ P z y) ∧ (∀ z, P x z ↔ P y z)

theorem scottWeakOrder_refl (x : A) : ScottWeakOrder P x x :=
  ⟨fun _ h ↦ h, fun _ h ↦ h⟩

theorem scottWeakOrder_trans :
    IsTrans A (ScottWeakOrder P) := by
  constructor
  intro x y z hxy hyz
  exact ⟨fun w hwx ↦ hyz.1 w (hxy.1 w hwx),
    fun w hzw ↦ hxy.2 w (hyz.2 w hzw)⟩

theorem scottWeakOrder_total
    (hA : ∀ x y z w, P x y → P z w → P x w ∨ P z y)
    (hB : ∀ x y z w, P x y → P z x → P w y ∨ P z w) :
    ∀ x y, ScottWeakOrder P x y ∨ ScottWeakOrder P y x := by
  intro x y
  classical
  by_cases hxy : ScottWeakOrder P x y
  · exact Or.inl hxy
  by_cases hyx : ScottWeakOrder P y x
  · exact Or.inr hyx
  exfalso
  unfold ScottWeakOrder at hxy hyx
  rw [not_and_or] at hxy hyx
  rcases hxy with hxy | hxy
  · push Not at hxy
    rcases hxy with ⟨z, hzx, hzyny⟩
    rcases hyx with hyx | hyx
    · push Not at hyx
      rcases hyx with ⟨w, hwy, hwnx⟩
      rcases hA z x w y hzx hwy with hzy | hwx
      · exact hzyny hzy
      · exact hwnx hwx
    · push Not at hyx
      rcases hyx with ⟨w, hxw, hnyw⟩
      rcases hB x w z y hxw hzx with hyw | hzy
      · exact hnyw hyw
      · exact hzyny hzy
  · push Not at hxy
    rcases hxy with ⟨z, hyz, hnxz⟩
    rcases hyx with hyx | hyx
    · push Not at hyx
      rcases hyx with ⟨w, hwy, hwnx⟩
      rcases hB y z w x hyz hwy with hxz | hwx
      · exact hnxz hxz
      · exact hwnx hwx
    · push Not at hyx
      rcases hyx with ⟨w, hxw, hnyw⟩
      rcases hA y z x w hyz hxw with hyw | hxz
      · exact hnyw hyw
      · exact hnxz hxz

theorem preferenceSubstitute_iff :
    PreferenceSubstitute P x y ↔
      ScottWeakOrder P x y ∧ ScottWeakOrder P y x := by
  constructor
  · rintro ⟨hin, hout⟩
    exact ⟨⟨fun z ↦ (hin z).mp, fun z ↦ (hout z).mpr⟩,
      ⟨fun z ↦ (hin z).mpr, fun z ↦ (hout z).mp⟩⟩
  · rintro ⟨hxy, hyx⟩
    exact ⟨fun z ↦ ⟨hxy.1 z, hyx.1 z⟩,
      fun z ↦ ⟨hyx.2 z, hxy.2 z⟩⟩

theorem preference_implies_scottWeakOrder
    (hirr : ∀ x, ¬P x x)
    (hA : ∀ x y z w, P x y → P z w → P x w ∨ P z y)
    {x y : A} (hxy : P x y) :
    ScottWeakOrder P x y := by
  have htrans : IsTrans A P := by
    constructor
    intro a b c hab hbc
    rcases hA a b b c hab hbc with hac | hbb
    · exact hac
    · exact (hirr b hbb).elim
  exact ⟨fun z hzx ↦ htrans.trans z x y hzx hxy, fun z hyz ↦ htrans.trans x y z hxy hyz⟩

theorem scottWeakOrder_preference_scottWeakOrder
    {x x₁ y₁ y : A} (hxx₁ : ScottWeakOrder P x x₁)
    (hx₁y₁ : P x₁ y₁) (hy₁y : ScottWeakOrder P y₁ y) : P x y :=
  hy₁y.1 x (hxx₁.2 y₁ hx₁y₁)

end WeakOrder

section FiniteStaircase

/-- A finite relation whose lower sections are nested along a linear order
has a unit-threshold representation.  This is the finite recursive core of
the Scott--Suppes construction. -/
theorem finite_staircase_representation
    (A : Type u) [Finite A] [LinearOrder A] (P : A → A → Prop)
    (hforward : ∀ {x y}, P x y → y < x)
    (hmono : ∀ {x x' y y'}, x ≤ x' → y' ≤ y → P x y → P x' y') :
    ∃ f : A → ℝ,
      (∀ x y, P x y ↔ f x ≥ f y + 1) ∧
      (∀ {x y}, x < y → f x < f y) := by
  let := Fintype.ofFinite A
  classical
  induction hcard : Fintype.card A using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hA : IsEmpty A
    · let := hA
      exact ⟨fun x ↦ isEmptyElim x, by simp, by simp⟩
    · let : Nonempty A := not_isEmpty_iff.mp hA
      let m : A := Finset.univ.max' Finset.univ_nonempty
      let B := {x : A // x ≠ m}
      by_cases hB : IsEmpty B
      · refine ⟨fun _ ↦ 0, ?_, ?_⟩
        · intro x y
          have hx : x = m := by
            by_contra hx
            exact hB.false ⟨x, hx⟩
          have hy : y = m := by
            by_contra hy
            exact hB.false ⟨y, hy⟩
          subst x
          subst y
          simp only [ge_iff_le]
          constructor
          · intro hmm
            exact (hforward hmm).false.elim
          · norm_num
        · intro x y hxy
          exact (hxy.ne (by
            have hx : x = m := by
              by_contra hx
              exact hB.false ⟨x, hx⟩
            have hy : y = m := by
              by_contra hy
              exact hB.false ⟨y, hy⟩
            simp [hx, hy])).elim
      · let : Nonempty B := not_isEmpty_iff.mp hB
        let PB : B → B → Prop := fun x y ↦ P x.1 y.1
        have hcardB : Fintype.card B < n := by
          have hc : Fintype.card B = Fintype.card A - 1 := by
            simp [B]
          have hpos : 0 < Fintype.card A := Fintype.card_pos
          rw [← hcard]
          omega
        obtain ⟨g, hg, gmono⟩ :=
          ih (Fintype.card B) hcardB B PB
            (fun h ↦ hforward h)
            (fun hxx' hyy' h ↦ hmono hxx' hyy' h)
            (by simp only [Fintype.card_eq_nat_card])
        let nonpref : Finset B := Finset.univ.filter fun x ↦ ¬P m x.1
        let score : B → ℝ := fun x ↦ if P m x.1 then g x + 1 else g x
        obtain ⟨b, -, hb⟩ :=
          Finset.exists_max_image (Finset.univ : Finset B) score Finset.univ_nonempty
        let top : ℝ :=
          if hn : nonpref.Nonempty then
            let j := nonpref.min' hn
            (score b + (g j + 1)) / 2
          else score b + 1
        have hscore_lt {j : B} (hj : ¬P m j.1) :
            score b < g j + 1 := by
          apply lt_of_le_of_lt (hb b (Finset.mem_univ b))
          dsimp [score]
          split_ifs with hpb
          · have hbj : b < j := by
              apply lt_of_not_ge
              intro hjb
              exact hj (hmono le_rfl hjb hpb)
            linarith [gmono hbj]
          · have hnot : ¬PB b j := by
              intro hbj
              have hbm : b.1 ≤ m :=
                Finset.le_max' Finset.univ b.1 (Finset.mem_univ b.1)
              exact hj (hmono hbm le_rfl hbj)
            have hlt := not_le.mp (mt (hg b j).mpr hnot)
            linarith
        have htop_score : score b < top := by
          dsimp [top]
          split_ifs with hn
          · let j := nonpref.min' hn
            have hj : ¬P m j.1 := by
              have hjmem := nonpref.min'_mem hn
              simpa [nonpref, j] using hjmem
            have hs := hscore_lt hj
            dsimp [j] at hs ⊢
            linarith
          · linarith
        have htop_nonpref {j : B} (hj : ¬P m j.1) :
            top < g j + 1 := by
          dsimp [top]
          split_ifs with hn
          · let k := nonpref.min' hn
            have hk_mem : k ∈ nonpref := nonpref.min'_mem hn
            have hkj : k ≤ j := nonpref.min'_le _ (by simp [nonpref, hj])
            have hgkj : g k ≤ g j := by
              rcases hkj.eq_or_lt with rfl | hlt
              · exact le_rfl
              · exact (gmono hlt).le
            have hk : ¬P m k.1 := by simpa [nonpref] using hk_mem
            have hs := hscore_lt hk
            dsimp [k] at hs hgkj ⊢
            linarith
          · exact (hn ⟨j, by simp [nonpref, hj]⟩).elim
        let f : A → ℝ := fun x ↦ if hx : x = m then top else g ⟨x, hx⟩
        refine ⟨f, ?_, ?_⟩
        · intro x y
          by_cases hx : x = m
          · subst x
            by_cases hy : y = m
            · subst y
              rw [show f m = top by simp [f]]
              exact ⟨fun hmm ↦ (hforward hmm).false.elim, by simp⟩
            · simp only [f, dite_eq_left rfl, dite_eq_right hy, ge_iff_le]
              constructor
              · intro hmy
                have hsc : g ⟨y, hy⟩ + 1 = score ⟨y, hy⟩ := by
                  simp [score, hmy]
                rw [hsc]
                exact (hb _ (Finset.mem_univ _)).trans htop_score.le
              · intro hle
                by_contra hmy
                have hlt := htop_nonpref (j := ⟨y, hy⟩) hmy
                linarith
          · by_cases hy : y = m
            · subst y
              simp only [f, dite_eq_right hx, dite_eq_left rfl]
              exact ⟨fun h ↦ ((not_lt_of_ge (Finset.le_max' Finset.univ x
                (Finset.mem_univ x))) (hforward h)).elim, by
                intro hbad
                have hgs : g ⟨x, hx⟩ ≤ score ⟨x, hx⟩ := by
                  dsimp [score]
                  split_ifs <;> linarith
                have hlt :=
                  (hgs.trans (hb _ (Finset.mem_univ _))).trans_lt htop_score
                linarith⟩
            · simpa [f, hx, hy, PB] using hg ⟨x, hx⟩ ⟨y, hy⟩
        · intro x y hxy
          by_cases hy : y = m
          · subst y
            have hx : x ≠ m := hxy.ne
            simp only [f, dite_eq_right hx, dite_eq_left rfl]
            have hgs : g ⟨x, hx⟩ ≤ score ⟨x, hx⟩ := by
              dsimp [score]
              split_ifs <;> linarith
            exact (hgs.trans (hb _ (Finset.mem_univ _))).trans_lt htop_score
          · have hx : x ≠ m := by
              intro hx
              subst x
              exact (not_lt_of_ge (Finset.le_max' Finset.univ y
                (Finset.mem_univ y))) hxy
            simpa [f, hx, hy] using gmono (show (⟨x, hx⟩ : B) < ⟨y, hy⟩ from hxy)

end FiniteStaircase

end Scott1964.MeasurementStructures
