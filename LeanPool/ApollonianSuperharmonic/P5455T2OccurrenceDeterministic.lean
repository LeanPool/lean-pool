/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5455T2RootAlignment
public import LeanPool.ApollonianSuperharmonic.P5455T2AlignedPredecessor
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientation

-- [TABLET NODE: P5455T2OccurrenceDeterministic]

/-!
# P5455T2OccurrenceDeterministic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OccurrenceDeterministicProof

private theorem Normalize :
    ∀ {q : Fin 4 → CircleCoordinates}, ∀ {i : Fin 3}, ∀ {o : Bool}, UnitOccurrenceOrientation q i
        o →
      ∃ (t : Fin 4 → CircleCoordinates) (r j : Fin 3),
        q = P4828T1Rotate t r ∧ i = j - r ∧
          ((∃ z, t = P4828T1Root z false ∧
              ((j = 0 ∧ o = true) ∨ (j = 2 ∧ o = false))) ∨
           (∃ z, t = P4828T1Root z true ∧
              ((j = 0 ∧ o = true) ∨ (j = 1 ∧ o = false))) ∨
           (∃ p e, ProperBandQuadruple p ∧ t = P4828T1Step p ∧
              ((j = 1 ∧ UnitOccurrenceOrientation p 1 e ∧
                  (((p 3).1 ≠ 1 ∧ o = e) ∨
                   ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 2) (p 3) ∧ o = false) ∨
                   ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 3) (p 2) ∧ o = true))) ∨
               (j = 2 ∧ UnitOccurrenceOrientation p 2 e ∧
                  (((p 2).1 ≠ 1 ∧ o = e) ∨
                   ((p 2).1 = 1 ∧ PrimitiveVectorOrientation (p 2) (p 3) ∧ o = true) ∨
                   ((p 2).1 = 1 ∧ PrimitiveVectorOrientation (p 3) (p 2) ∧ o = false)))))) := by
  classical
  intro q i o h
  induction h with
  | leftLower z =>
      let t := P4828T1Root z false
      refine ⟨t, 0, 0, ?_, rfl, Or.inl ⟨z, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      rw [P4828T1RotationLaws.1]
      rfl
  | leftUpper z =>
      let t := P4828T1Root z false
      refine ⟨t, 0, 2, ?_, rfl, Or.inl ⟨z, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
      rw [P4828T1RotationLaws.1]
      rfl
  | rightUpper z =>
      let t := P4828T1Root z true
      refine ⟨t, 0, 0, ?_, rfl, Or.inr (Or.inl ⟨z, rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩
      rw [P4828T1RotationLaws.1]
      rfl
  | rightLower z =>
      let t := P4828T1Root z true
      refine ⟨t, 0, 1, ?_, rfl, Or.inr (Or.inl ⟨z, rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩
      rw [P4828T1RotationLaws.1]
      rfl
  | @rotate q i o h ih =>
      obtain ⟨t, r, j, hq, hi, hc⟩ := ih
      refine ⟨t, 1 + r, j, ?_, ?_, hc⟩
      · have hrot : ![q 0, q 2, q 3, q 1] = P4828T1Rotate q 1 := by
          funext k
          fin_cases k <;> rfl
        rw [hrot, hq, P4828T1RotationLaws.2.1]
      · rw [hi]
        fin_cases j <;> fin_cases r <;> rfl
  | @retainSecondToThird p o hp hu horient h ih =>
      refine ⟨P4828T1Step p, 0, 1, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inl ⟨rfl, h,
          Or.inr (Or.inl ⟨hu, horient, rfl⟩)⟩⟩)⟩
      · funext k; fin_cases k <;> rfl
  | @retainSecondFromThird p o hp hu horient h ih =>
      refine ⟨P4828T1Step p, 0, 1, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inl ⟨rfl, h,
          Or.inr (Or.inr ⟨hu, horient, rfl⟩)⟩⟩)⟩
      · funext k; fin_cases k <;> rfl
  | @retainSecondOther p o hp hu h ih =>
      refine ⟨P4828T1Step p, 0, 1, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inl ⟨rfl, h,
          Or.inl ⟨hu, rfl⟩⟩⟩)⟩
      · funext k; fin_cases k <;> rfl
  | @retainThirdFromSecond p o hp hu horient h ih =>
      refine ⟨P4828T1Step p, 0, 2, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inr ⟨rfl, h,
          Or.inr (Or.inl ⟨hu, horient, rfl⟩)⟩⟩)⟩
      · funext k; fin_cases k <;> rfl
  | @retainThirdToSecond p o hp hu horient h ih =>
      refine ⟨P4828T1Step p, 0, 2, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inr ⟨rfl, h,
          Or.inr (Or.inr ⟨hu, horient, rfl⟩)⟩⟩)⟩
      · funext k; fin_cases k <;> rfl
  | @retainThirdOther p o hp hu h ih =>
      refine ⟨P4828T1Step p, 0, 2, ?_, rfl, Or.inr (Or.inr ⟨p, o, hp, rfl, Or.inr ⟨rfl, h,
          Or.inl ⟨hu, rfl⟩⟩⟩)⟩
      · funext k; fin_cases k <;> rfl

private theorem noMix :
    ∀ z s r p,
      ProperBandQuadruple p →
        ∀ r', P4828T1Rotate (P4828T1Root z s) r = P4828T1Rotate (P4828T1Step p) r' → False := by
  classical
  intro z s r p hp r' heq
  have hc := congrArg (fun x : Fin 4 → CircleCoordinates => (x 0).1) heq
  simp only [P4828T1Rotate, Fin.cases_zero] at hc
  have hg := P5455T2CurvatureGrowth p hp
  cases s <;> simp [P4828T1Root] at hc <;> omega

private theorem rotUnique :
    ∀ t, ProperBandQuadruple t → ∀ r r',
      P4828T1Rotate t r = P4828T1Rotate t r' → r = r' := by
  classical
  intro t ht r r' heq
  obtain ⟨d, hd, huniq⟩ := BandPredecessorNoCollision t t ht ht rfl
  have hzero : ∀ j : Fin 3, t j.succ = t ((j + 0).succ) := by
    intro j
    simp
  have hdzero := huniq 0 hzero
  have hcyc : ∀ j : Fin 3, t j.succ = t ((j + (r' - r)).succ) := by
    intro j
    have hh := congrFun heq ((j - r).succ)
    have hidx₁ : (j - r) + r = j := sub_add_cancel j r
    have hidx₂ : (j - r) + r' = j + (r' - r) := by
      abel
    simpa only [P4828T1Rotate, Fin.cases_succ, hidx₁, hidx₂] using hh
  have hdd := huniq (r' - r) hcyc
  have hdiff : r' - r = 0 := hdd.trans hdzero.symm
  exact (sub_eq_zero.mp hdiff).symm

private theorem main :
    (∀ {q : Fin 4 → CircleCoordinates}, ∀
        {i : Fin 3}, ∀ {o : Bool}, UnitOccurrenceOrientation q i o → ∃ (t : Fin 4 →
        CircleCoordinates) (r j : Fin 3), q = P4828T1Rotate t r ∧ i = j - r ∧ ((∃ z, t =
        P4828T1Root z false ∧ ((j = 0 ∧ o = true) ∨ (j = 2 ∧ o = false))) ∨ (∃ z, t =
        P4828T1Root z true ∧ ((j = 0 ∧ o = true) ∨ (j = 1 ∧ o = false))) ∨ (∃ p e,
        ProperBandQuadruple p ∧ t = P4828T1Step p ∧ ((j = 1 ∧ UnitOccurrenceOrientation p 1 e ∧
        (((p 3).1 ≠ 1 ∧ o = e) ∨ ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 2) (p 3) ∧ o =
        false) ∨ ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 3) (p 2) ∧ o = true))) ∨ (j = 2 ∧
        UnitOccurrenceOrientation p 2 e ∧ (((p 2).1 ≠ 1 ∧ o = e) ∨ ((p 2).1 = 1 ∧
        PrimitiveVectorOrientation (p 2) (p 3) ∧ o = true) ∨ ((p 2).1 = 1 ∧
        PrimitiveVectorOrientation (p 3) (p 2) ∧ o = false))))))) → ((∀ z s r p,
            ProperBandQuadruple p → ∀ r', P4828T1Rotate (P4828T1Root z s) r = P4828T1Rotate
        (P4828T1Step p) r' → False) → ((∀ t, ProperBandQuadruple t → ∀ r r', P4828T1Rotate t
        r = P4828T1Rotate t r' → r = r') → (∀ n : Nat, ∀ q : Fin 4 → CircleCoordinates,
      ProperBandQuadruple q → ∀ i : Fin 3, (q i.succ).1 = 1 →
      ∀ a b : Bool, UnitOccurrenceOrientation q i a →
        UnitOccurrenceOrientation q i b → (q 0).1.toNat = n → a = b))) := by
  classical
  intro Normalize noMix rotUnique n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q hq i hi a b ha hb hn
    obtain ⟨t, r, j, hqa, hia, enda⟩ := Normalize ha
    obtain ⟨t', r', j', hqb, hib, endb⟩ := Normalize hb
    have hrot : P4828T1Rotate t r = P4828T1Rotate t' r' := hqa.symm.trans hqb
    rcases enda with rootA | rootA | retainA
    · rcases rootA with ⟨z, hta, rowA⟩
      rcases endb with rootB | rootB | retainB
      · rcases rootB with ⟨z', htb, rowB⟩
        have align := P5455T2RootAlignment z z' false false r r' (by simpa [hta, htb] using hrot)
        rcases align with ⟨hz, _, hr⟩
        subst z'
        have hjEq : j = j' := by
          calc
            j = (j - r) + r := by simp
            _ = (j' - r') + r' := by rw [← hia, ← hib, hr]
            _ = j' := sub_add_cancel j' r'
        rcases rowA with ⟨hj, ho⟩ | ⟨hj, ho⟩ <;>
          rcases rowB with ⟨hj', ho'⟩ | ⟨hj', ho'⟩ <;> simp_all
      · rcases rootB with ⟨z', htb, rowB⟩
        have align := P5455T2RootAlignment z z' false true r r' (by simpa [hta, htb] using hrot)
        rcases align with ⟨_, ⟨hs, _⟩⟩
        cases hs
      · rcases retainB with ⟨p', e', hp', htb, rowB⟩
        exact False.elim (noMix z false r p' hp' r' (by simpa [hta, htb] using hrot))
    · rcases rootA with ⟨z, hta, rowA⟩
      rcases endb with rootB | rootB | retainB
      · rcases rootB with ⟨z', htb, rowB⟩
        have align := P5455T2RootAlignment z z' true false r r' (by simpa [hta, htb] using hrot)
        rcases align with ⟨_, ⟨hs, _⟩⟩
        cases hs
      · rcases rootB with ⟨z', htb, rowB⟩
        have align := P5455T2RootAlignment z z' true true r r' (by simpa [hta, htb] using hrot)
        rcases align with ⟨hz, _, hr⟩
        subst z'
        have hjEq : j = j' := by
          calc
            j = (j - r) + r := by simp
            _ = (j' - r') + r' := by rw [← hia, ← hib, hr]
            _ = j' := sub_add_cancel j' r'
        rcases rowA with ⟨hj, ho⟩ | ⟨hj, ho⟩ <;>
          rcases rowB with ⟨hj', ho'⟩ | ⟨hj', ho'⟩ <;> simp_all
      · rcases retainB with ⟨p', e', hp', htb, rowB⟩
        exact False.elim (noMix z true r p' hp' r' (by simpa [hta, htb] using hrot))
    · rcases retainA with ⟨p, e, hp, hta, rowA⟩
      rcases endb with rootB | rootB | retainB
      · rcases rootB with ⟨z', htb, rowB⟩
        exact False.elim (noMix z' false r' p hp r (by simpa [hta, htb] using hrot.symm))
      · rcases rootB with ⟨z', htb, rowB⟩
        exact False.elim (noMix z' true r' p hp r (by simpa [hta, htb] using hrot.symm))
      · rcases retainB with ⟨p', e', hp', htb, rowB⟩
        have hchild : P4828T1Step p 0 = P4828T1Step p' 0 := by
          have hc := congrArg (fun x : Fin 4 → CircleCoordinates => x 0) hrot
          simpa [hta, htb, P4828T1Rotate] using hc
        have heqP := P5455T2AlignedPredecessor p p' hp hp' hchild
        subst p'
        have hstepProper := (P5455T2CurvatureGrowth p hp).2.1
        have hr : r = r' := rotUnique (P4828T1Step p) hstepProper r r' (by simpa [hta, htb]
            using hrot)
        have hjEq : j = j' := by
          calc
            j = (j - r) + r := by simp
            _ = (j' - r') + r := by rw [← hia, ← hib, hr]
            _ = (j' - r') + r' := by rw [hr]
            _ = j' := sub_add_cancel j' r'
        have hcurv : (q 0).1 = (P4828T1Step p 0).1 := by
          have hh := congrFun hqa 0
          simpa [hta, P4828T1Rotate] using congrArg Prod.fst hh
        have hlt : (p 0).1.toNat < n := by
          have hg := (P5455T2CurvatureGrowth p hp)
          rw [hcurv] at hn
          omega
        have hnpre : (p 0).1.toNat = (p 0).1.toNat := rfl
        rcases rowA with ⟨hj, hpre, stateA⟩ | ⟨hj, hpre, stateA⟩
        · rw [← hjEq] at rowB
          simp only [hj, Fin.isValue, ne_eq, true_and, Fin.reduceEq, false_and, or_false]
              at rowB
          rcases rowB with ⟨hpre', stateB⟩
          have hunit : (p 2).1 = 1 := by
            have hidx : i + r = 1 := by rw [hia, hj]; exact sub_add_cancel 1 r
            have hi' : (P4828T1Step p ((i + r).succ)).1 = 1 := by
              simpa [hqa, hta, P4828T1Rotate] using hi
            rw [hidx] at hi'
            simpa [P4828T1Step] using hi'
          have heOld := ih _ hlt p hp 1 hunit e e' hpre hpre' hnpre
          have htan : BandTangency (p 2) (p 3) :=
            ⟨p, hp.1, 2, 3, by decide, rfl, rfl⟩
          have exclusive : ¬ (PrimitiveVectorOrientation (p 2) (p 3) ∧
              PrimitiveVectorOrientation (p 3) (p 2)) := by
            intro hd
            have hx := (PrimitiveVectorOrientationUnique (p 2) (p 3)).2 htan
            rcases hx.2 with ⟨hf, hnrev⟩ | ⟨hr, hnfor⟩
            · exact hnrev hd.2
            · exact hnfor hd.1
          by_cases hsib : (p 3).1 = 1
          · rcases stateA with hN | hF | hR
            · exact (hN.1 hsib).elim
            · rcases stateB with hN' | hF' | hR'
              · exact (hN'.1 hsib).elim
              · exact hF.2.2.trans hF'.2.2.symm
              · exact False.elim (exclusive ⟨hF.2.1, hR'.2.1⟩)
            · rcases stateB with hN' | hF' | hR'
              · exact (hN'.1 hsib).elim
              · exact False.elim (exclusive ⟨hF'.2.1, hR.2.1⟩)
              · exact hR.2.2.trans hR'.2.2.symm
          · rcases stateA with hN | hF | hR
            · rcases stateB with hN' | hF' | hR'
              · exact hN.2.trans (heOld.trans hN'.2.symm)
              · exact (hsib hF'.1).elim
              · exact (hsib hR'.1).elim
            · exact (hsib hF.1).elim
            · exact (hsib hR.1).elim
        · rw [← hjEq] at rowB
          simp only [hj, Fin.isValue, Fin.reduceEq, ne_eq, false_and, true_and, false_or]
              at rowB
          rcases rowB with ⟨hpre', stateB⟩
          have hunit : (p 3).1 = 1 := by
            have hidx : i + r = 2 := by rw [hia, hj]; exact sub_add_cancel 2 r
            have hi' : (P4828T1Step p ((i + r).succ)).1 = 1 := by
              simpa [hqa, hta, P4828T1Rotate] using hi
            rw [hidx] at hi'
            simpa [P4828T1Step] using hi'
          have heOld := ih _ hlt p hp 2 hunit e e' hpre hpre' hnpre
          have htan : BandTangency (p 2) (p 3) :=
            ⟨p, hp.1, 2, 3, by decide, rfl, rfl⟩
          have exclusive : ¬ (PrimitiveVectorOrientation (p 2) (p 3) ∧
              PrimitiveVectorOrientation (p 3) (p 2)) := by
            intro hd
            have hx := (PrimitiveVectorOrientationUnique (p 2) (p 3)).2 htan
            rcases hx.2 with ⟨hf, hnrev⟩ | ⟨hr, hnfor⟩
            · exact hnrev hd.2
            · exact hnfor hd.1
          by_cases hsib : (p 2).1 = 1
          · rcases stateA with hN | hF | hR
            · exact (hN.1 hsib).elim
            · rcases stateB with hN' | hF' | hR'
              · exact (hN'.1 hsib).elim
              · exact hF.2.2.trans hF'.2.2.symm
              · exact False.elim (exclusive ⟨hF.2.1, hR'.2.1⟩)
            · rcases stateB with hN' | hF' | hR'
              · exact (hN'.1 hsib).elim
              · exact False.elim (exclusive ⟨hF'.2.1, hR.2.1⟩)
              · exact hR.2.2.trans hR'.2.2.symm
          · rcases stateA with hN | hF | hR
            · rcases stateB with hN' | hF' | hR'
              · exact hN.2.trans (heOld.trans hN'.2.symm)
              · exact (hsib hF'.1).elim
              · exact (hsib hR'.1).elim
            · exact (hsib hF.1).elim
            · exact (hsib hR.1).elim

end OccurrenceDeterministicProof

theorem P5455T2OccurrenceDeterministic
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (hi : (q i.succ).1 = 1)
    (a b : Bool) (ha : UnitOccurrenceOrientation q i a)
    (hb : UnitOccurrenceOrientation q i b) : a = b := by
-- BODY
  exact (by
  let Normalize : ∀ {q : Fin 4 → CircleCoordinates} {i : Fin 3} {o : Bool},
      UnitOccurrenceOrientation q i o →
      ∃ (t : Fin 4 → CircleCoordinates) (r j : Fin 3),
        q = P4828T1Rotate t r ∧ i = j - r ∧
          ((∃ z, t = P4828T1Root z false ∧
              ((j = 0 ∧ o = true) ∨ (j = 2 ∧ o = false))) ∨
           (∃ z, t = P4828T1Root z true ∧
              ((j = 0 ∧ o = true) ∨ (j = 1 ∧ o = false))) ∨
           (∃ p e, ProperBandQuadruple p ∧ t = P4828T1Step p ∧
              ((j = 1 ∧ UnitOccurrenceOrientation p 1 e ∧
                  (((p 3).1 ≠ 1 ∧ o = e) ∨
                   ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 2) (p 3) ∧ o = false) ∨
                   ((p 3).1 = 1 ∧ PrimitiveVectorOrientation (p 3) (p 2) ∧ o = true))) ∨
               (j = 2 ∧ UnitOccurrenceOrientation p 2 e ∧
                  (((p 2).1 ≠ 1 ∧ o = e) ∨
                   ((p 2).1 = 1 ∧ PrimitiveVectorOrientation (p 2) (p 3) ∧ o = true) ∨
                   ((p 2).1 = 1 ∧ PrimitiveVectorOrientation (p 3) (p 2) ∧ o = false)))))) :=
                       OccurrenceDeterministicProof.Normalize
  have noMix : ∀ z s r p, ProperBandQuadruple p → ∀ r',
      P4828T1Rotate (P4828T1Root z s) r =
        P4828T1Rotate (P4828T1Step p) r' → False := OccurrenceDeterministicProof.noMix
  have rotUnique : ∀ t, ProperBandQuadruple t → ∀ r r',
      P4828T1Rotate t r = P4828T1Rotate t r' → r = r' := OccurrenceDeterministicProof.rotUnique
  have main : ∀ n : Nat, ∀ q : Fin 4 → CircleCoordinates,
      ProperBandQuadruple q → ∀ i : Fin 3, (q i.succ).1 = 1 →
      ∀ a b : Bool, UnitOccurrenceOrientation q i a →
        UnitOccurrenceOrientation q i b → (q 0).1.toNat = n → a = b :=
            OccurrenceDeterministicProof.main Normalize noMix rotUnique
  exact main _ q hq i hi a b ha hb rfl)

end ApollonianSuperharmonic

end
