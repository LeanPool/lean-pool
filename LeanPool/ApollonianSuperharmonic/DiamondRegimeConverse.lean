/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.P4840T6ProperGrowth
public import LeanPool.ApollonianSuperharmonic.P4840T6ShiftRoot
public import LeanPool.ApollonianSuperharmonic.P4840T6NegatedRoot
public import LeanPool.ApollonianSuperharmonic.P4840T6ConstructorCovariance
public import LeanPool.ApollonianSuperharmonic.P4840T6DiamondRecurrence

-- [TABLET NODE: DiamondRegimeConverse]

/-!
# DiamondRegimeConverse

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondRegimeConverse (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q)
    (hnoLine : ∀ i : Fin 4, (q i).1 ≠ 0)
    (htwoUnits : ∃ i j : Fin 4,
      i ≠ j ∧ (q i).1 = 1 ∧ (q j).1 = 1) :
    ∃ (r : Fin 3) (g : BandPackingSymmetry) (K : DiamondParameter),
      1 < K.1 ∧
      BandPackingSymmetryReversesOrientation g = false ∧
      (∃ w : GaussianInt,
        g = .shift w ∨ g = .comp (.shift w) .negate) ∧
      BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] =
        DiamondRecursiveQuadruple K := by
-- BODY
  let R := fun x : Fin 4 → CircleCoordinates => ![x 0, x 2, x 3, x 1]
  let S := fun x : Fin 4 → CircleCoordinates =>
    ![(2 * (x 0).1 + 2 * (x 2).1 + 2 * (x 3).1 - (x 1).1,
        2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2),
      x 0, x 2, x 3]
  let rot := fun (a : Fin 3) (x : Fin 4 → CircleCoordinates) =>
    ![x 0, x a.succ, x (a + 1).succ, x (a + 2).succ]
  let Q := BandPackingSymmetryQuadrupleAction
  let D := DiamondRecursiveQuadruple
  have rotate_action (g : BandPackingSymmetry)
      (hg : BandPackingSymmetryReversesOrientation g = false)
      (x : Fin 4 → CircleCoordinates) : Q g (R x) = R (Q g x) := by
    funext j
    fin_cases j <;> simp [Q, R, BandPackingSymmetryQuadrupleAction, hg]
  have undo_units (x : Fin 4 → CircleCoordinates)
      (hu : ∃ i j : Fin 4,
        i ≠ j ∧ ((R x) i).1 = 1 ∧ ((R x) j).1 = 1) :
      ∃ i j : Fin 4, i ≠ j ∧ (x i).1 = 1 ∧ (x j).1 = 1 := by
    let p : Fin 4 → Fin 4 := ![0, 2, 3, 1]
    have hinj : Function.Injective p := by
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    have heval (i : Fin 4) : (R x) i = x (p i) := by
      fin_cases i <;> rfl
    obtain ⟨i, j, hij, hi, hj⟩ := hu
    exact ⟨p i, p j, (fun h => hij (hinj h)),
      by simpa only [heval] using hi, by simpa only [heval] using hj⟩
  -- Retain the first proper normalizer while inducting through the forest.
  have main : ∀ x : Fin 4 → CircleCoordinates, SemiProperQuadruple x →
      ProperBandQuadruple x →
      (∃ i j : Fin 4, i ≠ j ∧ (x i).1 = 1 ∧ (x j).1 = 1) →
      ∃ (a : Fin 3) (g : BandPackingSymmetry) (K : DiamondParameter),
        BandPackingSymmetryReversesOrientation g = false ∧
        (∃ w : GaussianInt, g = .shift w ∨ g = .comp (.shift w) .negate) ∧
        Q g (rot a x) = D K := by
    intro x hx
    induction hx with
    | base z =>
        intro hp _
        have bad := hp.2 (0 : Fin 3)
        norm_num at bad
    | @rotate x hx ih =>
        intro hp hu
        have old : ProperBandQuadruple x := by
          refine ⟨hx, ?_⟩
          intro j
          fin_cases j
          · simpa using hp.2 2
          · simpa using hp.2 0
          · simpa using hp.2 1
        obtain ⟨a, g, K, hg, hw, heq⟩ := ih old (undo_units x hu)
        fin_cases a
        · refine ⟨2, g, K, hg, hw, ?_⟩
          simpa [rot, R] using heq
        · refine ⟨0, g, K, hg, hw, ?_⟩
          simpa [rot, R] using heq
        · refine ⟨1, g, K, hg, hw, ?_⟩
          simpa [rot, R] using heq
    | @successor x hx ih =>
        intro hp hu
        rcases (SemiProperForestClassification x hx).2 with
          root | root | root | old
        · obtain ⟨z, hz⟩ := root
          have bad := hp.2 (0 : Fin 3)
          rw [hz] at bad
          change (1 : Int) < 1 at bad
          exact (lt_irrefl _ bad).elim
        · obtain ⟨z, hz⟩ := root
          refine ⟨2, .shift (-z), ⟨1, by norm_num⟩, rfl,
            ⟨-z, Or.inl rfl⟩, ?_⟩
          have source : rot 2 (S x) =
              ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩),
                (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z), (0, -1)] := by
            rw [hz]
            funext j
            fin_cases j <;> apply Prod.ext
            all_goals simp [rot, S]
            all_goals ring
          change Q (.shift (-z)) (rot 2 (S x)) = D _
          rw [source]
          exact P4840T6ShiftRoot z
        · obtain ⟨z, hz⟩ := root
          refine ⟨0, .comp (.shift (z + 1 + ⟨0, 1⟩)) .negate,
            ⟨1, by norm_num⟩, rfl, ⟨z + 1 + ⟨0, 1⟩, Or.inr rfl⟩, ?_⟩
          have source : rot 0 (S x) =
              ![(4, 7 + 8 * z + 4 * ⟨0, 1⟩),
                (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (0, 1)] := by
            rw [hz]
            funext j
            fin_cases j <;> apply Prod.ext
            all_goals simp [rot, S]
            all_goals ring
          change Q (.comp (.shift (z + 1 + ⟨0, 1⟩)) .negate)
            (rot 0 (S x)) = D _
          rw [source]
          exact P4840T6NegatedRoot z
        · have retained : (x 2).1 = 1 ∧ (x 3).1 = 1 := by
            obtain ⟨hc, hd⟩ := P4840T6ProperGrowth x old
            obtain ⟨i, j, hij, hi, hj⟩ := hu
            fin_cases i <;> fin_cases j <;> simp at hij hi hj <;> omega
          obtain ⟨a, g, K, hg, hw, heq⟩ :=
            ih old ⟨2, 3, by decide, retained.1, retained.2⟩
          have hcurv := (P4840T6ConstructorCovariance g hw).2.1
          have nonunit : ((D K) 3).1 ≠ 1 := by
            change ((2 * (K.1 - 1) * K.1 : Nat) : Int) ≠ 1
            intro h
            have h' : 2 * (((K.1 - 1 : Nat) : Int) * (K.1 : Int)) = 1 := by
              simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h
            omega
          fin_cases a
          · exfalso
            apply nonunit
            have h := congrArg (fun y => (y 3).1) heq.symm
            simpa [Q, rot, BandPackingSymmetryQuadrupleAction, hg,
              hcurv, retained.2] using h
          · refine ⟨1, g, ⟨K.1 + 1, by omega⟩, hg, hw, ?_⟩
            have action : Q g x = R (R (D K)) := by
              have h : Q g (R x) = D K := by simpa [rot, R] using heq
              rw [rotate_action g hg x] at h
              have h' := congrArg (fun y => R (R y)) h
              funext j
              fin_cases j
              · exact congrFun h' 0
              · exact congrFun h' 1
              · exact congrFun h' 2
              · exact congrFun h' 3
            change Q g (R (S x)) = D _
            rw [rotate_action g hg (S x)]
            have cov := (P4840T6ConstructorCovariance g hw).2.2 x
            change Q g (S x) = S (Q g x) at cov
            rw [cov, action]
            exact P4840T6DiamondRecurrence K
          · exfalso
            apply nonunit
            have h := congrArg (fun y => (y 3).1) heq.symm
            simpa [Q, rot, BandPackingSymmetryQuadrupleAction, hg,
              hcurv, retained.1] using h
  obtain ⟨a, g, K, hg, hw, heq⟩ := main q hq.1 hq htwoUnits
  refine ⟨a, g, K, ?_, hg, hw, heq⟩
  by_contra hk
  have k1 : K.1 = 1 := by have := K.2; omega
  have h := congrArg (fun y => (y 3).1) heq
  have hcurv := (P4840T6ConstructorCovariance g hw).2.1
  have line : (q (a + 2).succ).1 = 0 := by
    simpa [Q, rot, D, DiamondRecursiveQuadruple, k1,
      BandPackingSymmetryQuadrupleAction, hg, hcurv] using h
  exact hnoLine _ line

end ApollonianSuperharmonic

end
