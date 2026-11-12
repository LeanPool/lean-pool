/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: ProperBandCurvatureStructure]

/-!
# ProperBandCurvatureStructure

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ProperBandCurvatureStructure (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    0 < (q 0).1 ∧
      (∀ i : Fin 3, 0 ≤ (q i.succ).1) ∧
      ∀ i j : Fin 3,
        (q i.succ).1 = 0 → (q j.succ).1 = 0 → i = j := by
-- BODY
  have main : ∀ (r : Fin 4 → CircleCoordinates),
      SemiProperQuadruple r → ProperBandQuadruple r →
      0 < (r 0).1 ∧
        (∀ i : Fin 3, 0 ≤ (r i.succ).1) ∧
        ∀ i j : Fin 3, (r i.succ).1 = 0 → (r j.succ).1 = 0 → i = j := by
    intro r hs
    induction hs with
    | base z =>
        intro hp
        rcases hp with ⟨_, hp⟩
        have bad := hp (0 : Fin 3)
        norm_num at bad
    | @rotate r hs ih =>
        intro hp
        rcases hp with ⟨hpsemi, hpbelow⟩
        have old : ProperBandQuadruple r := by
          refine ⟨hs, ?_⟩
          intro j
          fin_cases j
          · simpa using hpbelow 2
          · simpa using hpbelow 0
          · simpa using hpbelow 1
        have facts := ih old
        rcases facts with ⟨child, nonneg, unique⟩
        constructor
        · simpa using child
        constructor
        · intro i
          fin_cases i
          · simpa using nonneg 1
          · simpa using nonneg 2
          · simpa using nonneg 0
        · intro i j hi hj
          fin_cases i <;> fin_cases j
          · simp
          · simpa using unique 1 2 hi hj
          · simpa using unique 1 0 hi hj
          · simpa using unique 2 1 hi hj
          · simp
          · simpa using unique 2 0 hi hj
          · simpa using unique 0 1 hi hj
          · simpa using unique 0 2 hi hj
          · simp
    | @successor r hs ih =>
        intro hp
        rcases hp with ⟨hpsemi, hpbelow⟩
        have classified := SemiProperForestClassification _ hs
        rcases classified with ⟨nonneg, cases⟩
        constructor
        · have hbelow : (r 0).1 <
              2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1 := by
            simpa using hpbelow (0 : Fin 3)
          have a := nonneg (0 : Fin 4)
          have b := nonneg (1 : Fin 4)
          have c := nonneg (2 : Fin 4)
          have d := nonneg (3 : Fin 4)
          change 0 < 2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1
          omega
        constructor
        · intro i
          fin_cases i
          · exact nonneg 0
          · exact nonneg 2
          · exact nonneg 3
        · intro i j hi hj
          rcases cases with root | root | root | proper
          · rcases root with ⟨z, hz⟩
            have bad := hpbelow (0 : Fin 3)
            simp [hz] at bad
          · rcases root with ⟨z, hz⟩
            rw [hz] at hi hj
            fin_cases i <;> fin_cases j <;> simp_all
          · rcases root with ⟨z, hz⟩
            rw [hz] at hi hj
            fin_cases i <;> fin_cases j <;> simp_all
          · have old := ih proper
            rcases old with ⟨child, oldnonneg, oldunique⟩
            fin_cases i <;> fin_cases j
            all_goals simp only [Fin.isValue, Fin.mk_one, Fin.succ_one_eq_two,
                Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc, Fin.zero_eta,
                Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hi hj
            · omega
            · omega
            · omega
            · omega
            · exact oldunique 1 1 hi hj
            · exact oldunique 1 2 hi hj
            · omega
            · exact oldunique 2 1 hi hj
            · exact oldunique 2 2 hi hj
  exact main q hq.1 hq

end ApollonianSuperharmonic

end
