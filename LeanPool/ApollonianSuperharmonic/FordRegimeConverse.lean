/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.FordCircleCoordinate
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: FordRegimeConverse]

/-!
# FordRegimeConverse

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordRegimeProof

private theorem predecessorProper :
    ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple ![q (0 : Fin (4 : ℕ)), q (2 : Fin (4
        : ℕ)), q (3 : Fin (4 : ℕ)), q (1 : Fin (4 : ℕ))]) → (ProperBandQuadruple q) := by
  classical
  intro q hq
  have restored := SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1)
  have restored' : SemiProperQuadruple q := by
    convert restored using 1; funext x; fin_cases x <;> rfl
  refine ⟨restored', ?_⟩
  intro j
  fin_cases j
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)

private theorem retainedLine :
    ∀ (predecessor : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple ![((2 : ℤ) *
        (predecessor (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (predecessor (2 : Fin (4 : ℕ))).1 + (2 : ℤ)
        * (predecessor (3 : Fin (4 : ℕ))).1 - (predecessor (1 : Fin (4 : ℕ))).1, (2 :
        GaussianInt) * (predecessor (0 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (predecessor (2 :
        Fin (4 : ℕ))).2 + (2 : GaussianInt) * (predecessor (3 : Fin (4 : ℕ))).2 - (predecessor (1
        : Fin (4 : ℕ))).2), predecessor (0 : Fin (4 : ℕ)), predecessor (2 : Fin (4 : ℕ)),
        predecessor (3 : Fin (4 : ℕ))]) → ((∀ (k : Fin (4 : ℕ)), (0 : ℤ) ≤ (predecessor k).1) →
        (∀ (i : Fin (4 : ℕ)), ((![((2 : ℤ) * (predecessor (0 : Fin (4 : ℕ))).1 + (2 : ℤ) *
        (predecessor (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (predecessor (3 : Fin (4 : ℕ))).1 -
        (predecessor (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (predecessor (0 : Fin (4 : ℕ))).2
        + (2 : GaussianInt) * (predecessor (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) *
        (predecessor (3 : Fin (4 : ℕ))).2 - (predecessor (1 : Fin (4 : ℕ))).2), predecessor (0 :
        Fin (4 : ℕ)), predecessor (2 : Fin (4 : ℕ)), predecessor (3 : Fin (4 : ℕ))] i).1 = (0 :
        ℤ)) → ((predecessor 0).1 = 0 ∨ (predecessor 2).1 = 0 ∨
        (predecessor 3).1 = 0))) := by
  classical
  intro predecessor hq nonnegative i hi
  fin_cases i
  · have strict := hq.2 0
    have nonnegativeChild := nonnegative 0
    simp at hi strict nonnegativeChild
    omega
  · exact Or.inl (by simpa using hi)
  · exact Or.inr (Or.inl (by simpa using hi))
  · exact Or.inr (Or.inr (by simpa using hi))

private theorem successorAction :
    ∀ (g : BandPackingSymmetry), (∃ (w : GaussianInt), g = BandPackingSymmetry.shift w ∨ g =
        (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (∀ (x : Fin 4 →
        CircleCoordinates), BandPackingSymmetryQuadrupleAction g
          ![(2 * (x 0).1 + 2 * (x 2).1 + 2 * (x 3).1 - (x 1).1,
              2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2),
            x 0, x 2, x 3] =
        ![(2 * ((BandPackingSymmetryQuadrupleAction g x) 0).1 +
              2 * ((BandPackingSymmetryQuadrupleAction g x) 2).1 +
              2 * ((BandPackingSymmetryQuadrupleAction g x) 3).1 -
              ((BandPackingSymmetryQuadrupleAction g x) 1).1,
              2 * ((BandPackingSymmetryQuadrupleAction g x) 0).2 +
              2 * ((BandPackingSymmetryQuadrupleAction g x) 2).2 +
              2 * ((BandPackingSymmetryQuadrupleAction g x) 3).2 -
              ((BandPackingSymmetryQuadrupleAction g x) 1).2),
            (BandPackingSymmetryQuadrupleAction g x) 0,
            (BandPackingSymmetryQuadrupleAction g x) 2,
            (BandPackingSymmetryQuadrupleAction g x) 3]) := by
  classical
  intro g hw x
  rcases hw with ⟨w, relation⟩
  rcases relation with relation | relation
  · rw [relation]
    funext j
    fin_cases j <;>
      simp [BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction,
        BandPackingSymmetryReversesOrientation]; ring
  · rw [relation]
    funext j
    fin_cases j <;>
      simp [BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction,
        BandPackingSymmetryReversesOrientation]; ring

private theorem rotateAction :
    ∀ (g : BandPackingSymmetry), (∃ (w : GaussianInt), g = BandPackingSymmetry.shift w ∨ g =
        (BandPackingSymmetry.shift w).comp BandPackingSymmetry.negate) → (∀ (x : Fin 4 →
        CircleCoordinates), BandPackingSymmetryQuadrupleAction g ![x 0, x 2, x 3, x 1] =
        ![(BandPackingSymmetryQuadrupleAction g x) 0,
          (BandPackingSymmetryQuadrupleAction g x) 2,
          (BandPackingSymmetryQuadrupleAction g x) 3,
          (BandPackingSymmetryQuadrupleAction g x) 1]) := by
  classical
  intro g hw x
  rcases hw with ⟨w, relation⟩
  rcases relation with relation | relation
  · rw [relation]
    funext j
    fin_cases j <;>
      simp [BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction,
        BandPackingSymmetryReversesOrientation]
  · rw [relation]
    funext j
    fin_cases j <;>
      simp [BandPackingSymmetryQuadrupleAction,
        BandPackingSymmetryCircleAction,
        BandPackingSymmetryReversesOrientation]

private theorem determinantCoprime :
    ∀ (a : Int), ∀ (b : Nat), ∀ (d : Nat), ∀ (c : Int), a * (d : Int) - (b : Int) * c = 1 →
        Nat.Coprime b a.natAbs := by
  classical
  intro a b d c relation
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let divisor := Nat.gcd b a.natAbs
  have leftDivides : divisor ∣ b := Nat.gcd_dvd_left _ _
  have rightDivides : divisor ∣ a.natAbs := Nat.gcd_dvd_right _ _
  have leftInteger : (divisor : Int) ∣ (b : Int) := by
    exact_mod_cast leftDivides
  have rightInteger : (divisor : Int) ∣ a :=
    (Int.dvd_natAbs).mp (by exact_mod_cast rightDivides)
  have relationDivides : (divisor : Int) ∣
      a * (d : Int) - (b : Int) * c := by
    exact dvd_sub (dvd_mul_of_dvd_left rightInteger _)
      (dvd_mul_of_dvd_left leftInteger _)
  rw [relation] at relationDivides
  exact (Int.natCast_dvd_natCast).mp relationDivides

private theorem desiredAt325 :
    ∀ (predecessor : Fin (4 : ℕ) → CircleCoordinates), (Fin (4 : ℕ)) → (∀ (predecessorLine : ∃ i
        : Fin 4, (predecessor i).1 = 0), ∀ (g : BandPackingSymmetry), ∀ (P : FordFareyParameter),
        ∀ (hP : (1 : ℕ) < P.q), (∀ (x : Fin 4 →
        CircleCoordinates), BandPackingSymmetryQuadrupleAction g ![(2 * (x 0).1 + 2 * (x 2).1 + 2
        * (x 3).1 - (x 1).1, 2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2), x 0, x 2, x 3] =
        ![(2 * ((BandPackingSymmetryQuadrupleAction g x) 0).1 + 2 *
        ((BandPackingSymmetryQuadrupleAction g x) 2).1 + 2 * ((BandPackingSymmetryQuadrupleAction
        g x) 3).1 - ((BandPackingSymmetryQuadrupleAction g x) 1).1, 2 *
        ((BandPackingSymmetryQuadrupleAction g x) 0).2 + 2 * ((BandPackingSymmetryQuadrupleAction
        g x) 2).2 + 2 * ((BandPackingSymmetryQuadrupleAction g x) 3).2 -
        ((BandPackingSymmetryQuadrupleAction g x) 1).2), (BandPackingSymmetryQuadrupleAction g x)
        0, (BandPackingSymmetryQuadrupleAction g x) 2, (BandPackingSymmetryQuadrupleAction g x)
        3]) → (∀ (determinantCoprime : ∀ (a : Int), ∀ (b : Nat), ∀ (d : Nat), ∀ (c : Int), a * (d :
        Int) - (b : Int) * c = 1 → Nat.Coprime b a.natAbs), let next0 : FordFareyParameter :=
      { p := P.p + P.p₂, q := P.q + P.q₂,
        q_pos := by omega,
        reduced := by
          apply determinantCoprime (P.p + P.p₂) (P.q + P.q₂) P.q₂ P.p₂
          norm_num [Nat.cast_add]
          nlinarith [P.det₂],
        p₁ := P.p, q₁ := P.q, p₂ := P.p₂, q₂ := P.q₂,
        sum_p := by ring,
        sum_q := by ring,
        det₁ := by norm_num [Nat.cast_add]; nlinarith [P.det₂],
        det₂ := by norm_num [Nat.cast_add]; nlinarith [P.det₂],
        q₁_lt := by have := P.q₂_pos; omega, q₂_pos := P.q₂_pos,
        unit_case := by intro h; omega }
    (BandPackingSymmetryQuadrupleAction g predecessor = FordRecursiveQuadruple P) →
        (BandPackingSymmetryQuadrupleAction g
      ![(2 * (predecessor 0).1 + 2 * (predecessor 2).1 +
          2 * (predecessor 3).1 - (predecessor 1).1,
          2 * (predecessor 0).2 + 2 * (predecessor 2).2 +
          2 * (predecessor 3).2 - (predecessor 1).2),
        predecessor 0, predecessor 2, predecessor 3] =
    FordRecursiveQuadruple next0))) := by
  classical
  intro predecessor i predecessorLine g P hP successorAction determinantCoprime next0
      actionPredecessor
  rw [successorAction predecessor, actionPredecessor]
  simp? [next0, FordRecursiveQuadruple, FordCircleCoordinate]
  split_ifs <;> simp_all? [P.sum_q, P.sum_p] <;> ring
  repeat' first | constructor | (ext <;> simp; ring)
  all_goals try (intro hp; have := P.q₂_pos; omega)


private theorem actionPredecessorAt357 :
    ∀ (predecessor : Fin (4 : ℕ) → CircleCoordinates), ∀ (g : BandPackingSymmetry), ∀ (P :
        FordFareyParameter), (BandPackingSymmetryReversesOrientation g = false) → ((∀ (x : Fin 4
        → CircleCoordinates), BandPackingSymmetryQuadrupleAction g ![x 0, x 2, x 3, x 1] =
        ![(BandPackingSymmetryQuadrupleAction g x) 0, (BandPackingSymmetryQuadrupleAction g x) 2,
        (BandPackingSymmetryQuadrupleAction g x) 3, (BandPackingSymmetryQuadrupleAction g x) 1])
        → ((BandPackingSymmetryQuadrupleAction g ![predecessor (0 : Fin (4 : ℕ)), predecessor
        ((fun (i : Fin (3 : ℕ)) => i) ⟨nat_lit 2, by norm_num⟩).succ, predecessor ((fun (i : Fin
            (3 : ℕ))
        => i) ⟨nat_lit 2, by norm_num⟩ + (1 : Fin (3 : ℕ))).succ, predecessor ((fun (i : Fin (3 :
            ℕ)) => i)
        ⟨nat_lit 2, by norm_num⟩ + (2 : Fin (3 : ℕ))).succ] = FordRecursiveQuadruple P) →
        (BandPackingSymmetryQuadrupleAction g predecessor =
        ![(FordRecursiveQuadruple P) 0,
          (FordRecursiveQuadruple P) 2,
          (FordRecursiveQuadruple P) 3,
          (FordRecursiveQuadruple P) 1]))) := by
  classical
  intro predecessor g P hg rotateAction heq
  let rotatedInput : Fin 4 → CircleCoordinates :=
    ![predecessor 0, predecessor 2, predecessor 3, predecessor 1]
  have ordered := rotateAction rotatedInput
  have heq' : BandPackingSymmetryQuadrupleAction g
      ![rotatedInput 0, rotatedInput 2, rotatedInput 3,
        rotatedInput 1] = FordRecursiveQuadruple P := by
    simpa [rotatedInput] using heq
  rw [heq'] at ordered
  funext j
  fin_cases j
  · simpa [rotatedInput, hg, BandPackingSymmetryQuadrupleAction] using
      (congrFun ordered (0 : Fin 4)).symm
  · simpa [rotatedInput, hg, BandPackingSymmetryQuadrupleAction] using
      (congrFun ordered (2 : Fin 4)).symm
  · simpa [rotatedInput, hg, BandPackingSymmetryQuadrupleAction] using
      (congrFun ordered (3 : Fin 4)).symm
  · simpa [rotatedInput, hg, BandPackingSymmetryQuadrupleAction] using
      (congrFun ordered (1 : Fin 4)).symm

private theorem desiredAt381 :
    ∀ (predecessor : Fin (4 : ℕ) → CircleCoordinates), (Fin (4 : ℕ)) → (∀ (predecessorLine : ∃ i
        : Fin 4, (predecessor i).1 = 0), ∀ (g : BandPackingSymmetry), ∀ (P : FordFareyParameter),
        ∀ (hP : (1 : ℕ) < P.q), (BandPackingSymmetryReversesOrientation g = false) → ((∀ (x : Fin
        4 →
        CircleCoordinates), BandPackingSymmetryQuadrupleAction g ![(2 * (x 0).1 + 2 * (x 2).1 + 2
        * (x 3).1 - (x 1).1, 2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2), x 0, x 2, x 3] =
        ![(2 * ((BandPackingSymmetryQuadrupleAction g x) 0).1 + 2 *
        ((BandPackingSymmetryQuadrupleAction g x) 2).1 + 2 * ((BandPackingSymmetryQuadrupleAction
        g x) 3).1 - ((BandPackingSymmetryQuadrupleAction g x) 1).1, 2 *
        ((BandPackingSymmetryQuadrupleAction g x) 0).2 + 2 * ((BandPackingSymmetryQuadrupleAction
        g x) 2).2 + 2 * ((BandPackingSymmetryQuadrupleAction g x) 3).2 -
        ((BandPackingSymmetryQuadrupleAction g x) 1).2), (BandPackingSymmetryQuadrupleAction g x)
        0, (BandPackingSymmetryQuadrupleAction g x) 2, (BandPackingSymmetryQuadrupleAction g x)
        3]) → (∀ (determinantCoprime : ∀ (a : Int), ∀ (b : Nat), ∀ (d : Nat), ∀ (c : Int), a * (d :
        Int) - (b : Int) * c = 1 → Nat.Coprime b a.natAbs), let next2 : FordFareyParameter :=
      { p := P.p + P.p₁, q := P.q + P.q₁,
        q_pos := by omega,
        reduced := by
          apply determinantCoprime (P.p + P.p₁) (P.q + P.q₁) P.q P.p
          norm_num [Nat.cast_add]
          nlinarith [P.det₁],
        p₁ := P.p₁, q₁ := P.q₁, p₂ := P.p, q₂ := P.q,
        sum_p := by ring,
        sum_q := by ring,
        det₁ := by norm_num [Nat.cast_add]; nlinarith [P.det₁],
        det₂ := by norm_num [Nat.cast_add]; nlinarith [P.det₁],
        q₁_lt := by have := P.q_pos; omega, q₂_pos := P.q_pos,
        unit_case := by intro h; omega }
    (BandPackingSymmetryQuadrupleAction g predecessor = ![(FordRecursiveQuadruple P) 0,
        (FordRecursiveQuadruple P) 2, (FordRecursiveQuadruple P) 3, (FordRecursiveQuadruple P)
        1]) → (BandPackingSymmetryQuadrupleAction g
      ![(2 * (predecessor 0).1 + 2 * (predecessor 2).1 +
          2 * (predecessor 3).1 - (predecessor 1).1,
          2 * (predecessor 0).2 + 2 * (predecessor 2).2 +
          2 * (predecessor 3).2 - (predecessor 1).2),
        predecessor 3, predecessor 0, predecessor 2] =
    FordRecursiveQuadruple next2)))) := by
  classical
  intro predecessor i predecessorLine g P hP hg successorAction determinantCoprime next2
      actionPredecessor
  let y : Fin 4 → CircleCoordinates :=
    ![predecessor 3, predecessor 1, predecessor 0, predecessor 2]
  have actionY :
      BandPackingSymmetryQuadrupleAction g
          y =
        ![(BandPackingSymmetryQuadrupleAction g predecessor) 3,
          (BandPackingSymmetryQuadrupleAction g predecessor) 1,
          (BandPackingSymmetryQuadrupleAction g predecessor) 0,
          (BandPackingSymmetryQuadrupleAction g predecessor) 2] := by
    funext j
    fin_cases j <;> simp [y, hg, BandPackingSymmetryQuadrupleAction]
  have successorY := successorAction y
  rw [actionY, actionPredecessor] at successorY
  convert successorY using 1 <;>
    simp? [y, next2, FordRecursiveQuadruple,
      FordCircleCoordinate, P.sum_q, P.sum_p] <;>
    ring
  all_goals split_ifs <;>
    simp_all? [] <;>
    try constructor
  all_goals try ring
  all_goals ext <;> simp_all; ring

end FordRegimeProof

theorem FordRegimeConverse (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q)
    (hline : ∃ i : Fin 4, (q i).1 = 0) :
    ∃ (r : Fin 3) (g : BandPackingSymmetry) (P : FordFareyParameter),
      1 < P.q ∧
      BandPackingSymmetryReversesOrientation g = false ∧
      (∃ w : GaussianInt,
        g = .shift w ∨ g = .comp (.shift w) .negate) ∧
      (q ((r + 2).succ)).1 = 0 ∧
      BandPackingSymmetryQuadrupleAction g
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ] =
        FordRecursiveQuadruple P := by
-- BODY
  induction hq.1 with
  | base z =>
    have bad := hq.2 0
    simp at bad
  | @rotate q hq ih =>
    have predecessorProper : ProperBandQuadruple q := FordRegimeProof.predecessorProper q hq
    obtain ⟨i, hi⟩ := hline
    have predecessorLine : ∃ i : Fin 4, (q i).1 = 0 := by
      fin_cases i <;> simp_all <;> aesop
    obtain ⟨r, g, P, hP, hg, hw, hz, heq⟩ := ih predecessorProper predecessorLine
    fin_cases r
    · refine ⟨2, g, P, hP, hg, hw, ?_, ?_⟩
      · simpa using hz
      · simpa using heq
    · refine ⟨0, g, P, hP, hg, hw, ?_, ?_⟩
      · simpa using hz
      · simpa using heq
    · refine ⟨1, g, P, hP, hg, hw, ?_, ?_⟩
      · simpa using hz
      · simpa using heq
  | @successor predecessor predecessorSemi ih =>
    obtain ⟨nonnegative, cases⟩ := SemiProperForestClassification predecessor predecessorSemi
    rcases cases with root | root | root | ⟨predecessorTuple, predecessorProof⟩
    · rcases root with ⟨z, hz⟩
      have bad := hq.2 0
      rw [hz] at bad
      simp at bad
    · rcases root with ⟨z, hz⟩
      let standard : FordFareyParameter :=
        { p := 1, q := 2, q_pos := by norm_num, reduced := by norm_num,
          p₁ := 1, q₁ := 1, p₂ := 0, q₂ := 1,
          sum_p := by norm_num, sum_q := by norm_num,
          det₁ := by norm_num, det₂ := by norm_num,
          q₁_lt := by norm_num, q₂_pos := by norm_num,
          unit_case := by omega }
      refine ⟨2, .shift (-z), standard, by norm_num, by rfl, ?_, ?_, ?_⟩
      · exact ⟨-z, Or.inl rfl⟩
      · simp [hz]
      · simp? [standard, hz, FordRecursiveQuadruple, FordCircleCoordinate,
          BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
          BandPackingSymmetryReversesOrientation]
        repeat' first | constructor | (ext <;> simp <;> ring)
    · rcases root with ⟨z, hz⟩
      let standard : FordFareyParameter :=
        { p := 1, q := 2, q_pos := by norm_num, reduced := by norm_num,
          p₁ := 1, q₁ := 1, p₂ := 0, q₂ := 1,
          sum_p := by norm_num, sum_q := by norm_num,
          det₁ := by norm_num, det₂ := by norm_num,
          q₁_lt := by norm_num, q₂_pos := by norm_num,
          unit_case := by omega }
      refine ⟨0, .comp (.shift (z + 1 + ⟨0, 1⟩)) .negate, standard,
        by norm_num, by rfl, ?_, ?_, ?_⟩
      · exact ⟨z + 1 + ⟨0, 1⟩, Or.inr rfl⟩
      · simp [hz]
      · simp? [standard, hz, FordRecursiveQuadruple, FordCircleCoordinate,
          BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
          BandPackingSymmetryReversesOrientation]
        repeat' first | constructor | (ext <;> simp <;> ring)
    · obtain ⟨i, hi⟩ := hline
      have retainedLine :
          (predecessor 0).1 = 0 ∨ (predecessor 2).1 = 0 ∨
            (predecessor 3).1 = 0 := FordRegimeProof.retainedLine predecessor hq nonnegative i hi
      have predecessorLine : ∃ i : Fin 4, (predecessor i).1 = 0 := by
        fin_cases i
        · have strict := hq.2 0
          have nonnegativeChild := nonnegative 0
          simp at hi strict nonnegativeChild ⊢
          omega
        · exact ⟨0, by simpa using hi⟩
        · exact ⟨2, by simpa using hi⟩
        · exact ⟨3, by simpa using hi⟩
      obtain ⟨r, g, P, hP, hg, hw, hz, heq⟩ :=
        ih ⟨predecessorTuple, predecessorProof⟩ predecessorLine
      have unique := ProperBandCurvatureStructure predecessor
        ⟨predecessorTuple, predecessorProof⟩
      have successorAction (x : Fin 4 → CircleCoordinates) :
          BandPackingSymmetryQuadrupleAction g
              ![(2 * (x 0).1 + 2 * (x 2).1 + 2 * (x 3).1 - (x 1).1,
                  2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2),
                x 0, x 2, x 3] =
            ![(2 * ((BandPackingSymmetryQuadrupleAction g x) 0).1 +
                  2 * ((BandPackingSymmetryQuadrupleAction g x) 2).1 +
                  2 * ((BandPackingSymmetryQuadrupleAction g x) 3).1 -
                  ((BandPackingSymmetryQuadrupleAction g x) 1).1,
                  2 * ((BandPackingSymmetryQuadrupleAction g x) 0).2 +
                  2 * ((BandPackingSymmetryQuadrupleAction g x) 2).2 +
                  2 * ((BandPackingSymmetryQuadrupleAction g x) 3).2 -
                  ((BandPackingSymmetryQuadrupleAction g x) 1).2),
                (BandPackingSymmetryQuadrupleAction g x) 0,
                (BandPackingSymmetryQuadrupleAction g x) 2,
                (BandPackingSymmetryQuadrupleAction g x) 3] := FordRegimeProof.successorAction g
                    hw x
      have rotateAction (x : Fin 4 → CircleCoordinates) :
          BandPackingSymmetryQuadrupleAction g ![x 0, x 2, x 3, x 1] =
            ![(BandPackingSymmetryQuadrupleAction g x) 0,
              (BandPackingSymmetryQuadrupleAction g x) 2,
              (BandPackingSymmetryQuadrupleAction g x) 3,
              (BandPackingSymmetryQuadrupleAction g x) 1] := FordRegimeProof.rotateAction g hw x
      have determinantCoprime : ∀ (a : Int) (b d : Nat) (c : Int),
          a * (d : Int) - (b : Int) * c = 1 → Nat.Coprime b a.natAbs :=
              FordRegimeProof.determinantCoprime
      let next0 : FordFareyParameter :=
        { p := P.p + P.p₂, q := P.q + P.q₂,
          q_pos := by omega,
          reduced := by
            apply determinantCoprime (P.p + P.p₂) (P.q + P.q₂) P.q₂ P.p₂
            norm_num [Nat.cast_add]
            nlinarith [P.det₂],
          p₁ := P.p, q₁ := P.q, p₂ := P.p₂, q₂ := P.q₂,
          sum_p := by ring,
          sum_q := by ring,
          det₁ := by norm_num [Nat.cast_add]; nlinarith [P.det₂],
          det₂ := by norm_num [Nat.cast_add]; nlinarith [P.det₂],
          q₁_lt := by have := P.q₂_pos; omega, q₂_pos := P.q₂_pos,
          unit_case := by intro h; omega }
      let next2 : FordFareyParameter :=
        { p := P.p + P.p₁, q := P.q + P.q₁,
          q_pos := by omega,
          reduced := by
            apply determinantCoprime (P.p + P.p₁) (P.q + P.q₁) P.q P.p
            norm_num [Nat.cast_add]
            nlinarith [P.det₁],
          p₁ := P.p₁, q₁ := P.q₁, p₂ := P.p, q₂ := P.q,
          sum_p := by ring,
          sum_q := by ring,
          det₁ := by norm_num [Nat.cast_add]; nlinarith [P.det₁],
          det₂ := by norm_num [Nat.cast_add]; nlinarith [P.det₁],
          q₁_lt := by have := P.q_pos; omega, q₂_pos := P.q_pos,
          unit_case := by intro h; omega }
      fin_cases r
      · refine ⟨0, g, next0, ?_, hg, hw, ?_, ?_⟩
        · dsimp [next0]
          have := P.q₂_pos
          omega
        · simpa using hz
        · have actionPredecessor :
              BandPackingSymmetryQuadrupleAction g predecessor =
                FordRecursiveQuadruple P := by
            have shape : ![predecessor 0, predecessor 1,
                predecessor 2, predecessor 3] = predecessor := by
              funext j
              fin_cases j <;> rfl
            rw [← shape]
            exact heq
          have desired : BandPackingSymmetryQuadrupleAction g
              ![(2 * (predecessor 0).1 + 2 * (predecessor 2).1 +
                  2 * (predecessor 3).1 - (predecessor 1).1,
                  2 * (predecessor 0).2 + 2 * (predecessor 2).2 +
                  2 * (predecessor 3).2 - (predecessor 1).2),
                predecessor 0, predecessor 2, predecessor 3] =
            FordRecursiveQuadruple next0 := FordRegimeProof.desiredAt325 predecessor i
                predecessorLine g P hP successorAction determinantCoprime actionPredecessor
          simpa using desired
      · exfalso
        have removed : (predecessor 1).1 = 0 := by simpa using hz
        rcases retainedLine with h0 | retainedLine
        · have strict := predecessorProof (0 : Fin 3)
          have nonnegativeChild := nonnegative 1
          omega
        rcases retainedLine with h2 | h3
        · have different := unique.2.2 (0 : Fin 3) (1 : Fin 3)
            removed h2
          omega
        · have different := unique.2.2 (0 : Fin 3) (2 : Fin 3)
            removed h3
          omega
      · refine ⟨2, g, next2, ?_, hg, hw, ?_, ?_⟩
        · dsimp [next2]
          have := P.q₂_pos
          omega
        · simpa using hz
        · have actionPredecessor :
              BandPackingSymmetryQuadrupleAction g predecessor =
                ![(FordRecursiveQuadruple P) 0,
                  (FordRecursiveQuadruple P) 2,
                  (FordRecursiveQuadruple P) 3,
                  (FordRecursiveQuadruple P) 1] := FordRegimeProof.actionPredecessorAt357
                      predecessor g P hg rotateAction heq
          have desired : BandPackingSymmetryQuadrupleAction g
              ![(2 * (predecessor 0).1 + 2 * (predecessor 2).1 +
                  2 * (predecessor 3).1 - (predecessor 1).1,
                  2 * (predecessor 0).2 + 2 * (predecessor 2).2 +
                  2 * (predecessor 3).2 - (predecessor 1).2),
                predecessor 3, predecessor 0, predecessor 2] =
            FordRecursiveQuadruple next2 := FordRegimeProof.desiredAt381 predecessor i
                predecessorLine g P hP hg successorAction determinantCoprime actionPredecessor
          simpa using desired

end ApollonianSuperharmonic

end
