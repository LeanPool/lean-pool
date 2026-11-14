/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.P4566T1SmallPairCoordinates
public import LeanPool.ApollonianSuperharmonic.P4566T1UnitPairCharts
public import LeanPool.ApollonianSuperharmonic.UnitOccurrenceOrientationUnique

-- [TABLET NODE: P4566T1SmallRetainedSides]

/-!
# P4566T1SmallRetainedSides

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SmallRetainedSidesProof

private theorem nextProper :
    ∀ (u : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple u → ProperBandQuadruple ![((2 :
        ℤ) * (u (0 : Fin (4 : ℕ))).1 + (2 : ℤ) * (u (2 : Fin (4 : ℕ))).1 + (2 : ℤ) * (u (3 : Fin
        (4 : ℕ))).1 - (u (1 : Fin (4 : ℕ))).1, (2 : GaussianInt) * (u (0 : Fin (4 : ℕ))).2 + (2 :
        GaussianInt) * (u (2 : Fin (4 : ℕ))).2 + (2 : GaussianInt) * (u (3 : Fin (4 : ℕ))).2 - (u
        (1 : Fin (4 : ℕ))).2), u (0 : Fin (4 : ℕ)), u (2 : Fin (4 : ℕ)), u (3 : Fin (4 : ℕ))] := by
  classical
  intro u hu
  refine ⟨SemiProperQuadruple.successor hu.1, ?_⟩
  have nn := (SemiProperForestClassification u hu.1).1
  have h0 := nn 0
  have h2 := nn 2
  have h3 := nn 3
  have hx : (u 1).1 < (u 0).1 := hu.2 0
  intro k
  fin_cases k <;> dsimp <;> omega

private theorem unit :
    ∀ {u : Fin 4 → CircleCoordinates}, ∀ {k : Fin 3}, ∀ {b : Bool}, UnitOccurrenceOrientation u k
        b → (u k.succ).1 = 1 := by
  classical
  intro u k b cert
  induction cert with
  | leftLower z => rfl
  | leftUpper z => rfl
  | rightUpper z => rfl
  | rightLower z => rfl
  | @rotate u k b cert ih => fin_cases k <;> simpa using ih
  | retainSecondToThird _ _ _ _ ih => exact ih
  | retainSecondFromThird _ _ _ _ ih => exact ih
  | retainSecondOther _ _ _ ih => exact ih
  | retainThirdFromSecond _ _ _ _ ih => exact ih
  | retainThirdToSecond _ _ _ _ ih => exact ih
  | retainThirdOther _ _ _ ih => exact ih

private theorem rootValues :
    (
    let I : GaussianInt := ⟨0, 1⟩
    (∀ (z : GaussianInt), have q := ![((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z), ((1 :
        ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩),
        ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))]; BandVectors.1 (q (3 : Fin
        (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (0 : GaussianInt) ∧ BandVectors.1 (q (2 : Fin (4 : ℕ)))
        (q (1 : Fin (4 : ℕ))) = (-1 : GaussianInt) ∧ BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 :
        Fin (4 : ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 :
        ℕ))) = (1 : GaussianInt) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) =
        (-1 : GaussianInt) - z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 :
        Fin (4 : ℕ))) = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            SemiProperQuadruple q → BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) =
        BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧ BandVectors.1 (q (0 : Fin (4
        : ℕ))) (q (3 : Fin (4 : ℕ))) = BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))
        + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∧
        BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = BandVectors.2 (q (2 : Fin (4
        : ℕ))) (q (1 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 (q (3 : Fin (4 : ℕ)))
        (q (2 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) =
        BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))) → ((∀ (C : CircleCoordinates),
            ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D → BandVectors.1 D C = ⟨(0 :
            ℤ),
        (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 C
        D) → (∀ (z : GaussianInt), BandVectors.1 ((0 : ℤ), (-1 : GaussianInt)) ((1 : ℤ), (1 :
        GaussianInt) + (2 : GaussianInt) * z) = -I ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * z) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 :
        GaussianInt) * I) = (-1 : GaussianInt) + I ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * z + (2 : GaussianInt) * I) ((0 : ℤ), (-1 : GaussianInt)) = (1 :
        GaussianInt) ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 :
        GaussianInt) * I) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z) = (1 :
        GaussianInt) + I ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z) ((0
        : ℤ), (1 : GaussianInt)) = -I ∧ BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 :
        GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) * I) = (-1 : GaussianInt))))) := by
  classical
  intro I baseLaw stepLaw flipLaw z
  let b : Fin 4 → CircleCoordinates :=
    ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * I), (0, 1), (0, -1)]
  have hb : SemiProperQuadruple b := SemiProperQuadruple.base z
  have v32 : BandVectors.1 (b 3) (b 2) = 0 := (baseLaw z).1
  have v21 : BandVectors.1 (b 2) (b 1) = -1 := (baseLaw z).2.1
  have v13 : BandVectors.1 (b 1) (b 3) = 1 := (baseLaw z).2.2.1
  have v20 : BandVectors.1 (b 2) (b 0) = -1 := by
    rw [(stepLaw b hb).1, v21, v32]
    ring
  have v03 : BandVectors.1 (b 0) (b 3) = 1 := by
    rw [(stepLaw b hb).2.1, v13, v32]
    ring
  have v01 : BandVectors.1 (b 0) (b 1) = -1 + I := by
    have h := (stepLaw _ (SemiProperQuadruple.rotate hb)).2.1
    change BandVectors.1 (b 0) (b 1) =
      BandVectors.1 (b 2) (b 1) + I * BandVectors.1 (b 1) (b 3) at h
    rw [h, v21, v13]
    ring
  have pm : PrimitiveVectorOrientation (b 3) (b 0) := by
    convert PrimitiveVectorOrientation.base31 (z - I) using 1 <;>
      simp [b, I]; ring
  have pp : PrimitiveVectorOrientation (b 2) (b 0) := by
    convert PrimitiveVectorOrientation.base21 (z - I) using 1 <;>
      simp [b, I]; ring
  have v30 : BandVectors.1 (b 3) (b 0) = -I := by
    have h := (flipLaw _ _ pm).1
    rw [v03] at h
    have re := congrArg Zsqrtd.re h
    have im := congrArg Zsqrtd.im h
    apply Zsqrtd.ext <;>
      norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at re im ⊢ <;> omega
  have v10 : BandVectors.1 (b 1) (b 0) = 1 + I := by
    have h := (flipLaw _ _ (PrimitiveVectorOrientation.base10 z)).1
    change BandVectors.1 (b 0) (b 1) = I * BandVectors.1 (b 1) (b 0) at h
    rw [v01] at h
    have re := congrArg Zsqrtd.re h
    have im := congrArg Zsqrtd.im h
    apply Zsqrtd.ext <;>
      norm_num [I, Zsqrtd.re_mul, Zsqrtd.im_mul] at re im ⊢ <;> omega
  have v02 : BandVectors.1 (b 0) (b 2) = -I := by
    rw [(flipLaw _ _ pp).1, v20]
    ring
  exact ⟨v30, v01, v13, v10, v02, v21⟩

private theorem data :
    ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (((p (2 : Fin (4 : ℕ))).1 = (0 :
        ℤ) ∨ (p (2 : Fin (4 : ℕ))).1 = (1 : ℤ)) → (((p (3 : Fin (4 : ℕ))).1 = (0 : ℤ) ∨ (p (3 :
        Fin (4 : ℕ))).1 = (1 : ℤ)) → (
    let I : GaussianInt := ⟨0, 1⟩
    (∀ (z : GaussianInt), BandVectors.1 (0, -1) (1, 1 + 2 * z) = -I ∧ BandVectors.1 (1, 1 + 2 *
        z) (1, 1 + 2 * z + 2 * I) = -1 + I ∧ BandVectors.1 (1, 1 + 2 * z + 2 * I) (0, -1) = 1 ∧
        BandVectors.1 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z) = 1 + I ∧ BandVectors.1 (1, 1 + 2 *
        z) (0, 1) = -I ∧ BandVectors.1 (0, 1) (1, 1 + 2 * z + 2 * I) = -1) →
        ((PrimitiveVectorOrientation (p 2) (p 3) ∧ (∀ o : Bool, ((p 3).1 = 0 ∨ o = false) →
        UnitTriangularStep o (BandVectors.1 (p 3) (p 2))) ∧ (∀ o : Bool, ((p 2).1 = 0 ∨ o = true)
        → UnitTriangularStep o (I * BandVectors.1 (p 3) (p 2)))) ∨ (PrimitiveVectorOrientation (p
        3) (p 2) ∧ (∀ o : Bool, ((p 3).1 = 0 ∨ o = true) → UnitTriangularStep o (BandVectors.1 (p
        3) (p 2))) ∧ (∀ o : Bool, ((p 2).1 = 0 ∨ o = false) → UnitTriangularStep o (I *
        BandVectors.1 (p 3) (p 2)))))))) := by
  classical
  intro p hp h2 h3 I rootValues
  obtain ⟨z, rows⟩ := P4566T1SmallPairCoordinates p hp h2 h3
  rcases rootValues z with ⟨v30, v01, v13, v10, v02, v21⟩
  rcases rows with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [a, b]
      exact PrimitiveVectorOrientation.base31 z
    · intro o label
      rw [a, b, v13]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v13]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [a, b]
      exact PrimitiveVectorOrientation.base10 z
    · intro o label
      rw [a, b, v01]
      have ho : o = false := by simpa [b] using label
      subst o
      norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v01]
      have ho : o = true := by simpa [a] using label
      subst o
      norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [a, b]
      convert PrimitiveVectorOrientation.base31 (z - I) using 1; simp [I]; ring
    · intro o label
      rw [a, b, v30]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v30]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [a, b]
      exact PrimitiveVectorOrientation.base21 z
    · intro o label
      rw [a, b, v21]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v21]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [a, b]
      convert PrimitiveVectorOrientation.base21 (z - I) using 1; simp [I]; ring
    · intro o label
      rw [a, b, v02]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v02]
      cases o <;> norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [a, b]
      exact PrimitiveVectorOrientation.base10 z
    · intro o label
      rw [a, b, v10]
      have ho : o = true := by simpa [b] using label
      subst o
      norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]
    · intro o label
      rw [a, b, v10]
      have ho : o = false := by simpa [a] using label
      subst o
      norm_num [UnitTriangularStep, I, Zsqrtd.ext_iff]

end SmallRetainedSidesProof

theorem P4566T1SmallRetainedSides
    (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (h2 : (p 2).1 = 0 ∨ (p 2).1 = 1)
    (h3 : (p 3).1 = 0 ∨ (p 3).1 = 1) :
    let q : Fin 4 → CircleCoordinates :=
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]
    let r : Fin 4 → CircleCoordinates :=
      ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
          2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
        q 0, q 2, q 3]
    (PrimitiveVectorOrientation (p 2) (p 3) ∧
      (∀ orientation : Bool,
        UnitOccurrenceOrientation q 1 orientation →
          UnitTriangularStep orientation (BandVectors.1 (p 3) (p 2)) ∧
          ((p 3).1 = 0 ∨ orientation = false)) ∧
      (∀ orientation : Bool,
        UnitOccurrenceOrientation q 2 orientation →
          UnitTriangularStep orientation
            ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (p 3) (p 2)) ∧
          ((p 2).1 = 0 ∨ orientation = true)) ∧
      ((p 2).1 = 1 → (p 3).1 = 1 →
        UnitOccurrenceOrientation q 1 false ∧
        UnitOccurrenceOrientation q 2 true ∧
        UnitOccurrenceOrientation r 1 false ∧
        UnitOccurrenceOrientation r 2 true)) ∨
    (PrimitiveVectorOrientation (p 3) (p 2) ∧
      (∀ orientation : Bool,
        UnitOccurrenceOrientation q 1 orientation →
          UnitTriangularStep orientation (BandVectors.1 (p 3) (p 2)) ∧
          ((p 3).1 = 0 ∨ orientation = true)) ∧
      (∀ orientation : Bool,
        UnitOccurrenceOrientation q 2 orientation →
          UnitTriangularStep orientation
            ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (p 3) (p 2)) ∧
          ((p 2).1 = 0 ∨ orientation = false)) ∧
      ((p 2).1 = 1 → (p 3).1 = 1 →
        UnitOccurrenceOrientation q 1 true ∧
        UnitOccurrenceOrientation q 2 false ∧
        UnitOccurrenceOrientation r 1 true ∧
        UnitOccurrenceOrientation r 2 false)) := by
-- BODY
  classical
  dsimp only
  let I : GaussianInt := ⟨0, 1⟩
  let q : Fin 4 → CircleCoordinates :=
    ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
        2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
      p 0, p 2, p 3]
  let r : Fin 4 → CircleCoordinates :=
    ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
      q 0, q 2, q 3]
  have nextProper (u : Fin 4 → CircleCoordinates) (hu : ProperBandQuadruple u) :
      ProperBandQuadruple
        ![(2 * (u 0).1 + 2 * (u 2).1 + 2 * (u 3).1 - (u 1).1,
            2 * (u 0).2 + 2 * (u 2).2 + 2 * (u 3).2 - (u 1).2),
          u 0, u 2, u 3] := SmallRetainedSidesProof.nextProper u hu
  have hq : ProperBandQuadruple q := nextProper p hp
  have hr : ProperBandQuadruple r := nextProper q hq
  have unit : ∀ {u : Fin 4 → CircleCoordinates} {k : Fin 3} {b : Bool},
      UnitOccurrenceOrientation u k b → (u k.succ).1 = 1 := SmallRetainedSidesProof.unit
  have systemLaw : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases systemLaw with ⟨_, baseLaw, stepLaw, flipLaw⟩
  have rootValues (z : GaussianInt) :
      BandVectors.1 (0, -1) (1, 1 + 2 * z) = -I ∧
      BandVectors.1 (1, 1 + 2 * z) (1, 1 + 2 * z + 2 * I) = -1 + I ∧
      BandVectors.1 (1, 1 + 2 * z + 2 * I) (0, -1) = 1 ∧
      BandVectors.1 (1, 1 + 2 * z + 2 * I) (1, 1 + 2 * z) = 1 + I ∧
      BandVectors.1 (1, 1 + 2 * z) (0, 1) = -I ∧
      BandVectors.1 (0, 1) (1, 1 + 2 * z + 2 * I) = -1 := SmallRetainedSidesProof.rootValues
          baseLaw stepLaw flipLaw z
  have data :
      (PrimitiveVectorOrientation (p 2) (p 3) ∧
        (∀ o : Bool, ((p 3).1 = 0 ∨ o = false) →
          UnitTriangularStep o (BandVectors.1 (p 3) (p 2))) ∧
        (∀ o : Bool, ((p 2).1 = 0 ∨ o = true) →
          UnitTriangularStep o (I * BandVectors.1 (p 3) (p 2)))) ∨
      (PrimitiveVectorOrientation (p 3) (p 2) ∧
        (∀ o : Bool, ((p 3).1 = 0 ∨ o = true) →
          UnitTriangularStep o (BandVectors.1 (p 3) (p 2))) ∧
        (∀ o : Bool, ((p 2).1 = 0 ∨ o = false) →
          UnitTriangularStep o (I * BandVectors.1 (p 3) (p 2)))) := SmallRetainedSidesProof.data
              p hp h2 h3 rootValues
  rcases data with ⟨hd, stepB, stepD⟩ | ⟨hd, stepB, stepD⟩
  · refine Or.inl ⟨hd, ?_, ?_, ?_⟩
    · intro o cert
      have label : (p 3).1 = 0 ∨ o = false := by
        rcases h3 with zero | one
        · exact Or.inl zero
        · have selected : (p 2).1 = 1 := unit cert
          have pair := P4566T1UnitPairCharts q hq 1 2 (by decide) selected one hd
          exact Or.inr ((UnitOccurrenceOrientationUnique.1 q hq 1 selected).unique cert pair.1)
      exact ⟨stepB o label, label⟩
    · intro o cert
      have label : (p 2).1 = 0 ∨ o = true := by
        rcases h2 with zero | one
        · exact Or.inl zero
        · have selected : (p 3).1 = 1 := unit cert
          have pair := P4566T1UnitPairCharts q hq 1 2 (by decide) one selected hd
          exact Or.inr ((UnitOccurrenceOrientationUnique.1 q hq 2 selected).unique cert pair.2)
      exact ⟨stepD o label, label⟩
    · intro hb hdunit
      have a := P4566T1UnitPairCharts q hq 1 2 (by decide) hb hdunit hd
      have b := P4566T1UnitPairCharts r hr 1 2 (by decide) hb hdunit hd
      exact ⟨a.1, a.2, b.1, b.2⟩
  · refine Or.inr ⟨hd, ?_, ?_, ?_⟩
    · intro o cert
      have label : (p 3).1 = 0 ∨ o = true := by
        rcases h3 with zero | one
        · exact Or.inl zero
        · have selected : (p 2).1 = 1 := unit cert
          have pair := P4566T1UnitPairCharts q hq 2 1 (by decide) one selected hd
          exact Or.inr ((UnitOccurrenceOrientationUnique.1 q hq 1 selected).unique cert pair.2)
      exact ⟨stepB o label, label⟩
    · intro o cert
      have label : (p 2).1 = 0 ∨ o = false := by
        rcases h2 with zero | one
        · exact Or.inl zero
        · have selected : (p 3).1 = 1 := unit cert
          have pair := P4566T1UnitPairCharts q hq 2 1 (by decide) selected one hd
          exact Or.inr ((UnitOccurrenceOrientationUnique.1 q hq 2 selected).unique cert pair.1)
      exact ⟨stepD o label, label⟩
    · intro hb hdunit
      have a := P4566T1UnitPairCharts q hq 2 1 (by decide) hdunit hb hd
      have b := P4566T1UnitPairCharts r hr 2 1 (by decide) hdunit hb hd
      exact ⟨a.2, a.1, b.2, b.1⟩

end ApollonianSuperharmonic

end
