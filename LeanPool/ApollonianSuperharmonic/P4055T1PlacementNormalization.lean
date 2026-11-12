/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance

-- [TABLET NODE: P4055T1PlacementNormalization]

/-!
# P4055T1PlacementNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PlacementNormalizationProof

private theorem hq :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), (ProperBandQuadruple r) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ProperBandQuadruple q) ) := by
  classical
  intro r hproper a q
  fin_cases a
  · convert hproper using 1; funext x; fin_cases x <;> rfl
  · have rotated := SemiProperQuadruple.rotate hproper.1
    have properRotated : ProperBandQuadruple ![r 0, r 2, r 3, r 1] := by
      refine ⟨rotated, ?_⟩
      intro j
      fin_cases j
      · simpa using hproper.2 (1 : Fin 3)
      · simpa using hproper.2 (2 : Fin 3)
      · simpa using hproper.2 (0 : Fin 3)
    simpa [q] using properRotated
  · have rotated := SemiProperQuadruple.rotate
      (SemiProperQuadruple.rotate hproper.1)
    have properRotated : ProperBandQuadruple ![r 0, r 3, r 1, r 2] := by
      refine ⟨rotated, ?_⟩
      intro j
      fin_cases j
      · simpa using hproper.2 (2 : Fin 3)
      · simpa using hproper.2 (0 : Fin 3)
      · simpa using hproper.2 (1 : Fin 3)
    simpa [q] using properRotated

private theorem hU' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (U : ProtoTile), (BandPrototile (r (0 : Fin (4 :
            ℕ))) U) → (∀ (a : Fin 3), ∀ (g : BandPackingSymmetry),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry), (BandPackingSymmetryReversesOrientation g' =
            BandPackingSymmetryReversesOrientation g) → (
        let qg := BandPackingSymmetryQuadrupleAction g' q
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → (BandPrototile (qg 0) (BandPackingSymmetryTileAction g' U)))) ) := by
  classical
  intro r U hU a g q g' horientg qg htileCov
  simpa [qg, q, BandPackingSymmetryQuadrupleAction,
    BandPackingSymmetryCircleAction, horientg] using
    (htileCov.2.1 (r 0) U).mp hU

private theorem hWlabel :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (i a : Fin (3 : ℕ)),
          let q :=
            ![r (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ,
              r (a + (2 : Fin (3 : ℕ))).succ];
          ∀ (g' : BandPackingSymmetry),
            let qg := BandPackingSymmetryQuadrupleAction g' q;
            let k :=
              if
                  BandPackingSymmetryReversesOrientation g' =
                    true then
                -(i - a)
              else i - a;
            qg k.succ =
              BandPackingSymmetryCircleAction g' (r i.succ)) := by
  classical
  intro r i a q g' qg k
  dsimp [qg, k, q, BandPackingSymmetryQuadrupleAction]
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    fin_cases a <;> fin_cases i <;>
    simp []

private theorem cyclicIndex :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (a : Fin (3 : ℕ)),
          let q :=
            ![r (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ,
              r (a + (2 : Fin (3 : ℕ))).succ];
          ∀ (j₀ : Fin (3 : ℕ)), q j₀.succ = r (a + j₀).succ) := by
  classical
  intro r a q j₀
  dsimp [q]
  fin_cases a <;> fin_cases j₀ <;> rfl

private theorem actionParent :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        ∀ (j₀ : Fin 3), qg j₀.succ = BandPackingSymmetryCircleAction g' (q ((if
            BandPackingSymmetryReversesOrientation g' then -j₀ else j₀).succ)) ) := by
  classical
  intro r a q g' qg j₀
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    fin_cases j₀ <;>
      simp [qg, q, BandPackingSymmetryQuadrupleAction, ho,
        ]

private theorem hW' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (W : ProtoTile), (BandPrototile (r
            i.succ) W) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → ((qg k.succ = BandPackingSymmetryCircleAction g' (r i.succ)) →
            (BandPrototile (qg k.succ) (BandPackingSymmetryTileAction g' W)))) ) := by
  classical
  intro r i W hW a q g' qg k htileCov hWlabel
  rw [hWlabel]
  exact (htileCov.2.1 (r i.succ) W).mp hW

private theorem hparent :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        (∀ (j₀ : Fin 3), q j₀.succ = r (a + j₀).succ) → ((∀ (j₀ : Fin 3), qg j₀.succ =
            BandPackingSymmetryCircleAction g' (q ((if BandPackingSymmetryReversesOrientation g'
            then -j₀ else j₀).succ))) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        ∀ (m : Fin 3), qg (sigma m).succ = BandPackingSymmetryCircleAction g' (r (a + m).succ)))
            ) := by
  classical
  intro r a q g' qg cyclicIndex actionParent sigma m
  rw [actionParent]
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    simp [sigma, ho, cyclicIndex]

private theorem hparentAction :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), qg (sigma m).succ = BandPackingSymmetryCircleAction g' (r (a + m).succ))
            → (∀ (m : Fin 3), BandPackingSymmetryQuadrupleAction g' q (if
            BandPackingSymmetryReversesOrientation g' then -m else m).succ =
            BandPackingSymmetryCircleAction g' (r (a + m).succ)) ) := by
  classical
  intro r a q g' qg sigma hparent m
  simpa [qg, sigma] using hparent m

private theorem hrootAction :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        (qg 0 = BandPackingSymmetryCircleAction g' (r 0)) → (BandPackingSymmetryQuadrupleAction
            g' q 0 = BandPackingSymmetryCircleAction g' (r 0)) ) := by
  classical
  intro r a q g' qg hrootLabel
  simpa [qg] using hrootLabel

private theorem hphaseForward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry), (BandPackingSymmetryScopedPhase g' q false) → (
        let qg := BandPackingSymmetryQuadrupleAction g' q
        (∀ (j₀ : Fin 3), q j₀.succ = r (a + j₀).succ) → ((qg 0 = BandPackingSymmetryCircleAction
            g' (r 0)) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), qg (sigma m).succ = BandPackingSymmetryCircleAction g' (r (a + m).succ))
            → ((∀ (m : Fin 3), BandPackingSymmetryQuadrupleAction g' q (if
            BandPackingSymmetryReversesOrientation g' then -m else m).succ =
            BandPackingSymmetryCircleAction g' (r (a + m).succ)) →
            ((BandPackingSymmetryQuadrupleAction g' q 0 = BandPackingSymmetryCircleAction g' (r
            0)) → (∀ (m : Fin 3), BandVectors.1 (qg (sigma m).succ) (qg 0) =
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r (a + m).succ) (r 0)))))))) ) := by
  classical
  intro r a q g' hfalse qg cyclicIndex hrootLabel sigma hparent hparentAction hrootAction m
  have hp := (hfalse m).1
  dsimp [BandPackingSymmetryScopedPhase] at hp
  rw [hparentAction m, hrootAction, cyclicIndex m] at hp
  rw [hparent m, hrootLabel]
  simpa [q] using hp

private theorem hphaseBackward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry), (BandPackingSymmetryScopedPhase g' q false) → (
        let qg := BandPackingSymmetryQuadrupleAction g' q
        (∀ (j₀ : Fin 3), q j₀.succ = r (a + j₀).succ) → ((qg 0 = BandPackingSymmetryCircleAction
            g' (r 0)) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), qg (sigma m).succ = BandPackingSymmetryCircleAction g' (r (a + m).succ))
            → ((∀ (m : Fin 3), BandPackingSymmetryQuadrupleAction g' q (if
            BandPackingSymmetryReversesOrientation g' then -m else m).succ =
            BandPackingSymmetryCircleAction g' (r (a + m).succ)) →
            ((BandPackingSymmetryQuadrupleAction g' q 0 = BandPackingSymmetryCircleAction g' (r
            0)) → (∀ (m : Fin 3), BandVectors.1 (qg 0) (qg (sigma m).succ) = (if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ))))))))) ) := by
  classical
  intro r a q g' hfalse qg cyclicIndex hrootLabel sigma hparent hparentAction hrootAction m
  have hp := (hfalse m).2.1
  dsimp [BandPackingSymmetryScopedPhase] at hp
  rw [hparentAction m, hrootAction, cyclicIndex m] at hp
  rw [hparent m, hrootLabel]
  simpa [q] using hp

private theorem hvectorForward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (x : Fin 3), ∀ (y : Fin 3), x + (y - x) = y) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), BandVectors.1 (qg (sigma m).succ) (qg 0) =
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r (a + m).succ) (r 0))) → ((sigma
            (i - a) = k) → (BandVectors.1 (qg k.succ) (qg 0) = BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r i.succ) (r 0))))) ) := by
  classical
  intro r i a q g' qg k cyclicCancel sigma hphaseForward hk
  simpa [hk, cyclicCancel] using hphaseForward (i - a)

private theorem hvectorBackward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (x : Fin 3), ∀ (y : Fin 3), x + (y - x) = y) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), BandVectors.1 (qg 0) (qg (sigma m).succ) = (if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ)))) → ((sigma (i - a) = k) → (BandVectors.1 (qg
            0) (qg k.succ) = (if BandPackingSymmetryReversesOrientation g' then
            -BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r i.succ)) else
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r i.succ)))))) ) := by
  classical
  intro r i a q g' qg k cyclicCancel sigma hphaseBackward hk
  simpa [hk, cyclicCancel] using hphaseBackward (i - a)

private theorem notEvenOne :
    (by
      classical
      exact
        (Fin 4 → CircleCoordinates) → ((Fin 3) → ((Fin 4) → ((Fin 3) → ((BandPackingSymmetry) →
            (¬ Even 1))))) ) := by
  classical
  intro r i s a g'
  rintro ⟨n, hn⟩
  omega

private theorem notEvenThree :
    (by
      classical
      exact
        (Fin 4 → CircleCoordinates) → ((Fin 3) → ((Fin 4) → ((Fin 3) → ((BandPackingSymmetry) →
            (¬ Even 3))))) ) := by
  classical
  intro r i s a g'
  rintro ⟨n, hn⟩
  omega

private theorem hnegVal :
    (by
      classical
      exact
        ∀ (s₀ : Fin 4), ((-s₀ - 1 : Fin 4) : Nat) = (3 - s₀.val) % 4 ) := by
  classical
  intro s₀
  fin_cases s₀ <;> decide +kernel

private theorem iiCancel :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (∀ (x : GaussianInt), ii * x - ii ^ 2 * x = ii * x + x) ) := by
  classical
  intro ii iiSq x
  rw [iiSq]
  ring

private theorem iiCancelLiteral :
    (by
      classical
      exact
        ((⟨0, 1⟩ : GaussianInt) ^ 2 = -1) → (∀ (x : GaussianInt), (⟨0, 1⟩ : GaussianInt) * x -
            (⟨0, 1⟩ : GaussianInt) ^ 2 * x = (⟨0, 1⟩ : GaussianInt) * x + x) ) := by
  classical
  intro iiSqLiteral x
  rw [iiSqLiteral]
  ring

private theorem iiSquareMul :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii * ii = -1) → (∀ (x : GaussianInt), ii * (ii * x) = -x) ) := by
  classical
  intro ii iiMul x
  rw [← mul_assoc, iiMul]
  simp

private theorem iiNegSquareMul :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ii * (ii * x) = -x) → (∀ (x : GaussianInt), (-ii) * (ii * x) = x) )
            := by
  classical
  intro ii iiSquareMul x
  calc
    (-ii) * (ii * x) = -(ii * (ii * x)) := by rw [neg_mul]
    _ = -(-x) := by rw [iiSquareMul]
    _ = x := by simp

private theorem iiCaseA :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (∀ (x : GaussianInt), -(ii * x) + x = -(ii * x) - ii ^ 2 * x) ) := by
  classical
  intro ii iiSq x
  rw [iiSq]
  ring

private theorem iiCaseB :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (∀ (x : GaussianInt), -(ii * x) + ii ^ 2 * x = -(ii * x) - x) ) := by
  classical
  intro ii iiSq x
  rw [iiSq]
  ring

private theorem iiCaseC :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (∀ (x : GaussianInt), -x + x * ii = x * ii + x * ii ^ 2) ) := by
  classical
  intro ii iiSq x
  rw [iiSq]
  ring

private theorem iiCaseA' :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), (-ii) * (ii * x) = x) → (∀ (x : GaussianInt), x - ii * x = -ii * (x
            + ii * x)) ) := by
  classical
  intro ii iiNegSquareMul x
  rw [mul_add, neg_mul, iiNegSquareMul]
  ring

private theorem iiCaseB' :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), (-ii) * (ii * x) = x) → (∀ (x : GaussianInt), -ii * (x - ii * x) =
            -(x + ii * x)) ) := by
  classical
  intro ii iiNegSquareMul x
  rw [mul_sub, neg_mul, iiNegSquareMul, neg_add]
  ring

private theorem iiCaseC' :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ii * (ii * x) = -x) → (∀ (x : GaussianInt), -(x - ii * x) = ii * (x
            + ii * x)) ) := by
  classical
  intro ii iiSquareMul x
  rw [neg_sub, mul_add, iiSquareMul]
  ring

private theorem iiCaseD' :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ii * (ii * x) = -x) → (∀ (x : GaussianInt), ii * (x - ii * x) = x +
            ii * x) ) := by
  classical
  intro ii iiSquareMul x
  rw [mul_sub, iiSquareMul]
  ring

private theorem iiCaseE :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (∀ (x : GaussianInt), ii * x + ii ^ 2 * x = ii * x - x) ) := by
  classical
  intro ii iiSq x
  rw [iiSq]
  ring

private theorem iiZCaseA :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), (-ii) * (ii * x) = x) → (∀ (x : GaussianInt), -(ii * x) - x = -ii *
            (x - ii * x)) ) := by
  classical
  intro ii iiNegSquareMul x
  rw [mul_sub, neg_mul, iiNegSquareMul]

private theorem iiZCaseB :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), (-ii) * (ii * x) = x) → (∀ (x : GaussianInt), -ii * (x + ii * x) =
            -1 * (ii * x - x)) ) := by
  classical
  intro ii iiNegSquareMul x
  rw [mul_add, neg_mul, iiNegSquareMul]
  simp only [neg_one_mul, neg_sub]
  ring

private theorem iiZCaseC :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ii * (ii * x) = -x) → (∀ (x : GaussianInt), -(-(ii * x) - x) = ii *
            (x - ii * x)) ) := by
  classical
  intro ii iiSquareMul x
  simp only [neg_sub, mul_sub, iiSquareMul]
  ring

private theorem iiZCaseD :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ii * (ii * x) = -x) → (∀ (x : GaussianInt), ii * (x + ii * x) = ii
            * x - x) ) := by
  classical
  intro ii iiSquareMul x
  rw [mul_add, iiSquareMul]
  ring

private theorem iiCube :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (ii ^ 3 = -ii) ) := by
  classical
  intro ii iiSq
  rw [pow_succ, iiSq]
  simp

private theorem iiFourth :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii * ii = -1) → ((ii ^ 3 = -ii) → (ii ^ 4 = 1)) ) := by
  classical
  intro ii iiMul iiCube
  rw [show 4 = 3 + 1 by rfl, pow_succ, iiCube]
  calc
    -ii * ii = -(ii * ii) := by ring
    _ = -(-1) := by rw [iiMul]
    _ = 1 := by norm_num

private theorem negIiSq :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii * ii = -1) → ((-ii) ^ 2 = -1) ) := by
  classical
  intro ii iiMul
  rw [pow_two]
  calc
    (-ii) * (-ii) = ii * ii := by ring
    _ = -1 := iiMul

private theorem negIiCube :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        ((-ii) ^ 2 = -1) → ((-ii) ^ 3 = ii) ) := by
  classical
  intro ii negIiSq
  rw [show 3 = 2 + 1 by rfl, pow_succ, negIiSq]
  simp

private theorem ladd :
    (by
      classical
      exact
        ∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            BandPackingSymmetryVectorAction g₀ (x + y) = BandPackingSymmetryVectorAction g₀ x +
            BandPackingSymmetryVectorAction g₀ y ) := by
  classical
  intro g₀ x y
  induction g₀ generalizing x y with
  | identity => rfl
  | negate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]; abel
  | conjugate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]; abel
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ =>
      simp [BandPackingSymmetryVectorAction, ih₁, ih₂]

private theorem lneg :
    (by
      classical
      exact
        ∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryVectorAction g₀
            (-x) = -BandPackingSymmetryVectorAction g₀ x ) := by
  classical
  intro g₀ x
  induction g₀ generalizing x with
  | identity => rfl
  | negate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
  | conjugate => ext <;> simp [BandPackingSymmetryVectorAction, GaussianReflection]
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ => simp [BandPackingSymmetryVectorAction, ih₁, ih₂]

private theorem lquarter :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryVectorAction g₀
            (-x) = -BandPackingSymmetryVectorAction g₀ x) → (∀ (g₀ : BandPackingSymmetry), ∀ (x :
            GaussianInt), BandPackingSymmetryVectorAction g₀ (ii * x) = if
            BandPackingSymmetryReversesOrientation g₀ then -ii * BandPackingSymmetryVectorAction
            g₀ x else ii * BandPackingSymmetryVectorAction g₀ x) ) := by
  classical
  intro ii lneg g₀ x
  induction g₀ generalizing x with
  | identity => simp [BandPackingSymmetryVectorAction,
      BandPackingSymmetryReversesOrientation, ii]
  | negate => ext <;> simp [BandPackingSymmetryVectorAction,
      BandPackingSymmetryReversesOrientation, GaussianQuarterTurn, ii]
  | conjugate =>
      ext <;> simp [BandPackingSymmetryVectorAction,
        BandPackingSymmetryReversesOrientation, GaussianReflection,
        ii]
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ =>
      change BandPackingSymmetryVectorAction g₁
          (BandPackingSymmetryVectorAction g₂ (ii * x)) =
        if xor (BandPackingSymmetryReversesOrientation g₁)
            (BandPackingSymmetryReversesOrientation g₂) then
          -ii * BandPackingSymmetryVectorAction g₁
            (BandPackingSymmetryVectorAction g₂ x)
        else ii * BandPackingSymmetryVectorAction g₁
            (BandPackingSymmetryVectorAction g₂ x)
      rw [ih₂]
      cases h₁ : BandPackingSymmetryReversesOrientation g₁ <;>
        cases h₂ : BandPackingSymmetryReversesOrientation g₂ <;>
        simp [h₁,
          ih₁, lneg]

private theorem lpow :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryVectorAction g₀
            (ii * x) = if BandPackingSymmetryReversesOrientation g₀ then -ii *
            BandPackingSymmetryVectorAction g₀ x else ii * BandPackingSymmetryVectorAction g₀ x)
            → (∀ (g₀ : BandPackingSymmetry), ∀ (n : Nat), ∀ (x : GaussianInt),
            BandPackingSymmetryVectorAction g₀ (ii ^ n * x) = (if
            BandPackingSymmetryReversesOrientation g₀ then (-ii) ^ n else ii ^ n) *
            BandPackingSymmetryVectorAction g₀ x) ) := by
  classical
  intro ii lquarter g₀ n x
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, lquarter, ih]
      by_cases ho : BandPackingSymmetryReversesOrientation g₀ <;>
        simp [ho, pow_succ, mul_assoc]; ring

private theorem hbackEqual :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (BandVectors.1 (qg k.succ) (qg 0) = BandPackingSymmetryVectorAction g' (BandVectors.1 (r
            i.succ) (r 0))) → ((BandVectors.1 (qg 0) (qg k.succ) = (if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r i.succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r i.succ)))) → (
        let ii : GaussianInt := ⟨0, 1⟩
        (∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), BandPackingSymmetryVectorAction g₀
            (ii * x) = if BandPackingSymmetryReversesOrientation g₀ then -ii *
            BandPackingSymmetryVectorAction g₀ x else ii * BandPackingSymmetryVectorAction g₀ x)
            → ((BandVectors.1 (r 0) (r i.succ) = ii * BandVectors.1 (r i.succ) (r 0)) →
            (BandVectors.1 (qg 0) (qg k.succ) = ii * BandVectors.1 (qg k.succ) (qg 0))))) ) := by
  classical
  intro r i a q g' qg k hvectorForward hvectorBackward ii lquarter hflip
  rw [hvectorBackward, hvectorForward, hflip]
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    simp [ho, lquarter, ii]

private theorem hdispW :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r (if Even (↑s : ℕ) then i - (1 :
            Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) → (((0 : ℤ) < (r (if Even (↑s : ℕ)
            then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ).1) → ((TileCentroid W -
            TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 :
            Fin (4 : ℕ))) (r i.succ)))) → ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ)
            then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) -
            BandVectors.1 (r (i - (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) else
            BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) - BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 : ℕ))).succ))) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (BandVectors.1 (qg k.succ) (qg 0) = BandPackingSymmetryVectorAction g' (BandVectors.1 (r
            i.succ) (r 0))) → ((BandVectors.1 (qg 0) (qg k.succ) = (if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r i.succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r i.succ)))) → ((∀ (s₀ : Fin 4), ((-s₀ - 1 : Fin 4) : Nat) = (3
            - s₀.val) % 4) → (
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → ((∀ (x : GaussianInt), x - ii * x = -ii * (x + ii * x)) → ((∀ (x :
            GaussianInt), -ii * (x - ii * x) = -(x + ii * x)) → ((∀ (x : GaussianInt), -(x - ii *
            x) = ii * (x + ii * x)) → ((∀ (x : GaussianInt), ii * (x - ii * x) = x + ii * x) →
            ((ii ^ 3 = -ii) → (((-ii) ^ 2 = -1) → (((-ii) ^ 3 = ii) → ((∀ (g₀ :
            BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            BandPackingSymmetryVectorAction g₀ (x + y) = BandPackingSymmetryVectorAction g₀ x +
            BandPackingSymmetryVectorAction g₀ y) → ((∀ (g₀ : BandPackingSymmetry), ∀ (n : Nat),
            ∀ (x : GaussianInt), BandPackingSymmetryVectorAction g₀ (ii ^ n * x) = (if
            BandPackingSymmetryReversesOrientation g₀ then (-ii) ^ n else ii ^ n) *
            BandPackingSymmetryVectorAction g₀ x) → (
        let vR := BandVectors.1 (r i.succ) (r 0)
        let vL := BandVectors.1 (r 0) (r i.succ)
        let vR' := BandVectors.1 (qg k.succ) (qg 0)
        let vL' := BandVectors.1 (qg 0) (qg k.succ)
        (vL' = ii * vR') → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        BandPackingSymmetryVectorAction g' (ii ^ s.val * (vR + vL)) = ii ^ t.val * (vR' +
            vL'))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hZ hZpos hWcent hZcent a q g' qg k hvectorForward hvectorBackward hnegVal ii
      iiSq iiCaseA' iiCaseB' iiCaseC' iiCaseD' iiCube negIiSq negIiCube ladd lpow vR vL vR' vL'
      hbackEq' t
  have hvecR : BandPackingSymmetryVectorAction g' vR = vR' := by
    simpa [vR, vR'] using hvectorForward.symm
  have hvecL : BandPackingSymmetryVectorAction g' vL =
      if BandPackingSymmetryReversesOrientation g' then -vL' else vL' := by
    cases ho : BandPackingSymmetryReversesOrientation g'
    · have hb := hvectorBackward
      simp [ho] at hb
      exact hb.symm
    · have hb := hvectorBackward
      simp [ho] at hb
      have hn := congrArg (fun z : GaussianInt => -z) hb.symm
      simpa using hn
  have hsum : BandPackingSymmetryVectorAction g' (vR + vL) =
      if BandPackingSymmetryReversesOrientation g' then vR' - vL'
      else vR' + vL' := by
    rw [ladd, hvecR, hvecL]
    cases BandPackingSymmetryReversesOrientation g' <;> simp; abel
  rw [lpow, hsum]
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    fin_cases s <;>
    simp only [t, ho, hbackEq', hnegVal, ↓reduceIte,
      Bool.false_eq_true] <;>
    (try rw [iiSq]) <;>
    (try simp only [Nat.reduceSub, Nat.reduceMod]) <;>
    (try simp only [iiCube, negIiSq, negIiCube,
      pow_zero, pow_one, one_mul, neg_one_mul])
  all_goals first
    | exact iiCaseA' vR'
    | exact iiCaseB' vR'
    | exact iiCaseC' vR'
    | exact iiCaseD' vR'





private theorem quarterParity :
    (by
      classical
      exact
        (Even 0) → ((Even 2) → ((¬ Even 1) → ((¬ Even 3) → (∀ (s₀ : Fin 4), Even ((-s₀ - 1).val)
            ↔ ¬ Even s₀.val)))) ) := by
  classical
  intro evenZero evenTwo notEvenOne notEvenThree s₀
  fin_cases s₀
  · change Even 3 ↔ ¬ Even 0
    exact ⟨fun h _ => (notEvenThree h).elim, fun h => (h evenZero).elim⟩
  · change Even 2 ↔ ¬ Even 1
    exact ⟨fun _ => notEvenOne, fun _ => evenTwo⟩
  · change Even 1 ↔ ¬ Even 2
    exact ⟨fun h => (notEvenOne h).elim, fun h => (h evenTwo).elim⟩
  · change Even 0 ↔ ¬ Even 3
    exact ⟨fun _ => notEvenThree, fun _ => evenZero⟩

private theorem reversedAdjacent :
    (by
      classical
      exact
        (∀ (s₀ : Fin 4), Even ((-s₀ - 1).val) ↔ ¬ Even s₀.val) → (∀ (a₀ : Fin 3), ∀ (i₀ : Fin 3),
            ∀ (s₀ : Fin 4), (if Even ((-s₀ - 1).val) then -(i₀ - a₀) - 1 else -(i₀ - a₀) + 1) =
            -((if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀)) ) := by
  classical
  intro quarterParity a₀ i₀ s₀
  have hp := quarterParity s₀
  by_cases h : Even s₀.val
  · have hn : ¬ Even (-s₀ - 1).val := by
      intro ht
      exact (hp.mp ht) h
    simp only [Fin.isValue, hn, ↓reduceIte, neg_sub, h]; fin_cases a₀ <;> fin_cases i₀ <;> decide
        +kernel
  · have he : Even (-s₀ - 1).val := hp.mpr h
    simp only [Fin.isValue, he, ↓reduceIte, neg_sub, h]; fin_cases a₀ <;> fin_cases i₀ <;> decide
        +kernel

private theorem normalizedAdjacent :
    (by
      classical
      exact
        (∀ (a₀ : Fin 3), ∀ (i₀ : Fin 3), ∀ (s₀ : Fin 4), (if Even ((-s₀ - 1).val) then -(i₀ - a₀)
            - 1 else -(i₀ - a₀) + 1) = -((if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀)) → (∀
            (rev : Bool), ∀ (a₀ : Fin 3), ∀ (i₀ : Fin 3), ∀ (s₀ : Fin 4),
        let k₀ := if rev then -(i₀ - a₀) else i₀ - a₀
          let t₀ := if rev then -s₀ - 1 else s₀
          (if Even t₀.val then k₀ - 1 else k₀ + 1) =
            if rev then -((if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀)
            else (if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀) ) := by
  classical
  intro reversedAdjacent rev a₀ i₀ s₀
  cases rev
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h : Even s₀.val
    · simp only [h, ↓reduceIte, Fin.isValue]; fin_cases a₀ <;> fin_cases i₀ <;>
        fin_cases s₀ <;> decide +kernel
    · simp only [h, ↓reduceIte, Fin.isValue]; fin_cases a₀ <;> fin_cases i₀ <;>
        fin_cases s₀ <;> decide +kernel
  · simp only [↓reduceIte]
    exact reversedAdjacent a₀ i₀ s₀

private theorem hZindex :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3), ∀ (g' : BandPackingSymmetry),
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        (∀ (rev : Bool), ∀ (a₀ : Fin 3), ∀ (i₀ : Fin 3), ∀ (s₀ : Fin 4),
        let k₀ := if rev then -(i₀ - a₀) else i₀ - a₀
          let t₀ := if rev then -s₀ - 1 else s₀
          (if Even t₀.val then k₀ - 1 else k₀ + 1) =
            if rev then -((if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀)
            else (if Even s₀.val then i₀ - 1 else i₀ + 1) - a₀) → ((if Even t.val then k - 1 else
                k + 1) = if BandPackingSymmetryReversesOrientation g' then -((if Even s.val then
                i - 1 else i + 1) - a) else (if Even s.val then i - 1 else i + 1) - a) ) := by
  classical
  intro i s a g' k t normalizedAdjacent
  exact normalizedAdjacent (BandPackingSymmetryReversesOrientation g') a i s

private theorem hZparentIndex :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3), ∀ (g' : BandPackingSymmetry),
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        ((if Even t.val then k - 1 else k + 1) = if BandPackingSymmetryReversesOrientation g'
            then -((if Even s.val then i - 1 else i + 1) - a) else (if Even s.val then i - 1 else
            i + 1) - a) → (
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        (if BandPackingSymmetryReversesOrientation g' then -j else j) = (if Even s.val then i - 1
            else i + 1) - a) ) := by
  classical
  intro i s a g' k t hZindex j
  cases ho : BandPackingSymmetryReversesOrientation g'
  · simpa [j, ho] using hZindex
  · have hneg := congrArg (fun x : Fin 3 => -x) hZindex
    simpa [j, ho] using hneg

private theorem hZcircle :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (j₀ : Fin 3), q j₀.succ = r (a + j₀).succ) → ((∀ (x : Fin 3), ∀ (y : Fin 3), x + (y -
            x) = y) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        ((if BandPackingSymmetryReversesOrientation g' then -j else j) = (if Even s.val then i -
            1 else i + 1) - a) → (q ((if BandPackingSymmetryReversesOrientation g' then -j else
            j).succ) = r ((if Even s.val then i - 1 else i + 1).succ)))) ) := by
  classical
  intro r i s a q g' k cyclicIndex cyclicCancel t j hZparentIndex
  rw [hZparentIndex, cyclicIndex, cyclicCancel]

private theorem hZlabel :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (j₀ : Fin 3), qg j₀.succ = BandPackingSymmetryCircleAction g' (q ((if
            BandPackingSymmetryReversesOrientation g' then -j₀ else j₀).succ))) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        (q ((if BandPackingSymmetryReversesOrientation g' then -j else j).succ) = r ((if Even
            s.val then i - 1 else i + 1).succ)) → (qg j.succ = BandPackingSymmetryCircleAction g'
            (r ((if Even s.val then i - 1 else i + 1).succ)))) ) := by
  classical
  intro r i s a q g' qg k actionParent t j hZcircle
  rw [actionParent]
  rw [hZcircle]

private theorem hZrel :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3), ∀ (g' : BandPackingSymmetry),
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        ((if BandPackingSymmetryReversesOrientation g' then -j else j) = (if Even s.val then i -
            1 else i + 1) - a) → (
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let mZ : Fin 3 := adj - a
        (if BandPackingSymmetryReversesOrientation g' then -j else j) = mZ) ) := by
  classical
  intro i s a g' k t j hZparentIndex adj mZ
  simpa [mZ, adj] using hZparentIndex

private theorem hZsigma :
    (by
      classical
      exact
        ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3), ∀ (g' : BandPackingSymmetry),
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let mZ : Fin 3 := adj - a
        ((if BandPackingSymmetryReversesOrientation g' then -j else j) = mZ) → ((if
            BandPackingSymmetryReversesOrientation g' then -mZ else mZ) = j) ) := by
  classical
  intro i s a g' k t j adj mZ hZrel
  cases ho : BandPackingSymmetryReversesOrientation g'
  · simpa [ho] using hZrel.symm
  · have hn := congrArg (fun x : Fin 3 => -x) hZrel
    have h' : j = -mZ := by simpa [ho] using hn
    exact h'.symm

private theorem hZphaseForward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (x : Fin 3), ∀ (y : Fin 3), x + (y - x) = y) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), BandVectors.1 (qg (sigma m).succ) (qg 0) =
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r (a + m).succ) (r 0))) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let mZ : Fin 3 := adj - a
        (sigma mZ = j) → (BandVectors.1 (qg j.succ) (qg 0) = BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r adj.succ) (r 0))))) ) := by
  classical
  intro r i s a q g' qg k cyclicCancel sigma hphaseForward t j adj mZ hZsigma'
  have h := hphaseForward mZ
  rw [hZsigma', show a + mZ = adj from cyclicCancel a adj] at h
  exact h

private theorem hZphaseBackward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (x : Fin 3), ∀ (y : Fin 3), x + (y - x) = y) → (
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (∀ (m : Fin 3), BandVectors.1 (qg 0) (qg (sigma m).succ) = (if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r (a + m).succ)))) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let mZ : Fin 3 := adj - a
        (sigma mZ = j) → (BandVectors.1 (qg 0) (qg j.succ) = if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r adj.succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r adj.succ))))) ) := by
  classical
  intro r i s a q g' qg k cyclicCancel sigma hphaseBackward t j adj mZ hZsigma'
  have h := hphaseBackward mZ
  rw [hZsigma', show a + mZ = adj from cyclicCancel a adj] at h
  exact h

private theorem hZactionForward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        (BandVectors.1 (qg j.succ) (qg 0) = BandPackingSymmetryVectorAction g' (BandVectors.1 (r
            adj.succ) (r 0))) → (
        let xZ := BandVectors.1 (r adj.succ) (r 0)
        let xZ' := BandVectors.1 (qg j.succ) (qg 0)
        BandPackingSymmetryVectorAction g' xZ = xZ') ) := by
  classical
  intro r i s a q g' qg k t j adj hZphaseForward xZ xZ'
  simpa [xZ, xZ'] using hZphaseForward.symm

private theorem hZactionBackward :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        (BandVectors.1 (qg 0) (qg j.succ) = if BandPackingSymmetryReversesOrientation g' then
            -BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r adj.succ)) else
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r adj.succ))) → (
        let yZ := BandVectors.1 (r 0) (r adj.succ)
        let yZ' := BandVectors.1 (qg 0) (qg j.succ)
        BandPackingSymmetryVectorAction g' yZ = if BandPackingSymmetryReversesOrientation g' then
            -yZ' else yZ') ) := by
  classical
  intro r i s a q g' qg k t j adj hZphaseBackward yZ yZ'
  cases ho : BandPackingSymmetryReversesOrientation g'
  · have hb := hZphaseBackward
    simp [ho] at hb
    exact hb.symm
  · have hb := hZphaseBackward
    simp [ho] at hb
    have hn := congrArg (fun z : GaussianInt => -z) hb.symm
    simpa using hn

private theorem hZsourceAction :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (∀ (g₀ : BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            BandPackingSymmetryVectorAction g₀ (x + y) = BandPackingSymmetryVectorAction g₀ x +
            BandPackingSymmetryVectorAction g₀ y) → ((∀ (g₀ : BandPackingSymmetry), ∀ (x :
            GaussianInt), BandPackingSymmetryVectorAction g₀ (-x) =
            -BandPackingSymmetryVectorAction g₀ x) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let xZ := BandVectors.1 (r adj.succ) (r 0)
        let yZ := BandVectors.1 (r 0) (r adj.succ)
        let xZ' := BandVectors.1 (qg j.succ) (qg 0)
        let yZ' := BandVectors.1 (qg 0) (qg j.succ)
        (BandPackingSymmetryVectorAction g' xZ = xZ') → ((BandPackingSymmetryVectorAction g' yZ =
            if BandPackingSymmetryReversesOrientation g' then -yZ' else yZ') →
            (BandPackingSymmetryVectorAction g' (if Even s.val then yZ - xZ else xZ - yZ) = if
            Even s.val then (if BandPackingSymmetryReversesOrientation g' then -yZ' - xZ' else
            yZ' - xZ') else (if BandPackingSymmetryReversesOrientation g' then xZ' + yZ' else xZ'
            - yZ'))))) ) := by
  classical
  intro r i s a q g' qg k ladd lneg t j adj xZ yZ xZ' yZ' hZactionForward hZactionBackward
  by_cases he : Even s.val <;>
    cases ho : BandPackingSymmetryReversesOrientation g' <;>
    simp [he, ho, sub_eq_add_neg, ladd, lneg,
      hZactionForward, hZactionBackward]

private theorem hZvec :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (Z : ProtoTile), (BandPrototile (r (if Even (↑s : ℕ) then i - (1 :
            Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ) Z) → (((0 : ℤ) < (r (if Even (↑s : ℕ)
            then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ).1) → ((TileCentroid W -
            TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * (BandVectors.1 (r i.succ) (r (0 : Fin (4 : ℕ))) + BandVectors.1 (r (0 :
            Fin (4 : ℕ))) (r i.succ)))) → ((TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ)
            then BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) -
            BandVectors.1 (r (i - (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) else
            BandVectors.1 (r (i + (1 : Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) - BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r (i + (1 : Fin (3 : ℕ))).succ))) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let sigma : Fin 3 → Fin 3 := fun m =>
          if BandPackingSymmetryReversesOrientation g' then -m else m
        (Even 0) → ((Even 2) → ((¬ Even 1) → ((¬ Even 3) → ((∀ (s₀ : Fin 4), ((-s₀ - 1 : Fin 4) :
            Nat) = (3 - s₀.val) % 4) → (
        let ii : GaussianInt := ⟨0, 1⟩
        (ii * ii = -1) → ((∀ (x : GaussianInt), -(ii * x) - x = -ii * (x - ii * x)) → ((∀ (x :
            GaussianInt), -ii * (x + ii * x) = -1 * (ii * x - x)) → ((∀ (x : GaussianInt), -(-(ii
            * x) - x) = ii * (x - ii * x)) → ((∀ (x : GaussianInt), ii * (x + ii * x) = ii * x -
            x) → ((ii ^ 3 = -ii) → (((-ii) ^ 2 = -1) → (((-ii) ^ 3 = ii) → ((∀ (g₀ :
            BandPackingSymmetry), ∀ (n : Nat), ∀ (x : GaussianInt),
            BandPackingSymmetryVectorAction g₀ (ii ^ n * x) = (if
            BandPackingSymmetryReversesOrientation g₀ then (-ii) ^ n else ii ^ n) *
            BandPackingSymmetryVectorAction g₀ x) → (
        let vR := BandVectors.1 (r i.succ) (r 0)
        let vL := BandVectors.1 (r 0) (r i.succ)
        let vR' := BandVectors.1 (qg k.succ) (qg 0)
        let vL' := BandVectors.1 (qg 0) (qg k.succ)
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        (BandPackingSymmetryVectorAction g' (ii ^ s.val * (vR + vL)) = ii ^ t.val * (vR' + vL'))
            → (((if Even t.val then k - 1 else k + 1) = if BandPackingSymmetryReversesOrientation
            g' then -((if Even s.val then i - 1 else i + 1) - a) else (if Even s.val then i - 1
            else i + 1) - a) → (
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        ((if BandPackingSymmetryReversesOrientation g' then -j else j) = (if Even s.val then i -
            1 else i + 1) - a) → ((q ((if BandPackingSymmetryReversesOrientation g' then -j else
            j).succ) = r ((if Even s.val then i - 1 else i + 1).succ)) → ((qg j.succ =
            BandPackingSymmetryCircleAction g' (r ((if Even s.val then i - 1 else i + 1).succ))) → (
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let mZ : Fin 3 := adj - a
        ((if BandPackingSymmetryReversesOrientation g' then -j else j) = mZ) → (((if
            BandPackingSymmetryReversesOrientation g' then -mZ else mZ) = j) → ((sigma mZ = j) →
            ((BandVectors.1 (qg j.succ) (qg 0) = BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r adj.succ) (r 0))) → ((BandVectors.1 (qg 0) (qg j.succ) = if
            BandPackingSymmetryReversesOrientation g' then -BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r adj.succ)) else BandPackingSymmetryVectorAction g'
            (BandVectors.1 (r 0) (r adj.succ))) → (
        let xZ := BandVectors.1 (r adj.succ) (r 0)
        let yZ := BandVectors.1 (r 0) (r adj.succ)
        let xZ' := BandVectors.1 (qg j.succ) (qg 0)
        let yZ' := BandVectors.1 (qg 0) (qg j.succ)
        (yZ' = ii * xZ') → ((BandPackingSymmetryVectorAction g' xZ = xZ') →
            ((BandPackingSymmetryVectorAction g' yZ = if BandPackingSymmetryReversesOrientation
            g' then -yZ' else yZ') → ((BandPackingSymmetryVectorAction g' (if Even s.val then yZ
            - xZ else xZ - yZ) = if Even s.val then (if BandPackingSymmetryReversesOrientation g'
            then -yZ' - xZ' else yZ' - xZ') else (if BandPackingSymmetryReversesOrientation g'
            then xZ' + yZ' else xZ' - yZ')) → (BandPackingSymmetryVectorAction g' (ii ^ s.val *
            (if Even s.val then yZ - xZ else xZ - yZ)) = ii ^ t.val * (if Even t.val then yZ' -
            xZ' else xZ' - yZ'))))))))))))))))))))))))))))))))) ) := by
  classical
  intro r i s U W Z hZ hZpos hWcent hZcent a q g' qg k sigma evenZero evenTwo notEvenOne
      notEvenThree hnegVal ii iiMul iiZCaseA iiZCaseB iiZCaseC iiZCaseD iiCube negIiSq negIiCube
      lpow vR vL vR' vL' t hdispW hZindex j hZparentIndex hZcircle hZlabel adj mZ hZrel hZsigma
      hZsigma' hZphaseForward hZphaseBackward xZ yZ xZ' yZ' hZflip hZactionForward
      hZactionBackward hZsourceAction
  rw [lpow, hZsourceAction]
  cases ho : BandPackingSymmetryReversesOrientation g' <;>
    fin_cases s <;>
    simp only [t, ho, hZflip, hnegVal, ↓reduceIte,
      Bool.false_eq_true,
      evenZero, evenTwo, notEvenOne, notEvenThree,
      Nat.reduceSub, Nat.reduceMod] <;>
    simp only [iiCube, negIiSq, negIiCube,
      pow_zero, pow_one, one_mul, neg_one_mul] <;>
    (try simp only [pow_two, iiMul])
  all_goals first
    | exact iiZCaseA xZ'
    | exact iiZCaseB xZ'
    | exact iiZCaseC xZ'
    | exact iiZCaseD xZ'

private theorem hZ' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (Z : ProtoTile),
            (BandPrototile (r (if Even (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 :
            ℕ))).succ) Z) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        (qg j.succ = BandPackingSymmetryCircleAction g' (r ((if Even s.val then i - 1 else i +
            1).succ))) → (BandPrototile (qg j.succ) (BandPackingSymmetryTileAction g' Z)))) ) := by
  classical
  intro r i s Z hZ a q g' qg k htileCov t j hZlabel
  let sigma : Fin 3 → Fin 3 := fun m =>
    if BandPackingSymmetryReversesOrientation g' then -m else m
  rw [hZlabel]
  exact (htileCov.2.1
    (r ((if Even s.val then i - 1 else i + 1).succ)) Z).mp hZ

private theorem hUpos' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ((0 : ℤ) < (r (0 : Fin (4 : ℕ))).1) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → ((qg 0 = BandPackingSymmetryCircleAction g' (r 0)) → (0 < (qg 0).1))) )
            := by
  classical
  intro r hUpos a q g' qg htileCov hrootLabel
  let sigma : Fin 3 → Fin 3 := fun m =>
    if BandPackingSymmetryReversesOrientation g' then -m else m
  rw [hrootLabel, htileCov.1]
  exact hUpos

private theorem hWpos' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ((0 : ℤ) < (r i.succ).1) → (∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → ((qg k.succ = BandPackingSymmetryCircleAction g' (r i.succ)) → (0 < (qg
            k.succ).1))) ) := by
  classical
  intro r i hWpos a q g' qg k htileCov hWlabel
  let sigma : Fin 3 → Fin 3 := fun m =>
    if BandPackingSymmetryReversesOrientation g' then -m else m
  rw [hWlabel, htileCov.1]
  exact hWpos

private theorem hZpos' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ((0 : ℤ) < (r (if Even
            (↑s : ℕ) then i - (1 : Fin (3 : ℕ)) else i + (1 : Fin (3 : ℕ))).succ).1) → (∀ (a :
            Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        ((∀ (C : CircleCoordinates), (BandPackingSymmetryCircleAction g' C).1 = C.1) ∧ (∀ (C :
            CircleCoordinates), ∀ (T : ProtoTile), BandPrototile C T ↔ BandPrototile
            (BandPackingSymmetryCircleAction g' C) (BandPackingSymmetryTileAction g' T)) ∧ ∀ (q :
            Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ProperBandQuadruple q → BandPrototile (q (0 : Fin (4 : ℕ))) T → (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence q T i s (S i s)) → (∀ (x :
            LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) →
        let sigma := fun (i : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g' = true
            then -i else i; ∃ (negative : Bool) (e : Fin (3 : ℕ) × Bool ≃ Fin (3 : ℕ) × Bool) (S'
            : Fin (3 : ℕ) → Bool → ProtoTile), BandPackingSymmetryScopedPhase g' q negative ∧ (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), (e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)
            = (sigma i, s ^^ negative)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), S' ((e : Fin (3 :
            ℕ) × Bool → Fin (3 : ℕ) × Bool) (i, s)).1 ((e : Fin (3 : ℕ) × Bool → Fin (3 : ℕ) ×
            Bool) (i, s)).2 = BandPackingSymmetryTileAction g' (S i s)) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (s : Bool), BandSubtileOccurrence (BandPackingSymmetryQuadrupleAction g' q)
            (BandPackingSymmetryTileAction g' T) i s (S' i s)) ∧ ∀ (x : LatticeCell), x ∈
            (BandPackingSymmetryTileAction g' T).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S'
            i s).cells) → (
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        (qg j.succ = BandPackingSymmetryCircleAction g' (r ((if Even s.val then i - 1 else i +
            1).succ))) → (0 < (qg j.succ).1))) ) := by
  classical
  intro r i s hZpos a q g' qg k htileCov t j hZlabel
  let sigma : Fin 3 → Fin 3 := fun m =>
    if BandPackingSymmetryReversesOrientation g' then -m else m
  rw [hZlabel, htileCov.1]
  exact hZpos

private theorem rsub :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (g₀ : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (q₀ : Real × Real), R g₀ (p - q₀) =
            R g₀ p - R g₀ q₀ ) := by
  classical
  intro R g₀ p q₀
  induction g₀ generalizing p q₀ with
  | identity => rfl
  | negate => ext <;> simp [R]; ring
  | conjugate => ext <;> simp [R]; ring
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ => simp [R, ih₁, ih₂]

private theorem rsmul :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (g₀ : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real × Real), R g₀ (c • p) = c • R g₀
            p ) := by
  classical
  intro R g₀ c p
  induction g₀ generalizing c p with
  | identity => rfl
  | negate => ext <;> simp [R]
  | conjugate => ext <;> simp [R]
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ => simp [R, ih₁, ih₂]

private theorem rpoint :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (g₀ : BandPackingSymmetry), ∀ (v : GaussianInt), R g₀ (GaussianRealPoint v) =
            GaussianRealPoint (BandPackingSymmetryVectorAction g₀ v) ) := by
  classical
  intro R g₀ v
  induction g₀ generalizing v with
  | identity => rfl
  | negate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianQuarterTurn]
  | conjugate => simp [R, BandPackingSymmetryVectorAction, GaussianRealPoint,
      GaussianReflection]
  | shift w => rfl
  | comp g₁ g₂ ih₁ ih₂ =>
      simp [R, BandPackingSymmetryVectorAction, ih₁, ih₂]

private theorem rcentroid :
    (by
      classical
      exact
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        ∀ (g₀ : BandPackingSymmetry), ∀ (T₀ : ProtoTile), TileCentroid
            (BandPackingSymmetryTileAction g₀ T₀) = R g₀ (TileCentroid T₀) ) := by
  classical
  intro R g₀ T₀
  induction g₀ generalizing T₀ with
  | identity => rfl
  | shift w => rfl
  | negate => exact (TileQuarterTurnFormulas T₀).2.2.2.2.1
  | conjugate =>
      simp [BandPackingSymmetryTileAction, R,
        (TileQuarterTurnFormulas _).2.2.2.2.1,
        (TileReflectionFormulas _).2.2.2.2.1]
  | comp g₁ g₂ ih₁ ih₂ =>
      simp [BandPackingSymmetryTileAction, R, ih₁, ih₂]

private theorem hWcent' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), (TileCentroid W - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (r i.succ) (r (0 :
            Fin (4 : ℕ))) + BandVectors.1 (r (0 : Fin (4 : ℕ))) (r i.succ)))) → (∀ (g' :
            BandPackingSymmetry),
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (g₀ : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (q₀ : Real × Real), R g₀ (p - q₀) =
            R g₀ p - R g₀ q₀) → ((∀ (g₀ : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real ×
            Real), R g₀ (c • p) = c • R g₀ p) → ((∀ (g₀ : BandPackingSymmetry), ∀ (v :
            GaussianInt), R g₀ (GaussianRealPoint v) = GaussianRealPoint
            (BandPackingSymmetryVectorAction g₀ v)) → ((∀ (g₀ : BandPackingSymmetry), ∀ (T₀ :
            ProtoTile), TileCentroid (BandPackingSymmetryTileAction g₀ T₀) = R g₀ (TileCentroid
            T₀)) → (TileCentroid (BandPackingSymmetryTileAction g' W) - TileCentroid
            (BandPackingSymmetryTileAction g' U) = (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))))))) ) := by
  classical
  intro r i s U W hWcent g' R rsub rsmul rpoint rcentroid
  rw [rcentroid, rcentroid, ← rsub, ← rpoint, ← rsmul]
  exact congrArg (R g') hWcent

private theorem hZcent' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (Z
            : ProtoTile), (TileCentroid Z - TileCentroid U = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (r (0 : Fin (4 : ℕ))) (r (i - (1 : Fin (3 : ℕ))).succ) - BandVectors.1 (r (i - (1 :
            Fin (3 : ℕ))).succ) (r (0 : Fin (4 : ℕ))) else BandVectors.1 (r (i + (1 : Fin (3 :
            ℕ))).succ) (r (0 : Fin (4 : ℕ))) - BandVectors.1 (r (0 : Fin (4 : ℕ))) (r (i + (1 :
            Fin (3 : ℕ))).succ))) → (∀ (g' : BandPackingSymmetry),
        let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
          BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
            (fun p => (-p.1, p.2)) (fun _ p => p)
            (fun _ _ f k p => f (k p))
        (∀ (g₀ : BandPackingSymmetry), ∀ (p : Real × Real), ∀ (q₀ : Real × Real), R g₀ (p - q₀) =
            R g₀ p - R g₀ q₀) → ((∀ (g₀ : BandPackingSymmetry), ∀ (c : Real), ∀ (p : Real ×
            Real), R g₀ (c • p) = c • R g₀ p) → ((∀ (g₀ : BandPackingSymmetry), ∀ (v :
            GaussianInt), R g₀ (GaussianRealPoint v) = GaussianRealPoint
            (BandPackingSymmetryVectorAction g₀ v)) → ((∀ (g₀ : BandPackingSymmetry), ∀ (T₀ :
            ProtoTile), TileCentroid (BandPackingSymmetryTileAction g₀ T₀) = R g₀ (TileCentroid
            T₀)) → (TileCentroid (BandPackingSymmetryTileAction g' Z) - TileCentroid
            (BandPackingSymmetryTileAction g' U) = (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val * (if Even s.val
            then BandVectors.1 (r 0) (r ((i - 1).succ)) - BandVectors.1 (r ((i - 1).succ)) (r 0)
            else BandVectors.1 (r ((i + 1).succ)) (r 0) - BandVectors.1 (r 0) (r ((i +
            1).succ)))))))))) ) := by
  classical
  intro r i s U Z hZcent g' R rsub rsmul rpoint rcentroid
  rw [rcentroid, rcentroid, ← rsub, ← rpoint, ← rsmul]
  exact congrArg (R g') hZcent

private theorem hWvec :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let ii : GaussianInt := ⟨0, 1⟩
        let vR := BandVectors.1 (r i.succ) (r 0)
        let vL := BandVectors.1 (r 0) (r i.succ)
        let vR' := BandVectors.1 (qg k.succ) (qg 0)
        let vL' := BandVectors.1 (qg 0) (qg k.succ)
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        (BandPackingSymmetryVectorAction g' (ii ^ s.val * (vR + vL)) = ii ^ t.val * (vR' + vL'))
            → (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) = ii ^ t.val *
            (BandVectors.1 (qg k.succ) (qg 0) + BandVectors.1 (qg 0) (qg k.succ))) ) := by
  classical
  intro r i s a q g' qg k ii vR vL vR' vL' t hdispW
  simpa [ii, vR, vL, vR', vL'] using hdispW

private theorem hWcentNorm :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (W
            : ProtoTile), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let ii : GaussianInt := ⟨0, 1⟩
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        (TileCentroid (BandPackingSymmetryTileAction g' W) - TileCentroid
            (BandPackingSymmetryTileAction g' U) = (1 / 2 : Real) • GaussianRealPoint
            (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))))) →
            ((BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val * (BandVectors.1
            (r i.succ) (r 0) + BandVectors.1 (r 0) (r i.succ))) = ii ^ t.val * (BandVectors.1 (qg
            k.succ) (qg 0) + BandVectors.1 (qg 0) (qg k.succ))) → (TileCentroid
            (BandPackingSymmetryTileAction g' W) - TileCentroid (BandPackingSymmetryTileAction g'
            U) = (1 / 2 : Real) • GaussianRealPoint (ii ^ t.val * (BandVectors.1 (qg k.succ) (qg
            0) + BandVectors.1 (qg 0) (qg k.succ))))) ) := by
  classical
  intro r i s U W a q g' qg k ii t hWcent' hWvec
  rw [hWvec] at hWcent'
  exact hWcent'

private theorem hZvec' :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let ii : GaussianInt := ⟨0, 1⟩
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let xZ := BandVectors.1 (r adj.succ) (r 0)
        let yZ := BandVectors.1 (r 0) (r adj.succ)
        let xZ' := BandVectors.1 (qg j.succ) (qg 0)
        let yZ' := BandVectors.1 (qg 0) (qg j.succ)
        (BandPackingSymmetryVectorAction g' (ii ^ s.val * (if Even s.val then yZ - xZ else xZ -
            yZ)) = ii ^ t.val * (if Even t.val then yZ' - xZ' else xZ' - yZ')) →
            (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩ : GaussianInt) ^ s.val * (if Even s.val
            then BandVectors.1 (r 0) (r adj.succ) - BandVectors.1 (r adj.succ) (r 0) else
            BandVectors.1 (r adj.succ) (r 0) - BandVectors.1 (r 0) (r adj.succ))) = ii ^ t.val *
            (if Even t.val then BandVectors.1 (qg 0) (qg j.succ) - BandVectors.1 (qg j.succ) (qg
            0) else BandVectors.1 (qg j.succ) (qg 0) - BandVectors.1 (qg 0) (qg j.succ))) ) := by
  classical
  intro r i s a q g' qg k ii t j adj xZ yZ xZ' yZ' hZvec
  simpa [ii, adj, xZ, yZ, xZ', yZ'] using hZvec

private theorem hZcentNorm :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (s : Fin 4), ∀ (U : ProtoTile), ∀ (Z
            : ProtoTile), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        let ii : GaussianInt := ⟨0, 1⟩
        let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
          then -s - 1 else s
        let j : Fin 3 := if Even t.val then k - 1 else k + 1
        let adj : Fin 3 := if Even s.val then i - 1 else i + 1
        let xZ := BandVectors.1 (r adj.succ) (r 0)
        let yZ := BandVectors.1 (r 0) (r adj.succ)
        let xZ' := BandVectors.1 (qg j.succ) (qg 0)
        let yZ' := BandVectors.1 (qg 0) (qg j.succ)
        (BandPackingSymmetryVectorAction g' (ii ^ s.val * (if Even s.val then yZ - xZ else xZ -
            yZ)) = ii ^ t.val * (if Even t.val then yZ' - xZ' else xZ' - yZ')) → ((TileCentroid
            (BandPackingSymmetryTileAction g' Z) - TileCentroid (BandPackingSymmetryTileAction g'
            U) = (1 / 2 : Real) • GaussianRealPoint (BandPackingSymmetryVectorAction g' ((⟨0, 1⟩
            : GaussianInt) ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r ((i - 1).succ)) -
            BandVectors.1 (r ((i - 1).succ)) (r 0) else BandVectors.1 (r ((i + 1).succ)) (r 0) -
            BandVectors.1 (r 0) (r ((i + 1).succ)))))) → (TileCentroid
            (BandPackingSymmetryTileAction g' Z) - TileCentroid (BandPackingSymmetryTileAction g'
            U) = (1 / 2 : Real) • GaussianRealPoint (ii ^ t.val * (if Even t.val then
            BandVectors.1 (qg 0) (qg j.succ) - BandVectors.1 (qg j.succ) (qg 0) else
            BandVectors.1 (qg j.succ) (qg 0) - BandVectors.1 (qg 0) (qg j.succ))))) ) := by
  classical
  intro r i s U Z a q g' qg k ii t j adj xZ yZ xZ' yZ' hZvec hZcent'
  have hZvec'' : BandPackingSymmetryVectorAction g'
      ((⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then
          BandVectors.1 (r 0) (r ((i - 1).succ)) -
            BandVectors.1 (r ((i - 1).succ)) (r 0)
        else
          BandVectors.1 (r ((i + 1).succ)) (r 0) -
            BandVectors.1 (r 0) (r ((i + 1).succ)))) =
      ii ^ t.val * (if Even t.val then
        BandVectors.1 (qg 0) (qg j.succ) - BandVectors.1 (qg j.succ) (qg 0)
      else BandVectors.1 (qg j.succ) (qg 0) - BandVectors.1 (qg 0) (qg j.succ)) := by
    by_cases he : Even s.val
    · simpa [he, adj, ii, xZ, yZ, xZ', yZ'] using hZvec
    · simpa [he, adj, ii, xZ, yZ, xZ', yZ'] using hZvec
  rw [hZvec''] at hZcent'
  simpa [adj] using hZcent'

private theorem hvL :
    (by
      classical
      exact
        ∀ (r : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (a : Fin 3),
        let q : Fin 4 → CircleCoordinates :=
          ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
        ∀ (g' : BandPackingSymmetry),
        let qg := BandPackingSymmetryQuadrupleAction g' q
        let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
          then -(i - a) else i - a
        (BandVectors.1 (qg 0) (qg k.succ) = (if BandPackingSymmetryReversesOrientation g' then
            -BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r i.succ)) else
            BandPackingSymmetryVectorAction g' (BandVectors.1 (r 0) (r i.succ)))) → (
        let vL := BandVectors.1 (r 0) (r i.succ)
        let vL' := BandVectors.1 (qg 0) (qg k.succ)
        BandPackingSymmetryVectorAction g' vL = if BandPackingSymmetryReversesOrientation g' then
            -vL' else vL') ) := by
  classical
  intro r i a q g' qg k hvectorBackward vL vL'
  cases ho : BandPackingSymmetryReversesOrientation g'
  · simpa [ho, vL, vL'] using hvectorBackward.symm
  · have h := congrArg (fun z : GaussianInt => -z) hvectorBackward.symm
    simpa [ho, vL, vL'] using h

private theorem hdR :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)) (a : Fin (3 : ℕ)),
          let q :=
            ![r (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ,
              r (a + (2 : Fin (3 : ℕ))).succ];
          ∀ (g' : BandPackingSymmetry),
            let qg := BandPackingSymmetryQuadrupleAction g' q;
            let k :=
              if
                  BandPackingSymmetryReversesOrientation g' =
                    true then
                -(i - a)
              else i - a;
            Even (0 : ℕ) →
              Even (2 : ℕ) →
                ¬Even (1 : ℕ) →
                  ¬Even (3 : ℕ) →
                    (∀ (s₀ : Fin (4 : ℕ)),
                        (↑(-s₀ - (1 : Fin (4 : ℕ))) : ℕ) =
                          ((3 : ℕ) - (↑s₀ : ℕ)) % (4 : ℕ)) →
                      let ii := { re := (0 : ℤ), im := (1 : ℤ) };
                      ii ^ (2 : ℕ) = (-1 : GaussianInt) →
                        ii ^ (3 : ℕ) = -ii →
                          (-ii) ^ (2 : ℕ) = (-1 : GaussianInt) →
                            (-ii) ^ (3 : ℕ) = ii →
                              (∀ (g₀ : BandPackingSymmetry)
                                  (n : ℕ) (x : GaussianInt),
                                  BandPackingSymmetryVectorAction
                                      g₀ (ii ^ n * x) =
                                    (if
                                          BandPackingSymmetryReversesOrientation
                                              g₀ =
                                            true then
                                        (-ii) ^ n
                                      else ii ^ n) *
                                      BandPackingSymmetryVectorAction
                                        g₀ x) →
                                let vR :=
                                  BandVectors.1 (r i.succ)
                                    (r (0 : Fin (4 : ℕ)));
                                let vL :=
                                  BandVectors.1
                                    (r (0 : Fin (4 : ℕ))) (r i.succ);
                                let vR' :=
                                  BandVectors.1 (qg k.succ)
                                    (qg (0 : Fin (4 : ℕ)));
                                let vL' :=
                                  BandVectors.1
                                    (qg (0 : Fin (4 : ℕ))) (qg k.succ);
                                vL' = ii * vR' →
                                  let t :=
                                    if
                                        BandPackingSymmetryReversesOrientation
                                            g' =
                                          true then
                                      -s - (1 : Fin (4 : ℕ))
                                    else s;
                                  BandPackingSymmetryVectorAction
                                        g' vR =
                                      vR' →
                                    (BandPackingSymmetryVectorAction
                                          g' vL =
                                        if
                                            BandPackingSymmetryReversesOrientation
                                                g' =
                                              true then
                                          -vL'
                                        else vL') →
                                      BandPackingSymmetryVectorAction
                                          g'
                                          (ii ^ (↑s : ℕ) *
                                            if Even (↑s : ℕ) then vL else vR) =
                                        ii ^ (↑t : ℕ) *
                                          if Even (↑t : ℕ) then vL' else vR') := by
  classical
  intro r i s a q g' qg k evenZero evenTwo notEvenOne notEvenThree hnegVal ii iiSq iiCube
      negIiSq negIiCube lpow vR vL vR' vL' hbackEq' t hvR hvL
  rw [lpow]
  cases ho : BandPackingSymmetryReversesOrientation g' <;> fin_cases s <;>
    simp [t, ho, evenZero, evenTwo, notEvenOne, notEvenThree,
      hvR, hvL, hbackEq', hnegVal, iiSq, iiCube, negIiSq, negIiCube];


private theorem hdL :
    (by
      classical
      exact
        ∀ (r : Fin (4 : ℕ) → CircleCoordinates)
          (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)) (a : Fin (3 : ℕ)),
          let q :=
            ![r (0 : Fin (4 : ℕ)), r a.succ, r (a + (1 : Fin (3 : ℕ))).succ,
              r (a + (2 : Fin (3 : ℕ))).succ];
          ∀ (g' : BandPackingSymmetry),
            let qg := BandPackingSymmetryQuadrupleAction g' q;
            let k :=
              if
                  BandPackingSymmetryReversesOrientation g' =
                    true then
                -(i - a)
              else i - a;
            Even (0 : ℕ) →
              Even (2 : ℕ) →
                ¬Even (1 : ℕ) →
                  ¬Even (3 : ℕ) →
                    (∀ (s₀ : Fin (4 : ℕ)),
                        (↑(-s₀ - (1 : Fin (4 : ℕ))) : ℕ) =
                          ((3 : ℕ) - (↑s₀ : ℕ)) % (4 : ℕ)) →
                      let ii := { re := (0 : ℤ), im := (1 : ℤ) };
                      ii ^ (2 : ℕ) = (-1 : GaussianInt) →
                        ii ^ (3 : ℕ) = -ii →
                          (-ii) ^ (2 : ℕ) = (-1 : GaussianInt) →
                            (-ii) ^ (3 : ℕ) = ii →
                              (∀ (g₀ : BandPackingSymmetry)
                                  (n : ℕ) (x : GaussianInt),
                                  BandPackingSymmetryVectorAction
                                      g₀ (ii ^ n * x) =
                                    (if
                                          BandPackingSymmetryReversesOrientation
                                              g₀ =
                                            true then
                                        (-ii) ^ n
                                      else ii ^ n) *
                                      BandPackingSymmetryVectorAction
                                        g₀ x) →
                                let vR :=
                                  BandVectors.1 (r i.succ)
                                    (r (0 : Fin (4 : ℕ)));
                                let vL :=
                                  BandVectors.1
                                    (r (0 : Fin (4 : ℕ))) (r i.succ);
                                let vR' :=
                                  BandVectors.1 (qg k.succ)
                                    (qg (0 : Fin (4 : ℕ)));
                                let vL' :=
                                  BandVectors.1
                                    (qg (0 : Fin (4 : ℕ))) (qg k.succ);
                                vL' = ii * vR' →
                                  let t :=
                                    if
                                        BandPackingSymmetryReversesOrientation
                                            g' =
                                          true then
                                      -s - (1 : Fin (4 : ℕ))
                                    else s;
                                  BandPackingSymmetryVectorAction
                                        g' vR =
                                      vR' →
                                    (BandPackingSymmetryVectorAction
                                          g' vL =
                                        if
                                            BandPackingSymmetryReversesOrientation
                                                g' =
                                              true then
                                          -vL'
                                        else vL') →
                                      BandPackingSymmetryVectorAction
                                          g'
                                          (ii ^ (↑s : ℕ) *
                                            if Even (↑s : ℕ) then vR else vL) =
                                        ii ^ (↑t : ℕ) *
                                          if Even (↑t : ℕ) then vR' else vL') := by
  classical
  intro r i s a q g' qg k evenZero evenTwo notEvenOne notEvenThree hnegVal ii iiSq iiCube
      negIiSq negIiCube lpow vR vL vR' vL' hbackEq' t hvR hvL
  rw [lpow]
  cases ho : BandPackingSymmetryReversesOrientation g' <;> fin_cases s <;>
    simp [t, ho, evenZero, evenTwo, notEvenOne, notEvenThree,
      hvR, hvL, hbackEq', hnegVal, iiSq, iiCube, negIiSq, negIiCube] <;>
    ring_nf <;> simp only [iiSq, neg_one_mul, neg_neg]; ring

end PlacementNormalizationProof

theorem P4055T1PlacementNormalization
    (r : Fin 4 → CircleCoordinates) (hproper : ProperBandQuadruple r)
    (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile)
    (hU : BandPrototile (r 0) U)
    (hW : BandPrototile (r i.succ) W)
    (hZ : BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Z)
    (hUpos : 0 < (r 0).1) (hWpos : 0 < (r i.succ).1)
    (hZpos : 0 < (r ((if Even s.val then i - 1 else i + 1).succ)).1)
    (hWcent : TileCentroid W - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ))))
    (hZcent : TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (r 0) (r ((i - 1).succ)) -
              BandVectors.1 (r ((i - 1).succ)) (r 0)
          else
            BandVectors.1 (r ((i + 1).succ)) (r 0) -
              BandVectors.1 (r 0) (r ((i + 1).succ)))))
    (a : Fin 3) (g : BandPackingSymmetry) :
    ∃ g' : BandPackingSymmetry,
      (∀ p, BandPackingSymmetryQuadrupleAction g' p =
        BandPackingSymmetryQuadrupleAction g p) ∧
      let qg := BandPackingSymmetryQuadrupleAction g'
        ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
      let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
        then -(i - a) else i - a
      let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
        then -s - 1 else s
      let j : Fin 3 := if Even t.val then k - 1 else k + 1
      let U' := BandPackingSymmetryTileAction g' U
      let W' := BandPackingSymmetryTileAction g' W
      let Z' := BandPackingSymmetryTileAction g' Z
      let ii : GaussianInt := ⟨0, 1⟩
      ProperBandQuadruple qg ∧
      BandPrototile (qg 0) U' ∧ BandPrototile (qg k.succ) W' ∧
      BandPrototile (qg j.succ) Z' ∧
      0 < (qg 0).1 ∧ 0 < (qg k.succ).1 ∧ 0 < (qg j.succ).1 ∧
      TileCentroid W' - TileCentroid U' = (1 / 2 : Real) •
        GaussianRealPoint (ii ^ t.val *
          (BandVectors.1 (qg k.succ) (qg 0) + BandVectors.1 (qg 0) (qg k.succ))) ∧
      TileCentroid Z' - TileCentroid U' = (1 / 2 : Real) •
        GaussianRealPoint (ii ^ t.val * (if Even t.val then
          BandVectors.1 (qg 0) (qg j.succ) - BandVectors.1 (qg j.succ) (qg 0)
        else BandVectors.1 (qg j.succ) (qg 0) - BandVectors.1 (qg 0) (qg j.succ))) ∧
      BandPackingSymmetryVectorAction g'
        (ii ^ s.val * (if Even s.val then BandVectors.1 (r 0) (r i.succ)
          else BandVectors.1 (r i.succ) (r 0))) =
        ii ^ t.val * (if Even t.val then BandVectors.1 (qg 0) (qg k.succ)
          else BandVectors.1 (qg k.succ) (qg 0)) ∧
      BandPackingSymmetryVectorAction g'
        (ii ^ s.val * (if Even s.val then BandVectors.1 (r i.succ) (r 0)
          else BandVectors.1 (r 0) (r i.succ))) =
        ii ^ t.val * (if Even t.val then BandVectors.1 (qg k.succ) (qg 0)
          else BandVectors.1 (qg 0) (qg k.succ)) := by
-- BODY
  classical
  let q : Fin 4 → CircleCoordinates :=
    ![r 0, r a.succ, r (a + 1).succ, r (a + 2).succ]
  have hq := PlacementNormalizationProof.hq r hproper a
  have hprojective := BandPackingSymmetryProjectiveVectorCovariance g q hq
  dsimp at hprojective
  rcases hprojective with ⟨negative, hphase, hphase1, hphase2, hcircle,
    horient', hquad, hvec, g', hglift, hcircle', horientg, hquadg, hfalse,
    hfalse1, hfalse2⟩
  let qg := BandPackingSymmetryQuadrupleAction g' q
  let k : Fin 3 := if BandPackingSymmetryReversesOrientation g'
    then -(i - a) else i - a
  have hproperG : ProperBandQuadruple qg :=
    BandPackingSymmetryProperCovariance g' q hq
  have htileCov := BandPackingSymmetryCovariance g'
  let U' : ProtoTile := BandPackingSymmetryTileAction g' U
  let W' : ProtoTile := BandPackingSymmetryTileAction g' W
  let Z' : ProtoTile := BandPackingSymmetryTileAction g' Z
  have hU' := PlacementNormalizationProof.hU' r U hU a g g' horientg htileCov
  have hWlabel := PlacementNormalizationProof.hWlabel r i
      a g'
  have cyclicIndex (j₀ : Fin 3) := PlacementNormalizationProof.cyclicIndex r a j₀
  have cyclicCancel (x y : Fin 3) : x + (y - x) = y := by
    fin_cases x <;> fin_cases y <;> decide +kernel
  have actionParent (j₀ : Fin 3) := PlacementNormalizationProof.actionParent r a g' j₀
  have hrootLabel : qg 0 = BandPackingSymmetryCircleAction g' (r 0) := by
    simp [qg, q, BandPackingSymmetryQuadrupleAction]
  have hW' := PlacementNormalizationProof.hW' r i W hW a g' htileCov hWlabel
  let sigma : Fin 3 → Fin 3 := fun m =>
    if BandPackingSymmetryReversesOrientation g' then -m else m
  have hparent (m : Fin 3) := PlacementNormalizationProof.hparent r a g' cyclicIndex actionParent m
  have hparentAction (m : Fin 3) := PlacementNormalizationProof.hparentAction r a g' hparent m
  have hrootAction := PlacementNormalizationProof.hrootAction r a g' hrootLabel
  have hphaseForward (m : Fin 3) := PlacementNormalizationProof.hphaseForward r a g' hfalse
      cyclicIndex hrootLabel hparent hparentAction hrootAction m
  have hphaseBackward (m : Fin 3) := PlacementNormalizationProof.hphaseBackward r a g' hfalse
      cyclicIndex hrootLabel hparent hparentAction hrootAction m
  have hk : sigma (i - a) = k := by rfl
  have hvectorForward :
      BandVectors.1 (qg k.succ) (qg 0) =
        BandPackingSymmetryVectorAction g'
          (BandVectors.1 (r i.succ) (r 0)) := PlacementNormalizationProof.hvectorForward r i a g'
              cyclicCancel hphaseForward hk
  have hvectorBackward := PlacementNormalizationProof.hvectorBackward r i a g' cyclicCancel
      hphaseBackward hk
  have evenZero : Even 0 := ⟨0, by decide⟩
  have evenTwo : Even 2 := ⟨1, by decide⟩
  have notEvenOne := PlacementNormalizationProof.notEvenOne r i s a g'
  have notEvenThree := PlacementNormalizationProof.notEvenThree r i s a g'
  have hnegVal (s₀ : Fin 4) := PlacementNormalizationProof.hnegVal s₀
  let ii : GaussianInt := ⟨0, 1⟩
  have iiSq : ii ^ 2 = -1 := by decide +kernel
  have iiSqLiteral : (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 := by decide +kernel
  have iiMul : ii * ii = -1 := by simpa [pow_two] using iiSq
  have iiCancel (x : GaussianInt) := PlacementNormalizationProof.iiCancel iiSq x
  have iiCancelLiteral (x : GaussianInt) := PlacementNormalizationProof.iiCancelLiteral
      iiSqLiteral x
  have iiSquareMul (x : GaussianInt) := PlacementNormalizationProof.iiSquareMul iiMul x
  have iiNegSquareMul (x : GaussianInt) := PlacementNormalizationProof.iiNegSquareMul iiSquareMul x
  have iiCaseA (x : GaussianInt) := PlacementNormalizationProof.iiCaseA iiSq x
  have iiCaseB (x : GaussianInt) := PlacementNormalizationProof.iiCaseB iiSq x
  have iiCaseC (x : GaussianInt) := PlacementNormalizationProof.iiCaseC iiSq x
  have iiCaseA' (x : GaussianInt) := PlacementNormalizationProof.iiCaseA' iiNegSquareMul x
  have iiCaseB' (x : GaussianInt) := PlacementNormalizationProof.iiCaseB' iiNegSquareMul x
  have iiCaseC' (x : GaussianInt) := PlacementNormalizationProof.iiCaseC' iiSquareMul x
  have iiCaseD' (x : GaussianInt) := PlacementNormalizationProof.iiCaseD' iiSquareMul x
  have iiCaseE (x : GaussianInt) := PlacementNormalizationProof.iiCaseE iiSq x
  have iiZCaseA (x : GaussianInt) := PlacementNormalizationProof.iiZCaseA iiNegSquareMul x
  have iiZCaseB (x : GaussianInt) := PlacementNormalizationProof.iiZCaseB iiNegSquareMul x
  have iiZCaseC (x : GaussianInt) := PlacementNormalizationProof.iiZCaseC iiSquareMul x
  have iiZCaseD (x : GaussianInt) := PlacementNormalizationProof.iiZCaseD iiSquareMul x
  have iiCube := PlacementNormalizationProof.iiCube iiSq
  have iiFourth := PlacementNormalizationProof.iiFourth iiMul iiCube
  have negIiSq := PlacementNormalizationProof.negIiSq iiMul
  have negIiCube := PlacementNormalizationProof.negIiCube negIiSq
  have ladd (g₀ : BandPackingSymmetry) (x y : GaussianInt) := PlacementNormalizationProof.ladd g₀
      x y
  have lneg (g₀ : BandPackingSymmetry) (x : GaussianInt) := PlacementNormalizationProof.lneg g₀ x
  have lquarter (g₀ : BandPackingSymmetry) (x : GaussianInt) :=
      PlacementNormalizationProof.lquarter lneg g₀ x
  have lpow (g₀ : BandPackingSymmetry) (n : Nat) (x : GaussianInt) :=
      PlacementNormalizationProof.lpow lquarter g₀ n x
  have hflip : BandVectors.1 (r 0) (r i.succ) =
      ii * BandVectors.1 (r i.succ) (r 0) :=
    ((VectorRecursionLaws r hproper.1).2.2.2.2 hproper i).1
  have hbackEqual : BandVectors.1 (qg 0) (qg k.succ) =
      ii * BandVectors.1 (qg k.succ) (qg 0) := PlacementNormalizationProof.hbackEqual r i a g'
          hvectorForward hvectorBackward lquarter hflip
  let vR := BandVectors.1 (r i.succ) (r 0)
  let vL := BandVectors.1 (r 0) (r i.succ)
  let vR' := BandVectors.1 (qg k.succ) (qg 0)
  let vL' := BandVectors.1 (qg 0) (qg k.succ)
  have hbackEq' : vL' = ii * vR' := by
    simpa [vR', vL'] using hbackEqual
  let t : Fin 4 := if BandPackingSymmetryReversesOrientation g'
    then -s - 1 else s
  have hdispW := PlacementNormalizationProof.hdispW r i s U W Z hZ hZpos hWcent hZcent a g'
      hvectorForward hvectorBackward hnegVal iiSq iiCaseA' iiCaseB' iiCaseC' iiCaseD' iiCube
      negIiSq negIiCube ladd lpow hbackEq'
  have quarterParity (s₀ : Fin 4) := PlacementNormalizationProof.quarterParity evenZero evenTwo
      notEvenOne notEvenThree s₀
  have reversedAdjacent (a₀ i₀ : Fin 3) (s₀ : Fin 4) :=
      PlacementNormalizationProof.reversedAdjacent quarterParity a₀ i₀ s₀
  have normalizedAdjacent (rev : Bool) (a₀ i₀ : Fin 3) (s₀ : Fin 4) :=
      PlacementNormalizationProof.normalizedAdjacent reversedAdjacent rev a₀ i₀ s₀
  have hZindex := PlacementNormalizationProof.hZindex i s a g' normalizedAdjacent
  let j : Fin 3 := if Even t.val then k - 1 else k + 1
  have hZparentIndex := PlacementNormalizationProof.hZparentIndex i s a g' hZindex
  have hZcircle := PlacementNormalizationProof.hZcircle r i s a g' cyclicIndex cyclicCancel
      hZparentIndex
  have hZlabel := PlacementNormalizationProof.hZlabel r i s a g' actionParent hZcircle
  let adj : Fin 3 := if Even s.val then i - 1 else i + 1
  let mZ : Fin 3 := adj - a
  have hZrel := PlacementNormalizationProof.hZrel i s a g' hZparentIndex
  have hZsigma :
      (if BandPackingSymmetryReversesOrientation g' then -mZ else mZ) = j :=
          PlacementNormalizationProof.hZsigma i s a g' hZrel
  have hZsigma' : sigma mZ = j := by
    simpa [sigma] using hZsigma
  have hZphaseForward := PlacementNormalizationProof.hZphaseForward r i s a g' cyclicCancel
      hphaseForward hZsigma'
  have hZphaseBackward := PlacementNormalizationProof.hZphaseBackward r i s a g' cyclicCancel
      hphaseBackward hZsigma'
  let xZ := BandVectors.1 (r adj.succ) (r 0)
  let yZ := BandVectors.1 (r 0) (r adj.succ)
  let xZ' := BandVectors.1 (qg j.succ) (qg 0)
  let yZ' := BandVectors.1 (qg 0) (qg j.succ)
  have hZflip : yZ' = ii * xZ' :=
    ((VectorRecursionLaws qg hproperG.1).2.2.2.2 hproperG j).1
  have hZactionForward := PlacementNormalizationProof.hZactionForward r i s a g' hZphaseForward
  have hZactionBackward := PlacementNormalizationProof.hZactionBackward r i s a g' hZphaseBackward
  have hZsourceAction := PlacementNormalizationProof.hZsourceAction r i s a g' ladd lneg
      hZactionForward hZactionBackward
  have hZvec := PlacementNormalizationProof.hZvec r i s U W Z hZ hZpos hWcent hZcent a g'
      evenZero evenTwo notEvenOne notEvenThree hnegVal iiMul iiZCaseA iiZCaseB iiZCaseC iiZCaseD
      iiCube negIiSq negIiCube lpow hdispW hZindex hZparentIndex hZcircle hZlabel hZrel hZsigma
      hZsigma' hZphaseForward hZphaseBackward hZflip hZactionForward hZactionBackward hZsourceAction
  have hZ' := PlacementNormalizationProof.hZ' r i s Z hZ a g' htileCov hZlabel
  have hUpos' := PlacementNormalizationProof.hUpos' r hUpos a g' htileCov hrootLabel
  have hWpos' := PlacementNormalizationProof.hWpos' r i hWpos a g' htileCov hWlabel
  have hZpos' := PlacementNormalizationProof.hZpos' r i s hZpos a g' htileCov hZlabel
  let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
    BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
      (fun p => (-p.1, p.2)) (fun _ p => p)
      (fun _ _ f k p => f (k p))
  have rsub (g₀ : BandPackingSymmetry) (p q₀ : Real × Real) := PlacementNormalizationProof.rsub
      g₀ p q₀
  have rsmul (g₀ : BandPackingSymmetry) (c : Real) (p : Real × Real) :=
      PlacementNormalizationProof.rsmul g₀ c p
  have rpoint (g₀ : BandPackingSymmetry) (v : GaussianInt) := PlacementNormalizationProof.rpoint
      g₀ v
  have rcentroid (g₀ : BandPackingSymmetry) (T₀ : ProtoTile) :=
      PlacementNormalizationProof.rcentroid g₀ T₀
  have hWcent' := PlacementNormalizationProof.hWcent' r i s U W hWcent g' rsub rsmul rpoint
      rcentroid
  have hZcent' := PlacementNormalizationProof.hZcent' r i s U Z hZcent g' rsub rsmul rpoint
      rcentroid
  have hWvec := PlacementNormalizationProof.hWvec r i s a g' hdispW
  have hWcentNorm := PlacementNormalizationProof.hWcentNorm r i s U W a g' hWcent' hWvec
  have hZvec' := PlacementNormalizationProof.hZvec' r i s a g' hZvec
  have hZcentNorm := PlacementNormalizationProof.hZcentNorm r i s U Z a g' hZvec hZcent'
  have hvR : BandPackingSymmetryVectorAction g' vR = vR' := by
    simpa [vR, vR'] using hvectorForward.symm
  have hvL := PlacementNormalizationProof.hvL r i a g' hvectorBackward
  have hdR := PlacementNormalizationProof.hdR r i s a g' evenZero
      evenTwo notEvenOne notEvenThree hnegVal iiSq iiCube negIiSq negIiCube lpow hbackEq' hvR hvL
  have hdL := PlacementNormalizationProof.hdL r i s a g' evenZero
      evenTwo notEvenOne notEvenThree hnegVal iiSq iiCube negIiSq negIiCube lpow hbackEq' hvR hvL
  exact ⟨g', hquadg, hproperG, hU', hW', hZ', hUpos', hWpos', hZpos',
    hWcentNorm, hZcentNorm, hdR, hdL⟩

end ApollonianSuperharmonic

end
