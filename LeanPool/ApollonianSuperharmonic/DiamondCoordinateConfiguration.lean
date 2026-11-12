/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: DiamondCoordinateConfiguration]

/-!
# DiamondCoordinateConfiguration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondConfigurationProof

private theorem semi :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    ∀ n : Nat, SemiProperQuadruple (configuration n) := by
  classical
  intro configuration n
  induction n with
  | zero =>
      change SemiProperQuadruple
        ![((2 * 1 * (1 + 1) : Nat),
          ⟨2 * (1 : Int) ^ 2 - 1, 2 * (1 : Int) * (1 + 1)⟩),
          (1, ⟨1, 2⟩), (1, 1),
          ((2 * (1 - 1) * 1 : Nat),
            ⟨2 * ((1 - 1 : Nat) : Int) ^ 2 - 1,
              2 * ((1 - 1 : Nat) : Int) * 1⟩)]
      have constructed :=
        SemiProperQuadruple.rotate
          (SemiProperQuadruple.rotate
            (SemiProperQuadruple.successor
              (SemiProperQuadruple.rotate
                (SemiProperQuadruple.base (0 : GaussianInt)))))
      convert constructed using 1;
        simp [Zsqrtd.ext_iff]
  | succ n ih =>
      have next := SemiProperQuadruple.rotate
        (SemiProperQuadruple.successor
          (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate ih)))
      convert next using 1
      all_goals
        simp only [configuration, DiamondRecursiveQuadruple,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ n + 1)]
        norm_num
        constructor
        · ring
        apply Zsqrtd.ext <;> simp <;> ring

private theorem root10'At246 :
    (BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) *
        ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt)) → ((BandVectors.1 ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 : ℤ), (-1 : GaussianInt)) = (1 :
        GaussianInt)) → ((BandVectors.1 (![((1 : ℤ), (1 : GaussianInt)), ((1 : ℤ), (1 :
        GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0
        : ℤ), (-1 : GaussianInt))] (1 : Fin (4 : ℕ))) (![((1 : ℤ), (1 : GaussianInt)), ((1 : ℤ),
        (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 :
        GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))] (0 : Fin (4 : ℕ))) = BandVectors.1 (![((1 :
        ℤ), (1 : GaussianInt)), ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 :
        ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))] (1 : Fin (4 : ℕ)))
        (![((1 : ℤ), (1 : GaussianInt)), ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 :
        ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))] (3 : Fin (4 :
        ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (![((1 : ℤ), (1 : GaussianInt)), ((1 : ℤ), (1 :
        GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0
        : ℤ), (-1 : GaussianInt))] (2 : Fin (4 : ℕ))) (![((1 : ℤ), (1 : GaussianInt)), ((1 : ℤ),
        (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 :
        GaussianInt)), ((0 : ℤ), (-1 : GaussianInt))] (1 : Fin (4 : ℕ)))) → ((((1 : Int), 1 + 2 *
        (⟨0, 1⟩ : GaussianInt)) = ((1 : Int), ⟨1, 2⟩)) → (BandVectors.1 (1, ⟨1, 2⟩) (1, 1) =
      ⟨1, 1⟩)))) := by
  classical
  intro r21 r13 root10 coordU
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val] at root10
  try
  change BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) =
    BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) -
      (⟨0, 1⟩ : GaussianInt) *
        BandVectors.1 (0, 1) (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) at root10
  rw [r13, r21] at root10
  have e := congrArg (fun C : CircleCoordinates =>
    BandVectors.1 C (1, 1)) coordU
  calc
    BandVectors.1 (1, ⟨1, 2⟩) (1, 1) =
        BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) := e.symm
    _ = _ := by simpa [Zsqrtd.ext_iff] using root10

private theorem hxAt261 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 :
        ℤ), (-1 : GaussianInt)) = (1 : GaussianInt)) → ((((1 : Int), 1 + 2 * (⟨0, 1⟩ :
        GaussianInt)) = ((1 : Int), ⟨1, 2⟩)) → (BandVectors.1 (configuration 0 1) (configuration
        0 3) =
      ⟨(1 : Int), 0⟩)) := by
  classical
  intro configuration r13 coordU
  try
  change BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) =
    ⟨1, 0⟩ at r13
  have e := congrArg (fun C : CircleCoordinates =>
    BandVectors.1 C (0, -1)) coordU
  calc
    BandVectors.1 (configuration 0 1) (configuration 0 3) =
        BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) := by
          simpa [configuration, DiamondRecursiveQuadruple]
    _ = _ := by simpa [e, Zsqrtd.ext_iff] using r13

private theorem hzval :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.1 (configuration (0 : ℕ) (3 : Fin (4 : ℕ))) (configuration (0 : ℕ) (2 : Fin (4 :
        ℕ))) + ⟨(1 : ℤ), (0 : ℤ)⟩ + ⟨(-1 : ℤ), (1 : ℤ)⟩ = (0 : GaussianInt)) → (BandVectors.1
        (configuration 0 3) (configuration 0 2) =
      ⟨0, -1⟩) := by
  classical
  intro configuration hz
  rw [Zsqrtd.ext_iff] at hz ⊢
  constructor
  · have h := hz.1
    norm_num at h ⊢
    linarith
  · have h := hz.2
    norm_num at h ⊢
    linarith

private theorem thirdVal :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    ∀ (n : ℕ), (BandVectors.1 (configuration (n + (1 : ℕ)) (3 : Fin (4 : ℕ))) (configuration (n +
        (1 : ℕ)) (2 : Fin (4 : ℕ))) + ⟨(↑n : ℤ) + (2 : ℤ), (↑n : ℤ) + (1 : ℤ)⟩ + ⟨(-1 : ℤ), (1 :
        ℤ)⟩ = (0 : GaussianInt)) → (BandVectors.1 (configuration (n + 1) 3)
      (configuration (n + 1) 2) =
      ⟨-(n + 1 : Int), -(n + 2 : Int)⟩) := by
  classical
  intro configuration n third
  rw [Zsqrtd.ext_iff] at third ⊢
  constructor
  · have h := third.1
    norm_num at h ⊢
    linarith
  · have h := third.2
    norm_num at h ⊢
    linarith

private theorem thirdIncomingAt355 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    ∀ (n : ℕ), (BandVectors.1 (configuration n (1 : Fin (4 : ℕ))) (configuration n (0 : Fin (4 :
        ℕ))) = ⟨(↑n : ℤ) + (2 : ℤ), (↑n : ℤ) + (1 : ℤ)⟩ ∧ BandVectors.1 (configuration n (2 : Fin
        (4 : ℕ))) (configuration n (0 : Fin (4 : ℕ))) = ⟨-((↑n : ℤ) + (1 : ℤ)) - (1 : ℤ), (↑n :
        ℤ) + (1 : ℤ)⟩ ∧ BandVectors.1 (configuration n (3 : Fin (4 : ℕ))) (configuration n (0 :
        Fin (4 : ℕ))) = ⟨(0 : ℤ), -((2 : ℤ) * ((↑n : ℤ) + (1 : ℤ)))⟩ ∧ BandVectors.1
        (configuration n (1 : Fin (4 : ℕ))) (configuration n (3 : Fin (4 : ℕ))) = ⟨(↑n : ℤ) + (1
        : ℤ), (↑n : ℤ)⟩ ∧ BandVectors.1 (configuration n (2 : Fin (4 : ℕ))) (configuration n (1 :
        Fin (4 : ℕ))) = ⟨(-1 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.1 (configuration n (3 : Fin (4 : ℕ)))
        (configuration n (2 : Fin (4 : ℕ))) = ⟨-(↑n : ℤ), -((↑n : ℤ) + (1 : ℤ))⟩) →
        ((BandVectors.1 (configuration (n + (1 : ℕ)) (0 : Fin (4 : ℕ))) (configuration (n + (1 :
        ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (configuration (n
        + (1 : ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) (configuration (n + (1 : ℕ)) (0 : Fin (4 : ℕ))))
        → ((BandVectors.1 (configuration (n + (1 : ℕ)) (0 : Fin (4 : ℕ))) (configuration (n + (1
        : ℕ)) (3 : Fin (4 : ℕ))) = BandVectors.1 (configuration n (1 : Fin (4 : ℕ)))
        (configuration n (0 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ * ⟨-((↑n : ℤ) + (1 : ℤ)), -((↑n
        : ℤ) + (2 : ℤ))⟩) → (BandVectors.1 (configuration (n + 1) 3)
      (configuration (n + 1) 0) =
      ⟨0, -(2 * (n + 2 : Int))⟩))) := by
  classical
  intro configuration n ih new30 fourth
  have h := new30
  change BandVectors.1 (configuration (n + 1) 0)
      (configuration (n + 1) 3) =
    (⟨0, 1⟩ : GaussianInt) *
      BandVectors.1 (configuration (n + 1) 3)
        (configuration (n + 1) 0) at h
  rw [fourth] at h
  rw [ih.1] at h
  simp [Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  constructor <;> linarith

private theorem hxAt430 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 :
        ℤ), (-1 : GaussianInt)) = ⟨(0 : ℤ), (1 : ℤ)⟩) → ((((1 : Int), 1 + 2 * (⟨0, 1⟩ :
        GaussianInt)) = ((1 : Int), ⟨1, 2⟩)) → ((((0 : Int), (-1 : GaussianInt)) = ((0 : Int),
        ⟨-1, 0⟩)) → (BandVectors.2 (configuration 0 1) (configuration 0 3) =
      ⟨0, 1⟩))) := by
  classical
  intro configuration root13 coordU coordB
  change BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) =
    ⟨0, 1⟩ at root13
  have e := congrArg (fun C : CircleCoordinates =>
    BandVectors.2 C (0, -1)) coordU
  have eB := congrArg (fun C : CircleCoordinates =>
    BandVectors.2 (1, ⟨1, 2⟩) C) coordB
  calc
    BandVectors.2 (configuration 0 1) (configuration 0 3) =
        BandVectors.2 (1, ⟨1, 2⟩) (0, ⟨-1, 0⟩) := by
          simp [configuration, DiamondRecursiveQuadruple]
    _ = BandVectors.2 (1, ⟨1, 2⟩) (0, -1) := eB.symm
    _ = BandVectors.2
        (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) := e.symm
    _ = _ := root13

private theorem hyAt446 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * (0 : GaussianInt)) ((1 : ℤ),
        (1 : GaussianInt) + (2 : GaussianInt) * (0 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ),
        (1 : ℤ)⟩) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 :
        GaussianInt) * (0 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((1 : ℤ), (1 :
        GaussianInt) + (2 : GaussianInt) * (0 : GaussianInt))) → ((((1 : Int), 1 + 2 * (⟨0, 1⟩ :
        GaussianInt)) = ((1 : Int), ⟨1, 2⟩)) → ((BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ :
        GaussianInt)) (1, 1) = 1) → (BandVectors.2 (configuration 0 2) (configuration 0 1) =
      ⟨0, -1⟩))) := by
  classical
  intro configuration root01 coordU root10'
  have hh := root01
  change BandVectors.2 (1, 1) (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) at hh
  rw [root10'] at hh
  have e := congrArg (fun C : CircleCoordinates =>
    BandVectors.2 (1, 1) C) coordU
  calc
    BandVectors.2 (configuration 0 2) (configuration 0 1) =
        BandVectors.2 (1, 1) (1, ⟨1, 2⟩) := by
          simp [configuration, DiamondRecursiveQuadruple]
    _ = BandVectors.2
        (1, 1) (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) := e.symm
    _ = _ := by simpa [Zsqrtd.ext_iff] using hh

private theorem cyclicThirdValAt467 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.2 (configuration (0 : ℕ) (3 : Fin (4 : ℕ))) (configuration (0 : ℕ) (2 : Fin (4 :
        ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ + ⟨(0 : ℤ), (-1 : ℤ)⟩ = (0 : GaussianInt)) → (BandVectors.2
        (configuration 0 3)
      (configuration 0 2) = ⟨0, 0⟩) := by
  classical
  intro configuration cyclicThird
  rw [Zsqrtd.ext_iff] at cyclicThird ⊢
  constructor
  · have h := cyclicThird.1
    norm_num at h ⊢
    linarith
  · have h := cyclicThird.2
    norm_num at h ⊢
    linarith

private theorem thirdIncomingAt479 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (BandVectors.1 (configuration (0 : ℕ) (0 : Fin (4 : ℕ))) (configuration (0 : ℕ) (Fin.succ (2
        : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (configuration (0 : ℕ) (Fin.succ (2
        : Fin (3 : ℕ)))) (configuration (0 : ℕ) (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (configuration
        (0 : ℕ) (0 : Fin (4 : ℕ))) (configuration (0 : ℕ) (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 :
        ℤ), (1 : ℤ)⟩ * BandVectors.2 (configuration (0 : ℕ) (Fin.succ (2 : Fin (3 : ℕ))))
        (configuration (0 : ℕ) (0 : Fin (4 : ℕ)))) → ((BandVectors.2 (configuration (0 : ℕ) (0 :
        Fin (4 : ℕ))) (configuration (0 : ℕ) (3 : Fin (4 : ℕ))) = ⟨(0 : ℤ), (1 : ℤ)⟩ - ⟨(0 : ℤ),
        (1 : ℤ)⟩ * ⟨(0 : ℤ), (0 : ℤ)⟩) → (BandVectors.2 (configuration 0 3)
      (configuration 0 0) = ⟨-1, 0⟩)) := by
  classical
  intro configuration qFlip fourth
  have h := qFlip.2
  change BandVectors.2 (configuration 0 0) (configuration 0 3) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (configuration 0 3) (configuration 0 0) at h
  rw [fourth] at h
  rw [Zsqrtd.ext_iff] at h ⊢
  constructor <;>
    norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢ <;>
    linarith

private theorem cyclicThirdValAt517 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    ∀ (n : ℕ), (BandVectors.2 (configuration (n + (1 : ℕ)) (3 : Fin (4 : ℕ))) (configuration (n +
        (1 : ℕ)) (2 : Fin (4 : ℕ))) + ⟨(↑n : ℤ) + (1 : ℤ), (1 : ℤ)⟩ + ⟨(0 : ℤ), (-1 : ℤ)⟩ = (0 :
        GaussianInt)) → (BandVectors.2 (configuration (n + 1) 3)
      (configuration (n + 1) 2) =
      ⟨-(n + 1 : Int), 0⟩) := by
  classical
  intro configuration n cyclicThird
  rw [Zsqrtd.ext_iff] at cyclicThird ⊢
  constructor
  · have h := cyclicThird.1
    norm_num at h ⊢
    linarith
  · have h := cyclicThird.2
    norm_num at h ⊢
    linarith

private theorem thirdIncomingAt532 :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    ∀ (n : ℕ), (BandVectors.2 (configuration n (1 : Fin (4 : ℕ))) (configuration n (0 : Fin (4 :
        ℕ))) = ⟨(↑n : ℤ) + (1 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (configuration n (2 : Fin (4 : ℕ)))
        (configuration n (0 : Fin (4 : ℕ))) = ⟨(0 : ℤ), -((↑n : ℤ) + (1 : ℤ))⟩ ∧ BandVectors.2
        (configuration n (3 : Fin (4 : ℕ))) (configuration n (0 : Fin (4 : ℕ))) = ⟨-((↑n : ℤ) +
        (1 : ℤ)), (↑n : ℤ)⟩ ∧ BandVectors.2 (configuration n (3 : Fin (4 : ℕ))) (configuration n
        (2 : Fin (4 : ℕ))) = ⟨-(↑n : ℤ), (0 : ℤ)⟩ ∧ BandVectors.2 (configuration n (1 : Fin (4 :
        ℕ))) (configuration n (3 : Fin (4 : ℕ))) = ⟨(↑n : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2
        (configuration n (2 : Fin (4 : ℕ))) (configuration n (1 : Fin (4 : ℕ))) = ⟨(0 : ℤ), (-1 :
        ℤ)⟩) → ((BandVectors.1 (configuration (n + (1 : ℕ)) (0 : Fin (4 : ℕ))) (configuration (n
        + (1 : ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1
        (configuration (n + (1 : ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) (configuration (n + (1 : ℕ))
        (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (configuration (n + (1 : ℕ)) (0 : Fin (4 : ℕ)))
        (configuration (n + (1 : ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) = -⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (configuration (n + (1 : ℕ)) (Fin.succ (2 : Fin (3 : ℕ)))) (configuration
        (n + (1 : ℕ)) (0 : Fin (4 : ℕ)))) → ((BandVectors.2 (configuration (n + (1 : ℕ)) (0 : Fin
        (4 : ℕ))) (configuration (n + (1 : ℕ)) (3 : Fin (4 : ℕ))) = BandVectors.2 (configuration
        n (1 : Fin (4 : ℕ))) (configuration n (0 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ * ⟨-((↑n :
        ℤ) + (1 : ℤ)), (0 : ℤ)⟩) → (BandVectors.2 (configuration (n + 1) 3)
      (configuration (n + 1) 0) =
      ⟨-(n + 2 : Int), (n + 1 : Int)⟩))) := by
  classical
  intro configuration n ih newFlip fourth
  have h := newFlip.2
  change BandVectors.2 (configuration (n + 1) 0)
      (configuration (n + 1) 3) =
    -(⟨0, 1⟩ : GaussianInt) *
      BandVectors.2 (configuration (n + 1) 3)
        (configuration (n + 1) 0) at h
  rw [fourth] at h
  rw [ih.1] at h
  simp [Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢
  constructor <;> linarith

end DiamondConfigurationProof

namespace DiamondConfigurationDetails

private theorem currentSemi :
    ∀ (K : DiamondParameter),
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (∀ n : Nat, SemiProperQuadruple (configuration n)) → (SemiProperQuadruple
        (DiamondRecursiveQuadruple
        K)) := by
  classical
  intro K configuration semi
  obtain ⟨k, hk⟩ := K
  cases k with
  | zero => omega
  | succ n => simpa [configuration] using semi n

private theorem circleWitness :
    ∀ (K : DiamondParameter), (SemiProperQuadruple (DiamondRecursiveQuadruple K)) → (∃ C :
        BandCircle,
      C.1.1 = (DiamondRecursiveQuadruple K) 0) := by
  classical
  intro K currentSemi
  refine ⟨⟨⟨(DiamondRecursiveQuadruple K) 0, ?_⟩, ?_⟩, rfl⟩
  · constructor
    · simp only [DiamondRecursiveQuadruple, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, Int.succ_ofNat_pos,
        mul_pos_iff_of_pos_right, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Int.natCast_pos,
        mul_eq_zero, OfNat.ofNat_ne_zero, Int.natCast_eq_zero, false_or]
      exact Or.inl (by exact_mod_cast K.2)
    · exact ⟨DiamondRecursiveQuadruple K, currentSemi, 0, rfl⟩
  · simp only [DiamondRecursiveQuadruple, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Int.reduceNeg, Fin.isValue, Matrix.cons_val_zero, Int.succ_ofNat_pos,
      mul_pos_iff_of_pos_right, Nat.ofNat_pos, mul_pos_iff_of_pos_left, Int.natCast_pos]
    exact_mod_cast K.2

private theorem proper :
    ∀ (K : DiamondParameter), (SemiProperQuadruple (DiamondRecursiveQuadruple K)) →
        (ProperBandQuadruple (DiamondRecursiveQuadruple K)) := by
  classical
  intro K currentSemi
  refine ⟨currentSemi, ?_⟩
  have hk : 0 < K.1 := K.2
  have hk' : 1 ≤ K.1 := by omega
  have hsub : K.1 - 1 ≤ K.1 := Nat.sub_le _ _
  intro j
  fin_cases j <;> simp [DiamondRecursiveQuadruple]
  all_goals nlinarith

private theorem properAt :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (∀ n : Nat, SemiProperQuadruple (configuration n)) → (∀ n : Nat, ProperBandQuadruple
        (configuration
        n)) := by
  classical
  intro configuration semi n
  refine ⟨semi n, ?_⟩
  have hn : 0 < n + 1 := Nat.succ_pos n
  have hsub : (n + 1) - 1 ≤ n + 1 := Nat.sub_le _ _
  intro j
  fin_cases j <;> simp [configuration, DiamondRecursiveQuadruple]
  all_goals nlinarith

private theorem claims :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (∀ n : Nat, SemiProperQuadruple (configuration n)) → ((∀ (z : GaussianInt), have q := ![((1 :
        ℤ), (1
        : GaussianInt) + (2 : GaussianInt) * z), ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt)
        * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ),
        (-1 : GaussianInt))]; BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (0 :
        GaussianInt) ∧ BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (-1 :
        GaussianInt) ∧ BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (1 :
        GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (1 :
        GaussianInt) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (-1 :
        GaussianInt) - z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin
        (4 : ℕ))) = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (q : Fin (4 : ℕ) → CircleCoordinates),
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
        ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D → BandVectors.1 D C = ⟨(0 : ℤ),
        (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 C
        D) → ((∀ n : Nat, ProperBandQuadruple (configuration n)) → (∀ n : Nat,
      BandVectors.1 (configuration n 1) (configuration n 0) =
          ⟨(n + 2 : Int), (n + 1 : Int)⟩ ∧
      BandVectors.1 (configuration n 2) (configuration n 0) =
          ⟨-(n + 1 : Int) - 1, (n + 1 : Int)⟩ ∧
      BandVectors.1 (configuration n 3) (configuration n 0) =
          ⟨0, -(2 * (n + 1) : Int)⟩ ∧
      BandVectors.1 (configuration n 1) (configuration n 3) =
          ⟨(n + 1 : Int), (n : Int)⟩ ∧
      BandVectors.1 (configuration n 2) (configuration n 1) =
          ⟨-1, 1⟩ ∧
      BandVectors.1 (configuration n 3) (configuration n 2) =
          ⟨-(n : Int), -(n + 1 : Int)⟩))))) := by
  classical
  intro configuration semi baseLaw stepLaw flipLaw properAt n
  induction n with
  | zero =>
      have root := baseLaw (0 : GaussianInt)
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mul_zero, add_zero, Int.reduceNeg,
          Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero,
          zero_add] at root
      have rootStep := stepLaw
        (![(1, 1), (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1)])
        (SemiProperQuadruple.base (0 : GaussianInt))
      have rootRec := VectorRecursionLaws
        (![(1, 1), (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1)])
        (SemiProperQuadruple.base (0 : GaussianInt))
      have rootFlip := flipLaw _ _ (PrimitiveVectorOrientation.base10 0)
      have qLaw := VectorRecursionLaws (configuration 0) (semi 0)
      have qStep := stepLaw (configuration 0) (semi 0)
      have qFlip := flipLaw _ _
        (PrimitiveVectorOrientation.parentChild (properAt 0) 2)
      rcases root with ⟨r32, r21, r13, _, _, _⟩
      rcases rootStep with ⟨s20, s03, _, _⟩
      rcases rootRec with ⟨_, _, root10, _, _⟩
      rcases rootFlip with ⟨root01, _⟩
      rcases qLaw with ⟨sumv, _, q10, _, _⟩
      rcases qStep with ⟨q20, q03, _, _⟩
      have coordU : ((1 : Int), 1 + 2 * (⟨0, 1⟩ : GaussianInt)) =
          ((1 : Int), ⟨1, 2⟩) := by
        norm_num [Zsqrtd.ext_iff]
      have coordU2 : ((1 : Int), 1 + 2 * (0 : GaussianInt) +
          2 * (⟨0, 1⟩ : GaussianInt)) = (1, ⟨1, 2⟩) := by
        norm_num [Zsqrtd.ext_iff]
      have coordB : ((0 : Int), (-1 : GaussianInt)) =
          ((0 : Int), ⟨-1, 0⟩) := by rfl
      have root10' := DiamondConfigurationProof.root10'At246 r21 r13 root10 coordU
      have hx := DiamondConfigurationProof.hxAt261 r13 coordU
      have hy : BandVectors.1 (configuration 0 2) (configuration 0 1) =
          ⟨-1, 1⟩ := by
        have hh := root01
        simp only [mul_zero, add_zero, Int.reduceNeg] at hh
        change BandVectors.1 (1, 1) (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) =
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) at hh
        simp only [coordU, root10'] at hh
        simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hh
      have ha := q10
      have hb := q20
      have hc := q03
      have hz := sumv
      rw [hx, hy] at ha
      rw [hx, hy] at hz
      have hzval := DiamondConfigurationProof.hzval hz
      rw [hy, hzval] at hb
      rw [hx, hzval] at hc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using ha
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hb
      · have hd := qFlip.1
        have hdn : BandVectors.1 (configuration 0 0) (configuration 0 3) =
            (⟨0, 1⟩ : GaussianInt) *
              BandVectors.1 (configuration 0 3) (configuration 0 0) := by
          simpa using hd
        have hval := hdn
        rw [hc] at hval
        have hdval : BandVectors.1 (configuration 0 3) (configuration 0 0) =
            ⟨0, -2⟩ := by
          rw [Zsqrtd.ext_iff] at hval ⊢
          constructor <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at hval ⊢ <;>
            linarith
        simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hdval
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hx
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hy
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hzval
  | succ n ih =>
      have newLaw := VectorRecursionLaws (configuration (n + 1)) (semi (n + 1))
      have newStep := stepLaw (configuration (n + 1)) (semi (n + 1))
      have newFlip := flipLaw _ _
        (PrimitiveVectorOrientation.parentChild (properAt (n + 1)) 2)
      rcases newLaw with ⟨newSum, _, new10, _, _⟩
      rcases newStep with ⟨new20, new03, _, _⟩
      rcases newFlip with ⟨new30, _⟩
      have bridge13 : BandVectors.1 (configuration (n + 1) 1)
          (configuration (n + 1) 3) =
          BandVectors.1 (configuration n 1) (configuration n 0) := by
        simp [configuration, DiamondRecursiveQuadruple]
      have bridge21 : BandVectors.1 (configuration (n + 1) 2)
          (configuration (n + 1) 1) =
          BandVectors.1 (configuration n 2) (configuration n 1) := by
        rfl
      have first := new10
      rw [bridge13, bridge21, ih.1, ih.2.2.2.2.1] at first
      have fifth := bridge21.trans ih.2.2.2.2.1
      have third := newSum
      rw [bridge13, bridge21, ih.1, ih.2.2.2.2.1] at third
      have thirdVal := DiamondConfigurationProof.thirdVal n third
      have second := new20
      rw [fifth, thirdVal] at second
      have fourth := new03
      rw [bridge13, thirdVal] at fourth
      have thirdIncoming := DiamondConfigurationProof.thirdIncomingAt355 n ih new30
              fourth
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := first
        rw [Zsqrtd.ext_iff] at h ⊢
        constructor <;>
          norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢ <;>  linarith
      · have h := second
        rw [Zsqrtd.ext_iff] at h ⊢
        constructor <;>
          norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢ <;>  linarith
      · convert thirdIncoming using 1;
          simp []; ring
      · convert ih.1 using 1;
          simp []; ring
      · simpa [Zsqrtd.ext_iff] using fifth
      · convert thirdVal using 1;
          simp []; ring

private theorem slopeClaims :
    let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
      DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
    (∀ n : Nat, SemiProperQuadruple (configuration n)) → ((∀ (z : GaussianInt), have q := ![((1 :
        ℤ), (1
        : GaussianInt) + (2 : GaussianInt) * z), ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt)
        * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩), ((0 : ℤ), (1 : GaussianInt)), ((0 : ℤ),
        (-1 : GaussianInt))]; BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (0 :
        GaussianInt) ∧ BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (-1 :
        GaussianInt) ∧ BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))) = (1 :
        GaussianInt) ∧ BandVectors.2 (q (3 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (1 :
        GaussianInt) ∧ BandVectors.2 (q (2 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) = (-1 :
        GaussianInt) - z - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 (q (1 : Fin (4 : ℕ))) (q (3 : Fin
        (4 : ℕ))) = z + ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (q : Fin (4 : ℕ) → CircleCoordinates),
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
        ∀ (D : CircleCoordinates), PrimitiveVectorOrientation C D → BandVectors.1 D C = ⟨(0 : ℤ),
        (1 : ℤ)⟩ * BandVectors.1 C D ∧ BandVectors.2 D C = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 C
        D) → ((∀ n : Nat, ProperBandQuadruple (configuration n)) → (∀ n : Nat,
      BandVectors.2 (configuration n 1) (configuration n 0) =
          ⟨(n + 1 : Int), 1⟩ ∧
      BandVectors.2 (configuration n 2) (configuration n 0) =
          ⟨0, -(n + 1 : Int)⟩ ∧
      BandVectors.2 (configuration n 3) (configuration n 0) =
          ⟨-(n + 1 : Int), (n : Int)⟩ ∧
      BandVectors.2 (configuration n 3) (configuration n 2) =
          ⟨-(n : Int), 0⟩ ∧
      BandVectors.2 (configuration n 1) (configuration n 3) =
          ⟨(n : Int), 1⟩ ∧
      BandVectors.2 (configuration n 2) (configuration n 1) =
          ⟨0, -1⟩))))) := by
  classical
  intro configuration semi baseLaw stepLaw flipLaw properAt n
  induction n with
  | zero =>
      have root := baseLaw (0 : GaussianInt)
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mul_zero, add_zero, Int.reduceNeg,
          Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero,
          zero_add] at root
      have rootRec := VectorRecursionLaws
        (![(1, 1), (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1)])
        (SemiProperQuadruple.base (0 : GaussianInt))
      have rootFlip := flipLaw _ _ (PrimitiveVectorOrientation.base10 0)
      have qLaw := VectorRecursionLaws (configuration 0) (semi 0)
      have qStep := stepLaw (configuration 0) (semi 0)
      have qFlip := flipLaw _ _
        (PrimitiveVectorOrientation.parentChild (properAt 0) 2)
      rcases root with ⟨_, _, _, _, root21, root13⟩
      rcases rootRec with ⟨_, _, _, root10, _⟩
      rcases rootFlip with ⟨_, root01⟩
      rcases qLaw with ⟨_, sumA, _, q10, _⟩
      rcases qStep with ⟨_, _, q20, q03⟩
      have coordU : ((1 : Int), 1 + 2 * (⟨0, 1⟩ : GaussianInt)) =
          ((1 : Int), ⟨1, 2⟩) := by
        norm_num [Zsqrtd.ext_iff]
      have coordB : ((0 : Int), (-1 : GaussianInt)) =
          ((0 : Int), ⟨-1, 0⟩) := by rfl
      have root10' :
          BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) = 1 := by
        change BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (1, 1) =
          BandVectors.2 (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) (0, -1) +
            (⟨0, 1⟩ : GaussianInt) *
              BandVectors.2 (0, 1) (1, 1 + 2 * (⟨0, 1⟩ : GaussianInt)) at root10
        rw [root13, root21] at root10
        simpa [Zsqrtd.ext_iff] using root10
      have hx := DiamondConfigurationProof.hxAt430 root13 coordU coordB
      have hy := DiamondConfigurationProof.hyAt446 root01 coordU root10'
      have first := q10
      have second := q20
      have fourth := q03
      have cyclicThird := sumA
      rw [hx, hy] at first cyclicThird
      have cyclicThirdVal := DiamondConfigurationProof.cyclicThirdValAt467
              cyclicThird
      rw [hy, cyclicThirdVal] at second
      rw [hx, cyclicThirdVal] at fourth
      have thirdIncoming := DiamondConfigurationProof.thirdIncomingAt479 qFlip
              fourth
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using first
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using second
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using thirdIncoming
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using cyclicThirdVal
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hx
      · simpa [configuration, DiamondRecursiveQuadruple, Zsqrtd.ext_iff] using hy
  | succ n ih =>
      have newLaw := VectorRecursionLaws (configuration (n + 1)) (semi (n + 1))
      have newStep := stepLaw (configuration (n + 1)) (semi (n + 1))
      have newFlip := flipLaw _ _
        (PrimitiveVectorOrientation.parentChild (properAt (n + 1)) 2)
      rcases newLaw with ⟨_, newSum, _, new10, _⟩
      rcases newStep with ⟨_, _, new20, new03⟩
      have bridge13 : BandVectors.2 (configuration (n + 1) 1)
          (configuration (n + 1) 3) =
          BandVectors.2 (configuration n 1) (configuration n 0) := by
        simp [configuration, DiamondRecursiveQuadruple]
      have bridge21 : BandVectors.2 (configuration (n + 1) 2)
          (configuration (n + 1) 1) =
          BandVectors.2 (configuration n 2) (configuration n 1) := by
        rfl
      have first := new10
      rw [bridge13, bridge21, ih.1, ih.2.2.2.2.2] at first
      have sixth := bridge21.trans ih.2.2.2.2.2
      have cyclicThird := newSum
      rw [bridge13, bridge21, ih.1, ih.2.2.2.2.2] at cyclicThird
      have cyclicThirdVal := DiamondConfigurationProof.cyclicThirdValAt517 n cyclicThird
      have second := new20
      rw [sixth, cyclicThirdVal] at second
      have fourth := new03
      rw [bridge13, cyclicThirdVal] at fourth
      have thirdIncoming := DiamondConfigurationProof.thirdIncomingAt532 n ih
              newFlip fourth
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := first
        rw [Zsqrtd.ext_iff] at h ⊢
        constructor <;>
          norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢ <;>  linarith
      · have h := second
        rw [Zsqrtd.ext_iff] at h ⊢
        constructor <;>
          norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul] at h ⊢ <;>  linarith
      · exact thirdIncoming
      · exact cyclicThirdVal
      · convert ih.1 using 1;
          simp []
      · exact sixth

end DiamondConfigurationDetails

theorem DiamondCoordinateConfiguration (K : DiamondParameter) :
    (∃ C : BandCircle, C.1.1 = (DiamondRecursiveQuadruple K) 0) ∧
    ProperBandQuadruple (DiamondRecursiveQuadruple K) ∧
    BandVectors.1 ((DiamondRecursiveQuadruple K) 1)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨(K.1 + 1 : Int), (K.1 : Int)⟩ ∧
    BandVectors.1 ((DiamondRecursiveQuadruple K) 2)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨-(K.1 : Int) - 1, (K.1 : Int)⟩ ∧
    BandVectors.1 ((DiamondRecursiveQuadruple K) 3)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨0, -(2 * K.1 : Int)⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 1)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨(K.1 : Int), 1⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 2)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨0, -(K.1 : Int)⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 3)
        ((DiamondRecursiveQuadruple K) 0) =
      ⟨-(K.1 : Int), (K.1 : Int) - 1⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 3)
        ((DiamondRecursiveQuadruple K) 2) =
      ⟨1 - (K.1 : Int), 0⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 1)
        ((DiamondRecursiveQuadruple K) 3) =
      ⟨(K.1 : Int) - 1, 1⟩ ∧
    BandVectors.2 ((DiamondRecursiveQuadruple K) 2)
        ((DiamondRecursiveQuadruple K) 1) =
      ⟨0, -1⟩ := by
-- BODY
  let configuration (n : Nat) : Fin 4 → CircleCoordinates :=
    DiamondRecursiveQuadruple ⟨n + 1, Nat.succ_pos n⟩
  have semi := DiamondConfigurationProof.semi
  have currentSemi : SemiProperQuadruple (DiamondRecursiveQuadruple K) :=
      DiamondConfigurationDetails.currentSemi K semi
  have circleWitness : ∃ C : BandCircle,
      C.1.1 = (DiamondRecursiveQuadruple K) 0 := DiamondConfigurationDetails.circleWitness K
          currentSemi
  have proper : ProperBandQuadruple (DiamondRecursiveQuadruple K) :=
      DiamondConfigurationDetails.proper K currentSemi
  have systemLaw : RecursiveVectorSystem BandVectors :=
    by simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases systemLaw with ⟨zeroLaw, baseLaw, stepLaw, flipLaw⟩
  have properAt : ∀ n : Nat, ProperBandQuadruple (configuration n) :=
      DiamondConfigurationDetails.properAt semi
  have claims : ∀ n : Nat,
      BandVectors.1 (configuration n 1) (configuration n 0) =
          ⟨(n + 2 : Int), (n + 1 : Int)⟩ ∧
      BandVectors.1 (configuration n 2) (configuration n 0) =
          ⟨-(n + 1 : Int) - 1, (n + 1 : Int)⟩ ∧
      BandVectors.1 (configuration n 3) (configuration n 0) =
          ⟨0, -(2 * (n + 1) : Int)⟩ ∧
      BandVectors.1 (configuration n 1) (configuration n 3) =
          ⟨(n + 1 : Int), (n : Int)⟩ ∧
      BandVectors.1 (configuration n 2) (configuration n 1) =
          ⟨-1, 1⟩ ∧
      BandVectors.1 (configuration n 3) (configuration n 2) =
          ⟨-(n : Int), -(n + 1 : Int)⟩ := DiamondConfigurationDetails.claims semi baseLaw stepLaw
              flipLaw properAt
  have slopeClaims : ∀ n : Nat,
      BandVectors.2 (configuration n 1) (configuration n 0) =
          ⟨(n + 1 : Int), 1⟩ ∧
      BandVectors.2 (configuration n 2) (configuration n 0) =
          ⟨0, -(n + 1 : Int)⟩ ∧
      BandVectors.2 (configuration n 3) (configuration n 0) =
          ⟨-(n + 1 : Int), (n : Int)⟩ ∧
      BandVectors.2 (configuration n 3) (configuration n 2) =
          ⟨-(n : Int), 0⟩ ∧
      BandVectors.2 (configuration n 1) (configuration n 3) =
          ⟨(n : Int), 1⟩ ∧
      BandVectors.2 (configuration n 2) (configuration n 1) =
          ⟨0, -1⟩ := DiamondConfigurationDetails.slopeClaims semi baseLaw stepLaw flipLaw properAt
  refine ⟨circleWitness, proper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (claims n).1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (claims n).2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (claims n).2.2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).2.2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).2.2.2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).2.2.2.2.1
  · obtain ⟨k, hk⟩ := K
    cases k with
    | zero => omega
    | succ n =>
        simpa [configuration, Nat.cast_add, add_assoc] using (slopeClaims n).2.2.2.2.2

end ApollonianSuperharmonic

end
