/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.AffineCode
public import LeanPool.KLRandomness.AffineBlock
public import Mathlib.Data.List.OfFn

/-!
# Coverage of full-row-rank affine systems

Every surjective finite binary matrix has a right inverse, so supplying a
certificate imposes no restriction on the affine events representable by
the concrete codes. The certificate is part of the program's output. This
result does not bound the length of a program producing it.
-/

@[expose] public section

namespace Klr.AffineCode

open FiniteMeasure

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

/-- Encode a finite matrix, syndrome and right-inverse candidate as ordinary finite data. -/
def encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2)) (y : Fin r → ZMod 2)
    (R : Matrix (Fin m) (Fin r) (ZMod 2)) : Data :=
  ((m, r), (List.ofFn (fun i => List.ofFn (fun j => boolEquivF2.symm (A i j))),
    (List.ofFn (fun i => boolEquivF2.symm (y i)),
      List.ofFn (fun i => List.ofFn (fun j => boolEquivF2.symm (R i j))))))

@[simp] theorem width_encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    width (encode A y R) = m := rfl

@[simp] theorem rank_encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    rank (encode A y R) = r := rfl

@[simp] theorem matrix_encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    matrix (encode A y R) = A := by
  ext i j
  change Fin r at i
  change Fin m at j
  dsimp only [matrix, rows, encode, entry]
  rw [getD_ofFn _ i, getD_ofFn _ j, Equiv.apply_symm_apply]

@[simp] theorem rightMatrix_encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    rightMatrix (encode A y R) = R := by
  ext i j
  change Fin m at i
  change Fin r at j
  dsimp only [rightMatrix, certificate, encode, entry]
  rw [getD_ofFn _ i, getD_ofFn _ j, Equiv.apply_symm_apply]

@[simp] theorem syndromeVector_encode {m r : ℕ}
    (A : Matrix (Fin r) (Fin m) (ZMod 2)) (y : Fin r → ZMod 2)
    (R : Matrix (Fin m) (Fin r) (ZMod 2)) : syndromeVector (encode A y R) = y := by
  funext i
  change Fin r at i
  dsimp only [syndromeVector, syndrome, encode]
  rw [getD_ofFn _ i, Equiv.apply_symm_apply]

theorem valid_encode_iff {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    valid (encode A y R) = true ↔ A * R = 1 := by
  rw [valid_iff_right_inverse, matrix_encode, rightMatrix_encode]
  rfl

@[simp] theorem event_encode {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (y : Fin r → ZMod 2) (R : Matrix (Fin m) (Fin r) (ZMod 2)) :
    event (encode A y R) =
      FiniteStage.affineEvent (fun i : Fin m => i.val) A.mulVecLin y := by
  simp only [event, matrix_encode, syndromeVector_encode, width_encode]
  rfl

/-- Preimages of the standard basis vectors are the columns of a right inverse. -/
theorem exists_right_inverse {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (hA : Function.Surjective A.mulVecLin) :
    ∃ R : Matrix (Fin m) (Fin r) (ZMod 2), A * R = 1 := by
  classical
  choose x hx using fun j : Fin r => hA (fun i => (1 : Matrix (Fin r) (Fin r) (ZMod 2)) i j)
  refine ⟨fun k j => x j k, ?_⟩
  ext i j
  exact congrFun (hx j) i

/-- Every full-row-rank finite binary affine system occurs in the concrete code family. -/
theorem exists_valid_code {m r : ℕ} (A : Matrix (Fin r) (Fin m) (ZMod 2))
    (hA : Function.Surjective A.mulVecLin) (y : Fin r → ZMod 2) :
    ∃ c : Data, width c = m ∧ rank c = r ∧ valid c = true ∧
      event c = FiniteStage.affineEvent (fun i : Fin m => i.val) A.mulVecLin y := by
  obtain ⟨R, hR⟩ := exists_right_inverse A hA
  exact ⟨encode A y R, rfl, rfl, (valid_encode_iff A y R).mpr hR, event_encode A y R⟩

/-- Padding unused coordinates by zero columns represents every existing finite-support block. -/
theorem exists_valid_code_of_affineBlock (B : AffineBlock) :
    ∃ c : Data, rank c = B.rank ∧ valid c = true ∧ event c = B.event := by
  classical
  let m := B.support.sup id + 1
  have hbound (i : B.support) : i.val < m :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)
  let restrict : (Fin m → ZMod 2) →ₗ[ZMod 2] (B.support → ZMod 2) :=
    { toFun := fun x i => x ⟨i.val, hbound i⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrestrict : Function.Surjective restrict := by
    intro x
    refine ⟨fun j => if hj : j.val ∈ B.support then x ⟨j.val, hj⟩ else 0, ?_⟩
    funext i
    change (if hi : i.val ∈ B.support then x ⟨i.val, hi⟩ else 0) = x i
    simp [i.property]
  let D := B.matrix.comp restrict
  let A := LinearMap.toMatrix' D
  have hA : Function.Surjective A.mulVecLin := by
    intro y
    obtain ⟨x, hx⟩ := B.fullRank y
    obtain ⟨v, hv⟩ := hrestrict x
    refine ⟨v, ?_⟩
    change Matrix.mulVec (LinearMap.toMatrix' D) v = y
    rw [LinearMap.toMatrix'_mulVec]
    change B.matrix (restrict v) = y
    rw [hv, hx]
  obtain ⟨c, _, hr, hv, he⟩ := exists_valid_code A hA B.syndrome
  refine ⟨c, hr, hv, he.trans ?_⟩
  ext X
  change Matrix.mulVec (LinearMap.toMatrix' D)
    (coordinateValues (fun i : Fin m => i.val) X) = B.syndrome ↔ _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

end Klr.AffineCode
