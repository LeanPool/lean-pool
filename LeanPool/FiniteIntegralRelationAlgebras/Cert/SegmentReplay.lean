/-
Copyright (c) 2026 Chris Henson and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson, Lean Pool contributors
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Orbit

/-! # Orbit segment replay

Nearby representatives often agree on most of their high bits. Reuse the part of their
bit matrix contributed by those bits. When only the identity permutation still agrees,
it fixes the entire assignment, so the remaining rows need no comparison.
-/

@[expose] public section

namespace RACert.SegmentReplay

/-- Assemble the bit matrix from the high columns first. Giving the recursive call a
literal high part lets nearby orbit minima share the same matrix for those columns. -/
noncomputable def matrixOfColumns (columns : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun column _ next assignment =>
      Nat.rec (motive := fun _ => ℕ) 0
        (fun high _ => Nat.rec (motive := fun _ => ℕ) (next high)
          (fun _ _ => Nat.lor column (next high)) (Nat.land assignment 1))
        (Nat.succ (Nat.shiftRight assignment 1))) columns

private theorem matLoop_eq_matrixOfColumns (columns : List ℕ) (assignment acc : ℕ) :
    matLoop columns assignment acc = acc ||| matrixOfColumns columns assignment := by
  induction columns generalizing assignment acc with
  | nil => simp [matLoop, matrixOfColumns]
  | cons column columns ih =>
    rw [matLoop_cons]
    change _ = acc ||| (Nat.rec (motive := fun _ => ℕ) (matrixOfColumns columns (assignment >>> 1))
      (fun _ _ => column ||| matrixOfColumns columns (assignment >>> 1)) (assignment &&& 1))
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one assignment with h | h <;> rw [h]
    · exact ih _ _
    · exact (ih _ _).trans (Nat.lor_assoc _ _ _)

/-- Compare the images until only the identity permutation can still agree. -/
noncomputable def rowLoopUntilIdentity (size matrix : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) id
    (fun j next remaining =>
      Bool.rec (motive := fun _ => ℕ)
        (Nat.rec (motive := fun _ => ℕ)
          (next (Nat.xor remaining (Nat.land remaining (Nat.shiftRight matrix
            (Nat.mul j (Nat.succ size))))))
          (fun _ _ => Bool.rec (motive := fun _ => ℕ) 0 (next remaining)
            (Nat.beq (Nat.land remaining (Nat.shiftRight matrix (Nat.mul j (Nat.succ size))))
              remaining))
          (Nat.land (Nat.shiftRight matrix (Nat.mul j (Nat.succ size))) (Nat.pow 2 size)))
        1 (Nat.beq remaining 1))

private theorem rowLoopUntilIdentity_succ (size matrix j remaining : ℕ) :
    rowLoopUntilIdentity size matrix (j + 1) remaining =
      Bool.rec (motive := fun _ => ℕ)
        (Nat.rec (motive := fun _ => ℕ)
          (rowLoopUntilIdentity size matrix j
            (remaining ^^^ remaining &&& matrix >>> (j * (size + 1))))
          (fun _ _ => Bool.rec (motive := fun _ => ℕ) 0
            (rowLoopUntilIdentity size matrix j remaining)
            (Nat.beq (remaining &&& matrix >>> (j * (size + 1))) remaining))
          (matrix >>> (j * (size + 1)) &&& 2 ^ size))
        1 (Nat.beq remaining 1) := rfl

private theorem rowLoop_identity (size matrix n : ℕ)
    (identity : ∀ j < n, (matrix >>> (j * (size + 1))).testBit 0 =
      (matrix >>> (j * (size + 1))).testBit size) :
    rowLoop (size + 1) (2 ^ size) matrix n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ j ih =>
    have hj := identity j (Nat.lt_succ_self j)
    have hnext := ih fun i hi => identity i (Nat.lt_succ_of_lt hi)
    rw [rowLoop_succ]
    generalize hrow : matrix >>> (j * (size + 1)) = row at hj ⊢
    cases hbit : row.testBit size with
    | false =>
      rw [(and_two_pow_eq_zero_iff _ _).mpr hbit]
      have hzero : 1 &&& row = 0 := by
        rw [Nat.land_comm]
        simpa only [pow_zero] using (and_two_pow_eq_zero_iff row 0).mpr (hj.trans hbit)
      rw [hzero]
      exact hnext
    | true =>
      have hpos : 0 < row &&& 2 ^ size := Nat.pos_of_ne_zero fun h => by
        rw [(and_two_pow_eq_zero_iff _ _).mp h] at hbit
        contradiction
      obtain ⟨k, hk⟩ : ∃ k, row &&& 2 ^ size = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hleft : 1 &&& row = 1 := by
        rw [Nat.land_comm, Nat.and_one_is_mod]
        have hodd := hj.trans hbit
        rw [Nat.testBit_zero, decide_eq_true_iff] at hodd
        exact hodd
      rw [hk, hleft]
      exact hnext

private theorem rowLoopUntilIdentity_eq (size matrix n : ℕ)
    (identity : ∀ j < n, (matrix >>> (j * (size + 1))).testBit 0 =
      (matrix >>> (j * (size + 1))).testBit size) (remaining : ℕ) :
    rowLoopUntilIdentity size matrix n remaining =
      rowLoop (size + 1) (2 ^ size) matrix n remaining := by
  induction n generalizing remaining with
  | zero => rfl
  | succ j ih =>
    by_cases single : remaining = 1
    · subst remaining
      exact (rowLoop_identity size matrix (j + 1) identity).symm
    · have hnext := ih fun i hi => identity i (Nat.lt_succ_of_lt hi)
      have nonSingleton : Nat.beq remaining 1 = false :=
        Bool.eq_false_iff.mpr fun h => single (Nat.beq_eq.mp h)
      rw [rowLoopUntilIdentity_succ, rowLoop_succ, nonSingleton]
      dsimp only
      rw [hnext, hnext]

private theorem imgMat_identity {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ} (group : checkBitGroup t perms gens inv = true)
    (assignment j : ℕ) (hj : j < t) :
    (imgMat t perms assignment >>> (j * (perms.length + 1))).testBit 0 =
      (imgMat t perms assignment >>> (j * (perms.length + 1))).testBit perms.length := by
  obtain ⟨checked, positive, first, _⟩ := checkBitGroup_spec group
  have checked' := checked 0 positive
  have fixed := (checkBitPerm_spec checked' hj).2.2.1
  rw [first j hj] at fixed
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, testBit_imgMat_perm _ _ _ _ positive,
    testBit_imgMat_self _ _ _ hj, testBit_actBits checked', decide_eq_true hj, Bool.true_and, fixed]

/-- Check one representative and its orbit size with the shared matrix calculation. -/
noncomputable def checkRepresentative (t size bits full : ℕ) (columns : List ℕ)
    (assignment orbitSize : ℕ) : Bool :=
  Nat.beq (Nat.mul orbitSize
    (stabCount bits (rowLoopUntilIdentity size (matrixOfColumns columns assignment) t full))) size

private theorem checkRepresentative_eq (t size bits full : ℕ) (columns : List ℕ)
    (assignment orbitSize : ℕ)
    (identity : ∀ j < t, (matrixOfColumns columns assignment >>> (j * (size + 1))).testBit 0 =
      (matrixOfColumns columns assignment >>> (j * (size + 1))).testBit size) :
    checkRepresentative t size bits full columns assignment orbitSize =
      repCheck t size bits full (2 ^ size) columns assignment orbitSize := by
  rw [checkRepresentative, repCheck, rowLoopUntilIdentity_eq _ _ _ identity,
    matLoop_eq_matrixOfColumns,
    Nat.zero_or]

/-- Check increasing representatives in the segment, starting at the given lower bound. -/
noncomputable def segmentLoop (t size bits full hi : ℕ) (columns : List ℕ)
    (segment : List (ℕ × ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun lo => Nat.ble lo hi)
    (fun entry _ next lo => Prod.rec (motive := fun _ => Bool)
      (fun assignment orbitSize => and3 (Nat.ble lo assignment)
        (checkRepresentative t size bits full columns assignment orbitSize)
        (next (Nat.succ assignment))) entry) segment

private theorem segmentLoop_eq (t size bits full hi : ℕ)
    (columns : List ℕ)
    (segment : List (ℕ × ℕ)) (lo : ℕ)
    (identity : ∀ assignment j, j < t →
      (matrixOfColumns columns assignment >>> (j * (size + 1))).testBit 0 =
        (matrixOfColumns columns assignment >>> (j * (size + 1))).testBit size) :
    segmentLoop t size bits full hi columns segment lo =
      segLoop t size bits full (2 ^ size) hi columns segment lo := by
  induction segment generalizing lo with
  | nil => rfl
  | cons entry segment ih =>
    obtain ⟨assignment, orbitSize⟩ := entry
    rw [segLoop_cons]
    change and3 _ (checkRepresentative t size bits full columns assignment orbitSize)
      (segmentLoop t size bits full hi columns segment (assignment + 1)) = _
    rw [checkRepresentative_eq _ _ _ _ _ _ _ (identity assignment), ih]

/-- Check a segment using shared high-bit matrices and stopping comparisons at the identity. -/
noncomputable def checkSegment (t size lo hi : ℕ) (columns : List ℕ)
    (segment : List (ℕ × ℕ)) : Bool :=
  and3 (Nat.ble hi (Nat.pow 2 t)) (Nat.ble lo hi)
    (segmentLoop t size (Nat.succ (Nat.log2 size))
      (Nat.sub (Nat.pow 2 size) 1) hi columns segment lo)

/-- The shared check verifies the same segment when the group lists the identity first. -/
theorem checkSegUsingColumns_of_checkSegment {t size lo hi : ℕ} {columns : List ℕ}
    {perms : List (List ℕ × List ℕ)} {gens : List (ℕ × List ℕ)} {inv : List ℕ}
    {segment : List (ℕ × ℕ)} (group : checkBitGroup t perms gens inv = true)
    (groupSize : perms.length = size) (checkedColumns : cols t size perms = columns)
    (checked : checkSegment t size lo hi columns segment = true) :
    checkSegUsingColumns t size lo hi columns segment = true := by
  subst size columns
  have hmatrix (α : ℕ) : matrixOfColumns (cols t perms.length perms) α = imgMat t perms α := by
    rw [imgMat, matLoop_eq_matrixOfColumns, Nat.zero_or]
  have identity assignment j (hj : j < t) :=
    imgMat_identity group assignment j hj
  rw [checkSegment, segmentLoop_eq _ _ _ _ _ _ _ _ (fun assignment j hj => by
    rw [hmatrix]
    exact identity assignment j hj)] at checked
  exact checked

end RACert.SegmentReplay
