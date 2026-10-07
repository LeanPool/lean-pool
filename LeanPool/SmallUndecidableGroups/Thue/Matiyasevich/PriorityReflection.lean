/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.PriorityForward
public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.ContextualSelection

/-! ### Elementary interfaces used by the priority reflection proof -/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Compression

open Padding Binary Priority Precompression

variable {n r : ℕ}

theorem priority_encode_injective (u₀ : ℕ) :
    Function.Injective (Priority.encode u₀) := by
  intro X Y h
  have hmarker : liftBinary X ++ [a] = liftBinary Y ++ [a] :=
    List.append_left_injective (List.replicate u₀ e)
      (by simpa [Priority.encode, List.append_assoc] using h)
  exact liftBinary_injective
    (List.append_left_injective [a] hmarker)

theorem source_binary_iff (F E : Fin r → List (Fin n))
    (X Y : List (Fin n)) :
    ThueEq (finiteSystem F E) X Y ↔
      ThueEq (binarySystem F E)
        ((Precompression.embedding F E).encode X)
        ((Precompression.embedding F E).encode Y) := by
  rw [binarySystem_eq_unpadded]
  exact (Precompression.embedding F E).thueEq_iff X Y

private theorem context_counts_of_long
    {u₀ run : ℕ} {L W left right : List Priority.A₂}
    (hshape : LongShape run L)
    (hrequire : LongRunRequirement u₀ run)
    (hnormal : NoAAA (firstNormal W))
    (hcount : eCount W = u₀)
    (hword : W = left ++ L ++ right)
    (hL : eCount L = 0) :
    eCount left = u₀ ∧ eCount right = 0 := by
  obtain ⟨middle, hshape⟩ := hshape
  have hnormal' : NoAAA (firstNormal
      (left ++ List.replicate run a ++ (middle ++ [b] ++ right))) := by
    simpa only [hword, hshape, List.append_assoc] using hnormal
  have hleft : u₀ ≤ eCount left := hrequire left _ hnormal'
  have hsum : eCount left + eCount right = u₀ := by
    calc
      eCount left + eCount right = eCount W := by
        rw [hword, eCount_append, eCount_append, hL]
        omega
      _ = u₀ := hcount
  omega

/-- The contextual form of equation (25) needed by the reflection induction.
The hypotheses say that all `e` letters are in the left context of the
displayed long side. -/
def ContextualReplacement : Prop :=
  ∀ (u₀ p q : ℕ)
    (leftRows rightRows : Fin (2 ^ u₀) → List (Fin 2))
    (_hp : ∀ i, (leftRows i).length = p)
    (_hq : ∀ i, (rightRows i).length = q)
    (_hleftEnd : ∀ i, ∃ init, leftRows i = init ++ [(1 : Fin 2)])
    {left right : List Priority.A₂} {B : List (Fin 2)},
    eCount left = u₀ →
    eCount right = 0 →
    firstNormal
        (left ++ liftBinary (transpose p leftRows) ++ right) =
      encode u₀ B →
    ∃ j before after,
      B = before ++ leftRows j ++ after ∧
      firstNormal
          (left ++ liftBinary (transpose q rightRows) ++ right) =
        encode u₀ (before ++ rightRows j ++ after)

private theorem normal_after_housekeeping
    (left right : List Priority.A₂) (i : Fin 4)
    {W W' N : List Priority.A₂}
    (hwords :
      (W = left ++ housekeepingF i ++ right ∧
        W' = left ++ housekeepingE i ++ right) ∨
      (W = left ++ housekeepingE i ++ right ∧
        W' = left ++ housekeepingF i ++ right))
    (hnormal : firstNormal W = N) :
    firstNormal W' = N := by
  rcases hwords with ⟨hW, hW'⟩ | ⟨hW, hW'⟩
  · calc
      firstNormal W' =
          firstNormal (left ++ housekeepingE i ++ right) :=
        congrArg firstNormal hW'
      _ = firstNormal (left ++ housekeepingF i ++ right) :=
        (firstNormal_housekeeping left right i).symm
      _ = firstNormal W := congrArg firstNormal hW.symm
      _ = N := hnormal
  · calc
      firstNormal W' =
          firstNormal (left ++ housekeepingF i ++ right) :=
        congrArg firstNormal hW'
      _ = firstNormal (left ++ housekeepingE i ++ right) :=
        firstNormal_housekeeping left right i
      _ = firstNormal W := congrArg firstNormal hW.symm
      _ = N := hnormal

private theorem binary_row_step (F E : Fin r → List (Fin n))
    (j : Fin (t n r)) (before after : List (Fin 2)) :
    ThueStep (binarySystem F E)
      (before ++ paddedLeftRows F E j ++ after)
      (before ++ paddedRightRows F E j ++ after) :=
  ⟨before, after, paddedLeftRows F E j, paddedRightRows F E j,
    ⟨j, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

private theorem decode_long_forward
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X : List (Fin n))
    (B : List (Fin 2))
    {W W' left right : List Priority.A₂}
    (hreachable : ThueEq (binarySystem F E)
      ((Precompression.embedding F E).encode X) B)
    (hnormal : firstNormal W = encode (u n r) B)
    (hno : NoAAA (firstNormal W))
    (hcount : eCount W = u n r)
    (hW : W = left ++ leftLong F E ++ right)
    (hW' : W' = left ++ rightLong F E ++ right) :
    ∃ B',
      ThueEq (binarySystem F E)
        ((Precompression.embedding F E).encode X) B' ∧
      firstNormal W' = encode (u n r) B' := by
  have hrequire : LongRunRequirement (u n r) (2 * t n r) := by
    simpa [t, u, powerCount] using
      longRunRequirement_two_power (u n r)
  obtain ⟨hleft, hright⟩ := context_counts_of_long
    (leftShape F E) hrequire hno hcount hW (leftLong_eCount F E)
  have hclean :
      firstNormal
          (left ++ liftBinary (transpose (Precompression.leftWidth F E)
            (paddedLeftRows F E)) ++ right) =
        encode (u n r) B := by
    rw [← leftLong, ← hW]
    exact hnormal
  obtain ⟨j, before, after, hB, hnew⟩ :=
    hselect (u n r)
      (Precompression.leftWidth F E) (Precompression.rightWidth F E)
      (paddedLeftRows F E) (paddedRightRows F E)
      (paddedLeftRows_length F E) (paddedRightRows_length F E)
      (paddedLeftRows_ends_b F E)
      hleft hright hclean
  let B' := before ++ paddedRightRows F E j ++ after
  have hbinaryStep : ThueStep (binarySystem F E) B B' := by
    rw [hB]
    exact binary_row_step F E j before after
  refine ⟨B', hreachable.tail hbinaryStep, ?_⟩
  rw [hW']
  exact hnew

private theorem decode_long_reverse
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X : List (Fin n))
    (B : List (Fin 2))
    {W W' left right : List Priority.A₂}
    (hreachable : ThueEq (binarySystem F E)
      ((Precompression.embedding F E).encode X) B)
    (hnormal : firstNormal W = encode (u n r) B)
    (hno : NoAAA (firstNormal W))
    (hcount : eCount W = u n r)
    (hW : W = left ++ rightLong F E ++ right)
    (hW' : W' = left ++ leftLong F E ++ right) :
    ∃ B',
      ThueEq (binarySystem F E)
        ((Precompression.embedding F E).encode X) B' ∧
      firstNormal W' = encode (u n r) B' := by
  have hrequire : LongRunRequirement (u n r) (2 * t n r) := by
    simpa [t, u, powerCount] using
      longRunRequirement_two_power (u n r)
  obtain ⟨hleft, hright⟩ := context_counts_of_long
    (rightShape F E) hrequire hno hcount hW (rightLong_eCount F E)
  have hclean :
      firstNormal
          (left ++ liftBinary (transpose (Precompression.rightWidth F E)
            (paddedRightRows F E)) ++ right) =
        encode (u n r) B := by
    rw [← rightLong, ← hW]
    exact hnormal
  obtain ⟨j, before, after, hB, hnew⟩ :=
    hselect (u n r)
      (Precompression.rightWidth F E) (Precompression.leftWidth F E)
      (paddedRightRows F E) (paddedLeftRows F E)
      (paddedRightRows_length F E) (paddedLeftRows_length F E)
      (paddedRightRows_ends_b F E)
      hleft hright hclean
  let B' := before ++ paddedLeftRows F E j ++ after
  have hbinaryStep : ThueStep (binarySystem F E) B B' := by
    rw [hB]
    exact thueStep_symm (binary_row_step F E j before after)
  refine ⟨B', hreachable.tail hbinaryStep, ?_⟩
  rw [hW']
  exact hnew

private theorem decode_step_of_contextual
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X : List (Fin n))
    {W W' : List Priority.A₂}
    (hdecode : ∃ B,
      ThueEq (binarySystem F E)
          ((Precompression.embedding F E).encode X) B ∧
        firstNormal W = encode (u n r) B)
    (hstep : ThueStep
      (stage₂System (leftLong F E) (rightLong F E)) W W') :
    ∃ B,
      ThueEq (binarySystem F E)
          ((Precompression.embedding F E).encode X) B ∧
        firstNormal W' = encode (u n r) B := by
  obtain ⟨B, hreachable, hnormal⟩ := hdecode
  have hno : NoAAA (firstNormal W) := by
    rw [hnormal]
    exact noAAA_of_binary_reachable F E X hreachable
  have hcount : eCount W = u n r := by
    have h := congrArg eCount hnormal
    simpa only [firstNormal_eCount, encode_eCount] using h
  rcases hstep with ⟨left, right, x, y, ⟨i, hi⟩, hwords⟩
  injection hi with hx hy
  subst x
  subst y
  fin_cases i
  · refine ⟨B, hreachable, normal_after_housekeeping left right 0 ?_ hnormal⟩
    change
      (W = left ++ housekeepingF 0 ++ right ∧
        W' = left ++ housekeepingE 0 ++ right) ∨
      (W = left ++ housekeepingE 0 ++ right ∧
        W' = left ++ housekeepingF 0 ++ right) at hwords
    exact hwords
  · refine ⟨B, hreachable, normal_after_housekeeping left right 1 ?_ hnormal⟩
    change
      (W = left ++ housekeepingF 1 ++ right ∧
        W' = left ++ housekeepingE 1 ++ right) ∨
      (W = left ++ housekeepingE 1 ++ right ∧
        W' = left ++ housekeepingF 1 ++ right) at hwords
    exact hwords
  · refine ⟨B, hreachable, normal_after_housekeeping left right 2 ?_ hnormal⟩
    change
      (W = left ++ housekeepingF 2 ++ right ∧
        W' = left ++ housekeepingE 2 ++ right) ∨
      (W = left ++ housekeepingE 2 ++ right ∧
        W' = left ++ housekeepingF 2 ++ right) at hwords
    exact hwords
  · refine ⟨B, hreachable, normal_after_housekeeping left right 3 ?_ hnormal⟩
    change
      (W = left ++ housekeepingF 3 ++ right ∧
        W' = left ++ housekeepingE 3 ++ right) ∨
      (W = left ++ housekeepingE 3 ++ right ∧
        W' = left ++ housekeepingF 3 ++ right) at hwords
    exact hwords
  · simp only [stage₂F, stage₂E] at hwords
    rcases hwords with ⟨hW, hW'⟩ | ⟨hW, hW'⟩
    · exact decode_long_forward hselect F E X B hreachable hnormal hno
        hcount hW hW'
    · exact decode_long_reverse hselect F E X B hreachable hnormal hno
        hcount hW hW'

/-- Equation (25), packaged as the invariant needed in the remainder of the
construction: every reachable word has the normal form of a reachable binary
word. -/
theorem decode_reachable_of_contextual
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X : List (Fin n))
    {W : List Priority.A₂}
    (h : ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (priorityEncode F E X) W) :
    ∃ B,
      ThueEq (binarySystem F E)
          ((Precompression.embedding F E).encode X) B ∧
        firstNormal W = encode (u n r) B := by
  induction h with
  | refl =>
      exact ⟨(Precompression.embedding F E).encode X,
        Relation.ReflTransGen.refl,
        by simp [priorityEncode]⟩
  | tail _ hstep ih =>
      exact decode_step_of_contextual hselect F E X ih hstep

theorem reachableNoAAA_of_contextual
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X : List (Fin n)) :
    ReachableNoAAA (leftLong F E) (rightLong F E)
      (priorityEncode F E X) := by
  intro W hW
  obtain ⟨B, hbinary, hnormal⟩ :=
    decode_reachable_of_contextual hselect F E X hW
  rw [hnormal]
  exact noAAA_of_binary_reachable F E X hbinary

theorem priority_thueEq_iff_of_contextual
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) (X Y : List (Fin n)) :
    ThueEq (finiteSystem F E) X Y ↔
      ThueEq (stage₂System (leftLong F E) (rightLong F E))
        (priorityEncode F E X) (priorityEncode F E Y) := by
  constructor
  · intro hXY
    have hbinary := (source_binary_iff F E X Y).mp hXY
    simpa [priorityEncode] using simulate_binary F E hbinary
  · intro hXY
    obtain ⟨B, hbinary, hnormal⟩ :=
      decode_reachable_of_contextual hselect F E X hXY
    have hencoded :
        encode (u n r) ((Precompression.embedding F E).encode Y) =
          encode (u n r) B := by
      simpa [priorityEncode] using hnormal
    have hB : (Precompression.embedding F E).encode Y = B :=
      priority_encode_injective (u n r) hencoded
    rw [← hB] at hbinary
    exact (source_binary_iff F E X Y).mpr hbinary

theorem priorityBridge_of_contextual
    (hselect : ContextualReplacement)
    (F E : Fin r → List (Fin n)) : PriorityBridge F E where
  leftShape := leftShape F E
  rightShape := rightShape F E
  thueEq_iff := priority_thueEq_iff_of_contextual hselect F E
  reachableNoAAA := reachableNoAAA_of_contextual hselect F E

theorem compressionTheorem_of_contextual
    (hselect : ContextualReplacement) : CompressionTheorem := by
  apply compressionTheorem_of_priorityBridges
  intro n r _hn _hr F E
  exact priorityBridge_of_contextual hselect F E

theorem contextualReplacement : ContextualReplacement := by
  intro u p q leftRows rightRows hp hq hleftEnd
    left right B hleft hright hclean
  exact Priority.ContextualSelection.replace_transpose_clean
    u p q leftRows rightRows hp hq hleftEnd
      hleft hright hclean

/-- Matiyasevich's complete finite-system compression theorem. -/
theorem compressionTheorem : CompressionTheorem :=
  compressionTheorem_of_contextual contextualReplacement

end Compression
end Matiyasevich1993
end Thue
end Undecidability
