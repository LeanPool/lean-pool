/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.Compression
public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.RowSelection

/-! ### Housekeeping derivations are `T₂` derivations -/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Compression

open Priority Priority.RowSelection Precompression

variable {n r : ℕ}

private theorem width_gt_two (F E : Fin r → List (Fin n)) :
    2 < Precompression.leftWidth F E ∧
      2 < Precompression.rightWidth F E := by
  have hp := Padding.p_pos F E
  have hmul (k : ℕ) (hk : 0 < k) : 2 < k * (n + 5) := by
    calc
      2 < n + 5 := by omega
      _ = 1 * (n + 5) := by simp
      _ ≤ k * (n + 5) := Nat.mul_le_mul_right _ hk
  constructor
  · exact hmul _ hp
  · simpa [Precompression.rightWidth, Padding.q] using
      hmul (Padding.p F E + 1) (Nat.succ_pos _)

private theorem longShape_of_prefix_and_last
    {W : List Priority.A₂} {run : ℕ}
    (hprefix : ∃ tail, W = List.replicate run Priority.a ++ tail)
    (hlength : run < W.length)
    (hlast : ∃ init, W = init ++ [Priority.b]) : LongShape run W := by
  obtain ⟨tail, htail⟩ := hprefix
  have htail_ne : tail ≠ [] := by
    intro hempty
    subst tail
    rw [htail] at hlength
    simp at hlength
  have hlastW : W.getLast? = some Priority.b := by
    obtain ⟨init, rfl⟩ := hlast
    simp
  have hlastTail : tail.getLast? = some Priority.b := by
    calc
      tail.getLast? = (List.replicate run Priority.a ++ tail).getLast? :=
        (List.getLast?_append_of_ne_nil _ htail_ne).symm
      _ = W.getLast? := congrArg List.getLast? htail.symm
      _ = some Priority.b := hlastW
  obtain ⟨middle, hmiddle⟩ := List.getLast?_eq_some_iff.mp hlastTail
  exact ⟨middle, by rw [htail, hmiddle, List.append_assoc]⟩

private theorem transposedShape
    (rows : Fin (t n r) → List (Fin 2)) (width : ℕ)
    (hwidth : 2 < width)
    (hlength : ∀ i, (rows i).length = width)
    (hstarts : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail)
    (hends : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    LongShape (2 * t n r) (liftBinary (transpose width rows)) := by
  apply longShape_of_prefix_and_last
  · obtain ⟨tail, htail⟩ := transpose_starts_two_columns rows
      (Nat.le_of_lt hwidth) hstarts
    refine ⟨liftBinary tail, ?_⟩
    rw [htail, liftBinary_append]
    simp [liftBinary, liftBit, Priority.a]
  · simp only [liftBinary, List.length_map, transpose_length]
    exact Nat.mul_lt_mul_of_pos_right hwidth (t_pos n r)
  · exact liftBinary_transpose_ends_b rows (t_pos n r) (by omega)
      hlength hends

/-- The transposed left long word begins with `2t` copies of `a` and ends
with `b`, exactly as required in the page-50 counting argument. -/
theorem leftShape (F E : Fin r → List (Fin n)) :
    LongShape (2 * t n r) (leftLong F E) := by
  simpa [leftLong] using transposedShape (paddedLeftRows F E)
    (Precompression.leftWidth F E) (width_gt_two F E).1
    (paddedLeftRows_length F E) (paddedLeftRows_starts_aa F E)
    (paddedLeftRows_ends_b F E)

/-- The analogous shape theorem for the right long word. -/
theorem rightShape (F E : Fin r → List (Fin n)) :
    LongShape (2 * t n r) (rightLong F E) := by
  simpa [rightLong] using transposedShape (paddedRightRows F E)
    (Precompression.rightWidth F E) (width_gt_two F E).2
    (paddedRightRows_length F E) (paddedRightRows_starts_aa F E)
    (paddedRightRows_ends_b F E)

/-- The inclusion of the four housekeeping-rule indices into the five priority-rule indices. -/
def housekeepingIndex (i : Fin 4) : Fin 5 := Fin.castLE (by omega) i

@[simp] theorem stage₂F_housekeepingIndex (L : List Priority.A₂)
    (i : Fin 4) :
    stage₂F L (housekeepingIndex i) = housekeepingF i := by
  fin_cases i <;> simp only [stage₂F, housekeepingIndex, Fin.zero_eta, Fin.isValue, Fin.castLE_zero,
    Matrix.cons_val_zero, housekeepingF, List.cons.injEq, and_true, and_self, Fin.mk_one,
    Fin.reduceCastLE, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> decide

@[simp] theorem stage₂E_housekeepingIndex (M : List Priority.A₂)
    (i : Fin 4) :
    stage₂E M (housekeepingIndex i) = housekeepingE i := by
  fin_cases i <;> simp only [stage₂E, housekeepingIndex, Fin.zero_eta, Fin.isValue, Fin.castLE_zero,
    Matrix.cons_val_zero, housekeepingE, List.cons.injEq, and_true, Fin.mk_one,
    Fin.reduceCastLE, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> decide

theorem firstStep_to_thueStep (L M : List Priority.A₂)
    {X Y : List Priority.A₂} (h : FirstStep X Y) :
    ThueStep (stage₂System L M) X Y := by
  rcases h with ⟨l, s, i, rfl, rfl⟩
  exact ⟨l, s, housekeepingF i, housekeepingE i,
    ⟨housekeepingIndex i, by simp⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Every directed first-priority reduction is also a derivation in the
symmetric five-relation Thue system. -/
theorem firstEq_to_stage₂Eq (L M : List Priority.A₂)
    {X Y : List Priority.A₂} (h : FirstEq X Y) :
    ThueEq (stage₂System L M) X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (firstStep_to_thueStep L M hstep)

end Compression
end Matiyasevich1993
end Thue
end Undecidability

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Compression

open Priority Priority.RowSelection Precompression

variable {n r : ℕ}

/-- Normalize a padded transpose followed by an aligned expansion.  The
arbitrary final sampled bit is what lets the construction retain an
unrestricted right context. -/
private theorem firstEq_paddedTransposeLast_expand
    (u width : ℕ) (rows : Fin (2 ^ u) → List (Fin 2))
    (j : Fin (2 ^ u)) (z : Fin 2) (tail : List (Fin 2))
    (hlen : ∀ i, (rows i).length = width) :
    FirstEq
      (List.replicate u Priority.e ++
        liftBinary (paddedTransposeLast width rows j z ++ expand u tail))
      (liftBinary (rows j ++ z :: tail) ++ List.replicate u Priority.e) := by
  have hpad : 2 ^ u ∣ (paddedTransposeLast width rows j z).length := by
    refine ⟨width + 1, ?_⟩
    simpa [Nat.mul_comm] using paddedTransposeLast_length rows j z
  have htotal : 2 ^ u ∣
      (paddedTransposeLast width rows j z ++ expand u tail).length := by
    rw [List.length_append]
    exact Nat.dvd_add hpad (expand_length_dvd u tail)
  have hthin :
      thin u (paddedTransposeLast width rows j z ++ expand u tail) =
        rows j ++ z :: tail := by
    rw [thin_append_of_dvd u _ _ hpad,
      thin_paddedTranspose_last u width rows j z hlen, thin_expand]
    simp
  have h := firstNormal_reachable
    (List.replicate u Priority.e ++
      liftBinary (paddedTransposeLast width rows j z ++ expand u tail))
  rw [firstNormal_replicate_e_liftBinary u _ htotal, hthin] at h
  exact h

private theorem append_zero_eq_cons (right : List (Fin 2)) :
    ∃ z tail, right ++ [0] = z :: tail := by
  cases right with
  | nil => exact ⟨0, [], rfl⟩
  | cons z tail => exact ⟨z, tail ++ [0], rfl⟩

private theorem encode_append_eq (u : ℕ) (X Y : List (Fin 2)) :
    encode u (X ++ Y) = liftBinary X ++ encode u Y := by
  simp [encode, List.append_assoc]

/-- One directed binary row replacement is simulated by the four
housekeeping relations, one use of the long relation, and the housekeeping
relations again. -/
private theorem simulate_row (F E : Fin r → List (Fin n))
    (j : Fin (t n r)) (left right : List (Fin 2)) :
    ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (encode (u n r) (left ++ paddedLeftRows F E j ++ right))
      (encode (u n r) (left ++ paddedRightRows F E j ++ right)) := by
  obtain ⟨z, tail, hright⟩ := append_zero_eq_cons right
  let leftBlock := paddedTransposeLast
    (Precompression.leftWidth F E) (paddedLeftRows F E) j z ++
      expand (u n r) tail
  let rightBlock := paddedTransposeLast
    (Precompression.rightWidth F E) (paddedRightRows F E) j z ++
      expand (u n r) tail
  have liftBinary_nil : liftBinary [] = [] := rfl
  have hleft : FirstEq
      (List.replicate (u n r) Priority.e ++ liftBinary leftBlock)
      (encode (u n r) (paddedLeftRows F E j ++ right)) := by
    have h := firstEq_paddedTransposeLast_expand
      (u n r) (Precompression.leftWidth F E)
      (paddedLeftRows F E) j z tail (paddedLeftRows_length F E)
    have hrow : paddedLeftRows F E j ++ z :: tail =
        (paddedLeftRows F E j ++ right) ++ [0] := by
      rw [← hright]
      simp
    rw [hrow] at h
    convert h using 1 <;>
      (simp [leftBlock, encode, liftBinary_append, liftBit, Priority.a,
        liftBinary_nil, List.append_assoc]; try rfl)
  have hright' : FirstEq
      (List.replicate (u n r) Priority.e ++ liftBinary rightBlock)
      (encode (u n r) (paddedRightRows F E j ++ right)) := by
    have h := firstEq_paddedTransposeLast_expand
      (u n r) (Precompression.rightWidth F E)
      (paddedRightRows F E) j z tail (paddedRightRows_length F E)
    have hrow : paddedRightRows F E j ++ z :: tail =
        (paddedRightRows F E j ++ right) ++ [0] := by
      rw [← hright]
      simp
    rw [hrow] at h
    convert h using 1 <;>
      (simp [rightBlock, encode, liftBinary_append, liftBit, Priority.a,
        liftBinary_nil, List.append_assoc]; try rfl)
  have hlong : ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (List.replicate (u n r) Priority.e ++ liftBinary leftBlock)
      (List.replicate (u n r) Priority.e ++ liftBinary rightBlock) := by
    apply Relation.ReflTransGen.single
    refine ⟨List.replicate (u n r) Priority.e ++
        liftBinary (List.replicate (t n r - 1 - j.val) 0),
      liftBinary (List.replicate j.val 0 ++ [z] ++ expand (u n r) tail),
      leftLong F E, rightLong F E, ⟨4, by simp [stage₂F, stage₂E]⟩, ?_⟩
    left
    constructor <;>
      simp [leftBlock, rightBlock, paddedTransposeLast,
        leftLong, rightLong, liftBinary_append, List.append_assoc]
  have hinner : ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (encode (u n r) (paddedLeftRows F E j ++ right))
      (encode (u n r) (paddedRightRows F E j ++ right)) :=
    (thueEq_symm (firstEq_to_stage₂Eq _ _ hleft)).trans
      (hlong.trans (firstEq_to_stage₂Eq _ _ hright'))
  simpa [encode_append_eq, List.append_assoc] using
    thueEq_context (liftBinary left) [] hinner

/-- Forward half of Matiyasevich's priority-compression equivalence: every
binary rewrite, in arbitrary two-sided context, is simulated by the
five-relation system on `{a,b,e}`. -/
theorem simulate_binary (F E : Fin r → List (Fin n))
    {X Y : List (Fin 2)} (h : ThueEq (binarySystem F E) X Y) :
    ThueEq (stage₂System (leftLong F E) (rightLong F E))
      (encode (u n r) X) (encode (u n r) Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rcases hstep with ⟨left, right, x, y, ⟨j, hrow⟩, hwords⟩
      injection hrow with hx hy
      subst x
      subst y
      rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ih.trans (simulate_row F E j left right)
      · exact ih.trans (thueEq_symm (simulate_row F E j left right))

end Compression
end Matiyasevich1993
end Thue
end Undecidability
