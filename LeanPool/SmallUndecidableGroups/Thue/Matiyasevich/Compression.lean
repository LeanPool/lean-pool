/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.PriorityStage
public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.BinaryStage

/-!
The downstream composition of Sections 2.3--2.5.  The row-selection module
is imported below once its contextual normalization theorem is available;
the code-language lemmas here are independent of that combinatorics.
-/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace PowerPadding

open Priority

variable {r : ℕ} {A : Type*}

/-- Every original relation index occurs among the indices padded up to the
least power of two. -/
def includeIndex (i : Fin r) : Fin (powerCount r) :=
  Fin.castLE (relationCount_le_powerCount r) i

@[simp] theorem paddedIndex_include (hr : 0 < r) (i : Fin r) :
    paddedIndex hr (includeIndex i) = i := by
  apply Fin.ext
  simp [paddedIndex, includeIndex, i.isLt]

/-- Repeating the first relation until the relation count is a power of two
does not change the underlying set of Thue relations. -/
theorem finiteSystem_paddedSide (hr : 0 < r)
    (F E : Fin r → List A) :
    finiteSystem (paddedSide hr F) (paddedSide hr E) =
      finiteSystem F E := by
  ext relation
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨paddedIndex hr i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨includeIndex i, ?_⟩
    simp only [paddedSide, paddedIndex_include]

end PowerPadding
end Matiyasevich1993
end Thue
end Undecidability

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Precompression

open Padding Binary Priority

variable {n r : ℕ}

/-- Number of relations after the positive common-length padding stage. -/
def relationCount (n r : ℕ) : ℕ := r + (n + 1)

/-- Left binary rows obtained after Sections 2.2 and 2.3. -/
def leftRows (F E : Fin r → List (Fin n)) :
    Fin (relationCount n r) → List (Fin 2) :=
  Binary.stage₂PrimeF (Padding.stage₁F F E)

/-- Right binary rows obtained after Sections 2.2 and 2.3. -/
def rightRows (F E : Fin r → List (Fin n)) :
    Fin (relationCount n r) → List (Fin 2) :=
  Binary.stage₂PrimeE (Padding.stage₁E F E)

/-- Common length of the left binary rows. -/
def leftWidth (F E : Fin r → List (Fin n)) : ℕ :=
  Padding.p F E * (n + 5)

/-- Common length of the right binary rows. -/
def rightWidth (F E : Fin r → List (Fin n)) : ℕ :=
  Padding.q F E * (n + 5)

theorem relationCount_pos (n r : ℕ) : 0 < relationCount n r := by
  simp [relationCount]

private theorem scaledWidth_pos (k : ℕ) (hk : 0 < k) :
    0 < k * (n + 5) :=
  Nat.mul_pos hk (by omega)

private theorem two_le_scaledWidth (k : ℕ) (hk : 0 < k) :
    2 ≤ k * (n + 5) := by
  calc
    2 ≤ n + 5 := by omega
    _ = 1 * (n + 5) := by simp
    _ ≤ k * (n + 5) := Nat.mul_le_mul_right _ hk

theorem leftWidth_pos (F E : Fin r → List (Fin n)) :
    0 < leftWidth F E :=
  scaledWidth_pos _ (Padding.p_pos F E)

theorem rightWidth_pos (F E : Fin r → List (Fin n)) :
    0 < rightWidth F E := by
  unfold rightWidth Padding.q
  exact scaledWidth_pos _ (Nat.succ_pos _)

theorem leftWidth_ge_two (F E : Fin r → List (Fin n)) :
    2 ≤ leftWidth F E :=
  two_le_scaledWidth _ (Padding.p_pos F E)

theorem rightWidth_ge_two (F E : Fin r → List (Fin n)) :
    2 ≤ rightWidth F E := by
  unfold rightWidth Padding.q
  exact two_le_scaledWidth _ (Nat.succ_pos _)

@[simp] theorem leftRows_length (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    (leftRows F E i).length = leftWidth F E := by
  simpa [leftRows, leftWidth, relationCount, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    Binary.stage₂PrimeF_common_length (Padding.stage₁F F E)
      (Padding.p F E) (Padding.stage₁F_length F E) i

@[simp] theorem rightRows_length (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    (rightRows F E i).length = rightWidth F E := by
  simpa [rightRows, rightWidth, relationCount, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
    Binary.stage₂PrimeE_common_length (Padding.stage₁E F E)
      (Padding.q F E) (Padding.stage₁E_length F E) i

theorem stage₁F_nonempty (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) : Padding.stage₁F F E i ≠ [] := by
  rw [← List.length_pos_iff, Padding.stage₁F_length F E i]
  exact Padding.p_pos F E

theorem stage₁E_nonempty (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) : Padding.stage₁E F E i ≠ [] := by
  rw [← List.length_pos_iff, Padding.stage₁E_length F E i]
  simp [Padding.q]

theorem leftRows_starts_aa (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    ∃ tail, leftRows F E i = (0 : Fin 2) :: 0 :: tail :=
  Binary.rho₁_starts_aa (stage₁F_nonempty F E i)

theorem rightRows_starts_aa (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    ∃ tail, rightRows F E i = (0 : Fin 2) :: 0 :: tail :=
  Binary.rho₁_starts_aa (stage₁E_nonempty F E i)

/-- Every nonempty word has a binary code ending in `b`. -/
theorem rho₁_ends_b {N : ℕ} (W : List (Fin N)) (hW : W ≠ []) :
    ∃ init, Binary.rho₁ N W = init ++ [(1 : Fin 2)] := by
  induction W with
  | nil => exact (hW rfl).elim
  | cons j W ih =>
      cases W with
      | nil =>
          simpa [Binary.rho₁] using Binary.rho₁Letter_ends_b j
      | cons k W =>
          obtain ⟨init, hinit⟩ := ih (by simp)
          refine ⟨Binary.rho₁Letter N j ++ init, ?_⟩
          rw [Binary.rho₁_cons, hinit, List.append_assoc]

theorem leftRows_ends_b (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    ∃ init, leftRows F E i = init ++ [(1 : Fin 2)] :=
  rho₁_ends_b (Padding.stage₁F F E i) (stage₁F_nonempty F E i)

theorem rightRows_ends_b (F E : Fin r → List (Fin n))
    (i : Fin (relationCount n r)) :
    ∃ init, rightRows F E i = init ++ [(1 : Fin 2)] :=
  rho₁_ends_b (Padding.stage₁E F E i) (stage₁E_nonempty F E i)

/-- The already verified first two stages, packaged as one embedding. -/
def embedding (F E : Fin r → List (Fin n)) :
    Embedding (finiteSystem F E)
      (finiteSystem (leftRows F E) (rightRows F E)) :=
  Embedding.comp
    (Binary.embedding (Padding.stage₁F F E) (Padding.stage₁E F E)
      (Padding.p F E) (Padding.q F E)
      (Padding.p_pos F E)
      (by simp [Padding.q])
      (Padding.stage₁F_length F E)
      (Padding.stage₁E_length F E))
    (Padding.embedding F E)

end Precompression
end Matiyasevich1993
end Thue
end Undecidability

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Compression

open Padding Binary Priority Precompression

theorem noAAA_iff_not_infix {W : List Priority.A₂} :
    NoAAA W ↔ ¬ [a, a, a] <:+: W := by
  constructor
  · intro h hinfix
    obtain ⟨l, r, hword⟩ := hinfix
    exact h ⟨l, r, hword.symm⟩
  · intro h ⟨l, r, hword⟩
    exact h ⟨l, r, hword.symm⟩

/-- Avoidance of `000` is preserved by the inclusion of the binary alphabet
into `{a,b,e}`. -/
theorem noAAA_liftBinary {W : List (Fin 2)}
    (h : ¬ ∃ l r, W = l ++ [(0 : Fin 2), 0, 0] ++ r) :
    NoAAA (liftBinary W) := by
  rw [noAAA_iff_not_infix]
  intro hinfix
  obtain ⟨Z, hZW, hmap⟩ := (List.infix_map_iff).mp hinfix
  have hZ : Z = [(0 : Fin 2), 0, 0] := by
    apply liftBinary_injective
    simpa [liftBinary, liftBit, a] using hmap.symm
  subst Z
  obtain ⟨l, r, hword⟩ := hZW
  exact h ⟨l, r, hword.symm⟩

private theorem triple_not_infix_marker (u : ℕ) :
    ¬ [a, a, a] <:+: ([a] ++ List.replicate u e) := by
  intro hinfix
  have hcount := List.IsInfix.count_le a hinfix
  simp only [a, Fin.isValue, List.count_cons_self, List.nodup_cons, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_self, List.mem_cons, or_false,
    List.count_eq_one_of_mem, Nat.reduceAdd, e, List.cons_append, List.nil_append,
    Nat.reduceLeDiff] at hcount
  have hzero : List.count a (List.replicate u e) = 0 := by
    rw [List.count_eq_zero]
    simp [a, e]
  have hzero' : List.count (0 : Priority.A₂)
      (List.replicate u 2) = 0 := by
    simpa [a, e] using hzero
  rw [hzero'] at hcount
  omega

/-- Appending the marker `a e^u` preserves `aaa`-avoidance when the binary
prefix is empty or ends in `b`. -/
theorem noAAA_append_marker {W : List Priority.A₂}
    (hno : NoAAA W)
    (hend : W = [] ∨ ∃ init, W = init ++ [b]) (u : ℕ) :
    NoAAA (W ++ [a] ++ List.replicate u e) := by
  rw [noAAA_iff_not_infix] at hno ⊢
  rw [List.append_assoc, List.infix_append_iff]
  rintro (hinW | hinMarker | ⟨l₁, l₂, hsplit, hl₁, hl₂⟩)
  · exact hno hinW
  · exact triple_not_infix_marker u hinMarker
  · by_cases hl₁nil : l₁ = []
    · subst l₁
      simp only [List.nil_append] at hsplit
      subst l₂
      exact triple_not_infix_marker u hl₂.isInfix
    · have hl₁prefix : l₁ <+: List.replicate 3 a := by
        refine ⟨l₂, ?_⟩
        simpa using hsplit.symm
      have hl₁rep : l₁ = List.replicate l₁.length a :=
        (List.prefix_replicate_iff.mp hl₁prefix).2
      have hl₁pos : 1 ≤ l₁.length :=
        List.length_pos_iff.mpr hl₁nil
      have haSuffix : [a] <:+ l₁ := by
        rw [hl₁rep]
        exact List.suffix_replicate_iff.mpr
          ⟨by simpa using hl₁pos, by simp⟩
      have haW : [a] <:+ W := haSuffix.trans hl₁
      rcases hend with rfl | ⟨init, rfl⟩
      · simp at haW
      · have hab : a = b :=
          List.singleton_suffix_append_singleton_iff.mp haW
        exact (by decide : a ≠ b) hab

/-- The first-priority normal form of an encoded `rho₁` word has no
occurrence of `aaa`, including across its trailing marker. -/
theorem noAAA_encode_rho₁ {N u : ℕ} (W : List (Fin N)) :
    NoAAA (Priority.encode u (Binary.rho₁ N W)) := by
  apply noAAA_append_marker
  · exact noAAA_liftBinary (Binary.rho₁_noAAA W)
  · cases W with
    | nil => exact Or.inl rfl
    | cons x W =>
        right
        obtain ⟨init, hinit⟩ := Precompression.rho₁_ends_b (x :: W) (by simp)
        refine ⟨liftBinary init, ?_⟩
        rw [hinit, liftBinary_append]
        simp [liftBinary, liftBit, b]

/-! ### The concrete long words -/

variable {n r : ℕ}

/-- The exponent and power-of-two row count used in Sections 2.3--2.4. -/
def u (n r : ℕ) : ℕ := exponent (Precompression.relationCount n r)

/-- The least power-of-two row count large enough for the precompressed relation set. -/
def t (n r : ℕ) : ℕ := powerCount (Precompression.relationCount n r)

theorem t_pos (n r : ℕ) : 0 < t n r :=
  powerCount_pos (Precompression.relationCount n r)

/-- The binary rule rows, repeated to the least power of two. -/
def paddedLeftRows (F E : Fin r → List (Fin n)) :
    Fin (t n r) → List (Fin 2) :=
  paddedSide (Precompression.relationCount_pos n r)
    (Precompression.leftRows F E)

/-- The precompressed right-hand rule words padded to the power-of-two row count. -/
def paddedRightRows (F E : Fin r → List (Fin n)) :
    Fin (t n r) → List (Fin 2) :=
  paddedSide (Precompression.relationCount_pos n r)
    (Precompression.rightRows F E)

/-- The binary Thue system formed by the padded precompressed rule rows. -/
def binarySystem (F E : Fin r → List (Fin n)) : ThueSystem (Fin 2) :=
  finiteSystem (paddedLeftRows F E) (paddedRightRows F E)

theorem binarySystem_eq_unpadded (F E : Fin r → List (Fin n)) :
    binarySystem F E =
      finiteSystem (Precompression.leftRows F E)
        (Precompression.rightRows F E) := by
  unfold binarySystem paddedLeftRows paddedRightRows
  exact PowerPadding.finiteSystem_paddedSide
    (Precompression.relationCount_pos n r)
    (Precompression.leftRows F E) (Precompression.rightRows F E)

@[simp] theorem paddedLeftRows_length (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    (paddedLeftRows F E i).length = Precompression.leftWidth F E :=
  Precompression.leftRows_length F E _

@[simp] theorem paddedRightRows_length (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    (paddedRightRows F E i).length = Precompression.rightWidth F E :=
  Precompression.rightRows_length F E _

theorem paddedLeftRows_starts_aa (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    ∃ tail, paddedLeftRows F E i = (0 : Fin 2) :: 0 :: tail :=
  Precompression.leftRows_starts_aa F E _

theorem paddedRightRows_starts_aa (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    ∃ tail, paddedRightRows F E i = (0 : Fin 2) :: 0 :: tail :=
  Precompression.rightRows_starts_aa F E _

theorem paddedLeftRows_ends_b (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    ∃ init, paddedLeftRows F E i = init ++ [(1 : Fin 2)] :=
  Precompression.leftRows_ends_b F E _

theorem paddedRightRows_ends_b (F E : Fin r → List (Fin n))
    (i : Fin (t n r)) :
    ∃ init, paddedRightRows F E i = init ++ [(1 : Fin 2)] :=
  Precompression.rightRows_ends_b F E _

/-- Any binary word reachable from the preceding encoding is still a
`rho₁`-codeword.  This is the synchronization fact from Section 2.3,
transported across the harmless power-of-two relation padding. -/
theorem decode_binary_reachable (F E : Fin r → List (Fin n))
    (X : List (Fin n)) {W : List (Fin 2)}
    (h : ThueEq (binarySystem F E)
      ((Precompression.embedding F E).encode X) W) :
    ∃ Z : List (Fin (n + 1)),
      W = Binary.rho₁ (n + 1) Z ∧
      ThueEq (Padding.stage₁System F E) (Padding.encode F E X) Z := by
  have h' : ThueEq
      (finiteSystem (Precompression.leftRows F E)
        (Precompression.rightRows F E))
      (Binary.rho₁ (n + 1) (Padding.encode F E X)) W := by
    rw [binarySystem_eq_unpadded] at h
    have hencode :
        (Precompression.embedding F E).encode X =
          Binary.rho₁ (n + 1) (Padding.encode F E X) := rfl
    simpa only [hencode] using h
  simpa [Precompression.leftRows, Precompression.rightRows,
    Binary.stage₂PrimeSystem, Padding.stage₁System] using
    (Binary.decode_thueEq (Padding.stage₁F F E) (Padding.stage₁E F E)
      (Precompression.stage₁F_nonempty F E)
      (Precompression.stage₁E_nonempty F E) h')

theorem noAAA_of_binary_reachable (F E : Fin r → List (Fin n))
    (X : List (Fin n)) {W : List (Fin 2)}
    (h : ThueEq (binarySystem F E)
      ((Precompression.embedding F E).encode X) W) :
    NoAAA (Priority.encode (u n r) W) := by
  obtain ⟨Z, rfl, _⟩ := decode_binary_reachable F E X h
  exact noAAA_encode_rho₁ Z

/-- The long sides (24), converted to the alphabet `{a,b,e}`. -/
def leftLong (F E : Fin r → List (Fin n)) : List Priority.A₂ :=
  liftBinary (transpose (Precompression.leftWidth F E)
    (paddedLeftRows F E))

/-- The transposed right-hand rule word lifted to the three-letter priority alphabet. -/
def rightLong (F E : Fin r → List (Fin n)) : List Priority.A₂ :=
  liftBinary (transpose (Precompression.rightWidth F E)
    (paddedRightRows F E))

@[simp] theorem leftLong_eCount (F E : Fin r → List (Fin n)) :
    eCount (leftLong F E) = 0 := by
  simp [leftLong]

@[simp] theorem rightLong_eCount (F E : Fin r → List (Fin n)) :
    eCount (rightLong F E) = 0 := by
  simp [rightLong]

theorem leftLong_length (F E : Fin r → List (Fin n)) :
    (leftLong F E).length = Precompression.leftWidth F E * t n r := by
  simp [leftLong, liftBinary, transpose_length]

theorem rightLong_length (F E : Fin r → List (Fin n)) :
    (rightLong F E).length = Precompression.rightWidth F E * t n r := by
  simp [rightLong, liftBinary, transpose_length]

theorem leftLong_ne_nil (F E : Fin r → List (Fin n)) :
    leftLong F E ≠ [] := by
  rw [← List.length_pos_iff, leftLong_length]
  exact Nat.mul_pos (Precompression.leftWidth_pos F E) (t_pos n r)

theorem rightLong_ne_nil (F E : Fin r → List (Fin n)) :
    rightLong F E ≠ [] := by
  rw [← List.length_pos_iff, rightLong_length]
  exact Nat.mul_pos (Precompression.rightWidth_pos F E) (t_pos n r)

/-- The actual long words in the final two-letter, three-relation system. -/
def U₃ (F E : Fin r → List (Fin n)) : List (Fin 2) := rho₂ (leftLong F E)

/-- The final binary encoding of the transposed right-hand rule word. -/
def V₃ (F E : Fin r → List (Fin n)) : List (Fin 2) := rho₂ (rightLong F E)

theorem U₃_ne_nil (F E : Fin r → List (Fin n)) : U₃ F E ≠ [] :=
  rho₂_ne_nil (leftLong_ne_nil F E)

theorem V₃_ne_nil (F E : Fin r → List (Fin n)) : V₃ F E ≠ [] :=
  rho₂_ne_nil (rightLong_ne_nil F E)

/-- The word map through the first priority system, before applying `rho₂`. -/
def priorityEncode (F E : Fin r → List (Fin n))
    (W : List (Fin n)) : List Priority.A₂ :=
  Priority.encode (u n r) ((Precompression.embedding F E).encode W)

/-- The composed word map from `T₀` to `T₃`. -/
def fullEncode (F E : Fin r → List (Fin n))
    (W : List (Fin n)) : List (Fin 2) :=
  rho₂ (priorityEncode F E W)

theorem fullEncode_computable (F E : Fin r → List (Fin n)) :
    Computable (fullEncode F E) :=
  rho₂_computable.comp
    ((Priority.encode_computable (u n r)).comp
      (Precompression.embedding F E).encode_computable)

theorem fullEncode_ne_nil (F E : Fin r → List (Fin n))
    (W : List (Fin n)) : fullEncode F E W ≠ [] := by
  apply rho₂_ne_nil
  exact Priority.encode_ne_nil _ _

/-! ### Interface of the priority-stage proof -/

/-- The shape, equivalence, and reachability invariants from Section 2.4
for words from the preceding encodings.  The equivalence applies to encoded
source words, rather than to arbitrary words of the intermediate system. -/
structure PriorityBridge (F E : Fin r → List (Fin n)) : Prop where
  leftShape : LongShape (2 * t n r) (leftLong F E)
  rightShape : LongShape (2 * t n r) (rightLong F E)
  thueEq_iff : ∀ X Y : List (Fin n),
    ThueEq (finiteSystem F E) X Y ↔
      ThueEq (stage₂System (leftLong F E) (rightLong F E))
        (priorityEncode F E X) (priorityEncode F E Y)
  reachableNoAAA : ∀ X : List (Fin n),
    ReachableNoAAA (leftLong F E) (rightLong F E)
      (priorityEncode F E X)

/-- The final decoder combines with `PriorityBridge` to give an
equivalence-reflecting encoding into the three-relation system. -/
def embeddingOfBridge (F E : Fin r → List (Fin n))
    (bridge : PriorityBridge F E) :
    Embedding (finiteSystem F E) (baseSystem (U₃ F E) (V₃ F E)) where
  encode := fullEncode F E
  encode_computable := fullEncode_computable F E
  thueEq_iff := by
    intro X Y
    apply (bridge.thueEq_iff X Y).trans
    have hcount : eCount (priorityEncode F E X) = u n r :=
      Priority.encode_eCount _ _
    have hrun : LongRunRequirement (u n r) (2 * t n r) := by
      simpa [t, u, powerCount] using longRunRequirement_two_power (u n r)
    have hfinal := rho₂_iff_of_priority_invariants
      (u := u n r) (run := 2 * t n r)
      (L := leftLong F E) (M := rightLong F E)
      (X := priorityEncode F E X)
      (hLM := by simp)
      (hX := hcount)
      (bridge.reachableNoAAA X)
      hrun
      bridge.leftShape bridge.rightShape (priorityEncode F E Y)
    simpa [U₃, V₃, fullEncode] using hfinal

/-- A bridge for every finite source system is the final ingredient of the
public compression theorem. -/
theorem compressionTheorem_of_priorityBridges
    (bridges : ∀ (n r : ℕ), 0 < n → 0 < r →
      (F E : Fin r → List (Fin n)) → PriorityBridge F E) :
    CompressionTheorem := by
  intro n r hn hr F E
  refine ⟨U₃ F E, V₃ F E, U₃_ne_nil F E, V₃_ne_nil F E,
    embeddingOfBridge F E (bridges n r hn hr F E), ?_⟩
  exact fullEncode_ne_nil F E

end Compression
end Matiyasevich1993
end Thue
end Undecidability
