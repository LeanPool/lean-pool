/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.Generated.GenusFiveCanonicalClassifierData
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCubicAtlas
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ChunkedLookup

/-!
# The genus-five cubic classifier, without a replay tree

This module classifies every connected loopless cubic core on eight vertices
against `GenusFiveCubicAtlas.atlas`, unconditionally and by kernel reduction
alone. It is the `n = 8` instance of the machinery that
`Certificate/GenusFourCanonicalClassifier.lean` runs at `n = 6`.

## Why the traversal is chunked

The single `decide` that works at `n = 6` does not work at `n = 8`:
the pruned traversal reaches 934 leaves, and reducing all of them
inside one kernel reduction was measured at over ten gigabytes of
resident set.  So the traversal is cut two rows deep.

`prunedCheck accept leaf (fuel + 1) (c :: cs) path` is *definitionally*
a `List.all` over `boundedCompositions c cs`, which is
`prunedCheck_cons` below.  Unfolding it twice leaves 22 independent
subgoals, the largest of them 130 leaves; those are the `chunk` lemmas.
The branches that unfolding exposes but `canonicalPrefix` rejects are
discharged wholesale by the `branches` lemmas, each a single cheap
`decide` over an explicit branch list.

The chunk proofs replay the generated payload data with a Boolean leaf check.
The soundness lemmas transfer each completed traversal to the original leaf decision.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveCanonicalClassifier
open Utilities.Certificate

open Utilities

open Utilities.Certificate.CubicMatrixReplay
open Utilities.Certificate.CubicMatrixReplay
open AtanasovRanganathan.Generated.GenusFiveCanonicalClassifierData
open AtanasovRanganathan.GenusFiveCubicAtlas

/-! ## The emitted atlas tables are the real ones

`atlasEntry idx` is generated data; these 20 lemmas are what ties it
to the actual atlas rows.  The index has to be a literal, since
`(atlas.get idx).n` does not reduce for a symbolic `idx`. -/
theorem atlasEntry_row00 : ∀ a b : Fin 8,
    atlasEntry 0 a b = GenusFiveCubicAtlas.row01.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row01 : ∀ a b : Fin 8,
    atlasEntry 1 a b = GenusFiveCubicAtlas.row02.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row02 : ∀ a b : Fin 8,
    atlasEntry 2 a b = GenusFiveCubicAtlas.row03.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row03 : ∀ a b : Fin 8,
    atlasEntry 3 a b = GenusFiveCubicAtlas.row04.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row04 : ∀ a b : Fin 8,
    atlasEntry 4 a b = GenusFiveCubicAtlas.row05.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row05 : ∀ a b : Fin 8,
    atlasEntry 5 a b = GenusFiveCubicAtlas.row06.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row06 : ∀ a b : Fin 8,
    atlasEntry 6 a b = GenusFiveCubicAtlas.row07.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row07 : ∀ a b : Fin 8,
    atlasEntry 7 a b = GenusFiveCubicAtlas.row08.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row08 : ∀ a b : Fin 8,
    atlasEntry 8 a b = GenusFiveCubicAtlas.row09.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row09 : ∀ a b : Fin 8,
    atlasEntry 9 a b = GenusFiveCubicAtlas.row10.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row10 : ∀ a b : Fin 8,
    atlasEntry 10 a b = GenusFiveCubicAtlas.row11.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row11 : ∀ a b : Fin 8,
    atlasEntry 11 a b = GenusFiveCubicAtlas.row12.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row12 : ∀ a b : Fin 8,
    atlasEntry 12 a b = GenusFiveCubicAtlas.row13.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row13 : ∀ a b : Fin 8,
    atlasEntry 13 a b = GenusFiveCubicAtlas.row14.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row14 : ∀ a b : Fin 8,
    atlasEntry 14 a b = GenusFiveCubicAtlas.row15.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row15 : ∀ a b : Fin 8,
    atlasEntry 15 a b = GenusFiveCubicAtlas.row16.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row16 : ∀ a b : Fin 8,
    atlasEntry 16 a b = GenusFiveCubicAtlas.rootDouble.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row17 : ∀ a b : Fin 8,
    atlasEntry 17 a b = GenusFiveCubicAtlas.oneChord.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row18 : ∀ a b : Fin 8,
    atlasEntry 18 a b = GenusFiveCubicAtlas.square.core.pairMultiplicity a b := by
  decide
theorem atlasEntry_row19 : ∀ a b : Fin 8,
    atlasEntry 19 a b = GenusFiveCubicAtlas.doubleMatching.core.pairMultiplicity a b := by
  decide

/-! ## The leaf decision -/

/-- The check applied to a leaf, given the result of looking its row
list up in `payloadBuckets`.  A hit must exhibit an injective vertex
map matching the table against the indexed atlas row; a miss must
certify that the table is disconnected. -/
def payloadDecide (rows : List (List ℕ)) : Option Payload → Bool
  | some (idx, p) =>
      decide (∀ i j : Fin 8, permOf p i = permOf p j → i = j) &&
        decide (∀ i j : Fin 8,
          entryOf rows (i : ℕ) (j : ℕ)
            = atlasEntry idx (permOf p i) (permOf p j))
  | none => decide (¬ MatrixConnected 8 (entryOf rows))

/-- The leaf check of the pruned traversal.  It receives no payload
argument: the payload is fetched from the generated buckets by the
leaf's own row list. -/
def leafDecide (rows : List (List ℕ)) : Bool :=
  payloadDecide rows (payloadLookup (rowKey rows))

/-! ## One step of the traversal -/

/-- The defining equation of `prunedCheck` at a branching node.  This
is the only thing the assembly below needs to know about it. -/
theorem prunedCheck_cons (accept leaf : List (List ℕ) → Bool)
    (fuel capacity : ℕ) (capacities : List ℕ) (path : List (List ℕ)) :
    prunedCheck accept leaf (fuel + 1) (capacity :: capacities) path =
      (boundedCompositions capacity capacities).all fun part =>
        !accept (path ++ [part]) ||
          prunedCheck accept leaf fuel
            (List.zipWith (· - ·) capacities part) (path ++ [part]) :=
  rfl

/-- Grow the vertices reachable from the starting vertex until no new vertex is found. -/
private def growReachable (size : ℕ) (matrix : ℕ → ℕ → ℕ) :
    ℕ → List ℕ → List ℕ
  | 0, reached => reached
  | fuel + 1, reached =>
    let added := (List.range size).filter fun j =>
      !reached.contains j && reached.any (fun i => 0 < matrix i j)
    if added.isEmpty then reached else growReachable size matrix fuel (reached ++ added)

/-- Check a proposed nonempty proper cut for the absence of outgoing edges. -/
private def checkClosedCut (size : ℕ) (matrix : ℕ → ℕ → ℕ) (reached : List ℕ) : Bool :=
  reached.all (· < size) && reached.contains 0 &&
    (List.range size).any (fun j => !reached.contains j) &&
    reached.all (fun i => (List.range size).all fun j => reached.contains j || matrix i j == 0)

private theorem checkClosedCut_sound {size : ℕ} {matrix : ℕ → ℕ → ℕ} {reached : List ℕ}
    (checked : checkClosedCut size matrix reached = true) : ¬ MatrixConnected size matrix := by
  simp only [checkClosedCut, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    List.any_eq_true, List.contains_iff_mem, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at checked
  obtain ⟨⟨⟨bounded, root⟩, other, otherBound, otherOutside⟩, closed⟩ := checked
  have outside : other ∉ reached := by
    intro member
    rw [List.contains_iff_mem.mpr member] at otherOutside
    cases otherOutside
  intro connected
  have subset : reached.toFinset ⊆ Finset.range size := fun vertex member =>
    Finset.mem_range.mpr (bounded vertex (List.mem_toFinset.mp member))
  obtain ⟨i, hi, j, hj, hjOutside, edge⟩ := connected reached.toFinset
    (Finset.mem_powerset.mpr subset)
    ⟨0, List.mem_toFinset.mpr root, other, Finset.mem_range.mpr otherBound,
      fun member => outside (List.mem_toFinset.mp member)⟩
  obtain inside | zero := closed i (List.mem_toFinset.mp hi) j (Finset.mem_range.mp hj)
  · exact hjOutside (List.mem_toFinset.mpr inside)
  · exact (Nat.ne_of_gt edge) zero

/-- Check distinct values with one membership scan per vertex. -/
private def distinctVertices : List (Fin 8) → Bool
  | [] => true
  | vertex :: rest => !rest.contains vertex && distinctVertices rest

private theorem distinctVertices_sound {vertices : List (Fin 8)}
    (checked : distinctVertices vertices = true) : vertices.Nodup := by
  induction vertices with
  | nil => exact List.nodup_nil
  | cons vertex rest ih =>
    obtain ⟨fresh, distinct⟩ := Bool.and_eq_true_iff.mp checked
    refine List.nodup_cons.mpr ⟨?_, ih distinct⟩
    intro member
    rw [List.contains_iff_mem.mpr member] at fresh
    cases fresh

/-- Reuse the generated bucket blocks, skipping complete blocks during lookup. -/
private def bucketBlocks : List (ℕ × List (List (ℕ × Payload))) :=
  [(20, payloadBucketPart0), (20, payloadBucketPart1), (20, payloadBucketPart2),
    (20, payloadBucketPart3), (20, payloadBucketPart4), (20, payloadBucketPart5),
    (20, payloadBucketPart6), (20, payloadBucketPart7), (20, payloadBucketPart8),
    (20, payloadBucketPart9), (20, payloadBucketPart10), (20, payloadBucketPart11),
    (11, payloadBucketPart12)]

private theorem bucketBlocks_sizes :
    ∀ block ∈ bucketBlocks, block.1 = block.2.length := by
  decide

private def lookupByBlock (key : ℕ) : Option Payload :=
  List.lookup key (List.lookupChunks bucketBlocks (key % bucketCount) [])

private theorem lookupByBlock_eq (key : ℕ) : lookupByBlock key = payloadLookup key := by
  unfold lookupByBlock
  rw [List.lookupChunks_eq_getD_flatMap _ bucketBlocks_sizes]
  rfl

/-- Replay the stored permutation and matrix, or check the cut reached from vertex zero. -/
private def leafCheck (rows : List (List ℕ)) : Bool :=
  match lookupByBlock (rowKey rows) with
  | some (index, permutation) =>
    distinctVertices (List.ofFn (permOf permutation)) &&
      (List.finRange 8).all (fun i => (List.finRange 8).all fun j =>
        entryOf rows i.val j.val == atlasEntry index (permOf permutation i) (permOf permutation j))
  | none =>
    let matrix := entryOf rows
    checkClosedCut 8 matrix (growReachable 8 matrix 7 [0])

private theorem leafCheck_sound {rows : List (List ℕ)} (checked : leafCheck rows = true) :
    leafDecide rows = true := by
  cases lookupEquation : payloadLookup (rowKey rows) with
  | none =>
    simp only [leafCheck, lookupByBlock_eq, lookupEquation] at checked
    simpa only [leafDecide, lookupEquation, payloadDecide, decide_eq_true_eq]
      using checkClosedCut_sound checked
  | some payload =>
    obtain ⟨index, permutation⟩ := payload
    simp only [leafCheck, lookupByBlock_eq, lookupEquation, Bool.and_eq_true] at checked
    obtain ⟨distinct, agrees⟩ := checked
    simp only [leafDecide, lookupEquation, payloadDecide, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.nodup_ofFn.mp (distinctVertices_sound distinct),
      fun i j => beq_iff_eq.mp
        (List.all_eq_true.mp (List.all_eq_true.mp agrees i (List.mem_finRange i))
          j (List.mem_finRange j))⟩

/-- The unpruned traversal checks each completion of the supplied prefix. -/
private theorem prunedCheck_of_leafCheck (fuel : ℕ) (capacities : List ℕ)
    (path : List (List ℕ))
    (checked : prunedCheck (fun _ => true) leafCheck fuel capacities path = true) :
    prunedCheck canonicalPrefix leafDecide fuel capacities path = true := by
  induction fuel generalizing capacities path with
  | zero => exact checked
  | succ fuel ih =>
    cases capacities with
    | nil => exact leafCheck_sound checked
    | cons capacity capacities =>
      rw [prunedCheck, List.all_eq_true] at checked ⊢
      intro part member
      exact Bool.or_eq_true_iff.mpr (Or.inr (ih _ _ (checked part member)))

/-! ## The chunks

Each proof checks the completions of one canonical choice of rows `0` and `1`.
The named checks use kernel reduction, and the wrappers retain the original
auxiliary declarations. -/

private theorem chunk00_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 3, 0, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 3, 0]] = true := by
  decide +kernel

/-- 10 leaves. -/
theorem chunk00 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 3, 0, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 3, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk00_checked

private theorem chunk01_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk01 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 1, 2, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk01_checked

private theorem chunk02_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 1, 1, 1, 0]] = true := by
  decide +kernel

/-- 29 leaves. -/
theorem chunk02 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 0, 0, 3], [0, 0, 1, 1, 1, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk02_checked

private theorem chunk03_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 3, 0, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 1]] = true := by
  decide +kernel

/-- 10 leaves. -/
theorem chunk03 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 3, 0, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 2, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk03_checked

private theorem chunk04_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 1, 1]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk04 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 1, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk04_checked

private theorem chunk05_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 2, 0, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 2, 0]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk05 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 2, 0, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 2, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk05_checked

private theorem chunk06_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 1, 2, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 1]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk06 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 1, 2, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 0, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk06_checked

private theorem chunk07_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 1, 1, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 1, 0]] = true := by
  decide +kernel

/-- 36 leaves. -/
theorem chunk07 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 1, 1, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 2, 1, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk07_checked

private theorem chunk08_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 0, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk08 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 0, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 3, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk08_checked

private theorem chunk09_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 1, 0, 1]] = true := by
  decide +kernel

/-- 29 leaves. -/
theorem chunk09 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 1, 0, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk09_checked

private theorem chunk10_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 2, 1, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 1, 1, 0]] = true := by
  decide +kernel

/-- 56 leaves. -/
theorem chunk10 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 2, 1, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 1, 1, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk10_checked

private theorem chunk11_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 1, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 2, 0, 0]] = true := by
  decide +kernel

/-- 56 leaves. -/
theorem chunk11 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 1, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 2, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk11_checked

private theorem chunk12_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 2, 2, 2, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 1, 1, 1, 0, 0]] = true := by
  decide +kernel

/-- 82 leaves. -/
theorem chunk12 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 2, 2, 2, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2], [0, 1, 1, 1, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk12_checked

private theorem chunk13_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 2]] = true := by
  decide +kernel

/-- 21 leaves. -/
theorem chunk13 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 2, 1, 0]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 1, 2]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk13_checked

private theorem chunk14_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 3, 1, 1, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1]] = true := by
  decide +kernel

/-- 36 leaves. -/
theorem chunk14 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 3, 1, 1, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk14_checked

private theorem chunk15_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 0, 2]] = true := by
  decide +kernel

/-- 29 leaves. -/
theorem chunk15 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 2, 2, 0]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 0, 2]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk15_checked

private theorem chunk16_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 2, 2, 1, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 1, 1]] = true := by
  decide +kernel

/-- 56 leaves. -/
theorem chunk16 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 2, 2, 1, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 1, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk16_checked

private theorem chunk17_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 1, 2, 2, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 2, 0, 0, 1]] = true := by
  decide +kernel

/-- 56 leaves. -/
theorem chunk17 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 1, 2, 2, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 2, 0, 0, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk17_checked

private theorem chunk18_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 3, 0, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 3, 0, 0, 0]] = true := by
  decide +kernel

/-- 29 leaves. -/
theorem chunk18 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 3, 0, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [0, 0, 3, 0, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk18_checked

private theorem chunk19_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 2, 2, 2, 2, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 1, 1, 0, 0, 1]] = true := by
  decide +kernel

/-- 82 leaves. -/
theorem chunk19 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 2, 2, 2, 2, 1]
      [[0, 0, 0, 0, 1, 1, 1], [0, 1, 1, 0, 0, 1]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk19_checked

private theorem chunk20_checked :
    prunedCheck (fun _ => true) leafCheck 7 [3, 2, 1, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [0, 1, 2, 0, 0, 0]] = true := by
  decide +kernel

/-- 82 leaves. -/
theorem chunk20 :
    prunedCheck canonicalPrefix leafDecide 7 [3, 2, 1, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [0, 1, 2, 0, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk20_checked

private theorem chunk21_checked :
    prunedCheck (fun _ => true) leafCheck 7 [2, 2, 2, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [1, 1, 1, 0, 0, 0]] = true := by
  decide +kernel

/-- 130 leaves. -/
theorem chunk21 :
    prunedCheck canonicalPrefix leafDecide 7 [2, 2, 2, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1], [1, 1, 1, 0, 0, 0]] = true := by
  as_aux_lemma =>
    exact prunedCheck_of_leafCheck _ _ _ chunk21_checked

/-! ## The branch lists

Unfolding `prunedCheck` once exposes every capacity-bounded
composition, most of which `canonicalPrefix` rejects.  Rather than
discharge those one at a time, each lemma here names the canonical
survivors of one branch list and is proved by one cheap `decide`. -/

theorem row0Branches : ∀ part ∈ boundedCompositions 3 [3, 3, 3, 3, 3, 3, 3],
    canonicalPrefix [part] = true →
      part = [0, 0, 0, 0, 0, 0, 3] ∨
        part = [0, 0, 0, 0, 0, 1, 2] ∨
        part = [0, 0, 0, 0, 1, 1, 1] := by
  decide

theorem row1Branches0 : ∀ part ∈ boundedCompositions 3 [3, 3, 3, 3, 3, 0],
    canonicalPrefix [[0, 0, 0, 0, 0, 0, 3], part] = true →
      part = [0, 0, 0, 0, 3, 0] ∨
        part = [0, 0, 0, 1, 2, 0] ∨
        part = [0, 0, 1, 1, 1, 0] := by
  decide

theorem row1Branches1 : ∀ part ∈ boundedCompositions 3 [3, 3, 3, 3, 2, 1],
    canonicalPrefix [[0, 0, 0, 0, 0, 1, 2], part] = true →
      part = [0, 0, 0, 0, 2, 1] ∨
        part = [0, 0, 0, 1, 1, 1] ∨
        part = [0, 0, 0, 1, 2, 0] ∨
        part = [0, 0, 0, 2, 0, 1] ∨
        part = [0, 0, 0, 2, 1, 0] ∨
        part = [0, 0, 0, 3, 0, 0] ∨
        part = [0, 0, 1, 1, 0, 1] ∨
        part = [0, 0, 1, 1, 1, 0] ∨
        part = [0, 0, 1, 2, 0, 0] ∨
        part = [0, 1, 1, 1, 0, 0] := by
  decide

theorem row1Branches2 : ∀ part ∈ boundedCompositions 3 [3, 3, 3, 2, 2, 2],
    canonicalPrefix [[0, 0, 0, 0, 1, 1, 1], part] = true →
      part = [0, 0, 0, 0, 1, 2] ∨
        part = [0, 0, 0, 1, 1, 1] ∨
        part = [0, 0, 1, 0, 0, 2] ∨
        part = [0, 0, 1, 0, 1, 1] ∨
        part = [0, 0, 2, 0, 0, 1] ∨
        part = [0, 0, 3, 0, 0, 0] ∨
        part = [0, 1, 1, 0, 0, 1] ∨
        part = [0, 1, 2, 0, 0, 0] ∨
        part = [1, 1, 1, 0, 0, 0] := by
  decide

/-! ## Assembling the chunks -/

/-- Everything below row `0` = `[0, 0, 0, 0, 0, 0, 3]`. -/
theorem level1_0 :
    prunedCheck canonicalPrefix leafDecide 8 [3, 3, 3, 3, 3, 3, 0]
      [[0, 0, 0, 0, 0, 0, 3]] = true := by
  rw [prunedCheck_cons]
  simp only [List.all_eq_true]
  intro part hPart
  rcases Bool.eq_false_or_eq_true
      (canonicalPrefix ([[0, 0, 0, 0, 0, 0, 3]] ++ [part])) with hAccept | hAccept
  · rw [hAccept]
    simp only [Bool.not_true, Bool.false_or]
    have hCanonical : canonicalPrefix [[0, 0, 0, 0, 0, 0, 3], part] = true := by
      simpa using hAccept
    rcases row1Branches0 part hPart hCanonical with rfl | rfl | rfl
    · exact chunk00
    · exact chunk01
    · exact chunk02
  · rw [hAccept]; rfl

/-- Everything below row `0` = `[0, 0, 0, 0, 0, 1, 2]`. -/
theorem level1_1 :
    prunedCheck canonicalPrefix leafDecide 8 [3, 3, 3, 3, 3, 2, 1]
      [[0, 0, 0, 0, 0, 1, 2]] = true := by
  rw [prunedCheck_cons]
  simp only [List.all_eq_true]
  intro part hPart
  rcases Bool.eq_false_or_eq_true
      (canonicalPrefix ([[0, 0, 0, 0, 0, 1, 2]] ++ [part])) with hAccept | hAccept
  · rw [hAccept]
    simp only [Bool.not_true, Bool.false_or]
    have hCanonical : canonicalPrefix [[0, 0, 0, 0, 0, 1, 2], part] = true := by
      simpa using hAccept
    rcases row1Branches1 part hPart hCanonical with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact chunk03
    · exact chunk04
    · exact chunk05
    · exact chunk06
    · exact chunk07
    · exact chunk08
    · exact chunk09
    · exact chunk10
    · exact chunk11
    · exact chunk12
  · rw [hAccept]; rfl

/-- Everything below row `0` = `[0, 0, 0, 0, 1, 1, 1]`. -/
theorem level1_2 :
    prunedCheck canonicalPrefix leafDecide 8 [3, 3, 3, 3, 2, 2, 2]
      [[0, 0, 0, 0, 1, 1, 1]] = true := by
  rw [prunedCheck_cons]
  simp only [List.all_eq_true]
  intro part hPart
  rcases Bool.eq_false_or_eq_true
      (canonicalPrefix ([[0, 0, 0, 0, 1, 1, 1]] ++ [part])) with hAccept | hAccept
  · rw [hAccept]
    simp only [Bool.not_true, Bool.false_or]
    have hCanonical : canonicalPrefix [[0, 0, 0, 0, 1, 1, 1], part] = true := by
      simpa using hAccept
    rcases row1Branches2 part hPart hCanonical with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact chunk13
    · exact chunk14
    · exact chunk15
    · exact chunk16
    · exact chunk17
    · exact chunk18
    · exact chunk19
    · exact chunk20
    · exact chunk21
  · rw [hAccept]; rfl

/-- **The pruned traversal passes.**  Pure kernel reduction: no
`native_decide`, no generated tree, and no single reduction larger
than one chunk. -/
theorem pruned_valid :
    prunedCheck canonicalPrefix leafDecide 9 (List.replicate 8 3) []
      = true := by
  have hCapacities : (List.replicate 8 3 : List ℕ) = 3 :: [3, 3, 3, 3, 3, 3, 3] := rfl
  rw [hCapacities, prunedCheck_cons]
  simp only [List.all_eq_true]
  intro part hPart
  rcases Bool.eq_false_or_eq_true
      (canonicalPrefix ([] ++ [part])) with hAccept | hAccept
  · rw [hAccept]
    simp only [Bool.not_true, Bool.false_or]
    have hCanonical : canonicalPrefix [part] = true := by
      simpa using hAccept
    rcases row0Branches part hPart hCanonical with rfl | rfl | rfl
    · exact level1_0
    · exact level1_1
    · exact level1_2
  · rw [hAccept]; rfl

/-! ## Decoding an accepted leaf -/

/-- Decoding an accepted leaf.  The lookup-miss branch is discharged
against the connectedness hypothesis, and the hit branch turns the
checked injection into the required equivalence.  The index must be
made concrete before the equivalence typechecks, since `row.n` only
reduces to `8` for a literal row. -/
theorem decode (rows : List (List ℕ)) (hLeaf : leafDecide rows = true)
    (hConnected : MatrixConnected 8 (entryOf rows)) :
    ∃ row ∈ GenusFiveCubicAtlas.atlas, ∃ vertexEquiv : Fin 8 ≃ Fin 8,
      ∀ i j : Fin 8, entryOf rows (i : ℕ) (j : ℕ)
        = row.core.pairMultiplicity (vertexEquiv i) (vertexEquiv j) := by
  rw [leafDecide] at hLeaf
  cases hLookup : payloadLookup (rowKey rows) with
  | none =>
      rw [hLookup] at hLeaf
      exfalso
      have hNot : ¬ MatrixConnected 8 (entryOf rows) := by
        simpa [payloadDecide] using hLeaf
      exact hNot hConnected
  | some pair =>
      obtain ⟨idx, p⟩ := pair
      rw [hLookup] at hLeaf
      rw [payloadDecide, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq] at hLeaf
      obtain ⟨hInjective, hMatch⟩ := hLeaf
      have hBij : Function.Bijective (permOf p) :=
        Finite.injective_iff_bijective.mp
          (fun i j hij => hInjective i j hij)
      fin_cases idx
      · refine ⟨GenusFiveCubicAtlas.row01, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row00 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row02, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row01 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row03, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row02 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row04, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row03 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row05, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row04 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row06, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row05 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row07, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row06 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row08, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row07 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row09, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row08 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row10, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row09 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row11, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row10 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row12, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row11 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row13, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row12 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row14, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row13 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row15, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row14 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.row16, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row15 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.rootDouble, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row16 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.oneChord, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row17 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.square, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row18 (permOf p i) (permOf p j)
      · refine ⟨GenusFiveCubicAtlas.doubleMatching, ?_,
          Equiv.ofBijective (permOf p) hBij, fun i j => ?_⟩
        · simp [GenusFiveCubicAtlas.atlas, GenusFiveCubicAtlas.arAtlas,
            GenusFiveCubicAtlas.bridgeAtlas]
        · rw [hMatch i j]
          exact atlasEntry_row19 (permOf p i) (permOf p j)

/-! ## The classifier -/

/-- Every connected loopless cubic core on eight vertices has the unordered
multiplicity table of one of the twenty public atlas rows. -/
theorem genusFiveCubicPairMultiplicityComplete
    (candidate : Utilities.Certificate.ExplicitPotential.Core 8 12)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 12, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ∃ row ∈ GenusFiveCubicAtlas.atlas,
      ∃ vertexEquiv : Fin 8 ≃ Fin 8,
        ∀ i j : Fin 8,
          candidate.pairMultiplicity i j =
            row.core.pairMultiplicity (vertexEquiv i) (vertexEquiv j) := by
  obtain ⟨sigma, hCanonicalConnected, hCanonicalDegree, hCanonical,
      hRelabel⟩ :=
    exists_canonical_relabel candidate hConnected hCubic
  let other := candidate.relabel sigma
  have hOtherLoopless :
      ∀ edge : Fin 12, other.tail edge ≠ other.head edge :=
    Utilities.Certificate.ExplicitPotential.Core.relabel_loopless
      candidate sigma hLoopless
  have hConditions : Conditions 8 3 (matrixOf other) :=
    conditions_matrixOf other hOtherLoopless hCanonicalDegree
  have hFollows :
      Follows (List.replicate 8 3) (rowsOf (matrixOf other) 0 8) := by
    have h :=
      follows_capsOf_rowsOf hConditions 8 0 (by omega)
    simpa [capsOf_zero] using h
  have hLeaf :=
    prunedCheck_sound canonicalPrefix leafDecide hFollows 9 [] pruned_valid
      (acceptsAlong_canonicalPrefix _ hCanonical)
  rw [List.nil_append] at hLeaf
  have hEntries : ∀ i j, i < 8 → j < 8 →
      matrixOf other i j = entryOf (rowsOf (matrixOf other) 0 8) i j :=
    fun i j hi hj => (entryOf_rowsOf hConditions i j hi hj).symm
  obtain ⟨row, hRow, vertexEquiv, hMatch⟩ :=
    decode _ hLeaf
      (matrixConnected_congr hEntries
        (matrixConnected_matrixOf other hCanonicalConnected))
  refine ⟨row, hRow, sigma.trans vertexEquiv, fun i j => ?_⟩
  rw [hRelabel i j]
  have hij := hMatch (sigma i) (sigma j)
  rw [entryOf_rowsOf hConditions (sigma i : ℕ) (sigma j : ℕ)
    (sigma i).isLt (sigma j).isLt] at hij
  simpa [other, matrixOf, (sigma i).isLt, (sigma j).isLt] using hij

/-- The multiplicity match lifts to an occurrence-sensitive public core
relabeling, which is the form consumed by closed-face transport. -/
theorem genusFiveCubicRelabelingComplete
    (candidate : Utilities.Certificate.ExplicitPotential.Core 8 12)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 12, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ∃ row ∈ GenusFiveCubicAtlas.atlas,
      Nonempty (candidate.Relabeling row.core) := by
  obtain ⟨row, hRow, vertexEquiv, hMultiplicity⟩ :=
    genusFiveCubicPairMultiplicityComplete candidate hConnected hLoopless hCubic
  exact ⟨row, hRow,
    Utilities.Certificate.ExplicitPotential.Core.nonempty_relabeling_of_pairMultiplicity_eq
      candidate row.core hLoopless vertexEquiv hMultiplicity⟩

end AtanasovRanganathan.GenusFiveCanonicalClassifier
