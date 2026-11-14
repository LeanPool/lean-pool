/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Basic

/-!
# Generations of a plane tree

A minimal generation API for the proof of Lemma `lem:S_lh` (source lines 3066–3083,
inventory P23):

* `gen i T`: the fringe subtrees rooted at the vertices of generation (depth) `i`, in
  depth-first order (one entry per vertex, multiplicity preserved);
* `genCount i T = Z_i(T)`: the number of vertices at generation `i`;
* `skelSize k T = C_k(T) = Z_0(T) + ⋯ + Z_{k-1}(T)`: the number of vertices in the first `k`
  generations (the paper's skeleton size), while `L_k(T) = Z_k(T) = (gen k T).length`;
* `vertexCount_eq_skelSize_add`: `|T| = C_k(T) + ∑_{v ∈ gen k T} |T_v|`, the deterministic
  identity behind the decomposition `|𝒯| = C_k + ∑_{i ≤ L_k} |𝒯^{(i)}|`.
-/

@[expose] public section

namespace PoissonDeclumping.PlaneTree

/-- The fringe subtrees rooted at generation `i`, in depth-first order. -/
def gen : ℕ → PlaneTree → List PlaneTree
  | 0, T => [T]
  | i + 1, T => T.children.flatMap (gen i)

/-- `Z_i(T)`, the number of vertices of `T` at generation `i`. -/
def genCount (i : ℕ) (T : PlaneTree) : ℕ := (gen i T).length

/-- `C_k(T) = ∑_{i < k} Z_i(T)`, the number of vertices in generations `0, …, k - 1`. -/
def skelSize (k : ℕ) (T : PlaneTree) : ℕ := ∑ i ∈ Finset.range k, genCount i T

@[simp] theorem gen_zero (T : PlaneTree) : gen 0 T = [T] := rfl

theorem gen_succ (i : ℕ) (T : PlaneTree) : gen (i + 1) T = T.children.flatMap (gen i) := rfl

@[simp] theorem gen_succ_node (i : ℕ) (ts : List PlaneTree) :
    gen (i + 1) (node ts) = ts.flatMap (gen i) := rfl

@[simp] theorem genCount_zero (T : PlaneTree) : genCount 0 T = 1 := rfl

theorem genCount_succ (i : ℕ) (T : PlaneTree) :
    genCount (i + 1) T = (T.children.map (genCount i)).sum := by
  simp only [genCount, gen_succ, List.length_flatMap]
  rfl

theorem genCount_succ_node (i : ℕ) (ts : List PlaneTree) :
    genCount (i + 1) (node ts) = (ts.map (genCount i)).sum :=
  genCount_succ i (node ts)

@[simp] theorem skelSize_zero (T : PlaneTree) : skelSize 0 T = 0 := rfl

/-- `C_{k+1}(T) = 1 + ∑_{u ∈ Γ_∅(T)} C_k(T_u)`. -/
theorem skelSize_succ (k : ℕ) (T : PlaneTree) :
    skelSize (k + 1) T = (T.children.map (skelSize k)).sum + 1 := by
  rw [skelSize, Finset.sum_range_succ']
  simp only [genCount_succ, genCount_zero]
  congr 1
  induction T.children with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih, skelSize]

/-- `|T| = C_k(T) + ∑_{v ∈ gen k T} |T_v|` (source lines 3076–3082). -/
theorem vertexCount_eq_skelSize_add (k : ℕ) (T : PlaneTree) :
    T.vertexCount = skelSize k T + ((gen k T).map vertexCount).sum := by
  induction k generalizing T with
  | zero => simp
  | succ k ih =>
    cases T with
    | node ts =>
      rw [skelSize_succ, gen_succ_node, vertexCount_node, children_node, List.map_flatMap,
        List.flatMap_def, List.sum_flatten, List.map_map]
      have : (ts.map vertexCount).sum =
          (ts.map (skelSize k)).sum + (ts.map fun U => ((gen k U).map vertexCount).sum).sum := by
        rw [← List.sum_map_add]
        exact congrArg List.sum (List.map_congr_left fun U _ => ih U)
      simp only [Function.comp_def]
      omega

end PoissonDeclumping.PlaneTree
