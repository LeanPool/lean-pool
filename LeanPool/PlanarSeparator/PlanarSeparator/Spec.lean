/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Spec
public import LeanPool.PlanarSeparator.Kasteleyn.Spec
public import LeanPool.PlanarSeparator.WordRAM.Spec
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Specification: planar separators and nested dissection

This file states the eight results from planar separators, nested dissection, and the
separator program using the rotation-system and word RAM models.

## Conventions

* A plane graph is a Mathlib `SimpleGraph` `G` on a finite vertex type with a plane rotation system
  `R : Kasteleyn.RotationSystem G` (`R.IsPlane`: `G` is connected and Euler's formula
  `|V| + |F| = |E| + 2` holds for the set `F` of faces of `R`). That rotation systems are the
  combinatorial form of embeddings in oriented surfaces, and that Euler's formula singles out the
  sphere, is classical and not formalized.
* A separator tree of `G` (`NestedDissection.SepTree`) splits the vertex set recursively into a
  separator and two parts with no edge between them. Its nested dissection order
  (`SepTree.order`) lists the first part, the second part, then the separator, recursively.
* Elimination in the nested dissection order is elimination of `A.submatrix σ σ`, where
  `σ k` is the `k`-th vertex of the order. `NestedDissection.stage A n` is the matrix after the
  `n` in-place elimination steps `M i j ↦ M i j - M i k (M k k)⁻¹ M k j` for `i, j > k`, with the
  inverse of the field, which Lean totalizes by `0⁻¹ = 0`. When all the pivots `M k k` met are
  nonzero (for instance, when all leading principal minors of `A` are nonzero), this is Gaussian
  elimination without pivoting (the upper triangle and diagonal of the result are the upper
  factor and the pivots, its strict lower triangle times the pivots the lower factor). At a zero
  pivot, where elimination without pivoting is undefined, the totalized step leaves the matrix
  unchanged. The elimination statements hold for every matrix with the given pattern in this
  totalized sense.
  `NestedDissection.sparseCounted H A n` is the same elimination restricted to the positions of a
  graph `H`, in the counting monad `WordRAM.Algebraic.Counted`: one operation per ring operation
  performed through the charged primitives (an inversion counts as one multiplication), data
  movement free. The cost statements are about this explicit algorithm.
* The machine is `WordRAM`: natural and real registers and memory, unit cost per executed
  instruction and one step for the final `halt`, and a bound on every natural word along the run
  (`WordRAM.RunsWithin`).

## Contents

* `IsSeparation G U S A B`: `S` separates `U` into `A` and `B`.
* The targets: `SeparatorTheorem`, `SeparatorTheoremInduced`, `SepTreeExists`,
  `SquareSepTreeExists`, `FillBound`, `PlanarNestedDissection`, `SquareNestedDissection` and
  `SeparatorMachine` (with the input `sepInput`).
-/

@[expose] public section

namespace PlanarSeparator

open Finset

section Separation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `S` separates the vertex set `U` into the parts `A` and `B`: the three sets are disjoint with
union `U`, and no edge joins `A` to `B`. -/
structure IsSeparation (G : SimpleGraph V) (U S A B : Finset V) : Prop where
  union_eq : S ∪ A ∪ B = U
  disjoint_sep_left : Disjoint S A
  disjoint_sep_right : Disjoint S B
  disjoint : Disjoint A B
  not_adj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

end Separation

/-! ### The targets -/

open NestedDissection NestedDissection.SepTree

universe u

/-- **The planar separator theorem** (Lipton and Tarjan 1979), weighted form. Let `R` be a plane
rotation system of a graph `G` with `n` vertices, and let `w` be nonnegative weights on the
vertices with total at most `1`. Then a set `S` of at most `6 √n` vertices separates the graph
into two parts `A` and `B`, with no edge between them, each of weight at most `2/3`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∑ v, w v ≤ 1 →
    ∃ S A B, IsSeparation G univ S A B ∧ (#S : ℝ) ≤ 6 * √(Fintype.card V : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3

/-- **The planar separator theorem for induced subgraphs.** Let `R` be a plane rotation system of
a graph `G`, let `U` be a set of `k` vertices and let `w` be nonnegative weights with total weight
on `U` at most `1`. Then `U` is separated by a set `S` of at most `6 √k` of its vertices into two
parts `A` and `B`, with no edge of `G` between them, each of weight at most `2/3`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorTheoremInduced : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ (U : Finset V) (w : V → ℝ),
    (∀ v, 0 ≤ w v) → ∑ v ∈ U, w v ≤ 1 →
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ 6 * √(#U : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3

/-- **Separator trees of plane graphs with boundary bounds** (Lipton, Rose and Tarjan 1979). Every
plane graph has a separator tree on all its vertices in which every subtree with `k` vertices has
a separator (at a leaf: a leaf set) of at most `50000 √k` vertices and a boundary of at most
`50000 √k` vertices, and in which the two parts of every node have at most `2k/3` vertices.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SepTreeExists : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane →
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection G t ∧
      AllNodes (SqrtBound G 50000 50000) t ∧ AllNodes Shrinks t

/-- **Separator trees of squares of plane graphs of bounded degree.** If `G` is plane with
maximum degree at most `Δ`, its square has a separator tree as in `SepTreeExists`, with the
constant `T = 40 (1062 (Δ + 1)² + 1)` in place of `50000`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareSepTreeExists : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) →
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection (square G) t ∧
      AllNodes (SqrtBound (square G) (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1))
        (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1))) t ∧ AllNodes Shrinks t

/-- **The fill of nested dissection is `O(n log n)`** (Lipton, Rose and Tarjan 1979). Let `t` be
a separator tree of a graph `G` on `Fin n` covering all vertices, with separators of at most
`α √k` and boundaries of at most `β √k` vertices at every subtree with `k` vertices, and parts of
at most `2k/3` vertices. If the vertices are eliminated in the nested dissection order of `t`
(rank of `x` = position of `x` in `t.order`), the filled graph has at most
`α (α + β) n (1 + log_{3/2} n)` edges. -/
def FillBound : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {α β : ℝ}, 0 ≤ α → 0 ≤ β →
    ∀ t : SepTree (Fin n), IsDissection G t → t.verts = univ →
      AllNodes (SqrtBound G α β) t → AllNodes Shrinks t →
      ∀ [DecidableRel (fill G fun x => t.order.idxOf x).Adj],
        ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          α * (α + β) * (n * (1 + Real.logb (3 / 2) n))

/-- **Nested dissection of plane graphs** (George 1973; Lipton, Rose and Tarjan 1979). For every
plane graph `G` on `Fin n` there is a separator tree `t` of `G`, with nested dissection order
`σ` (`σ k` is the `k`-th vertex of `t.order`), such that
* the filled graph of the nested dissection order has at most
  `T (T + T) n (1 + log_{3/2} n)` edges, `T = 50000`;
* for every matrix `A` over a field whose off-diagonal nonzero entries are edges of `G`,
  elimination of `A.submatrix σ σ` restricted to the filled graph `H` computes exactly
  `stage (A.submatrix σ σ) n`, the matrix after all `n` in-place elimination steps (Gaussian
  elimination without pivoting when its pivots are nonzero; a step at a zero pivot, totalized by
  `0⁻¹ = 0`, leaves the matrix unchanged), with at most `12 T (T + T)² n √n` operations.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def PlanarNestedDissection : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
    R.IsPlane →
    ∃ (t : SepTree (Fin n)) (σ : Equiv.Perm (Fin n)), t.verts = univ ∧ IsDissection G t ∧
      (∀ k : Fin n, t.order[k.val]? = some (σ k)) ∧
      (∀ [DecidableRel (fill G fun x => t.order.idxOf x).Adj],
        ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          50000 * (50000 + 50000) * (n * (1 + Real.logb (3 / 2) n))) ∧
      ∀ (K : Type u) [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill (G.comap σ) Fin.val →
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) →
          (sparseCounted H (A.submatrix σ σ) n).val = stage (A.submatrix σ σ) n ∧
            ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
              12 * 50000 * (50000 + 50000) ^ 2 * (n * √n)

/-- **Nested dissection for squares of plane graphs of bounded degree.** As
`PlanarNestedDissection`, for the square of a plane graph `G` of maximum degree at most `Δ` (the
matrices whose off-diagonal nonzero entries join vertices at distance at most `2` in `G`, such
as `Kᵀ K` for a matrix `K` with pattern `G`), with `T = 40 (1062 (Δ + 1)² + 1)`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareNestedDissection : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
    R.IsPlane → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) →
    ∃ (t : SepTree (Fin n)) (σ : Equiv.Perm (Fin n)), t.verts = univ ∧
      IsDissection (square G) t ∧ (∀ k : Fin n, t.order[k.val]? = some (σ k)) ∧
      (∀ [DecidableRel (fill (square G) fun x => t.order.idxOf x).Adj],
        ((fill (square G) fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) *
            (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) *
            (n * (1 + Real.logb (3 / 2) n))) ∧
      ∀ (K : Type u) [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill ((square G).comap σ) Fin.val →
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ i j, i ≠ j → A i j ≠ 0 → (square G).Adj i j) →
          (sparseCounted H (A.submatrix σ σ) n).val = stage (A.submatrix σ σ) n ∧
            ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
              12 * (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) *
                (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) ^ 2 *
                (n * √n)

/-- The input of the separator program for a rotation system `R` of a graph on `Fin n` with
vertex weights `w` and a numbering `di` of its `m` darts: the words `n, m`, then
`ofs 0, …, ofs n` where `ofs v` is the number of darts leaving the vertices below `v`, then
`w 0, …, w (n-1)`, then for each dart number `i` the initial vertex of the dart, the number of its
reversal and the number of its successor in the rotation at its initial vertex. -/
def sepInput {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m) : WordRAM.Input :=
  ⟨[n, m] ++ (List.range (n + 1)).map (fun v => #{d : G.Dart | (d.fst : ℕ) < v}) ++
      (List.finRange n).map w ++
      (List.finRange m).flatMap (fun i =>
        [((di.symm i).fst : ℕ), (di (di.symm i).symm : ℕ), (di (R.rot (di.symm i)) : ℕ)]),
    fun _ => 0⟩

/-- **The planar separator theorem on the machine in linear time.** One fixed program for the
machine `WordRAM`, run on the input `sepInput R w di` of a plane rotation system `R` of a graph on
`Fin n` with `m` darts, vertex weights `w` and a numbering `di` of the darts in which the darts
leaving lower vertices come first, with words of at least `16 m + 12 n + 3 Σ w + 22`, halts
within `320 m + 191 n + 403` steps and prints a list of words; reading word `v` of the list for
each vertex `v` (`0` if the list is shorter), the vertices read as `0` form a set `S` of at most
`6 √n + 3` vertices separating those read as `1` from those read as `2`, and each of these two
parts weighs at most `2/3` of the total.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorMachine : Prop :=
  ∃ prog : WordRAM.Program, ∀ {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ (w : Fin n → ℕ) (di : G.Dart ≃ Fin m),
    (∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') → ∀ W : ℕ,
    16 * m + 12 * n + 3 * ∑ v, w v + 22 ≤ W →
    ∃ out : List ℕ, WordRAM.RunsWithin prog (sepInput R w di) W (320 * m + 191 * n + 403) out ∧
      IsSeparation G univ {v : Fin n | out.getD v 0 = 0} {v : Fin n | out.getD v 0 = 1}
        {v : Fin n | out.getD v 0 = 2} ∧
      (#{v : Fin n | out.getD v 0 = 0} : ℝ) ≤ 6 * √(n : ℝ) + 3 ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 1), w v ≤ 2 * ∑ v, w v ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 2), w v ≤ 2 * ∑ v, w v

end PlanarSeparator

end
