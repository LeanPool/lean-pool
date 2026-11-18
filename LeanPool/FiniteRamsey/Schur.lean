/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual
import LeanPool.FiniteRamsey.MulticolorRamseyUnconditional
import LeanPool.FiniteRamsey.OrderedRamsey

/-!
# Schur's theorem

Every finite colouring of the positive naturals has a monochromatic solution to `x + y = z`.
This file derives that result as an application of the graph Ramsey framework.

The pool already subsumes this conclusion through
`DensityHalesJewett.FiniteUnions.exists_monochromaticUnions`: colour finite sets by the colour of
their cardinality and request two disjoint nonempty blocks. The block cardinalities and the
cardinality of their union give the bounded Schur triple. The application here exhibits the
framework's difference-colouring and ordered-copy APIs.

## Main declarations

* `SimpleGraph.schur`: for every colour count `r`, there is a threshold `N` such that every
  `r`-colouring of the positive naturals has `x, y, z ≤ N` all the same colour with `x + y = z`.

## Proof

A Ramsey-theoretic proof. Given a colouring `c` of the positive naturals, colour the edges of
`K_N` by `(i, j) ↦ c |i - j|`. A monochromatic triangle with vertices sorted `p < q < t` gives
`c (q - p) = c (t - q) = c (t - p)` and `(q - p) + (t - q) = t - p`, a monochromatic Schur triple.
The triangle comes from `exists_multicolorCliqueArrow`, instantiated at constant clique target
`3` for `r` colours. The ordered-copy bridge presents its vertices already sorted.

Schur's paper below is cited for the theorem. The proof implemented here uses the graph Ramsey
framework developed in this project.

## References

* I. Schur, *Über die Kongruenz x^m + y^m ≡ z^m (mod p)*, Jahresber. Deutsch. Math.-Verein. 25
  (1916), 114-116.

## Tags

ramsey theory, additive combinatorics, number theory
-/

@[expose] public section

namespace SimpleGraph

/-- Schur's theorem. For every number of colours `r`, there is a threshold `N` such that any
`r`-colouring of the positive naturals has a monochromatic solution `x + y = z` with
`x, y, z ≤ N`. -/
theorem schur (r : ℕ) : ∃ N : ℕ, ∀ c : ℕ → Fin r, ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ x ≤ N ∧ y ≤ N ∧ z ≤ N ∧ c x = c y ∧ c y = c z ∧ x + y = z := by
  obtain ⟨N, hN⟩ := exists_multicolorCliqueArrow r (fun _ : Fin r => 3)
  refine ⟨N, fun c => ?_⟩
  let C : (⊤ : SimpleGraph (Fin N)).EdgeLabeling (Fin r) :=
    EdgeLabeling.mk (fun (x y : Fin N) (_ : x ≠ y) => c (max x.val y.val - min x.val y.val))
      (fun x y _ => by simp [max_comm, min_comm])
  obtain ⟨col, hcol⟩ := hN C
  -- an order-preserving monochromatic triangle `f 0 < f 1 < f 2`
  obtain ⟨f, hf⟩ := completeGraph_isContained_iff_orderedIsContained.mp hcol
  have e (i j : Fin 3) (hij : i < j) : c ((f j).val - (f i).val) = col := by
    obtain ⟨_, h⟩ := (EdgeLabeling.labelGraph_adj _ _).mp (hf i j ((top_adj _ _).mpr hij.ne))
    have := Fin.lt_def.mp (f.strictMono hij)
    rwa [show (f j).val - (f i).val = max (f i).val (f j).val - min (f i).val (f j).val by omega]
  have h01 := Fin.lt_def.mp (f.strictMono (show (0 : Fin 3) < 1 by decide))
  have h12 := Fin.lt_def.mp (f.strictMono (show (1 : Fin 3) < 2 by decide))
  have h2 := (f 2).isLt
  exact ⟨_, _, _, by omega, by omega, by omega, by omega, by omega,
    (e 0 1 (by decide)).trans (e 1 2 (by decide)).symm,
    (e 1 2 (by decide)).trans (e 0 2 (by decide)).symm, (by omega : (f 1).val - (f 0).val +
      ((f 2).val - (f 1).val) = (f 2).val - (f 0).val)⟩

/-- Worked example: the classical Schur number `S(2) = 5`, in the form that every `2`-colouring of
`{1, ..., 5}` has a monochromatic solution to `x + y = z`. Unlike `schur`, whose threshold `N` is
produced non-effectively from Ramsey's theorem, this bound is small enough to check by direct
case analysis over all `64` colourings and `216` candidate triples. -/
theorem schur_two_colors_five_example :
    ∀ c : Fin 6 → Fin 2, ∃ x y z : Fin 6,
      0 < x.val ∧ 0 < y.val ∧ x.val + y.val = z.val ∧ c x = c y ∧ c y = c z := by decide

end SimpleGraph
