/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.AffineH54
public import LeanPool.SplitCliqueGap.R434.ResidualArithmetic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Edge locations and signed triangle prices on the affine core. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.H54

variable {R : Type} [Fintype R] [DecidableEq R] [CommRing R]

/-- The affine role graph with edge directions restricted to `A`. -/
abbrev coreGraph (h : R) (A : Finset R) :=
  directionCore roleGraph (roleStep h) A (roleStep_swap h)

omit [DecidableEq R] [Fintype R] in
theorem core_is_tripartite (h : R) (A : Finset R) {u v : Role × R}
    (hadj : (coreGraph h A).Adj u v) : u.1.1 ≠ v.1.1 := by
  change (orderedAdj u.1 v.1 ∨ orderedAdj v.1 u.1) ∧ _ at hadj
  exact hadj.1.elim (fun hu => ne_of_lt hu.1) (fun hv => ne_of_gt hv.1)

theorem core_edges_image (h : R) (hh : 2 * h = 1) (A : Finset R) :
    (coreGraph h A).edgeFinset = (A ×ˢ (univ ×ˢ edges)).image
      (fun t : R × R × Edge => blockEdge t.1 t.2.1 t.2.2) := by
  ext f
  constructor
  · intro hf
    induction f using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨a, ha, x, e, he, heq⟩ := blockEdge_of_adj h hh (SimpleGraph.mem_edgeFinset.mp hf)
      exact mem_image.mpr ⟨(a,x,e), by simpa using And.intro ha he, heq⟩
  · intro hf
    obtain ⟨⟨a,x,e⟩, hax, rfl⟩ := mem_image.mp hf
    simp only [mem_product, mem_univ, true_and] at hax
    exact SimpleGraph.mem_edgeFinset.mpr (blockEdge_adj h hh hax.1 hax.2)

theorem core_edge_count (h : R) (hh : 2 * h = 1) (A : Finset R) :
    (coreGraph h A).edgeFinset.card = 54 * (A.card * Fintype.card R) := by
  rw [core_edges_image h hh, card_image_of_injective _ (blockEdge_injective h hh)]
  simp only [card_product, card_univ, edge_count]
  ring

omit [DecidableEq R] [Fintype R] in
theorem triangle_directions_of_parts (h : R) (hh : 2 * h = 1) {u v w : Role × R}
    (hu : u.1.1 = 0) (hv : v.1.1 = 1) (hw : w.1.1 = 2) :
    pairDirection (roleStep h) u v + pairDirection (roleStep h) v w =
      2 * pairDirection (roleStep h) u w := by
  simp only [pairDirection, roleStep, directedStep, hu, hv, hw]
  norm_num
  rw [← mul_assoc, hh, one_mul]

omit [DecidableEq R] [Fintype R] in
theorem local_vertices_of_short_directions (h : R) {u v w : Role × R}
    (hu : u.1.1 = 0) (hv : v.1.1 = 1) (hw : w.1.1 = 2)
    (hloc : pairDirection (roleStep h) u v = pairDirection (roleStep h) v w) :
    ∃ a x : R, a = pairDirection (roleStep h) u v ∧
      affineVertex a x u.1 = u ∧ affineVertex a x v.1 = v ∧ affineVertex a x w.1 = w := by
  have hduv : pairDirection (roleStep h) u v = v.2 - u.2 := by
    simp [pairDirection, roleStep, directedStep, hu, hv]
  have hdvw : pairDirection (roleStep h) v w = w.2 - v.2 := by
    simp [pairDirection, roleStep, directedStep, hv, hw]
  rw [hduv, hdvw] at hloc
  refine ⟨v.2 - u.2, u.2, hduv.symm, Prod.ext rfl ?_, Prod.ext rfl ?_, Prod.ext rfl ?_⟩
  · simp [affineVertex, hu]
  · simp only [affineVertex, hv]
    norm_num
  · simp only [affineVertex, hw]
    norm_num
    linear_combination hloc

/-- The price for slope `a`, with the outer pair carrying the negative doubled price. -/
noncomputable def signedPrice (R₀ : ℝ) (f : R → ℝ) (a : R) (k : Fin 3) : ℝ :=
  if k = 2 then -2 * (f a - 2 * R₀ / 3) else f a - 2 * R₀ / 3

omit [CommRing R] [DecidableEq R] [Fintype R] in
theorem signedPrice_lower (R₀ : ℝ) (f : R → ℝ) {a : R} (ha₀ : 0 ≤ f a) (ha₁ : f a ≤ R₀)
    (k : Fin 3) : -(2 * R₀ / 3) ≤ signedPrice R₀ f a k := by
  unfold signedPrice
  split <;> linarith

omit [CommRing R] [DecidableEq R] [Fintype R] in
theorem signedPrice_triangle (R₀ : ℝ) (f : R → ℝ) (a b c : R) :
    signedPrice R₀ f a 0 + signedPrice R₀ f b 1 + signedPrice R₀ f c 2 =
      f a + f b - 2 * f c := by
  norm_num [signedPrice]
  ring

omit [CommRing R] [DecidableEq R] [Fintype R] in
theorem signedPrice_block (R₀ : ℝ) (f : R → ℝ) (a : R) :
    ∑ e ∈ edges, signedPrice R₀ f a e.1 = 0 := by
  have htwo := balanced_edge_counts 2
  have hcompl : (edges.filter (fun e => e.1 ≠ 2)).card = 36 := by
    decide +kernel
  simp only [signedPrice, sum_ite, sum_const, nsmul_eq_mul, htwo, hcompl]
  push_cast
  ring

end GapExtremal.R434.H54
