/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Form.BilinearForm


/-!
# Wiring the test-function Poincaré bound from the box geometry

The density Poincaré inequality `poincare_H01` and the coercivity theorems
(`EllipticCoeff.bilin_coercive`) consume the bound

  `‖(h.testGraph 0 : L2D Ω)‖² ≤ C_P · ∑ᵢ ‖h.testGraph i.succ‖²`   (`hbase`)

as a hypothesis phrased through the **graph coordinates** (abstract `L²` norms). This file
discharges it from the **domain Poincaré inequality** `poincare_domain`, which lives at the
level of box integrals `∫_Ω φ²` and `∫_Ω (∂ᵢφ)²`. Two bridges do the work:

* `norm_testGraph_zero_sq_eq` / `norm_testGraph_succ_sq_eq`: the squared `L²` norm of a graph
  coordinate **is** the box integral of the corresponding classical quantity
  (`‖tg 0‖² = ∫_Ω φ²`, `‖tg i.succ‖² = ∫_Ω (∂ᵢφ)²`), via the `L²` self-inner product.
* `poincare_testfn`: feeding the per-direction slice bounds `∫_Ω φ² ≤ C ∫_Ω (∂ᵢφ)²` (the
  geometric content of `poincare_box_dir`) into `poincare_domain`'s averaging yields `hbase`
  with `C_P = C / d`. For a box of maximal side `L` the slice bound holds with `C = L²/2`
  (the 1-D step), giving the diameter constant `C_P = L²/(2d)` of `notes/constants.md`.

The remaining input, the per-direction integral slice bound on a coordinate box, is exactly the
conclusion of `poincare_box_dir` (`Poincare/Fubini.lean`); this file is the bridge that turns
it into the abstract-norm `hbase` the Hilbert-space layer wants.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- The squared `L²` norm of the function coordinate of a test-function graph is the box
integral of `φ²`. -/
lemma norm_testGraph_zero_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 = ∫ x in Ω, (φ x) ^ 2 := by
  rw [IsTestFn.testGraph_zero]
  simp only [IsTestFn.testCls]
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq h.mem_lp h.mem_lp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (pow_two _).symm)

/-- The squared `L²` norm of the `i`-th gradient coordinate of a test-function graph is the
box integral of `(∂ᵢφ)²`. -/
lemma norm_testGraph_succ_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    ‖(h.testGraph i.succ : L2D Ω)‖ ^ 2 = ∫ x in Ω, (partialD i φ x) ^ 2 := by
  rw [IsTestFn.testGraph_succ]
  simp only [IsTestFn.partialCls]
  rw [← real_inner_self_eq_norm_sq,
    inner_toLp_eq (h.memLp_partialD i) (h.memLp_partialD i)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (pow_two _).symm)

/-- **Test-function Poincaré bound from box geometry.** If on the box `Ω` every test
function obeys the per-direction slice bound `∫_Ω φ² ≤ C ∫_Ω (∂ᵢφ)²` (the geometric content
of `poincare_box_dir`), then it obeys the graph-coordinate bound `hbase` with Poincaré
constant `C_P = C / d`. This is `poincare_domain` (averaging the `d` directions) re-expressed
through the `L²` self-inner products. -/
theorem poincare_testfn {Ω : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (C : ℝ)
    (hslice : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (_h : IsTestFn Ω φ) (i : Fin d),
      ∫ x in Ω, (φ x) ^ 2 ≤ C * ∫ x in Ω, (partialD i φ x) ^ 2)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2
      ≤ (C / d) * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2 := by
  rw [norm_testGraph_zero_sq_eq h]
  refine le_trans (poincare_domain (μ := volume) (Ω := Ω) hd (u := φ)
    (d := fun i => partialD i φ) (c := fun _ => C) (fun i => hslice h i)) ?_
  have hconv : ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2
      = ∑ i : Fin d, ∫ x in Ω, (partialD i φ x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => norm_testGraph_succ_sq_eq h i)
  rw [hconv, ← Finset.mul_sum]
  apply le_of_eq
  ring

/-- **Closing the loop:** on a box with the per-direction slice bound, the Poisson
(Dirichlet) form is coercive *unconditionally* (no abstract Poincaré hypothesis), with
constant `1 / (C/d + 1)`. The slice bound is the only geometric input, supplied by
`poincare_box_dir`. -/
theorem laplaceBilin_coercive_of_slices {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hd : 0 < d) (C : ℝ) (hC : 0 ≤ C)
    (hslice : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (_h : IsTestFn Ω φ) (i : Fin d),
      ∫ x in Ω, (φ x) ^ 2 ≤ C * ∫ x in Ω, (partialD i φ x) ^ 2) :
    IsCoercive (EllipticPdes.laplaceBilin Ω) :=
  EllipticPdes.laplaceBilin_coercive Ω (C / d)
    (div_nonneg hC (Nat.cast_nonneg d))
    (fun {_φ} h => poincare_testfn hd C (fun {_ψ} h' i => hslice h' i) h)

end EllipticPdes.Poincare
