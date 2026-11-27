/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Hessian

/-!
# Guerra, Theorem 1.1: the quasiconvexity of `L` for Hessians

A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, preprint,
arXiv:2608.23388v1 (2026), Theorem 1.1 (labelled `thm:L` in its TeX): "For every
`A ∈ ℝ^{2×2}` and every `u ∈ C_c^∞ (ℝ²)` we have `∫_{ℝ²} [L (A + D²u) − L (A)] dx ≥ 0`."

The paper (arXiv:2609.28311, TeX line 285) attributes the Hessian case of its Theorem 1, for
periodic `u ∈ C^∞_per (Q)`, to this theorem; the two forms are equivalent
(`Agazzi.theorem1_hessian_iff`; report, E1).

## Proof

Not Guerra's, which uses Morse theory: Theorem 1 for `φ = Du` (`Agazzi.theorem1_hessian`), and the
passage from periodic to compactly supported test functions (`Agazzi.theorem1_hessian_iff`, the
second-order form of Dacorogna's Prop. 5.13 in the package `CalculusOfVariations`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace External.Guerra

open Agazzi

/-- **Guerra, Theorem 1.1** (claimed in arXiv:2608.23388): for every `A ∈ ℝ^{2×2}` and every
`u ∈ C_c^∞ (ℝ²)`, `∫_{ℝ²} [L (A + D²u) − L (A)] dx ≥ 0`.

Proof: `Agazzi.theorem1_hessian` and `Agazzi.theorem1_hessian_iff` (see the module docstring). -/
theorem theorem1_1 (A : Matrix (Fin 2) (Fin 2) ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) :
    0 ≤ ∫ x,
      (integrandL (A + jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x) - integrandL A) :=
  (theorem1_hessian_iff A).1 (fun _ hv hper => theorem1_hessian A hv hper) u hu hc

end External.Guerra
