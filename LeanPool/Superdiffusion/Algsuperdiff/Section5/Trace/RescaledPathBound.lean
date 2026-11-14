/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.PathBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.CubeTrace

/-!
# RescaledPathBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The percolation path bound on the paper lattice

The paper indexes its cube events by `3^(n-1) ℤ^d`.  This file embeds that
lattice in `Vec d`, identifies its centered crossing annulus with
`Percolation.IsPathFrom (m-n)`, and restates `Percolation.path_bound` with
events evaluated at the physical lattice points.

Throughout Section 5, both path adjacency and spatial separation are measured
in the `ℓ∞` metric.  The equivalence below makes this explicit:
lattice site distance at most `L` is the same as physical sup distance at most
`L * 3^(n-1)`.
-/

open HCPolySupport MeasureTheory Set
open scoped BigOperators

namespace Algsuperdiff.Section5.Trace

noncomputable section

/-- The paper's embedding of `ℤ^d` as the lattice `3^(n-1) ℤ^d`. -/
def paperLatticePoint {d : ℕ} (n : ℤ) (z : Section5.Percolation.Site d) : Vec d :=
  rescaleSite (n - 1) z

end

end Algsuperdiff.Section5.Trace
