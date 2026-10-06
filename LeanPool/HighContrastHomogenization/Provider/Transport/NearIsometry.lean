/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.TransportObjects
public import Mathlib.Analysis.MeanInequalitiesPow
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSpectral

/-!
# High-contrast homogenization: Provider.Transport.NearIsometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The near-isometric comparison of the transport

This is the second half of the matrix calculation the proof of
`p.two.grid.transport` isolates and uses at every target cell.
The convex combination `P̄` of the previous module lives on the old grid; the
target cell lives on the new one, and the two normalizations differ by the
bridge congruence `S`.  The display `e.two.grid.whitney.mean.bound` says
that transporting `P̄` costs a factor depending only on `d` and `Q` plus one
*additive* multiple of the bridge error — the error never multiplies the gain.

The mechanism is the splitting
`S^tP̄S - I = S^t(P̄ - I)S + (S^tS - I)`.  The first term is positive and its
trace is at most `(1 + η)tr(P̄ - I)`; the second is bounded above by `η` times
the identity.  So the whole matrix is dominated by a positive matrix of trace at
most `(1 + η)tr(P̄ - I) + 2dη`, and the trace of a spectral positive part is at
most the trace of any positive matrix above it.

The passage from the trace bound to the gain bound is scalar and uses the
convexity of the gain twice: once to absorb the factor `1 + 2dη` into a
constant, and once to see the remaining `(1 + 2dη)^Q - 1` as a multiple of `η`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

section Blocks

variable {d : ℕ}

/-- The doubled identity has trace `2d`. -/
private theorem trace_one_blockCoord :
    Matrix.trace (1 : FullBlockMat d) = 2 * (d : ℝ) := by
  rw [Matrix.trace_one]
  simp [Fintype.card_sum, two_mul]

/-- The trace gap of the transported block is the trace of the positive
part. -/
private theorem trace_gap_eq_trace_posPart {Mblk Phat : BlockMat d}
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk)) :
    blockTrace Phat - 2 * (d : ℝ) =
      Matrix.trace (cfc (fun x : ℝ => max x 0) (toFullBlockMat Mblk)) := by
  have hval : blockTrace Phat = Matrix.trace (toFullBlockMat Phat) := rfl
  rw [hval, hPhat, Matrix.trace_add, trace_one_blockCoord, blockPosPart,
    toFullBlockMat_ofFullBlockMat]
  ring

end Blocks

end

end Transport
end HighContrast
end HCPolySupport
