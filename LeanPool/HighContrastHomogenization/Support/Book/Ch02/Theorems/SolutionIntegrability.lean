/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives

/-!
# Coarse-graining support: Support.Book.Ch02.Theorems.SolutionIntegrability

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch02

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Solution

/-- Public solutions have `L²` flux on their Chapter 2 domain.

The public coefficient object is only a.e.-elliptic.  The proof changes to the
internal pointwise-good representative, applies the deterministic flux `L²`
bound there, and transports the result back across the a.e. equality of
coefficient representatives. -/
theorem flux_memVectorL2 {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (u : Solution U a) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) := by
  let b : CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hb : CoeffOn.AEEq b a := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hbase :
      MemVectorL2 (U : Set (Vec d))
        (fun x => matVecMul (b.toCoeffField x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  refine MeasureTheory.MemLp.ae_eq ?_ hbase
  exact hb.mono fun x hx => by
    simp [hx]

end Solution

end

end Ch02
end Book
end HCPolySupport
