/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.CommonScaleFactorBound
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RowRetainingGoodScaleInterface

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.RootInterface.GoodScaleInstantiation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The root certificate, instantiated

`GoodScale` is instantiated at the **row-retaining printed-order certificate**:
the printed-order rate-bearing certificate at the common affine scale, carrying
alongside it the physical block row that produced it.  That row is exactly what
the Dirichlet provider consumes and what no producer supplied.

With this instantiation the root's `hhomogenized` hypothesis is **proved**, not
assumed — at the enlarged scale forced by the common affine multiplier, whose
law-free amplitude and eccentricity power are the `Lcert`, `pCert` the restated
interface exports.

The certificate rate is `min (kappa / 2) ((1 + g) / 4)`: the printed conversion
halves the quenched row rate, and the frozen order window
`s₀ ∈ Ico ((1+g)/4) (1/2)` caps the Dirichlet exponent at `(1+g)/4`.  Both the
certificate and the row are downward closed in the rate, so the minimum is
available.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  witnessEccentricity_nonneg)

noncomputable section

variable {d : ℕ}

/-- **The root certificate.**  The printed-order rate-bearing certificate at the
common affine scale, with the producing physical block row retained, and with
the row's own amplitude window `delta ∈ Ioo 0 1` exposed — the Dirichlet
provider reads `√delta ≤ 1` off it, and the row-retaining structure carries only
`0 ≤ delta`. -/
@[expose]
def RootGoodScale (d : ℕ) [NeZero d] (g kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  ∃ (c : ℝ)
      (h : RowSupply.RowRetainingPrintOrderGoodScale d g c kappaRate abar a x),
    c ∈ Set.Ioo (0 : ℝ) 1 ∧ h.delta ∈ Set.Ioo (0 : ℝ) 1

/-- The certificate rate the root exports: the halved quenched row rate, capped
at the frozen order window's left endpoint. -/
@[expose]
def rootCertificateRate (g kappa : ℝ) : ℝ := min (kappa / 2) ((1 + g) / 4)

theorem rootCertificateRate_pos {g kappa : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hkappa : 0 < kappa) : 0 < rootCertificateRate g kappa :=
  lt_min (by positivity) (by linarith only [hg.1])

theorem rootCertificateRate_le {g kappa : ℝ} :
    rootCertificateRate g kappa ≤ (1 + g) / 4 := min_le_right _ _

end

end RootInterface
end HighContrast
end HCPolySupport
