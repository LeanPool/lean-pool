/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.ExactRootTerminalCube
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.GaugeRepresentativeJoin

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.IdentityGaugeTerminalCube

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The terminal cube solution for the row's own family — (b1) + (b4)

`CorrectorComposition.exists_exactRootTerminalCubeSolution` produces a cube solution for any
family whose representative is a.e. the exact-root coefficient `bRef`.  The
undelayed simultaneous-slope row
`Root.exists_printOrderUndelayedExactGaugeRow` quantifies over
`u : Book.Ch03.CubeSolution (originCube d m) aIdentity` for **its own**
identity-gauge family `aIdentity`, characterised by

```
∀ Q, (aIdentity.coeffOn Q).toCoeffField =
  ⇑(geom.centeredCoeffSpace 1 hI (exactGaugeCoeffSpace a abar hS)).1
```

The bridge between the two is available: `rawIdentityCoeff_ae_global`
identifies that representative, globally and cube by cube, with the exact-root
one, and `exists_normalizedReferenceCoeffFamily` manufactures a family carrying
the exact-root identity **pointwise**.  Composing the three closes items
**(b1)** and **(b4)** together: the ball datum of the large-scale C¹ slope
approximation terminal yields a
cube solution *of the very type the row consumes*.

What is still missing for `ExactRootGaugeTerminal` after this module is
recorded in the report: the two volume-ratio comparisons **(b2)** at the
exact root (the Euclidean-ball analogues of the two rounded-ellipsoid
weighted-gradient comparisons), and the carrier
identification, which is the *same* residue
`Root.SelectedReferenceCoeffExact` that the corrector-and-flux decay clause and the Liouville
characterization clause carry.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- **The terminal cube solution at the identity-gauge family.**  From a
physical `MemH1a` weak solution on the ellipsoid, a Chapter 3 cube solution for
the canonical identity-gauge family `aIdentity` on any origin cube whose exact-root
image lies inside the ellipsoid. -/
theorem exists_identityGaugeTerminalCubeSolution (d : ℕ) [NeZero d]
    (geom : RoundedGenerationAnalyticGeometry d)
    {a : CoeffSpace d} {abar : Mat d} (hS : (symmPart abar).PosDef)
    (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI
          (exactGaugeCoeffSpace a abar hS)).1 : CoeffField d))
    {R : ℝ} (m : ℤ)
    (hm : matImage (Selection.normalizedRoot (symmPart abar))
        (openCubeSet (originCube d m)) ⊆ ellipsoid abar R)
    (u : Vec d → ℝ) (Du : Vec d → Vec d)
    (hu : MemH1a (⇑a.1 : CoeffField d) (ellipsoid abar R) u Du)
    (hweak : IsWeakSolutionOn (⇑a.1 : CoeffField d)
      (ellipsoid abar R) Du) :
    ∃ w : Book.Ch03.CubeSolution (originCube d m) aIdentity,
      w.toH1.grad =
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
          (Du (matVecMul (Selection.normalizedRoot (symmPart abar)) y)) := by
  obtain ⟨aRaw, hRaw⟩ := exists_normalizedReferenceCoeffFamily a abar hS 0
  have hRaw' : ∀ Q : TriadicCube d,
      (aRaw.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          (⇑(normalizedCenteredCoeff a abar hS).1) := by
    intro Q
    simpa using hRaw Q
  refine exists_exactRootTerminalCubeSolution a abar hS aIdentity ?_ m hm u Du
    hu hweak
  intro Q
  have hglobal := rawIdentityCoeff_ae_global geom hS aRaw hRaw' hI
    aIdentity hIdentity Q
  rw [← hRaw' Q]
  exact hglobal.symm

end

end CorrectorComposition
end HighContrast
end HCPolySupport
