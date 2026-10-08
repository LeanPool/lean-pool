/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Definitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.CutoffProduct
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SubadditivityScaling
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.CoeffFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.CanonicalSolutions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoliCutoffProduct
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls
public import LeanPool.HighContrastHomogenization.Support.PDE.EnergyIdentities
public import LeanPool.HighContrastHomogenization.Support.Probability.LocalEllipticitySlices.SymmetricL2
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# Coarse-graining support: Support.Book.Ch05.Theorems.Section53.Common

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch05
namespace Section53

/-!
# Section 5.3 common imports

Shared base context for the split Section 5.3 files.  The mathematical content
lives in the three manuscript-lemma modules and their proof subdirectories.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

end Section53
end Ch05
end Book
end HCPolySupport
