/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHS
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.Duality
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.ForceLocalization
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.TerminalBounds
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakFluxRHS.GlobalIteration
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakFluxRHS.WeakSolutionBridge
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise
public import LeanPool.HighContrastHomogenization.Support.PDE.EnergyIdentities
public import LeanPool.HighContrastHomogenization.Support.PDE.NeumannRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalCubeBridge

/-!
# Coarse-graining support: Support.Book.Ch03.Theorems.PublicInternalBridges.H1Casts

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport
namespace Book
namespace Ch03

/-!
# Public H1 domain casts for Chapter 3

This file contains small domain-cast helpers used to transport public open-cube
H1, H10, and mean-zero H1 data to the deterministic cube realization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

@[expose]
noncomputable def castH1Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

@[expose]
noncomputable def castH10Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

@[simp] theorem castH1Domain_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

@[simp] theorem castH1Domain_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

@[expose]
noncomputable def castH1MeanZeroDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) : H1MeanZeroFunction V :=
  hUV ▸ u

@[simp] theorem castH1MeanZeroDomain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.grad =
      u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH1MeanZeroDomain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.toFun =
      u.toH1Function.toFun := by
  subst V
  rfl


end

end Ch03
end Book
end HCPolySupport
