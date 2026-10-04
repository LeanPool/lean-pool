/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalRecanonTransportDev

/-! NF weak partition development: NominalDefinitionRefl. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006

/-! Proof-object reflexivity for class-valued definitional leaves. -/


/-- Proof-translation construction identified upstream as `classEqRefl`. -/
@[expose]
noncomputable def classEqRefl (A : Class) : NPrf (.classEq A A) := fun rho =>
  by
  simp only [lowerWff]
  exact Fol.prf.allI (Fol.biimpReflCertificate _ _)


end NFChoice.DirectNominalPrf.Nominal
