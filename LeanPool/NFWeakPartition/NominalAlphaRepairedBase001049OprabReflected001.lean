/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaOprabCompactCertificate001

/-! NF weak partition development: NominalAlphaRepairedBase001049OprabReflected001. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

/-- Checked nominal proof certificate identified upstream as `nominal_df_oprab`. -/
@[expose]
noncomputable def nominalDfOprab (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) :
    Nominal.NPrf
      (.classEq (synCoprab x y z ph) (.cab w (synWex x (synWex y (synWex z
                (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z)))
                  ph)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (nb049OprabAlphaCertificate ph x y z w dv_ph_w dv_w_x dv_w_y dv_w_z)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
