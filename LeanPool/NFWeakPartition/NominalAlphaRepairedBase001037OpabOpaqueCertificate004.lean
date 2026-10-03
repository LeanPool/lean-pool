/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001037OpabFVReflOnHelpers004

/-! NF weak partition development: NominalAlphaRepairedBase001037OpabOpaqueCertificate004. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nb037_opab_alpha_certificate_opaque004 (ph : Wff) (x : Var) (y : Var)
    (z : Var) (dv_ph_z : z ∉ ph.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaClass [] (syn_copab x y ph)
      (.cab z (syn_wex x
          (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))) :=
  by
  let alpha_dummy_000 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ (ph).fv) 0)
  have alpha_dummy_ne_x : alpha_dummy_000 ≠ x := by
    simpa only [alpha_dummy_000] using nb037_opab_fresh_ne_x ph x y
  have alpha_dummy_ne_y : alpha_dummy_000 ≠ y := by
    simpa only [alpha_dummy_000] using nb037_opab_fresh_ne_y ph x y
  have wpp_notmem_0004 : alpha_dummy_000 ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
    simpa only [alpha_dummy_000] using nb037_opab_fresh_notmem_syn_cop_cv_cv ph x y
  have wpp_notmem_0005 : z ∉ ((syn_cop (Class.cv x) (Class.cv y))).fv := by
    exact nb037_opab_z_notmem_syn_cop_cv_cv x y z dv_x_z dv_y_z
  have wpp_refl_0002 :
    TReflOn [(y, y), (x, x), (alpha_dummy_000, z)]
      ((syn_cop (Class.cv x) (Class.cv y))).fv :=
    nb037_opab_reflOn_three_pair ((syn_cop (Class.cv x) (Class.cv y)).fv) x y
      alpha_dummy_000 z wpp_notmem_0004 wpp_notmem_0005
  have wpp_notmem_0002 : alpha_dummy_000 ∉ ((Wff.neg ph)).fv := by
    simpa only [alpha_dummy_000] using nb037_opab_fresh_notmem_neg ph x y
  have wpp_notmem_0003 : z ∉ ((Wff.neg ph)).fv := by
    exact nb037_opab_z_notmem_neg ph z dv_ph_z
  have wpp_refl_0003 : TReflOn [(y, y), (x, x), (alpha_dummy_000, z)] ((Wff.neg ph)).fv :=
    nb037_opab_reflOn_three_pair ((Wff.neg ph).fv) x y alpha_dummy_000 z wpp_notmem_0002
      wpp_notmem_0003
  exact
    TAlphaClass.cab
      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there alpha_dummy_ne_y (Ne.symm dv_y_z)
                    (TAlphaVar.there alpha_dummy_ne_x (Ne.symm dv_x_z) (TAlphaVar.here _ _ _))))
                (TAlphaClass.refl_of_reflOn [(y, y), (x, x), (alpha_dummy_000, z)]
                  (syn_cop (Class.cv x) (Class.cv y)) wpp_refl_0002))
              (TAlphaWff.refl_of_reflOn [(y, y), (x, x), (alpha_dummy_000, z)]
                (Wff.neg ph) wpp_refl_0003)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
