/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C056C001Part001`. -/


section

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
noncomputable def nb056_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb056_alpha_dummy_001 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb056_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_002 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_003 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb056_alpha_dummy_000))
          (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_004 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_005 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_006 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_007 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_000))).fv ∪
      ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_008 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_009 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_010 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_011 : Var :=
  (freshVar
    (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
      ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000))) (Class.cv (nb056_alpha_dummy_007)))
            (syn_wbr (Class.cv (nb056_alpha_dummy_007)) (Class.cv (nb056_alpha_dummy_000))
              (Class.cv (nb056_alpha_dummy_006)))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_012 (f : Var) : Var :=
  (freshVar (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪
        ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪ ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
            (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb056_alpha_dummy_010 f)))
            (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
              (Class.cv (nb056_alpha_dummy_009 f)))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_013 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_014 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_015 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_009 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_016 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_009 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_017 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_018 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_019 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_013)
          (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
              (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_013)
          (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
              (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_020 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_015 f)
          (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_015 f)
          (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_014))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_022 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_014))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_023 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_016 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_024 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_016 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_025 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_026 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_023 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_027 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_028 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_029 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_030 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_031 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_032 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_033 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_028))
          (Class.cv (nb056_alpha_dummy_029)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_034 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
          (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f)) (Class.cv (nb056_alpha_dummy_032 f)))).fv)
    0)

@[expose]
noncomputable def nb056_alpha_dummy_035 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_036 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_032 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_038 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_039 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_040 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_031 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_041 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_042 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_032 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_043 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_013)
          (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013)
          (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_044 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_015 f)
          (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f)
          (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_045 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_046 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_047 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_048 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_049 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_050 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_051 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_010 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_052 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_010 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_053 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_054 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_055 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_049)
          (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
              (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_049)
          (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
              (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_056 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_051 f)
          (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_051 f)
          (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_057 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_050))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_058 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_050))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_059 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_052 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_060 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_052 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_061 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_057))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_062 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_059 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_063 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_064 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_065 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_066 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_067 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_068 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_069 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_064))
          (Class.cv (nb056_alpha_dummy_065)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_070 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
          (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f)) (Class.cv (nb056_alpha_dummy_068 f)))).fv)
    0)

@[expose]
noncomputable def nb056_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_072 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_068 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_073 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_074 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_075 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_076 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_067 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_077 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_078 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_068 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_079 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_049)
          (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049)
          (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_080 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_051 f)
          (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f)
          (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_081 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_082 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_083 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_084 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_085 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_086 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_087 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_088 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_089 : Var :=
  (freshVar
    (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
          (Class.cv (nb056_alpha_dummy_085)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_090 (f : Var) : Var :=
  (freshVar (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪
        ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
          (Class.cv (nb056_alpha_dummy_087 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_091 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_092 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_093 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_088 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_094 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_088 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_095 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_096 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_097 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_091)
          (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
              (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_091)
          (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
              (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_098 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_093 f)
          (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_093 f)
          (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_099 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_092))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_100 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_092))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_101 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_094 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_102 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_094 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_103 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_099))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_104 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_101 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_105 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_106 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_107 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_108 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_109 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_110 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_111 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_106))
          (Class.cv (nb056_alpha_dummy_107)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_112 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
          (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f)) (Class.cv (nb056_alpha_dummy_110 f)))).fv)
    0)

@[expose]
noncomputable def nb056_alpha_dummy_113 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_114 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_110 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_115 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_116 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_117 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_118 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_109 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_119 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_120 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_110 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_121 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_091)
          (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091)
          (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_122 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_093 f)
          (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f)
          (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_123 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_124 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_125 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_126 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_127 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_128 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_129 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_087 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_130 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_087 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_131 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_132 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_133 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_127)
          (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
              (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_127)
          (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
              (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_134 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_129 f)
          (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_129 f)
          (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_135 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_128))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_136 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_128))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_137 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_130 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_138 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_130 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_139 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_135))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_140 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_137 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_141 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_142 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_143 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_144 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_145 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_146 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_147 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_142))
          (Class.cv (nb056_alpha_dummy_143)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_148 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
          (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f)) (Class.cv (nb056_alpha_dummy_146 f)))).fv)
    0)

@[expose]
noncomputable def nb056_alpha_dummy_149 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part002`. -/


section

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
noncomputable def nb056_alpha_dummy_150 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_151 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_152 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_153 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_154 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_145 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_155 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_156 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_146 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_157 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_127)
          (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127)
          (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_158 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_129 f)
          (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f)
          (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_159 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_160 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_161 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_162 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_163 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_164 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_165 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_009 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_166 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_009 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_167 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_168 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_169 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_163)
          (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
              (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_163)
          (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
              (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_170 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_165 f)
          (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪
      ((Class.cab (nb056_alpha_dummy_165 f)
          (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
              (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_171 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_164))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_172 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_164))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_173 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_166 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_174 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_166 f))).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_175 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_171))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_176 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb056_alpha_dummy_173 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_177 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_178 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_179 : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_180 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_181 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb056_alpha_dummy_182 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb056_alpha_dummy_183 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_178))
          (Class.cv (nb056_alpha_dummy_179)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_184 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
          (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪
      ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f)) (Class.cv (nb056_alpha_dummy_182 f)))).fv)
    0)

@[expose]
noncomputable def nb056_alpha_dummy_185 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_186 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_187 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_188 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_189 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_190 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_181 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_191 : Var :=
  (freshVar
    (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_192 (f : Var) : Var :=
  (freshVar (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪
      ((Class.cv (nb056_alpha_dummy_182 f))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_193 : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_163)
          (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163)
          (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_194 (f : Var) : Var :=
  (freshVar (((Class.cab (nb056_alpha_dummy_165 f)
          (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f)
          (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
            (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
              (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_195 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_196 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_197 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) 0)

@[expose]
noncomputable def nb056_alpha_dummy_198 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪
      ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) 0)

theorem nb056_fresh_000 :
    (nb056_alpha_dummy_019) ∉
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_019] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv)
      0

theorem nb056_fresh_001 :
    (nb056_alpha_dummy_043) ∉
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_002 (f : Var) :
    (nb056_alpha_dummy_020 f) ∉
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv)
      0

theorem nb056_fresh_003 (f : Var) :
    (nb056_alpha_dummy_044 f) ∉
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_004 :
    (nb056_alpha_dummy_055) ∉
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv)
      0

theorem nb056_fresh_005 :
    (nb056_alpha_dummy_079) ∉
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_006 (f : Var) :
    (nb056_alpha_dummy_056 f) ∉
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_056] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv)
      0

theorem nb056_fresh_007 (f : Var) :
    (nb056_alpha_dummy_080 f) ∉
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_008 :
    (nb056_alpha_dummy_097) ∉
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv)
      0

theorem nb056_fresh_009 :
    (nb056_alpha_dummy_121) ∉
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_010 (f : Var) :
    (nb056_alpha_dummy_098 f) ∉
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv)
      0

theorem nb056_fresh_011 (f : Var) :
    (nb056_alpha_dummy_122 f) ∉
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_012 :
    (nb056_alpha_dummy_157) ∉
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_013 :
    (nb056_alpha_dummy_133) ∉
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv)
      0

theorem nb056_fresh_014 (f : Var) :
    (nb056_alpha_dummy_158 f) ∉
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_015 (f : Var) :
    (nb056_alpha_dummy_134 f) ∉
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv)
      0

theorem nb056_fresh_016 :
    (nb056_alpha_dummy_193) ∉
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_193] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_017 :
    (nb056_alpha_dummy_169) ∉
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_163)
            (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                (syn_cphi (Class.cv (nb056_alpha_dummy_164))))))).fv)
      0

theorem nb056_fresh_018 (f : Var) :
    (nb056_alpha_dummy_194 f) ∉
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_194] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb056_fresh_019 (f : Var) :
    (nb056_alpha_dummy_170 f) ∉
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_165 f)
            (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))))).fv)
      0

theorem nb056_fresh_020 :
    (nb056_alpha_dummy_085) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv) := by
  simpa only [nb056_alpha_dummy_085] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv) 0

theorem nb056_fresh_021 :
    (nb056_alpha_dummy_086) ∉ (((Class.cv (nb056_alpha_dummy_000))).fv) := by
  simpa only [nb056_alpha_dummy_086] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_000))).fv) 1

theorem nb056_distinct_022 : (nb056_alpha_dummy_085) ≠ (nb056_alpha_dummy_086) := by
  simpa only [nb056_alpha_dummy_085, nb056_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_023 :
    (nb056_alpha_dummy_005) ∉
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv)
      0

theorem nb056_fresh_024 :
    (nb056_alpha_dummy_006) ∉
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv)
      1

theorem nb056_fresh_025 :
    (nb056_alpha_dummy_007) ∉
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv)
      2

theorem nb056_distinct_026 : (nb056_alpha_dummy_005) ≠ (nb056_alpha_dummy_006) := by
  simpa only [nb056_alpha_dummy_005, nb056_alpha_dummy_006] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_distinct_027 : (nb056_alpha_dummy_005) ≠ (nb056_alpha_dummy_007) := by
  simpa only [nb056_alpha_dummy_005, nb056_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb056_distinct_028 : (nb056_alpha_dummy_006) ≠ (nb056_alpha_dummy_007) := by
  simpa only [nb056_alpha_dummy_006, nb056_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb056_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb056_fresh_029 :
    (nb056_alpha_dummy_013) ∉
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  simpa only [nb056_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      0

theorem nb056_fresh_030 :
    (nb056_alpha_dummy_014) ∉
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  simpa only [nb056_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      1

theorem nb056_distinct_031 : (nb056_alpha_dummy_013) ≠ (nb056_alpha_dummy_014) := by
  simpa only [nb056_alpha_dummy_013, nb056_alpha_dummy_014] using
    (freshVar_injective
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_032 :
    (nb056_alpha_dummy_049) ∉
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) :=
  by
  simpa only [nb056_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv)
      0

theorem nb056_fresh_033 :
    (nb056_alpha_dummy_050) ∉
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) :=
  by
  simpa only [nb056_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv)
      1

theorem nb056_distinct_034 : (nb056_alpha_dummy_049) ≠ (nb056_alpha_dummy_050) := by
  simpa only [nb056_alpha_dummy_049, nb056_alpha_dummy_050] using
    (freshVar_injective
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_035 :
    (nb056_alpha_dummy_163) ∉
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  simpa only [nb056_alpha_dummy_163] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      0

theorem nb056_fresh_036 :
    (nb056_alpha_dummy_164) ∉
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  simpa only [nb056_alpha_dummy_164] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      1

theorem nb056_distinct_037 : (nb056_alpha_dummy_163) ≠ (nb056_alpha_dummy_164) := by
  simpa only [nb056_alpha_dummy_163, nb056_alpha_dummy_164] using
    (freshVar_injective
      (((Class.cv (nb056_alpha_dummy_007))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_038 (f : Var) :
    (nb056_alpha_dummy_015 f) ∉
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv)
      0

theorem nb056_fresh_039 (f : Var) :
    (nb056_alpha_dummy_016 f) ∉
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_016] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv)
      1

theorem nb056_distinct_040 (f : Var) :
    (nb056_alpha_dummy_015 f) ≠ (nb056_alpha_dummy_016 f) := by
  simpa only [nb056_alpha_dummy_015, nb056_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
        ((Class.cv (nb056_alpha_dummy_009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_041 (f : Var) :
    (nb056_alpha_dummy_051 f) ∉
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv)
      0

theorem nb056_fresh_042 (f : Var) :
    (nb056_alpha_dummy_052 f) ∉
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv)
      1

theorem nb056_distinct_043 (f : Var) :
    (nb056_alpha_dummy_051 f) ≠ (nb056_alpha_dummy_052 f) := by
  simpa only [nb056_alpha_dummy_051, nb056_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪
        ((Class.cv (nb056_alpha_dummy_010 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_044 (f : Var) :
    (nb056_alpha_dummy_165 f) ∉
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_165] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv)
      0

theorem nb056_fresh_045 (f : Var) :
    (nb056_alpha_dummy_166 f) ∉
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_166] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv)
      1

theorem nb056_distinct_046 (f : Var) :
    (nb056_alpha_dummy_165 f) ≠ (nb056_alpha_dummy_166 f) := by
  simpa only [nb056_alpha_dummy_165, nb056_alpha_dummy_166] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_010 f))).fv ∪
        ((Class.cv (nb056_alpha_dummy_009 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_047 :
    (nb056_alpha_dummy_021) ∉ (((Class.cv (nb056_alpha_dummy_014))).fv) := by
  simpa only [nb056_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_014))).fv) 0

theorem nb056_fresh_048 :
    (nb056_alpha_dummy_022) ∉ (((Class.cv (nb056_alpha_dummy_014))).fv) := by
  simpa only [nb056_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_014))).fv) 1

theorem nb056_distinct_049 : (nb056_alpha_dummy_021) ≠ (nb056_alpha_dummy_022) := by
  simpa only [nb056_alpha_dummy_021, nb056_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_014))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_050 (f : Var) :
    (nb056_alpha_dummy_023 f) ∉ (((Class.cv (nb056_alpha_dummy_016 f))).fv) := by
  simpa only [nb056_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_016 f))).fv) 0

theorem nb056_fresh_051 (f : Var) :
    (nb056_alpha_dummy_024 f) ∉ (((Class.cv (nb056_alpha_dummy_016 f))).fv) := by
  simpa only [nb056_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_016 f))).fv) 1

theorem nb056_distinct_052 (f : Var) :
    (nb056_alpha_dummy_023 f) ≠ (nb056_alpha_dummy_024 f) := by
  simpa only [nb056_alpha_dummy_023, nb056_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_016 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_053 :
    (nb056_alpha_dummy_027) ∉
      (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_054 :
    (nb056_alpha_dummy_028) ∉
      (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_055 :
    (nb056_alpha_dummy_029) ∉
      (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_029] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_056 : (nb056_alpha_dummy_027) ≠ (nb056_alpha_dummy_028) := by
  simpa only [nb056_alpha_dummy_027, nb056_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_057 : (nb056_alpha_dummy_027) ≠ (nb056_alpha_dummy_029) := by
  simpa only [nb056_alpha_dummy_027, nb056_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_058 : (nb056_alpha_dummy_028) ≠ (nb056_alpha_dummy_029) := by
  simpa only [nb056_alpha_dummy_028, nb056_alpha_dummy_029] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_059 (f : Var) :
    (nb056_alpha_dummy_030 f) ∉
      (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_030] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_060 (f : Var) :
    (nb056_alpha_dummy_031 f) ∉
      (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_061 (f : Var) :
    (nb056_alpha_dummy_032 f) ∉
      (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_062 (f : Var) :
    (nb056_alpha_dummy_030 f) ≠ (nb056_alpha_dummy_031 f) := by
  simpa only [nb056_alpha_dummy_030, nb056_alpha_dummy_031] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_063 (f : Var) :
    (nb056_alpha_dummy_030 f) ≠ (nb056_alpha_dummy_032 f) := by
  simpa only [nb056_alpha_dummy_030, nb056_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_064 (f : Var) :
    (nb056_alpha_dummy_031 f) ≠ (nb056_alpha_dummy_032 f) := by
  simpa only [nb056_alpha_dummy_031, nb056_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_065 :
    (nb056_alpha_dummy_039) ∉
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) :=
  by
  simpa only [nb056_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv)
      0

theorem nb056_fresh_066 :
    (nb056_alpha_dummy_035) ∉
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) :=
  by
  simpa only [nb056_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv)
      0

theorem nb056_fresh_067 :
    (nb056_alpha_dummy_041) ∉
      (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) :=
  by
  simpa only [nb056_alpha_dummy_041] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv)
      0

theorem nb056_fresh_068 (f : Var) :
    (nb056_alpha_dummy_040 f) ∉
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv)
      0

theorem nb056_fresh_069 (f : Var) :
    (nb056_alpha_dummy_036 f) ∉
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv)
      0

theorem nb056_fresh_070 (f : Var) :
    (nb056_alpha_dummy_042 f) ∉
      (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv)
      0

theorem nb056_fresh_071 :
    (nb056_alpha_dummy_057) ∉ (((Class.cv (nb056_alpha_dummy_050))).fv) := by
  simpa only [nb056_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_050))).fv) 0

theorem nb056_fresh_072 :
    (nb056_alpha_dummy_058) ∉ (((Class.cv (nb056_alpha_dummy_050))).fv) := by
  simpa only [nb056_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_050))).fv) 1

theorem nb056_distinct_073 : (nb056_alpha_dummy_057) ≠ (nb056_alpha_dummy_058) := by
  simpa only [nb056_alpha_dummy_057, nb056_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_050))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_074 (f : Var) :
    (nb056_alpha_dummy_059 f) ∉ (((Class.cv (nb056_alpha_dummy_052 f))).fv) := by
  simpa only [nb056_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_052 f))).fv) 0

theorem nb056_fresh_075 (f : Var) :
    (nb056_alpha_dummy_060 f) ∉ (((Class.cv (nb056_alpha_dummy_052 f))).fv) := by
  simpa only [nb056_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_052 f))).fv) 1

theorem nb056_distinct_076 (f : Var) :
    (nb056_alpha_dummy_059 f) ≠ (nb056_alpha_dummy_060 f) := by
  simpa only [nb056_alpha_dummy_059, nb056_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_052 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_077 :
    (nb056_alpha_dummy_063) ∉
      (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_078 :
    (nb056_alpha_dummy_064) ∉
      (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_079 :
    (nb056_alpha_dummy_065) ∉
      (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_080 : (nb056_alpha_dummy_063) ≠ (nb056_alpha_dummy_064) := by
  simpa only [nb056_alpha_dummy_063, nb056_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_081 : (nb056_alpha_dummy_063) ≠ (nb056_alpha_dummy_065) := by
  simpa only [nb056_alpha_dummy_063, nb056_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_082 : (nb056_alpha_dummy_064) ≠ (nb056_alpha_dummy_065) := by
  simpa only [nb056_alpha_dummy_064, nb056_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_083 (f : Var) :
    (nb056_alpha_dummy_066 f) ∉
      (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_084 (f : Var) :
    (nb056_alpha_dummy_067 f) ∉
      (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_067] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_085 (f : Var) :
    (nb056_alpha_dummy_068 f) ∉
      (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_068] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_086 (f : Var) :
    (nb056_alpha_dummy_066 f) ≠ (nb056_alpha_dummy_067 f) := by
  simpa only [nb056_alpha_dummy_066, nb056_alpha_dummy_067] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_087 (f : Var) :
    (nb056_alpha_dummy_066 f) ≠ (nb056_alpha_dummy_068 f) := by
  simpa only [nb056_alpha_dummy_066, nb056_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_088 (f : Var) :
    (nb056_alpha_dummy_067 f) ≠ (nb056_alpha_dummy_068 f) := by
  simpa only [nb056_alpha_dummy_067, nb056_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_089 :
    (nb056_alpha_dummy_075) ∉
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) :=
  by
  simpa only [nb056_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv)
      0

theorem nb056_fresh_090 :
    (nb056_alpha_dummy_071) ∉
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) :=
  by
  simpa only [nb056_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv)
      0

theorem nb056_fresh_091 :
    (nb056_alpha_dummy_077) ∉
      (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) :=
  by
  simpa only [nb056_alpha_dummy_077] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv)
      0

theorem nb056_fresh_092 (f : Var) :
    (nb056_alpha_dummy_076 f) ∉
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv)
      0

theorem nb056_fresh_093 (f : Var) :
    (nb056_alpha_dummy_072 f) ∉
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv)
      0

theorem nb056_fresh_094 (f : Var) :
    (nb056_alpha_dummy_078 f) ∉
      (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv)
      0

theorem nb056_fresh_095 :
    (nb056_alpha_dummy_091) ∉
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) :=
  by
  simpa only [nb056_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv)
      0

theorem nb056_fresh_096 :
    (nb056_alpha_dummy_092) ∉
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) :=
  by
  simpa only [nb056_alpha_dummy_092] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv)
      1

theorem nb056_distinct_097 : (nb056_alpha_dummy_091) ≠ (nb056_alpha_dummy_092) := by
  simpa only [nb056_alpha_dummy_091, nb056_alpha_dummy_092] using
    (freshVar_injective
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb056_fresh_098 :
    (nb056_alpha_dummy_127) ∉
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) :=
  by
  simpa only [nb056_alpha_dummy_127] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv)
      0

theorem nb056_fresh_099 :
    (nb056_alpha_dummy_128) ∉
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) :=
  by
  simpa only [nb056_alpha_dummy_128] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv)
      1

theorem nb056_distinct_100 : (nb056_alpha_dummy_127) ≠ (nb056_alpha_dummy_128) := by
  simpa only [nb056_alpha_dummy_127, nb056_alpha_dummy_128] using
    (freshVar_injective
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv)
      (i := 0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part003`. -/


section

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

theorem nb056_fresh_101 (f : Var) :
    (nb056_alpha_dummy_093 f) ∉
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv)
      0

theorem nb056_fresh_102 (f : Var) :
    (nb056_alpha_dummy_094 f) ∉
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv)
      1

theorem nb056_distinct_103 (f : Var) :
    (nb056_alpha_dummy_093 f) ≠ (nb056_alpha_dummy_094 f) := by
  simpa only [nb056_alpha_dummy_093, nb056_alpha_dummy_094] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪
        ((Class.cv (nb056_alpha_dummy_088 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_104 (f : Var) :
    (nb056_alpha_dummy_129 f) ∉
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_129] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv)
      0

theorem nb056_fresh_105 (f : Var) :
    (nb056_alpha_dummy_130 f) ∉
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv)
      1

theorem nb056_distinct_106 (f : Var) :
    (nb056_alpha_dummy_129 f) ≠ (nb056_alpha_dummy_130 f) := by
  simpa only [nb056_alpha_dummy_129, nb056_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪
        ((Class.cv (nb056_alpha_dummy_087 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_107 :
    (nb056_alpha_dummy_099) ∉ (((Class.cv (nb056_alpha_dummy_092))).fv) := by
  simpa only [nb056_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_092))).fv) 0

theorem nb056_fresh_108 :
    (nb056_alpha_dummy_100) ∉ (((Class.cv (nb056_alpha_dummy_092))).fv) := by
  simpa only [nb056_alpha_dummy_100] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_092))).fv) 1

theorem nb056_distinct_109 : (nb056_alpha_dummy_099) ≠ (nb056_alpha_dummy_100) := by
  simpa only [nb056_alpha_dummy_099, nb056_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_092))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_110 (f : Var) :
    (nb056_alpha_dummy_101 f) ∉ (((Class.cv (nb056_alpha_dummy_094 f))).fv) := by
  simpa only [nb056_alpha_dummy_101] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_094 f))).fv) 0

theorem nb056_fresh_111 (f : Var) :
    (nb056_alpha_dummy_102 f) ∉ (((Class.cv (nb056_alpha_dummy_094 f))).fv) := by
  simpa only [nb056_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_094 f))).fv) 1

theorem nb056_distinct_112 (f : Var) :
    (nb056_alpha_dummy_101 f) ≠ (nb056_alpha_dummy_102 f) := by
  simpa only [nb056_alpha_dummy_101, nb056_alpha_dummy_102] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_094 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_113 :
    (nb056_alpha_dummy_105) ∉
      (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_114 :
    (nb056_alpha_dummy_106) ∉
      (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_115 :
    (nb056_alpha_dummy_107) ∉
      (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_116 : (nb056_alpha_dummy_105) ≠ (nb056_alpha_dummy_106) := by
  simpa only [nb056_alpha_dummy_105, nb056_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_117 : (nb056_alpha_dummy_105) ≠ (nb056_alpha_dummy_107) := by
  simpa only [nb056_alpha_dummy_105, nb056_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_118 : (nb056_alpha_dummy_106) ≠ (nb056_alpha_dummy_107) := by
  simpa only [nb056_alpha_dummy_106, nb056_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_119 (f : Var) :
    (nb056_alpha_dummy_108 f) ∉
      (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_120 (f : Var) :
    (nb056_alpha_dummy_109 f) ∉
      (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_109] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_121 (f : Var) :
    (nb056_alpha_dummy_110 f) ∉
      (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_110] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_122 (f : Var) :
    (nb056_alpha_dummy_108 f) ≠ (nb056_alpha_dummy_109 f) := by
  simpa only [nb056_alpha_dummy_108, nb056_alpha_dummy_109] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_123 (f : Var) :
    (nb056_alpha_dummy_108 f) ≠ (nb056_alpha_dummy_110 f) := by
  simpa only [nb056_alpha_dummy_108, nb056_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_124 (f : Var) :
    (nb056_alpha_dummy_109 f) ≠ (nb056_alpha_dummy_110 f) := by
  simpa only [nb056_alpha_dummy_109, nb056_alpha_dummy_110] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_125 :
    (nb056_alpha_dummy_117) ∉
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) :=
  by
  simpa only [nb056_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv)
      0

theorem nb056_fresh_126 :
    (nb056_alpha_dummy_113) ∉
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) :=
  by
  simpa only [nb056_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv)
      0

theorem nb056_fresh_127 :
    (nb056_alpha_dummy_119) ∉
      (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) :=
  by
  simpa only [nb056_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv)
      0

theorem nb056_fresh_128 (f : Var) :
    (nb056_alpha_dummy_118 f) ∉
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv)
      0

theorem nb056_fresh_129 (f : Var) :
    (nb056_alpha_dummy_114 f) ∉
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv)
      0

theorem nb056_fresh_130 (f : Var) :
    (nb056_alpha_dummy_120 f) ∉
      (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv)
      0

theorem nb056_fresh_131 :
    (nb056_alpha_dummy_135) ∉ (((Class.cv (nb056_alpha_dummy_128))).fv) := by
  simpa only [nb056_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_128))).fv) 0

theorem nb056_fresh_132 :
    (nb056_alpha_dummy_136) ∉ (((Class.cv (nb056_alpha_dummy_128))).fv) := by
  simpa only [nb056_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_128))).fv) 1

theorem nb056_distinct_133 : (nb056_alpha_dummy_135) ≠ (nb056_alpha_dummy_136) := by
  simpa only [nb056_alpha_dummy_135, nb056_alpha_dummy_136] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_128))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_134 (f : Var) :
    (nb056_alpha_dummy_137 f) ∉ (((Class.cv (nb056_alpha_dummy_130 f))).fv) := by
  simpa only [nb056_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_130 f))).fv) 0

theorem nb056_fresh_135 (f : Var) :
    (nb056_alpha_dummy_138 f) ∉ (((Class.cv (nb056_alpha_dummy_130 f))).fv) := by
  simpa only [nb056_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_130 f))).fv) 1

theorem nb056_distinct_136 (f : Var) :
    (nb056_alpha_dummy_137 f) ≠ (nb056_alpha_dummy_138 f) := by
  simpa only [nb056_alpha_dummy_137, nb056_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_130 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_137 :
    (nb056_alpha_dummy_141) ∉
      (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_138 :
    (nb056_alpha_dummy_142) ∉
      (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_142] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_139 :
    (nb056_alpha_dummy_143) ∉
      (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_143] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_140 : (nb056_alpha_dummy_141) ≠ (nb056_alpha_dummy_142) := by
  simpa only [nb056_alpha_dummy_141, nb056_alpha_dummy_142] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_141 : (nb056_alpha_dummy_141) ≠ (nb056_alpha_dummy_143) := by
  simpa only [nb056_alpha_dummy_141, nb056_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_142 : (nb056_alpha_dummy_142) ≠ (nb056_alpha_dummy_143) := by
  simpa only [nb056_alpha_dummy_142, nb056_alpha_dummy_143] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_135))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_143 (f : Var) :
    (nb056_alpha_dummy_144 f) ∉
      (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_144 (f : Var) :
    (nb056_alpha_dummy_145 f) ∉
      (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_145 (f : Var) :
    (nb056_alpha_dummy_146 f) ∉
      (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_146 (f : Var) :
    (nb056_alpha_dummy_144 f) ≠ (nb056_alpha_dummy_145 f) := by
  simpa only [nb056_alpha_dummy_144, nb056_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_147 (f : Var) :
    (nb056_alpha_dummy_144 f) ≠ (nb056_alpha_dummy_146 f) := by
  simpa only [nb056_alpha_dummy_144, nb056_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_148 (f : Var) :
    (nb056_alpha_dummy_145 f) ≠ (nb056_alpha_dummy_146 f) := by
  simpa only [nb056_alpha_dummy_145, nb056_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_137 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_149 :
    (nb056_alpha_dummy_153) ∉
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv) :=
  by
  simpa only [nb056_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_142))).fv)
      0

theorem nb056_fresh_150 :
    (nb056_alpha_dummy_149) ∉
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) :=
  by
  simpa only [nb056_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_142))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv)
      0

theorem nb056_fresh_151 :
    (nb056_alpha_dummy_155) ∉
      (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv) :=
  by
  simpa only [nb056_alpha_dummy_155] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_143))).fv ∪ ((Class.cv (nb056_alpha_dummy_143))).fv)
      0

theorem nb056_fresh_152 (f : Var) :
    (nb056_alpha_dummy_154 f) ∉
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_154] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_145 f))).fv)
      0

theorem nb056_fresh_153 (f : Var) :
    (nb056_alpha_dummy_150 f) ∉
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_145 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv)
      0

theorem nb056_fresh_154 (f : Var) :
    (nb056_alpha_dummy_156 f) ∉
      (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_146 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_146 f))).fv)
      0

theorem nb056_fresh_155 :
    (nb056_alpha_dummy_171) ∉ (((Class.cv (nb056_alpha_dummy_164))).fv) := by
  simpa only [nb056_alpha_dummy_171] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_164))).fv) 0

theorem nb056_fresh_156 :
    (nb056_alpha_dummy_172) ∉ (((Class.cv (nb056_alpha_dummy_164))).fv) := by
  simpa only [nb056_alpha_dummy_172] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_164))).fv) 1

theorem nb056_distinct_157 : (nb056_alpha_dummy_171) ≠ (nb056_alpha_dummy_172) := by
  simpa only [nb056_alpha_dummy_171, nb056_alpha_dummy_172] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_164))).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_158 (f : Var) :
    (nb056_alpha_dummy_173 f) ∉ (((Class.cv (nb056_alpha_dummy_166 f))).fv) := by
  simpa only [nb056_alpha_dummy_173] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_166 f))).fv) 0

theorem nb056_fresh_159 (f : Var) :
    (nb056_alpha_dummy_174 f) ∉ (((Class.cv (nb056_alpha_dummy_166 f))).fv) := by
  simpa only [nb056_alpha_dummy_174] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_166 f))).fv) 1

theorem nb056_distinct_160 (f : Var) :
    (nb056_alpha_dummy_173 f) ≠ (nb056_alpha_dummy_174 f) := by
  simpa only [nb056_alpha_dummy_173, nb056_alpha_dummy_174] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_166 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb056_fresh_161 :
    (nb056_alpha_dummy_177) ∉
      (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_162 :
    (nb056_alpha_dummy_178) ∉
      (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_178] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_163 :
    (nb056_alpha_dummy_179) ∉
      (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_179] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_164 : (nb056_alpha_dummy_177) ≠ (nb056_alpha_dummy_178) := by
  simpa only [nb056_alpha_dummy_177, nb056_alpha_dummy_178] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_165 : (nb056_alpha_dummy_177) ≠ (nb056_alpha_dummy_179) := by
  simpa only [nb056_alpha_dummy_177, nb056_alpha_dummy_179] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_166 : (nb056_alpha_dummy_178) ≠ (nb056_alpha_dummy_179) := by
  simpa only [nb056_alpha_dummy_178, nb056_alpha_dummy_179] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_171))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_167 (f : Var) :
    (nb056_alpha_dummy_180 f) ∉
      (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_180] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb056_fresh_168 (f : Var) :
    (nb056_alpha_dummy_181 f) ∉
      (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_181] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb056_fresh_169 (f : Var) :
    (nb056_alpha_dummy_182 f) ∉
      (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb056_alpha_dummy_182] using
    freshVar_not_mem (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb056_distinct_170 (f : Var) :
    (nb056_alpha_dummy_180 f) ≠ (nb056_alpha_dummy_181 f) := by
  simpa only [nb056_alpha_dummy_180, nb056_alpha_dummy_181] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb056_distinct_171 (f : Var) :
    (nb056_alpha_dummy_180 f) ≠ (nb056_alpha_dummy_182 f) := by
  simpa only [nb056_alpha_dummy_180, nb056_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb056_distinct_172 (f : Var) :
    (nb056_alpha_dummy_181 f) ≠ (nb056_alpha_dummy_182 f) := by
  simpa only [nb056_alpha_dummy_181, nb056_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb056_alpha_dummy_173 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb056_fresh_173 :
    (nb056_alpha_dummy_189) ∉
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv) :=
  by
  simpa only [nb056_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_178))).fv)
      0

theorem nb056_fresh_174 :
    (nb056_alpha_dummy_185) ∉
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) :=
  by
  simpa only [nb056_alpha_dummy_185] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_178))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv)
      0

theorem nb056_fresh_175 :
    (nb056_alpha_dummy_191) ∉
      (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv) :=
  by
  simpa only [nb056_alpha_dummy_191] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_179))).fv ∪ ((Class.cv (nb056_alpha_dummy_179))).fv)
      0

theorem nb056_fresh_176 (f : Var) :
    (nb056_alpha_dummy_190 f) ∉
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_190] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_181 f))).fv)
      0

theorem nb056_fresh_177 (f : Var) :
    (nb056_alpha_dummy_186 f) ∉
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_186] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_181 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv)
      0

theorem nb056_fresh_178 (f : Var) :
    (nb056_alpha_dummy_192 f) ∉
      (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_192] using
    freshVar_not_mem
      (((Class.cv (nb056_alpha_dummy_182 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_182 f))).fv)
      0

theorem nb056_fresh_179 (f : Var) : (nb056_alpha_dummy_087 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056_alpha_dummy_087] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb056_fresh_180 (f : Var) : (nb056_alpha_dummy_088 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb056_alpha_dummy_088] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb056_distinct_181 (f : Var) :
    (nb056_alpha_dummy_087 f) ≠ (nb056_alpha_dummy_088 f) := by
  simpa only [nb056_alpha_dummy_087, nb056_alpha_dummy_088] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb056_fresh_182 (f : Var) :
    (nb056_alpha_dummy_008 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb056_fresh_183 (f : Var) :
    (nb056_alpha_dummy_009 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb056_fresh_184 (f : Var) :
    (nb056_alpha_dummy_010 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb056_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb056_distinct_185 (f : Var) :
    (nb056_alpha_dummy_008 f) ≠ (nb056_alpha_dummy_009 f) := by
  simpa only [nb056_alpha_dummy_008, nb056_alpha_dummy_009] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb056_distinct_186 (f : Var) :
    (nb056_alpha_dummy_008 f) ≠ (nb056_alpha_dummy_010 f) := by
  simpa only [nb056_alpha_dummy_008, nb056_alpha_dummy_010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb056_distinct_187 (f : Var) :
    (nb056_alpha_dummy_009 f) ≠ (nb056_alpha_dummy_010 f) := by
  simpa only [nb056_alpha_dummy_009, nb056_alpha_dummy_010] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb056_fresh_188 :
    (nb056_alpha_dummy_025) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_021))).fv) :=
  by
  simpa only [nb056_alpha_dummy_025] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_021))).fv)
      0

theorem nb056_fresh_189 (f : Var) :
    (nb056_alpha_dummy_026 f) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_023 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_026] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_023 f))).fv)
      0

theorem nb056_fresh_190 :
    (nb056_alpha_dummy_061) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_057))).fv) :=
  by
  simpa only [nb056_alpha_dummy_061] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_057))).fv)
      0

theorem nb056_fresh_191 (f : Var) :
    (nb056_alpha_dummy_062 f) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_059 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_062] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_059 f))).fv)
      0

theorem nb056_fresh_192 :
    (nb056_alpha_dummy_103) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_099))).fv) :=
  by
  simpa only [nb056_alpha_dummy_103] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_099))).fv)
      0

theorem nb056_fresh_193 (f : Var) :
    (nb056_alpha_dummy_104 f) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_101 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_104] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_101 f))).fv)
      0

theorem nb056_fresh_194 :
    (nb056_alpha_dummy_139) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_135))).fv) :=
  by
  simpa only [nb056_alpha_dummy_139] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_135)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_135)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_135))).fv)
      0

theorem nb056_fresh_195 (f : Var) :
    (nb056_alpha_dummy_140 f) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_137 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_140] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_137 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_137 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_137 f))).fv)
      0

theorem nb056_fresh_196 :
    (nb056_alpha_dummy_175) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_171))).fv) :=
  by
  simpa only [nb056_alpha_dummy_175] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_171)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_171)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_171))).fv)
      0

theorem nb056_fresh_197 (f : Var) :
    (nb056_alpha_dummy_176 f) ∉
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_173 f))).fv) :=
  by
  simpa only [nb056_alpha_dummy_176] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_173 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_173 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_173 f))).fv)
      0

theorem nb056_fresh_198 :
    (nb056_alpha_dummy_003) ∉
      (((syn_ccom (Class.cv (nb056_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb056_alpha_dummy_003] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb056_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb056_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb056_fresh_199 (f : Var) :
    (nb056_alpha_dummy_004 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb056_alpha_dummy_004] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb056_fresh_200 :
    (nb056_alpha_dummy_017) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_017] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_201 (f : Var) :
    (nb056_alpha_dummy_018 f) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_018] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_202 :
    (nb056_alpha_dummy_053) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_053] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_203 (f : Var) :
    (nb056_alpha_dummy_054 f) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_054] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_204 :
    (nb056_alpha_dummy_095) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_095] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_205 (f : Var) :
    (nb056_alpha_dummy_096 f) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_096] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_206 :
    (nb056_alpha_dummy_131) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_131] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_207 (f : Var) :
    (nb056_alpha_dummy_132 f) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_132] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_208 :
    (nb056_alpha_dummy_167) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_167] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_164)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_163)
              (syn_wrex (nb056_alpha_dummy_164) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_163))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_164)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_209 (f : Var) :
    (nb056_alpha_dummy_168 f) ∉
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_168] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_165 f)
              (syn_wrex (nb056_alpha_dummy_166 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_165 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb056_fresh_210 :
    (nb056_alpha_dummy_037) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv)
      0

theorem nb056_fresh_211 (f : Var) :
    (nb056_alpha_dummy_038 f) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv)
      0

theorem nb056_fresh_212 :
    (nb056_alpha_dummy_073) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_073] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv)
      0

theorem nb056_fresh_213 (f : Var) :
    (nb056_alpha_dummy_074 f) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv)
      0

theorem nb056_fresh_214 :
    (nb056_alpha_dummy_115) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_115] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv)
      0

theorem nb056_fresh_215 (f : Var) :
    (nb056_alpha_dummy_116 f) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_116] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv)
      0

theorem nb056_fresh_216 :
    (nb056_alpha_dummy_151) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_142)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_143)))).fv)
      0

theorem nb056_fresh_217 (f : Var) :
    (nb056_alpha_dummy_152 f) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_145 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_146 f)))).fv)
      0

theorem nb056_fresh_218 :
    (nb056_alpha_dummy_187) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_187] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_178)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_179)))).fv)
      0

theorem nb056_fresh_219 (f : Var) :
    (nb056_alpha_dummy_188 f) ∉
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_188] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_181 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_182 f)))).fv)
      0

theorem nb056_fresh_220 :
    (nb056_alpha_dummy_045) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_221 (f : Var) :
    (nb056_alpha_dummy_046 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_222 :
    (nb056_alpha_dummy_081) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_081] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_223 (f : Var) :
    (nb056_alpha_dummy_082 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_082] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_224 :
    (nb056_alpha_dummy_123) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_225 (f : Var) :
    (nb056_alpha_dummy_124 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_226 :
    (nb056_alpha_dummy_159) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_159] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_128))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_227 (f : Var) :
    (nb056_alpha_dummy_160 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_160] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_228 :
    (nb056_alpha_dummy_195) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_195] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_164))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_229 (f : Var) :
    (nb056_alpha_dummy_196 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_196] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_166 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb056_fresh_230 :
    (nb056_alpha_dummy_033) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_028))
            (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_033] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv)
      0

theorem nb056_fresh_231 (f : Var) :
    (nb056_alpha_dummy_034 f) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_034] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv)
      0

theorem nb056_fresh_232 :
    (nb056_alpha_dummy_069) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_064))
            (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv)
      0

theorem nb056_fresh_233 (f : Var) :
    (nb056_alpha_dummy_070 f) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv)
      0

theorem nb056_fresh_234 :
    (nb056_alpha_dummy_111) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_106))
            (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_111] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv)
      0

theorem nb056_fresh_235 (f : Var) :
    (nb056_alpha_dummy_112 f) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv)
      0

theorem nb056_fresh_236 :
    (nb056_alpha_dummy_147) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_142))
            (Class.cv (nb056_alpha_dummy_143)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_147] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_142)) (Class.cv (nb056_alpha_dummy_143)))).fv)
      0

theorem nb056_fresh_237 (f : Var) :
    (nb056_alpha_dummy_148 f) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_148] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_145 f))
            (Class.cv (nb056_alpha_dummy_146 f)))).fv)
      0

theorem nb056_fresh_238 :
    (nb056_alpha_dummy_183) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_178))
            (Class.cv (nb056_alpha_dummy_179)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_183] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_178)) (Class.cv (nb056_alpha_dummy_179)))).fv)
      0

theorem nb056_fresh_239 (f : Var) :
    (nb056_alpha_dummy_184 f) ∉
      (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_184] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_181 f))
            (Class.cv (nb056_alpha_dummy_182 f)))).fv)
      0

theorem nb056_fresh_240 :
    (nb056_alpha_dummy_001) ∉
      (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv) :=
  by
  simpa only [nb056_alpha_dummy_001] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb056_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))) (syn_cid))).fv)
      0

theorem nb056_fresh_241 (f : Var) :
    (nb056_alpha_dummy_002 f) ∉
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
  by
  simpa only [nb056_alpha_dummy_002] using
    freshVar_not_mem
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv)
      0

theorem nb056_fresh_242 :
    (nb056_alpha_dummy_047) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv)
      0

theorem nb056_fresh_243 (f : Var) :
    (nb056_alpha_dummy_048 f) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv)
      0

theorem nb056_fresh_244 :
    (nb056_alpha_dummy_083) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_083] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv)
      0

theorem nb056_fresh_245 (f : Var) :
    (nb056_alpha_dummy_084 f) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_084] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv)
      0

theorem nb056_fresh_246 :
    (nb056_alpha_dummy_125) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_125] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv)
      0

theorem nb056_fresh_247 (f : Var) :
    (nb056_alpha_dummy_126 f) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_126] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv)
      0

theorem nb056_fresh_248 :
    (nb056_alpha_dummy_161) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_161] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_128)))).fv)
      0

theorem nb056_fresh_249 (f : Var) :
    (nb056_alpha_dummy_162 f) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_162] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))).fv)
      0

theorem nb056_fresh_250 :
    (nb056_alpha_dummy_197) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_197] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_164)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C056C001Part004`. -/


section

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

theorem nb056_fresh_251 (f : Var) :
    (nb056_alpha_dummy_198 f) ∉
      (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_198] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_166 f)))).fv)
      0

theorem nb056_fresh_252 :
    (nb056_alpha_dummy_011) ∉
      (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
                (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))
                (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007))
                (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_011] using
    freshVar_not_mem
      (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
                (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))
                (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007))
                (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv)
      0

theorem nb056_fresh_253 (f : Var) :
    (nb056_alpha_dummy_012 f) ∉
      (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv) :=
  by
  simpa only [nb056_alpha_dummy_012] using
    freshVar_not_mem
      (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv)
      0

theorem nb056_fresh_254 :
    (nb056_alpha_dummy_089) ∉
      (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_089] using
    freshVar_not_mem
      (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))).fv)
      0

theorem nb056_fresh_255 (f : Var) :
    (nb056_alpha_dummy_090 f) ∉
      (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f)))).fv) :=
  by
  simpa only [nb056_alpha_dummy_090] using
    freshVar_not_mem
      (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f)))).fv)
      0

theorem nb056_fresh_256 : (nb056_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb056_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb056_support_mem_0000 :
    (nb056_alpha_dummy_005) ∈
      (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
                (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))
                (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007))
                (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0001 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb056_alpha_dummy_008 f)) (s :=
        ({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var))
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0002 :
    (nb056_alpha_dummy_006) ∈
      (({(nb056_alpha_dummy_005)} : Finset Var) ∪ ({(nb056_alpha_dummy_006)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_007) (syn_wa (syn_wbr (Class.cv (nb056_alpha_dummy_005))
                (syn_ccnv (Class.cv (nb056_alpha_dummy_000)))
                (Class.cv (nb056_alpha_dummy_007))) (syn_wbr (Class.cv (nb056_alpha_dummy_007))
                (Class.cv (nb056_alpha_dummy_000)) (Class.cv (nb056_alpha_dummy_006)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0003 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var) ∪
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb056_alpha_dummy_009 f)) (s :=
        ({(nb056_alpha_dummy_008 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_009 f)} : Finset Var))
        ((syn_wex (nb056_alpha_dummy_010 f) (syn_wa
              (syn_wbr (Class.cv (nb056_alpha_dummy_008 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb056_alpha_dummy_010 f)))
              (syn_wbr (Class.cv (nb056_alpha_dummy_010 f)) (Class.cv f)
                (Class.cv (nb056_alpha_dummy_009 f)))))).fv
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0004 :
    (nb056_alpha_dummy_005) ∈
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0005 :
    (nb056_alpha_dummy_005) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0006 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0007 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0008 :
    (nb056_alpha_dummy_005) ∈
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cphi (Class.cv (nb056_alpha_dummy_014))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0009 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0006 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0010 :
    (nb056_alpha_dummy_014) ∈ (((Class.cv (nb056_alpha_dummy_014))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0011 (f : Var) :
    (nb056_alpha_dummy_016 f) ∈ (((Class.cv (nb056_alpha_dummy_016 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0012 :
    (nb056_alpha_dummy_021) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_021)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_021)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0013 (f : Var) :
    (nb056_alpha_dummy_023 f) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_023 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_023 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_023 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0014 :
    (nb056_alpha_dummy_021) ∈
      (((Class.cv (nb056_alpha_dummy_021))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0015 (f : Var) :
    (nb056_alpha_dummy_023 f) ∈
      (((Class.cv (nb056_alpha_dummy_023 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0016 :
    (nb056_alpha_dummy_028) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_028))
            (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0017 (f : Var) :
    (nb056_alpha_dummy_031 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0018 :
    (nb056_alpha_dummy_028) ∈
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0019 (f : Var) :
    (nb056_alpha_dummy_031 f) ∈
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0020 :
    (nb056_alpha_dummy_029) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_028)) (Class.cv (nb056_alpha_dummy_029)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_028))
            (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0021 (f : Var) :
    (nb056_alpha_dummy_032 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_031 f))
            (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0022 :
    (nb056_alpha_dummy_029) ∈
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0023 (f : Var) :
    (nb056_alpha_dummy_032 f) ∈
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0024 :
    (nb056_alpha_dummy_028) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0025 (f : Var) :
    (nb056_alpha_dummy_031 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0026 :
    (nb056_alpha_dummy_028) ∈
      (((Class.cv (nb056_alpha_dummy_028))).fv ∪ ((Class.cv (nb056_alpha_dummy_028))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0027 (f : Var) :
    (nb056_alpha_dummy_031 f) ∈
      (((Class.cv (nb056_alpha_dummy_031 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_031 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0028 :
    (nb056_alpha_dummy_029) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_028)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_029)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0029 (f : Var) :
    (nb056_alpha_dummy_032 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_031 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_032 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0030 :
    (nb056_alpha_dummy_029) ∈
      (((Class.cv (nb056_alpha_dummy_029))).fv ∪ ((Class.cv (nb056_alpha_dummy_029))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0031 (f : Var) :
    (nb056_alpha_dummy_032 f) ∈
      (((Class.cv (nb056_alpha_dummy_032 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_032 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0032 :
    (nb056_alpha_dummy_006) ∈
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_006))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0033 :
    (nb056_alpha_dummy_006) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_014)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_013)
              (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0034 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_009 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0035 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_015 f)
              (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0036 :
    (nb056_alpha_dummy_006) ∈
      (((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_013)
            (syn_wrex (nb056_alpha_dummy_014) (Class.cv (nb056_alpha_dummy_006))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_013))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_014)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0037 (f : Var) :
    (nb056_alpha_dummy_009 f) ∈
      (((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_015 f)
            (syn_wrex (nb056_alpha_dummy_016 f) (Class.cv (nb056_alpha_dummy_009 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_015 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0034 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0038 :
    (nb056_alpha_dummy_014) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_014))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0039 (f : Var) :
    (nb056_alpha_dummy_016 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_016 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0040 :
    (nb056_alpha_dummy_014) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_014)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0041 (f : Var) :
    (nb056_alpha_dummy_016 f) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_016 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0042 :
    (nb056_alpha_dummy_005) ∈
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0043 :
    (nb056_alpha_dummy_005) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0044 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0045 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0046 :
    (nb056_alpha_dummy_005) ∈
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cphi (Class.cv (nb056_alpha_dummy_050))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0042) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0047 (f : Var) :
    (nb056_alpha_dummy_008 f) ∈
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0044 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0048 :
    (nb056_alpha_dummy_050) ∈ (((Class.cv (nb056_alpha_dummy_050))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0049 (f : Var) :
    (nb056_alpha_dummy_052 f) ∈ (((Class.cv (nb056_alpha_dummy_052 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0050 :
    (nb056_alpha_dummy_057) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_057)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_057)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_057))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0051 (f : Var) :
    (nb056_alpha_dummy_059 f) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_059 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_059 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_059 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0052 :
    (nb056_alpha_dummy_057) ∈
      (((Class.cv (nb056_alpha_dummy_057))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0053 (f : Var) :
    (nb056_alpha_dummy_059 f) ∈
      (((Class.cv (nb056_alpha_dummy_059 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0054 :
    (nb056_alpha_dummy_064) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_064))
            (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0055 (f : Var) :
    (nb056_alpha_dummy_067 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0056 :
    (nb056_alpha_dummy_064) ∈
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0057 (f : Var) :
    (nb056_alpha_dummy_067 f) ∈
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0058 :
    (nb056_alpha_dummy_065) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_064)) (Class.cv (nb056_alpha_dummy_065)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_064))
            (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0059 (f : Var) :
    (nb056_alpha_dummy_068 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_067 f))
            (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0060 :
    (nb056_alpha_dummy_065) ∈
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0061 (f : Var) :
    (nb056_alpha_dummy_068 f) ∈
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0062 :
    (nb056_alpha_dummy_064) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0063 (f : Var) :
    (nb056_alpha_dummy_067 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0064 :
    (nb056_alpha_dummy_064) ∈
      (((Class.cv (nb056_alpha_dummy_064))).fv ∪ ((Class.cv (nb056_alpha_dummy_064))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0065 (f : Var) :
    (nb056_alpha_dummy_067 f) ∈
      (((Class.cv (nb056_alpha_dummy_067 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_067 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0066 :
    (nb056_alpha_dummy_065) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_064)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_065)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0067 (f : Var) :
    (nb056_alpha_dummy_068 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_067 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_068 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0068 :
    (nb056_alpha_dummy_065) ∈
      (((Class.cv (nb056_alpha_dummy_065))).fv ∪ ((Class.cv (nb056_alpha_dummy_065))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0069 (f : Var) :
    (nb056_alpha_dummy_068 f) ∈
      (((Class.cv (nb056_alpha_dummy_068 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_068 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0070 :
    (nb056_alpha_dummy_007) ∈
      (((Class.cv (nb056_alpha_dummy_005))).fv ∪ ((Class.cv (nb056_alpha_dummy_007))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0071 :
    (nb056_alpha_dummy_007) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_050)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_049)
              (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0072 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((Class.cv (nb056_alpha_dummy_008 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_010 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0073 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_008 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_051 f)
              (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0074 :
    (nb056_alpha_dummy_007) ∈
      (((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_049)
            (syn_wrex (nb056_alpha_dummy_050) (Class.cv (nb056_alpha_dummy_007))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_049))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_050)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0070) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0075 (f : Var) :
    (nb056_alpha_dummy_010 f) ∈
      (((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_051 f)
            (syn_wrex (nb056_alpha_dummy_052 f) (Class.cv (nb056_alpha_dummy_010 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_051 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0072 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0076 :
    (nb056_alpha_dummy_050) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_050))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0077 (f : Var) :
    (nb056_alpha_dummy_052 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_052 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0078 :
    (nb056_alpha_dummy_050) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_050)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0079 (f : Var) :
    (nb056_alpha_dummy_052 f) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_052 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0080 :
    (nb056_alpha_dummy_085) ∈
      (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0081 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0082 :
    (nb056_alpha_dummy_086) ∈
      (({(nb056_alpha_dummy_085)} : Finset Var) ∪ ({(nb056_alpha_dummy_086)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_086)) (Class.cv (nb056_alpha_dummy_000))
            (Class.cv (nb056_alpha_dummy_085)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0083 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (({(nb056_alpha_dummy_087 f)} : Finset Var) ∪ ({(nb056_alpha_dummy_088 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb056_alpha_dummy_088 f)) (Class.cv f)
            (Class.cv (nb056_alpha_dummy_087 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0084 :
    (nb056_alpha_dummy_085) ∈
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0085 :
    (nb056_alpha_dummy_085) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0086 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0087 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0088 :
    (nb056_alpha_dummy_085) ∈
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cphi (Class.cv (nb056_alpha_dummy_092))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0089 (f : Var) :
    (nb056_alpha_dummy_087 f) ∈
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0090 :
    (nb056_alpha_dummy_092) ∈ (((Class.cv (nb056_alpha_dummy_092))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0091 (f : Var) :
    (nb056_alpha_dummy_094 f) ∈ (((Class.cv (nb056_alpha_dummy_094 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0092 :
    (nb056_alpha_dummy_099) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_099)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_099)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_099))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0093 (f : Var) :
    (nb056_alpha_dummy_101 f) ∈
      (((Wff.classMem (Class.cv (nb056_alpha_dummy_101 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb056_alpha_dummy_101 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb056_alpha_dummy_101 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0094 :
    (nb056_alpha_dummy_099) ∈
      (((Class.cv (nb056_alpha_dummy_099))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0095 (f : Var) :
    (nb056_alpha_dummy_101 f) ∈
      (((Class.cv (nb056_alpha_dummy_101 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0096 :
    (nb056_alpha_dummy_106) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_106))
            (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0097 (f : Var) :
    (nb056_alpha_dummy_109 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0098 :
    (nb056_alpha_dummy_106) ∈
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0099 (f : Var) :
    (nb056_alpha_dummy_109 f) ∈
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0100 :
    (nb056_alpha_dummy_107) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_106)) (Class.cv (nb056_alpha_dummy_107)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_106))
            (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0101 (f : Var) :
    (nb056_alpha_dummy_110 f) ∈
      (((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv ∪
        ((syn_cnin (Class.cv (nb056_alpha_dummy_109 f))
            (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0102 :
    (nb056_alpha_dummy_107) ∈
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0103 (f : Var) :
    (nb056_alpha_dummy_110 f) ∈
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0104 :
    (nb056_alpha_dummy_106) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0105 (f : Var) :
    (nb056_alpha_dummy_109 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0106 :
    (nb056_alpha_dummy_106) ∈
      (((Class.cv (nb056_alpha_dummy_106))).fv ∪ ((Class.cv (nb056_alpha_dummy_106))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0107 (f : Var) :
    (nb056_alpha_dummy_109 f) ∈
      (((Class.cv (nb056_alpha_dummy_109 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_109 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0108 :
    (nb056_alpha_dummy_107) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_106)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0109 (f : Var) :
    (nb056_alpha_dummy_110 f) ∈
      (((syn_ccompl (Class.cv (nb056_alpha_dummy_109 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb056_alpha_dummy_110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0110 :
    (nb056_alpha_dummy_107) ∈
      (((Class.cv (nb056_alpha_dummy_107))).fv ∪ ((Class.cv (nb056_alpha_dummy_107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0111 (f : Var) :
    (nb056_alpha_dummy_110 f) ∈
      (((Class.cv (nb056_alpha_dummy_110 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0112 :
    (nb056_alpha_dummy_086) ∈
      (((Class.cv (nb056_alpha_dummy_085))).fv ∪ ((Class.cv (nb056_alpha_dummy_086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0113 :
    (nb056_alpha_dummy_086) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_092)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_091)
              (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0114 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((Class.cv (nb056_alpha_dummy_087 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0115 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_093 f)
              (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0116 :
    (nb056_alpha_dummy_086) ∈
      (((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_091)
            (syn_wrex (nb056_alpha_dummy_092) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_091))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_092)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0117 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb056_alpha_dummy_093 f)
            (syn_wrex (nb056_alpha_dummy_094 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_093 f))
                (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0118 :
    (nb056_alpha_dummy_092) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_092))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0119 (f : Var) :
    (nb056_alpha_dummy_094 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb056_alpha_dummy_094 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0120 :
    (nb056_alpha_dummy_092) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_092)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0121 (f : Var) :
    (nb056_alpha_dummy_094 f) ∈
      (((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv ∪
        ((syn_cphi (Class.cv (nb056_alpha_dummy_094 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0122 :
    (nb056_alpha_dummy_086) ∈
      (((Class.cv (nb056_alpha_dummy_086))).fv ∪ ((Class.cv (nb056_alpha_dummy_085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0123 :
    (nb056_alpha_dummy_086) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_128)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_127)
              (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_085))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_128)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0124 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((Class.cv (nb056_alpha_dummy_088 f))).fv ∪ ((Class.cv (nb056_alpha_dummy_087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb056_support_mem_0125 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((syn_ccompl (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb056_alpha_dummy_129 f)
              (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_087 f))
                (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                  (syn_cun (syn_cphi (Class.cv (nb056_alpha_dummy_130 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0126 :
    (nb056_alpha_dummy_086) ∈
      (((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_127)
            (syn_wrex (nb056_alpha_dummy_128) (Class.cv (nb056_alpha_dummy_086))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_127))
                (syn_cphi (Class.cv (nb056_alpha_dummy_128))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0122) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb056_support_mem_0127 (f : Var) :
    (nb056_alpha_dummy_088 f) ∈
      (((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv ∪
        ((Class.cab (nb056_alpha_dummy_129 f)
            (syn_wrex (nb056_alpha_dummy_130 f) (Class.cv (nb056_alpha_dummy_088 f))
              (Wff.classEq (Class.cv (nb056_alpha_dummy_129 f))
                (syn_cphi (Class.cv (nb056_alpha_dummy_130 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb056_support_mem_0124 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
