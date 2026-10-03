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

/-! Certificates from `NAR4C090C001Part001`. -/


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
noncomputable def nb090_alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_002 (A : Class) : Var :=
  (freshVar ((A).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_003 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_001 A)} : Finset Var) ∪
        ({(nb090_alpha_dummy_002 A)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb090_alpha_dummy_001 A)) (syn_chwcodes A))
            (Wff.classMem (Class.cv (nb090_alpha_dummy_002 A)) (syn_chwcodes A)))
          (syn_wex (nb090_alpha_dummy_000 A) (syn_wiso (Class.cv (nb090_alpha_dummy_000 A))
              (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))
              (syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))
              (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))
              (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_004 (v : Var) (u : Var) (A : Class) (h : Var) : Var :=
  (freshVar (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv u) (syn_chwcodes A))
            (Wff.classMem (Class.cv v) (syn_chwcodes A))) (syn_wex h
            (syn_wiso (Class.cv h) (syn_cfv (syn_c1st) (Class.cv u))
              (syn_cfv (syn_c1st) (Class.cv v)) (syn_cfv (syn_c2nd) (Class.cv u))
              (syn_cfv (syn_c2nd) (Class.cv v)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_005 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_006 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_002 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_007 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_008 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv v)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_009 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_005 A)
            (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_010 (v : Var) (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_007 v u)
            (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_011 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_005 A)
          (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_005 A)
          (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_012 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_007 v u)
          (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_007 v u) (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_013 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_006 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_014 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_006 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_015 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_016 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_008 v u))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_017 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_013 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_013 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_013 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_018 (v : Var) (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_015 v u)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_015 v u)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_015 v u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_019 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_020 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_021 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_013 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_022 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_023 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_024 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_015 v u))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_025 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_020 A))
          (Class.cv (nb090_alpha_dummy_021 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_020 A)) (Class.cv (nb090_alpha_dummy_021 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_026 (v : Var) (u : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
          (Class.cv (nb090_alpha_dummy_024 v u)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_023 v u))
          (Class.cv (nb090_alpha_dummy_024 v u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_027 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_028 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_029 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_020 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_021 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_030 (v : Var) (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_023 v u)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_024 v u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_031 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_020 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_020 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_032 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_023 v u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_023 v u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_033 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_021 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_021 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_034 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_024 v u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_024 v u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_035 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_005 A)
          (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_005 A)
          (syn_wrex (nb090_alpha_dummy_006 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_005 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_036 (v : Var) (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_007 v u)
          (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_007 v u)
          (syn_wrex (nb090_alpha_dummy_008 v u) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_007 v u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_037 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_006 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_038 (v : Var) (u : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_008 v u))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_039 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_006 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_040 (v : Var) (u : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_008 v u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_041 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
          ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
      ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_042 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
          ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
      ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_043 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
          ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
      ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_044 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
          ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
      ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_045 (A : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
            (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_046 (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_047 (A : Class) : Var :=
  (freshVar (((syn_ccom (Class.cv (nb090_alpha_dummy_000 A))
          (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_048 (h : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_049 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
      ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_050 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
      ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_051 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
      ((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_052 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_053 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_054 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_055 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_049 A)} : Finset Var) ∪
        ({(nb090_alpha_dummy_050 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_051 A) (syn_wa
            (syn_wbr (Class.cv (nb090_alpha_dummy_049 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (Class.cv (nb090_alpha_dummy_051 A)))
            (syn_wbr (Class.cv (nb090_alpha_dummy_051 A)) (Class.cv (nb090_alpha_dummy_000 A))
              (Class.cv (nb090_alpha_dummy_050 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_056 (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_052 h)} : Finset Var) ∪
        ({(nb090_alpha_dummy_053 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_054 h) (syn_wa
            (syn_wbr (Class.cv (nb090_alpha_dummy_052 h)) (syn_ccnv (Class.cv h))
              (Class.cv (nb090_alpha_dummy_054 h)))
            (syn_wbr (Class.cv (nb090_alpha_dummy_054 h)) (Class.cv h)
              (Class.cv (nb090_alpha_dummy_053 h)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_057 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_058 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_059 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_060 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_061 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_057 A)
            (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_062 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_059 h)
            (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_063 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_057 A)
          (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_057 A)
          (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_049 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_064 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_059 h)
          (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_059 h)
          (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_052 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_065 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_058 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_066 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_058 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_067 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_060 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_068 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_060 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_069 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_065 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_065 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_065 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_070 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_067 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_067 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_067 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_071 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_072 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_073 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_065 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_074 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_075 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_076 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_067 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_077 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_072 A))
          (Class.cv (nb090_alpha_dummy_073 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_072 A)) (Class.cv (nb090_alpha_dummy_073 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_078 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_075 h))
          (Class.cv (nb090_alpha_dummy_076 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_075 h)) (Class.cv (nb090_alpha_dummy_076 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_079 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_080 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_081 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_072 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_073 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_082 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_075 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_076 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_083 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_072 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_072 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_084 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_075 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_075 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_085 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_073 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_073 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_086 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_076 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_076 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_087 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_057 A)
          (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_057 A)
          (syn_wrex (nb090_alpha_dummy_058 A) (Class.cv (nb090_alpha_dummy_050 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_057 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_088 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_059 h)
          (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_059 h)
          (syn_wrex (nb090_alpha_dummy_060 h) (Class.cv (nb090_alpha_dummy_053 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_059 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_089 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_058 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_090 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_060 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_091 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_058 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_092 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_060 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_093 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_051 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_094 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_049 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_051 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_095 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_054 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_096 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_052 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_054 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_097 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_093 A)
            (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_098 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_095 h)
            (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_099 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_093 A)
          (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_093 A)
          (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_049 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_100 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_095 h)
          (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_095 h)
          (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_052 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_101 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_094 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_102 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_094 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_103 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_096 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_104 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_096 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_105 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_101 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_101 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_101 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_106 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_103 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_103 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_103 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_107 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_108 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_109 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_110 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_111 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_112 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_113 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_108 A))
          (Class.cv (nb090_alpha_dummy_109 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_108 A)) (Class.cv (nb090_alpha_dummy_109 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_114 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_111 h))
          (Class.cv (nb090_alpha_dummy_112 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_111 h)) (Class.cv (nb090_alpha_dummy_112 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_115 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_116 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_117 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_108 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_109 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_118 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_111 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_112 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_119 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_108 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_108 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_120 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_111 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_111 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_121 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_109 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_109 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_122 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_112 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_112 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_123 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_093 A)
          (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_093 A)
          (syn_wrex (nb090_alpha_dummy_094 A) (Class.cv (nb090_alpha_dummy_051 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_093 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_124 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_095 h)
          (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_095 h)
          (syn_wrex (nb090_alpha_dummy_096 h) (Class.cv (nb090_alpha_dummy_054 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_095 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_125 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_126 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_096 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_127 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_128 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_129 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_130 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_131 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_132 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_133 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_129 A)} : Finset Var) ∪
        ({(nb090_alpha_dummy_130 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_130 A)) (Class.cv (nb090_alpha_dummy_000 A))
          (Class.cv (nb090_alpha_dummy_129 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_134 (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_131 h)} : Finset Var) ∪
        ({(nb090_alpha_dummy_132 h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_132 h)) (Class.cv h)
          (Class.cv (nb090_alpha_dummy_131 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_135 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_130 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_136 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_130 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_137 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_132 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_138 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_132 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_139 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_140 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_141 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_135 A)
          (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_135 A)
          (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_142 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_137 h)
          (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_137 h)
          (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_143 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_136 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_144 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_136 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_145 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_138 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_146 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_138 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_147 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_143 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_143 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_143 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_148 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_145 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_145 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_145 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_149 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part002`. -/


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
noncomputable def nb090_alpha_dummy_150 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_151 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_152 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_153 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_154 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_155 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_150 A))
          (Class.cv (nb090_alpha_dummy_151 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_150 A)) (Class.cv (nb090_alpha_dummy_151 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_156 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_153 h))
          (Class.cv (nb090_alpha_dummy_154 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_153 h)) (Class.cv (nb090_alpha_dummy_154 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_157 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_158 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_159 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_150 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_151 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_160 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_153 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_154 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_161 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_150 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_150 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_162 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_153 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_153 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_163 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_151 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_151 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_164 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_154 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_154 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_165 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_135 A)
          (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_135 A)
          (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_130 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_166 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_137 h)
          (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_137 h)
          (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_132 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_167 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_168 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_169 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_170 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_171 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_129 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_172 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_130 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_129 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_173 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_131 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_174 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_132 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_131 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_175 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_171 A)
            (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_176 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_173 h)
            (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_177 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_171 A)
          (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_171 A)
          (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_130 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_178 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_173 h)
          (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_173 h)
          (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_132 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_179 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_172 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_180 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_172 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_181 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_174 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_182 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_174 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_183 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_179 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_179 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_179 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_184 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_181 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_181 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_181 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_185 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_186 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_187 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_179 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_188 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_189 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_190 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_181 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_191 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_186 A))
          (Class.cv (nb090_alpha_dummy_187 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_186 A)) (Class.cv (nb090_alpha_dummy_187 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_192 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_189 h))
          (Class.cv (nb090_alpha_dummy_190 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_189 h)) (Class.cv (nb090_alpha_dummy_190 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_193 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_194 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_195 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_186 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_187 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_196 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_189 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_190 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_197 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_186 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_186 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_198 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_189 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_189 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_199 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_187 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_187 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_200 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_190 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_190 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_201 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_171 A)
          (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_171 A)
          (syn_wrex (nb090_alpha_dummy_172 A) (Class.cv (nb090_alpha_dummy_129 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_171 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_202 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_173 h)
          (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_173 h)
          (syn_wrex (nb090_alpha_dummy_174 h) (Class.cv (nb090_alpha_dummy_131 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_173 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_203 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_172 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_204 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_174 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_205 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_172 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_206 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_174 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_207 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_050 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_208 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_051 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_050 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_209 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_053 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_210 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_054 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_053 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_211 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_207 A)
            (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_212 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_209 h)
            (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_213 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_207 A)
          (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_207 A)
          (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_051 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_214 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_209 h)
          (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_209 h)
          (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_054 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_215 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_208 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_216 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_208 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_217 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_210 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_218 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_210 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_219 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_215 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_215 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_215 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_220 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_217 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_217 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_217 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_221 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_222 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_223 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_215 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_224 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_225 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_226 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_217 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_227 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_222 A))
          (Class.cv (nb090_alpha_dummy_223 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_222 A)) (Class.cv (nb090_alpha_dummy_223 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_228 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_225 h))
          (Class.cv (nb090_alpha_dummy_226 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_225 h)) (Class.cv (nb090_alpha_dummy_226 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_229 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_230 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_231 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_222 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_223 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_232 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_225 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_226 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_233 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_222 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_222 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_234 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_225 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_225 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_235 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_223 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_223 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_236 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_226 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_226 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_237 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_207 A)
          (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_207 A)
          (syn_wrex (nb090_alpha_dummy_208 A) (Class.cv (nb090_alpha_dummy_050 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_207 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_238 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_209 h)
          (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_209 h)
          (syn_wrex (nb090_alpha_dummy_210 h) (Class.cv (nb090_alpha_dummy_053 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_209 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_239 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_208 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_240 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_210 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_241 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_208 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_242 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_210 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_243 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_244 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_245 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_246 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_247 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_243 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_248 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_244 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_243 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_249 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_245 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_250 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_246 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_245 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_251 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_247 A)
            (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_252 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_249 h)
            (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_253 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_247 A)
          (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_247 A)
          (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_244 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_254 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_249 h)
          (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_249 h)
          (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_246 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_255 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_248 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_256 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_248 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_257 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_250 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_258 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_250 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_259 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_255 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_255 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_255 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_260 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_257 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_257 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_257 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_261 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_262 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_263 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_255 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_264 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_265 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_266 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_257 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_267 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_262 A))
          (Class.cv (nb090_alpha_dummy_263 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_262 A)) (Class.cv (nb090_alpha_dummy_263 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_268 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_265 h))
          (Class.cv (nb090_alpha_dummy_266 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_265 h)) (Class.cv (nb090_alpha_dummy_266 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_269 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_270 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_271 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_262 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_263 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_272 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_265 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_266 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_273 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_262 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_262 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_274 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_265 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_265 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_275 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_263 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_263 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_276 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_266 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_266 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_277 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_247 A)
          (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_247 A)
          (syn_wrex (nb090_alpha_dummy_248 A) (Class.cv (nb090_alpha_dummy_243 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_247 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_278 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_249 h)
          (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_249 h)
          (syn_wrex (nb090_alpha_dummy_250 h) (Class.cv (nb090_alpha_dummy_245 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_249 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_279 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_248 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_280 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_250 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_281 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_248 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_282 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_250 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_283 (A : Class) : Var :=
  (freshVar (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_284 (u : Var) : Var :=
  (freshVar (((syn_c2nd)).fv ∪ ((Class.cv u)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_285 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_283 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
          (Class.cv (nb090_alpha_dummy_283 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_286 (u : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_284 u)} : Finset Var) ∪
      ((syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_287 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_283 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
              (Class.cv (nb090_alpha_dummy_283 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_288 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_285 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_283 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c2nd)
              (Class.cv (nb090_alpha_dummy_283 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_285 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_289 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_284 u)
            (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
          (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_290 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_286 u) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_284 u)
            (syn_wbr (Class.cv u) (syn_c2nd) (Class.cv (nb090_alpha_dummy_284 u))))
          (syn_csn (Class.cv (nb090_alpha_dummy_286 u)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_291 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_283 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_292 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_283 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_293 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_294 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_284 u))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_295 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_291 A)
            (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_296 (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_293 u)
            (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_297 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_291 A)
          (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_291 A)
          (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_298 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_293 u)
          (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_293 u) (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_299 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_292 A))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part003`. -/


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
noncomputable def nb090_alpha_dummy_300 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_292 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_301 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_294 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_302 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_294 u))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_303 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_299 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_299 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_299 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_304 (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_301 u)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_301 u)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_301 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_305 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_306 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_307 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_299 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_308 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_309 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_310 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_301 u))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_311 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_306 A))
          (Class.cv (nb090_alpha_dummy_307 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_306 A)) (Class.cv (nb090_alpha_dummy_307 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_312 (u : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_309 u))
          (Class.cv (nb090_alpha_dummy_310 u)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_309 u)) (Class.cv (nb090_alpha_dummy_310 u)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_313 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_314 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_315 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_306 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_307 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_316 (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_309 u)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_310 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_317 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_306 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_306 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_318 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_309 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_309 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_319 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_307 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_307 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_320 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_310 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_310 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_321 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_291 A)
          (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_291 A)
          (syn_wrex (nb090_alpha_dummy_292 A) (Class.cv (nb090_alpha_dummy_283 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_291 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_322 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_293 u)
          (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_293 u)
          (syn_wrex (nb090_alpha_dummy_294 u) (Class.cv (nb090_alpha_dummy_284 u))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_293 u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_323 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_292 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_324 (u : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_294 u))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_325 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_292 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_326 (u : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_294 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_327 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_285 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_328 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_286 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_329 (A : Class) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb090_alpha_dummy_000 A)))
          (syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_330 (v : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv ∪
      ((syn_cnin (syn_crn (Class.cv h)) (syn_cfv (syn_c2nd) (Class.cv v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_331 (A : Class) : Var :=
  (freshVar (((syn_crn (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
      ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_332 (v : Var) (h : Var) : Var :=
  (freshVar (((syn_crn (Class.cv h))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_333 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_334 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_335 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_336 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_337 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_333 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_338 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_334 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_333 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_339 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_335 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_340 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_336 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_335 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_341 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_337 A)
            (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_342 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_339 h)
            (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_343 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_337 A)
          (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_337 A)
          (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_334 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_344 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_339 h)
          (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_339 h)
          (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_336 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_345 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_338 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_346 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_338 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_347 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_340 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_348 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_340 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_349 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_345 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_345 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_345 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_350 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_347 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_347 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_347 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_351 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_352 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_353 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_345 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_354 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_355 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_356 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_347 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_357 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_352 A))
          (Class.cv (nb090_alpha_dummy_353 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_352 A)) (Class.cv (nb090_alpha_dummy_353 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_358 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_355 h))
          (Class.cv (nb090_alpha_dummy_356 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_355 h)) (Class.cv (nb090_alpha_dummy_356 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_359 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_360 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_361 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_352 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_353 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_362 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_355 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_356 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_363 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_352 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_352 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_364 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_355 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_355 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_365 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_353 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_353 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_366 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_356 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_356 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_367 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_337 A)
          (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_337 A)
          (syn_wrex (nb090_alpha_dummy_338 A) (Class.cv (nb090_alpha_dummy_333 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_337 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_368 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_339 h)
          (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_339 h)
          (syn_wrex (nb090_alpha_dummy_340 h) (Class.cv (nb090_alpha_dummy_335 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_339 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_369 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_338 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_370 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_340 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_371 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_338 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_372 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_340 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_373 (A : Class) : Var :=
  (freshVar (((syn_c2nd)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_374 (v : Var) : Var :=
  (freshVar (((syn_c2nd)).fv ∪ ((Class.cv v)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_375 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_373 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
          (Class.cv (nb090_alpha_dummy_373 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_376 (v : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_374 v)} : Finset Var) ∪
      ((syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_377 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_373 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
              (Class.cv (nb090_alpha_dummy_373 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_378 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_375 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_373 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c2nd)
              (Class.cv (nb090_alpha_dummy_373 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_375 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_379 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_374 v)
            (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
          (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_380 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_376 v) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_374 v)
            (syn_wbr (Class.cv v) (syn_c2nd) (Class.cv (nb090_alpha_dummy_374 v))))
          (syn_csn (Class.cv (nb090_alpha_dummy_376 v)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_381 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_373 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_382 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_373 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_383 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_384 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_374 v))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_385 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_381 A)
            (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_386 (v : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_383 v)
            (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_387 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_381 A)
          (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_381 A)
          (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_002 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_388 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_383 v)
          (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
              (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_383 v) (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
              (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_389 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_382 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_390 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_382 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_391 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_384 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_392 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_384 v))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_393 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_389 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_389 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_389 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_394 (v : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_391 v)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_391 v)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_391 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_395 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_396 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_397 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_389 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_398 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_399 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_400 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_391 v))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_401 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_396 A))
          (Class.cv (nb090_alpha_dummy_397 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_396 A)) (Class.cv (nb090_alpha_dummy_397 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_402 (v : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_399 v))
          (Class.cv (nb090_alpha_dummy_400 v)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_399 v)) (Class.cv (nb090_alpha_dummy_400 v)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_403 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_404 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_405 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_396 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_397 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_406 (v : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_399 v)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_400 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_407 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_396 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_396 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_408 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_399 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_399 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_409 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_397 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_397 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_410 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_400 v))).fv ∪
      ((Class.cv (nb090_alpha_dummy_400 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_411 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_381 A)
          (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_381 A)
          (syn_wrex (nb090_alpha_dummy_382 A) (Class.cv (nb090_alpha_dummy_373 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_381 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_412 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_383 v)
          (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_383 v)
          (syn_wrex (nb090_alpha_dummy_384 v) (Class.cv (nb090_alpha_dummy_374 v))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_383 v))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_413 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_382 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_414 (v : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_384 v))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_415 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_382 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_416 (v : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_384 v)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_417 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_375 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_418 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_376 v))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_419 (A : Class) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
            (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_420 (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
          (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_421 (A : Class) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
          (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_422 (h : Var) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_423 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_424 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_425 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_426 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_427 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_428 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_429 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_423 A)} : Finset Var) ∪
        ({(nb090_alpha_dummy_424 A)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_425 A) (syn_wa
            (syn_wbr (Class.cv (nb090_alpha_dummy_423 A))
              (syn_ccnv (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))
              (Class.cv (nb090_alpha_dummy_425 A)))
            (syn_wbr (Class.cv (nb090_alpha_dummy_425 A))
              (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
              (Class.cv (nb090_alpha_dummy_424 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_430 (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_426 h)} : Finset Var) ∪
        ({(nb090_alpha_dummy_427 h)} : Finset Var) ∪ ((syn_wex (nb090_alpha_dummy_428 h) (syn_wa
            (syn_wbr (Class.cv (nb090_alpha_dummy_426 h))
              (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb090_alpha_dummy_428 h)))
            (syn_wbr (Class.cv (nb090_alpha_dummy_428 h)) (syn_ccnv (Class.cv h))
              (Class.cv (nb090_alpha_dummy_427 h)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_431 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_432 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_433 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_434 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_435 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_436 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_437 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_431 A)
          (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_431 A)
          (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_438 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_433 h)
          (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_433 h)
          (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_439 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_432 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_440 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_432 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_441 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_434 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_442 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_434 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_443 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_439 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_439 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_439 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_444 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_441 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_441 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_441 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_445 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_446 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_447 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_448 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_449 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part004`. -/


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
noncomputable def nb090_alpha_dummy_450 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_451 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_446 A))
          (Class.cv (nb090_alpha_dummy_447 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_446 A)) (Class.cv (nb090_alpha_dummy_447 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_452 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_449 h))
          (Class.cv (nb090_alpha_dummy_450 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_449 h)) (Class.cv (nb090_alpha_dummy_450 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_453 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_454 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_455 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_446 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_447 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_456 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_449 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_450 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_457 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_446 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_446 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_458 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_449 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_449 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_459 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_447 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_447 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_460 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_450 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_450 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_461 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_431 A)
          (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_431 A)
          (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_424 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_462 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_433 h)
          (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_433 h)
          (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_427 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_463 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_464 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_465 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_466 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_434 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_467 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_425 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_468 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_425 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_469 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_428 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_470 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_428 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_471 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_472 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_473 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_467 A)
          (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_467 A)
          (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_474 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_469 h)
          (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_469 h)
          (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_475 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_468 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_476 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_468 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_477 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_470 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_478 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_470 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_479 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_475 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_475 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_475 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_480 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_477 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_477 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_477 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_481 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_482 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_483 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_484 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_485 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_486 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_487 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_482 A))
          (Class.cv (nb090_alpha_dummy_483 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_482 A)) (Class.cv (nb090_alpha_dummy_483 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_488 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_485 h))
          (Class.cv (nb090_alpha_dummy_486 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_485 h)) (Class.cv (nb090_alpha_dummy_486 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_489 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_490 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_491 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_482 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_483 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_492 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_485 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_486 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_493 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_482 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_482 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_494 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_485 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_485 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_495 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_483 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_483 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_496 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_486 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_486 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_497 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_467 A)
          (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_467 A)
          (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_425 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_498 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_469 h)
          (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_469 h)
          (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_428 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_499 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_500 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_501 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_502 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_470 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_503 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_504 (A : Class) : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_505 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_506 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_507 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_503 A)} : Finset Var) ∪
        ({(nb090_alpha_dummy_504 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_504 A))
          (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))
          (Class.cv (nb090_alpha_dummy_503 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_508 (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_505 h)} : Finset Var) ∪
        ({(nb090_alpha_dummy_506 h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_506 h)) (syn_ccnv (Class.cv h))
          (Class.cv (nb090_alpha_dummy_505 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_509 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_504 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_510 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_504 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_511 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_506 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_512 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_506 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_513 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_514 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_515 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_509 A)
          (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_509 A)
          (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_516 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_511 h)
          (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_511 h)
          (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_517 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_510 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_518 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_510 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_519 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_512 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_520 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_512 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_521 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_517 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_517 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_517 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_522 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_519 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_519 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_519 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_523 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_524 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_525 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_526 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_527 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_528 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_529 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_524 A))
          (Class.cv (nb090_alpha_dummy_525 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_524 A)) (Class.cv (nb090_alpha_dummy_525 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_530 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_527 h))
          (Class.cv (nb090_alpha_dummy_528 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_527 h)) (Class.cv (nb090_alpha_dummy_528 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_531 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_532 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_533 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_524 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_525 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_534 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_527 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_528 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_535 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_524 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_524 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_536 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_527 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_527 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_537 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_525 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_525 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_538 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_528 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_528 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_539 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_509 A)
          (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_509 A)
          (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_504 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_540 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_511 h)
          (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_511 h)
          (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_506 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_541 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_542 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_543 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_544 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_545 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_503 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_546 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_503 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_547 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_505 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_548 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_505 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_549 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_550 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_551 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_545 A)
          (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_545 A)
          (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_552 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_547 h)
          (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_547 h)
          (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_553 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_546 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_554 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_546 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_555 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_548 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_556 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_548 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_557 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_553 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_553 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_553 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_558 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_555 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_555 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_555 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_559 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_560 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_561 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_562 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_563 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_564 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_565 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_560 A))
          (Class.cv (nb090_alpha_dummy_561 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_560 A)) (Class.cv (nb090_alpha_dummy_561 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_566 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_563 h))
          (Class.cv (nb090_alpha_dummy_564 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_563 h)) (Class.cv (nb090_alpha_dummy_564 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_567 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_568 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_569 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_560 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_561 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_570 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_563 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_564 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_571 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_560 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_560 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_572 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_563 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_563 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_573 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_561 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_561 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_574 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_564 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_564 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_575 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_545 A)
          (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_545 A)
          (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_503 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_576 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_547 h)
          (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_547 h)
          (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_505 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_577 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_578 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_579 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_580 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_581 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_424 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_582 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_425 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_424 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_583 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_427 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_584 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_428 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_427 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_585 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_586 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_587 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_581 A)
          (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_581 A)
          (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_425 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_588 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_583 h)
          (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_583 h)
          (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_589 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_582 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_590 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_582 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_591 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_584 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_592 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_584 h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_593 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_589 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_589 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_589 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_594 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_591 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_591 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_591 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_595 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_596 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_597 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_589 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_598 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_599 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 1)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part005`. -/


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
noncomputable def nb090_alpha_dummy_600 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_591 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_601 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_596 A))
          (Class.cv (nb090_alpha_dummy_597 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_596 A)) (Class.cv (nb090_alpha_dummy_597 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_602 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_599 h))
          (Class.cv (nb090_alpha_dummy_600 h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_599 h)) (Class.cv (nb090_alpha_dummy_600 h)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_603 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_604 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_605 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_596 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_597 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_606 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_599 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_600 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_607 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_596 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_596 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_608 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_599 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_599 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_609 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_597 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_597 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_610 (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_600 h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_600 h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_611 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_581 A)
          (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A)
          (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_612 (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_583 h)
          (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h)
          (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_613 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_614 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_615 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_616 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_617 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_042 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_618 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_042 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_619 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_620 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_621 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_622 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h)
            (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_623 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_617 A)
          (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_617 A)
          (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_624 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_619 v u h)
          (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_619 v u h)
          (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_625 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_618 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_626 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_618 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_627 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_628 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_629 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_625 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_630 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_631 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_632 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_633 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_634 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_635 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_636 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_637 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
          (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A)) (Class.cv (nb090_alpha_dummy_633 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_638 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
          (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
          (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_639 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_640 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_641 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_642 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_643 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_632 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_644 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_645 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_633 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_646 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_647 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_617 A)
          (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A)
          (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_648 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_619 v u h)
          (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h)
          (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_649 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_650 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_651 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_652 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_653 (A : Class) : Var :=
  (freshVar (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_654 (u : Var) : Var :=
  (freshVar (((syn_c1st)).fv ∪ ((Class.cv u)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_655 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
          (Class.cv (nb090_alpha_dummy_653 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_656 (u : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪
      ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_657 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_653 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
              (Class.cv (nb090_alpha_dummy_653 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_658 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_653 A)
            (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
              (Class.cv (nb090_alpha_dummy_653 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_659 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_654 u)
            (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
          (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_660 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_654 u)
            (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
          (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_661 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_653 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_662 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_653 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_663 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_664 (u : Var) : Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_665 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_666 (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_667 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_661 A)
          (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_661 A)
          (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_668 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_663 u)
          (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
            (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
              (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_669 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_662 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_670 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_662 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_671 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_664 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_672 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_664 u))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_673 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_669 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_674 (u : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_671 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_675 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_676 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_677 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_678 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_679 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_680 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_681 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
          (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A)) (Class.cv (nb090_alpha_dummy_677 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_682 (u : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
          (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u)) (Class.cv (nb090_alpha_dummy_680 u)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_683 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_684 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_685 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_686 (u : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_687 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_676 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_688 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_679 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_689 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_677 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_690 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪
      ((Class.cv (nb090_alpha_dummy_680 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_691 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_661 A)
          (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A)
          (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_692 (u : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_663 u)
          (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u)
          (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_693 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_694 (u : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_695 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_696 (u : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_697 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_655 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_698 (u : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_656 u))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_699 (A : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
          (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
      ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_700 (A : Class) : Var :=
  (freshVar (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
          (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
      ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_042 A)))).fv)
    1)

@[expose]
noncomputable def nb090_alpha_dummy_701 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
      ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_702 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
      ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_703 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A)
            (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_704 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
            (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_705 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
            (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
            (syn_cfv (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_041 A)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_706 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
            (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
            (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_707 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_041 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_708 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_709 (A : Class) : Var :=
  (freshVar (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
          (Class.cv (nb090_alpha_dummy_707 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_710 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
          (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_711 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
              (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_712 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_707 A) (syn_wbr (Class.cv (nb090_alpha_dummy_041 A))
              (Class.cv (nb090_alpha_dummy_000 A)) (Class.cv (nb090_alpha_dummy_707 A))))
          (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_713 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_708 v u h)
            (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
              (Class.cv (nb090_alpha_dummy_708 v u h))))
          (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_714 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
          (Class.cab (nb090_alpha_dummy_708 v u h)
            (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
              (Class.cv (nb090_alpha_dummy_708 v u h))))
          (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_715 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_707 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_716 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_707 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_717 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_718 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_719 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_720 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h)
            (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_721 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_715 A)
          (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_715 A)
          (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
              (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_722 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_717 v u h)
          (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪
      ((Class.cab (nb090_alpha_dummy_717 v u h)
          (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
              (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_723 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_716 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_724 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_716 A))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_725 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_726 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_727 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_723 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_728 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪
      ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_729 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_730 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_731 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_732 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_733 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb090_alpha_dummy_734 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb090_alpha_dummy_735 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
          (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A)) (Class.cv (nb090_alpha_dummy_731 A)))).fv)
    0)

@[expose]
noncomputable def nb090_alpha_dummy_736 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
          (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪
      ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
          (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_737 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_738 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_739 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_740 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪
      ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_741 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_730 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_742 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_743 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪
      ((Class.cv (nb090_alpha_dummy_731 A))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_744 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪
      ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_745 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_715 A)
          (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A)
          (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_746 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090_alpha_dummy_717 v u h)
          (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h)
          (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h))
            (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
              (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_747 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_748 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb090_alpha_dummy_749 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪
      ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
