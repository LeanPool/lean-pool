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

/-! Certificates from `NAR4C057C001Part001`. -/


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
noncomputable def nb057_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb057_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb057_alpha_dummy_002 : Var :=
  (freshVar
    (({(nb057_alpha_dummy_001)} : Finset Var) ∪ ({(nb057_alpha_dummy_000)} : Finset Var) ∪
      ((syn_wfn (Class.cv (nb057_alpha_dummy_001)) (Class.cv (nb057_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_003 (f : Var) (a : Var) : Var :=
  (freshVar (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ((syn_wfn (Class.cv f) (Class.cv a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_004 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_006 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_007 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_008 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_009 (f : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_010 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_004)
          (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
              (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_004)
          (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
              (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_011 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_006 f a)
          (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
            (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
              (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_006 f a) (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
            (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
              (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_012 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_005))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_005))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_014 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_015 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_016 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_012))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_017 (f : Var) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_014 f a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_018 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_021 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_022 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_023 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_024 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_019))
          (Class.cv (nb057_alpha_dummy_020)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_025 (f : Var) (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
          (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
          (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_026 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_027 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
      ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_028 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_029 (f : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_030 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_031 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
      ((Class.cv (nb057_alpha_dummy_022 f a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_032 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_033 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪
      ((Class.cv (nb057_alpha_dummy_023 f a))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_034 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_004)
          (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004)
          (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_035 (f : Var) (a : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_006 f a)
          (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
            (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a)
          (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
            (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_036 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_037 (f : Var) (a : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_038 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_005)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_039 (f : Var) (a : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_040 : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv (nb057_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv ∪ ((syn_cnin
          (syn_ccom (Class.cv (nb057_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_041 (f : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_042 : Var :=
  (freshVar (((syn_ccom (Class.cv (nb057_alpha_dummy_001))
          (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_043 (f : Var) : Var :=
  (freshVar (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_044 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_045 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_046 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv ∪
      ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_047 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_048 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_049 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_050 : Var :=
  (freshVar
    (({(nb057_alpha_dummy_044)} : Finset Var) ∪ ({(nb057_alpha_dummy_045)} : Finset Var) ∪
      ((syn_wex (nb057_alpha_dummy_046) (syn_wa (syn_wbr (Class.cv (nb057_alpha_dummy_044))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046)))
            (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001))
              (Class.cv (nb057_alpha_dummy_045)))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_051 (f : Var) : Var :=
  (freshVar (({(nb057_alpha_dummy_047 f)} : Finset Var) ∪
        ({(nb057_alpha_dummy_048 f)} : Finset Var) ∪ ((syn_wex (nb057_alpha_dummy_049 f) (syn_wa
            (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
              (Class.cv (nb057_alpha_dummy_049 f)))
            (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
              (Class.cv (nb057_alpha_dummy_048 f)))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_052 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_053 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_054 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_055 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_056 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_057 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_058 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_052)
          (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
              (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_052)
          (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
              (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_059 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_054 f)
          (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_054 f)
          (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_060 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_053))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_053))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_062 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_055 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_063 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_055 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_064 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_060))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_065 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_062 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_066 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_067 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_068 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_069 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_070 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_071 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_072 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_067))
          (Class.cv (nb057_alpha_dummy_068)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_073 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_070 f))
          (Class.cv (nb057_alpha_dummy_071 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_070 f)) (Class.cv (nb057_alpha_dummy_071 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_074 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_075 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_076 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_077 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_078 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_079 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_070 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_080 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_081 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_071 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_082 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_052)
          (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052)
          (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_083 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_054 f)
          (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f)
          (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_084 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_085 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_086 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_053)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_087 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_088 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_089 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_090 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_049 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_091 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_049 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_092 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_093 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_094 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_088)
          (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
              (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_088)
          (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
              (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_095 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_090 f)
          (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_090 f)
          (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_096 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_089))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_097 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_089))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_098 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_091 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_099 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_091 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_100 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_096))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_101 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_098 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_102 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_103 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_104 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_105 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_106 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_107 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_108 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_103))
          (Class.cv (nb057_alpha_dummy_104)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_109 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_106 f))
          (Class.cv (nb057_alpha_dummy_107 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_106 f)) (Class.cv (nb057_alpha_dummy_107 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_110 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_111 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_112 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_113 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_114 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_115 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_106 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_116 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_117 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_107 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_118 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_088)
          (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088)
          (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_119 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_090 f)
          (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f)
          (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_120 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_121 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_122 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_089)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_123 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_124 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_125 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_126 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_127 (f : Var) : Var :=
  (freshVar (((Class.cv f)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_128 : Var :=
  (freshVar
    (({(nb057_alpha_dummy_124)} : Finset Var) ∪ ({(nb057_alpha_dummy_125)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
          (Class.cv (nb057_alpha_dummy_124)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_129 (f : Var) : Var :=
  (freshVar (({(nb057_alpha_dummy_126 f)} : Finset Var) ∪
        ({(nb057_alpha_dummy_127 f)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
          (Class.cv (nb057_alpha_dummy_126 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_130 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_131 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_132 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_127 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_133 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_127 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_134 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_135 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_136 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_130)
          (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
              (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_130)
          (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
              (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_137 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_132 f)
          (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_132 f)
          (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_138 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_131))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_139 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_131))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_140 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_133 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_141 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_133 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_142 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_138))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_143 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_140 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_144 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_145 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_146 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_147 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_148 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_149 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 2)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part002`. -/


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
noncomputable def nb057_alpha_dummy_150 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_145))
          (Class.cv (nb057_alpha_dummy_146)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_151 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_148 f))
          (Class.cv (nb057_alpha_dummy_149 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_148 f)) (Class.cv (nb057_alpha_dummy_149 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_152 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_153 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_154 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_155 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_156 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_157 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_148 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_158 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_159 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_149 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_160 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_130)
          (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130)
          (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_161 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_132 f)
          (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f)
          (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_162 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_163 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_164 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_131)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_165 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_166 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_167 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_168 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_126 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_169 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_126 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_170 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_171 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_172 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_166)
          (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
              (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_166)
          (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
              (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_173 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_168 f)
          (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_168 f)
          (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_174 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_167))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_175 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_167))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_176 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_169 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_177 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_169 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_178 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_174))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_179 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_176 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_180 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_181 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_182 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_183 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_184 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_185 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_186 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_181))
          (Class.cv (nb057_alpha_dummy_182)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_187 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_184 f))
          (Class.cv (nb057_alpha_dummy_185 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_184 f)) (Class.cv (nb057_alpha_dummy_185 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_188 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_189 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_190 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_191 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_192 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_193 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_184 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_194 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_195 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_185 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_196 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_166)
          (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166)
          (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_197 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_168 f)
          (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f)
          (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_198 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_199 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_200 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_167)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_201 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_202 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_203 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_204 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_048 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_205 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_048 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_206 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_207 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_208 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_202)
          (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
              (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_202)
          (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
              (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_209 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_204 f)
          (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_204 f)
          (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_210 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_203))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_211 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_203))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_212 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_205 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_213 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_205 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_214 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_210))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_215 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_212 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_216 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_217 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_218 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_219 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_220 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_221 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_222 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_217))
          (Class.cv (nb057_alpha_dummy_218)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_223 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_220 f))
          (Class.cv (nb057_alpha_dummy_221 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_220 f)) (Class.cv (nb057_alpha_dummy_221 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_224 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_225 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_226 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_227 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_228 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_229 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_220 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_230 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_231 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_221 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_232 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_202)
          (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202)
          (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_233 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_204 f)
          (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f)
          (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_234 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_235 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_236 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_203)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_237 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_238 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_239 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_240 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_241 (f : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_242 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_243 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_244 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_240 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_245 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_240 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_246 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_247 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_248 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_242)
          (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
              (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_242)
          (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
              (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_249 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_244 f)
          (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪
      ((Class.cab (nb057_alpha_dummy_244 f)
          (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
              (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_250 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_243))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_251 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_243))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_252 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_245 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_253 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_245 f))).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_254 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_250))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_255 (f : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪
      ((Class.cv (nb057_alpha_dummy_252 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_256 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_257 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_258 : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_259 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_260 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb057_alpha_dummy_261 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb057_alpha_dummy_262 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_257))
          (Class.cv (nb057_alpha_dummy_258)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_263 (f : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb057_alpha_dummy_260 f))
          (Class.cv (nb057_alpha_dummy_261 f)))).fv ∪
      ((syn_cnin (Class.cv (nb057_alpha_dummy_260 f)) (Class.cv (nb057_alpha_dummy_261 f)))).fv)
    0)

@[expose]
noncomputable def nb057_alpha_dummy_264 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_265 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_266 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_267 (f : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪
      ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_268 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_269 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_260 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_270 : Var :=
  (freshVar
    (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_271 (f : Var) : Var :=
  (freshVar (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪
      ((Class.cv (nb057_alpha_dummy_261 f))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_272 : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_242)
          (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242)
          (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_273 (f : Var) : Var :=
  (freshVar (((Class.cab (nb057_alpha_dummy_244 f)
          (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f)
          (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
            (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
              (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_274 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_275 (f : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_276 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_243)))).fv) 0)

@[expose]
noncomputable def nb057_alpha_dummy_277 (f : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv ∪
      ((syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))).fv) 0)

theorem nb057_fresh_000 :
    (nb057_alpha_dummy_034) ∉
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_001 :
    (nb057_alpha_dummy_010) ∉
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_004)
            (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                (syn_cphi (Class.cv (nb057_alpha_dummy_005))))))).fv)
      0

theorem nb057_fresh_002 (f : Var) (a : Var) :
    (nb057_alpha_dummy_035 f a) ∉
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_003 (f : Var) (a : Var) :
    (nb057_alpha_dummy_011 f a) ∉
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_006 f a)
            (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))))).fv)
      0

theorem nb057_fresh_004 :
    (nb057_alpha_dummy_058) ∉
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_058] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cphi (Class.cv (nb057_alpha_dummy_053))))))).fv)
      0

theorem nb057_fresh_005 :
    (nb057_alpha_dummy_082) ∉
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_006 (f : Var) :
    (nb057_alpha_dummy_059 f) ∉
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_059] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))))).fv)
      0

theorem nb057_fresh_007 (f : Var) :
    (nb057_alpha_dummy_083 f) ∉
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_008 :
    (nb057_alpha_dummy_094) ∉
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cphi (Class.cv (nb057_alpha_dummy_089))))))).fv)
      0

theorem nb057_fresh_009 :
    (nb057_alpha_dummy_118) ∉
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_118] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_010 (f : Var) :
    (nb057_alpha_dummy_095 f) ∉
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))))).fv)
      0

theorem nb057_fresh_011 (f : Var) :
    (nb057_alpha_dummy_119 f) ∉
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_012 :
    (nb057_alpha_dummy_136) ∉
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_136] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cphi (Class.cv (nb057_alpha_dummy_131))))))).fv)
      0

theorem nb057_fresh_013 :
    (nb057_alpha_dummy_160) ∉
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_160] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_014 (f : Var) :
    (nb057_alpha_dummy_137 f) ∉
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_137] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))))).fv)
      0

theorem nb057_fresh_015 (f : Var) :
    (nb057_alpha_dummy_161 f) ∉
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_016 :
    (nb057_alpha_dummy_196) ∉
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_196] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_017 :
    (nb057_alpha_dummy_172) ∉
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_172] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cphi (Class.cv (nb057_alpha_dummy_167))))))).fv)
      0

theorem nb057_fresh_018 (f : Var) :
    (nb057_alpha_dummy_197 f) ∉
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_019 (f : Var) :
    (nb057_alpha_dummy_173 f) ∉
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))))).fv)
      0

theorem nb057_fresh_020 :
    (nb057_alpha_dummy_232) ∉
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_232] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_021 :
    (nb057_alpha_dummy_208) ∉
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_208] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cphi (Class.cv (nb057_alpha_dummy_203))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part003`. -/


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

theorem nb057_fresh_022 (f : Var) :
    (nb057_alpha_dummy_233 f) ∉
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_233] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_023 (f : Var) :
    (nb057_alpha_dummy_209 f) ∉
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_209] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))))).fv)
      0

theorem nb057_fresh_024 :
    (nb057_alpha_dummy_272) ∉
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_272] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_025 :
    (nb057_alpha_dummy_248) ∉
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_248] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))).fv)
      0

theorem nb057_fresh_026 (f : Var) :
    (nb057_alpha_dummy_273 f) ∉
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_273] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb057_fresh_027 (f : Var) :
    (nb057_alpha_dummy_249 f) ∉
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_249] using
    freshVar_not_mem
      (((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv ∪
        ((Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))))).fv)
      0

theorem nb057_fresh_028 :
    (nb057_alpha_dummy_124) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv) := by
  simpa only [nb057_alpha_dummy_124] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv) 0

theorem nb057_fresh_029 :
    (nb057_alpha_dummy_125) ∉ (((Class.cv (nb057_alpha_dummy_001))).fv) := by
  simpa only [nb057_alpha_dummy_125] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_001))).fv) 1

theorem nb057_distinct_030 : (nb057_alpha_dummy_124) ≠ (nb057_alpha_dummy_125) := by
  simpa only [nb057_alpha_dummy_124, nb057_alpha_dummy_125] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_031 :
    (nb057_alpha_dummy_004) ∉
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) :=
  by
  simpa only [nb057_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv)
      0

theorem nb057_fresh_032 :
    (nb057_alpha_dummy_005) ∉
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv) :=
  by
  simpa only [nb057_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv)
      1

theorem nb057_distinct_033 : (nb057_alpha_dummy_004) ≠ (nb057_alpha_dummy_005) := by
  simpa only [nb057_alpha_dummy_004, nb057_alpha_dummy_005] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((Class.cv (nb057_alpha_dummy_000))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_034 :
    (nb057_alpha_dummy_044) ∉
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv)
      0

theorem nb057_fresh_035 :
    (nb057_alpha_dummy_045) ∉
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv)
      1

theorem nb057_fresh_036 :
    (nb057_alpha_dummy_046) ∉
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv)
      2

theorem nb057_distinct_037 : (nb057_alpha_dummy_044) ≠ (nb057_alpha_dummy_045) := by
  simpa only [nb057_alpha_dummy_044, nb057_alpha_dummy_045] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_distinct_038 : (nb057_alpha_dummy_044) ≠ (nb057_alpha_dummy_046) := by
  simpa only [nb057_alpha_dummy_044, nb057_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb057_distinct_039 : (nb057_alpha_dummy_045) ≠ (nb057_alpha_dummy_046) := by
  simpa only [nb057_alpha_dummy_045, nb057_alpha_dummy_046] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb057_fresh_040 :
    (nb057_alpha_dummy_012) ∉ (((Class.cv (nb057_alpha_dummy_005))).fv) := by
  simpa only [nb057_alpha_dummy_012] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_005))).fv) 0

theorem nb057_fresh_041 :
    (nb057_alpha_dummy_013) ∉ (((Class.cv (nb057_alpha_dummy_005))).fv) := by
  simpa only [nb057_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_005))).fv) 1

theorem nb057_distinct_042 : (nb057_alpha_dummy_012) ≠ (nb057_alpha_dummy_013) := by
  simpa only [nb057_alpha_dummy_012, nb057_alpha_dummy_013] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_005))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_043 (f : Var) (a : Var) :
    (nb057_alpha_dummy_014 f a) ∉ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) := by
  simpa only [nb057_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 0

theorem nb057_fresh_044 (f : Var) (a : Var) :
    (nb057_alpha_dummy_015 f a) ∉ (((Class.cv (nb057_alpha_dummy_007 f a))).fv) := by
  simpa only [nb057_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_007 f a))).fv) 1

theorem nb057_distinct_045 (f : Var) (a : Var) :
    (nb057_alpha_dummy_014 f a) ≠ (nb057_alpha_dummy_015 f a) := by
  simpa only [nb057_alpha_dummy_014, nb057_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_007 f a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_046 :
    (nb057_alpha_dummy_018) ∉
      (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_047 :
    (nb057_alpha_dummy_019) ∉
      (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_048 :
    (nb057_alpha_dummy_020) ∉
      (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_049 : (nb057_alpha_dummy_018) ≠ (nb057_alpha_dummy_019) := by
  simpa only [nb057_alpha_dummy_018, nb057_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_050 : (nb057_alpha_dummy_018) ≠ (nb057_alpha_dummy_020) := by
  simpa only [nb057_alpha_dummy_018, nb057_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_051 : (nb057_alpha_dummy_019) ≠ (nb057_alpha_dummy_020) := by
  simpa only [nb057_alpha_dummy_019, nb057_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_012))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_052 (f : Var) (a : Var) :
    (nb057_alpha_dummy_021 f a) ∉
      (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_053 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ∉
      (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_054 (f : Var) (a : Var) :
    (nb057_alpha_dummy_023 f a) ∉
      (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_055 (f : Var) (a : Var) :
    (nb057_alpha_dummy_021 f a) ≠ (nb057_alpha_dummy_022 f a) := by
  simpa only [nb057_alpha_dummy_021, nb057_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_distinct_056 (f : Var) (a : Var) :
    (nb057_alpha_dummy_021 f a) ≠ (nb057_alpha_dummy_023 f a) := by
  simpa only [nb057_alpha_dummy_021, nb057_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb057_distinct_057 (f : Var) (a : Var) :
    (nb057_alpha_dummy_022 f a) ≠ (nb057_alpha_dummy_023 f a) := by
  simpa only [nb057_alpha_dummy_022, nb057_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_014 f a))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb057_fresh_058 :
    (nb057_alpha_dummy_030) ∉
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv) :=
  by
  simpa only [nb057_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_019))).fv)
      0

theorem nb057_fresh_059 :
    (nb057_alpha_dummy_026) ∉
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) :=
  by
  simpa only [nb057_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_019))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv)
      0

theorem nb057_fresh_060 :
    (nb057_alpha_dummy_032) ∉
      (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv) :=
  by
  simpa only [nb057_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_020))).fv ∪ ((Class.cv (nb057_alpha_dummy_020))).fv)
      0

theorem nb057_fresh_061 (f : Var) (a : Var) :
    (nb057_alpha_dummy_031 f a) ∉
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_022 f a))).fv) :=
  by
  simpa only [nb057_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_022 f a))).fv)
      0

theorem nb057_fresh_062 (f : Var) (a : Var) :
    (nb057_alpha_dummy_027 f a) ∉
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv) :=
  by
  simpa only [nb057_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_022 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv)
      0

theorem nb057_fresh_063 (f : Var) (a : Var) :
    (nb057_alpha_dummy_033 f a) ∉
      (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv) :=
  by
  simpa only [nb057_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_023 f a))).fv ∪
        ((Class.cv (nb057_alpha_dummy_023 f a))).fv)
      0

theorem nb057_fresh_064 :
    (nb057_alpha_dummy_052) ∉
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  simpa only [nb057_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      0

theorem nb057_fresh_065 :
    (nb057_alpha_dummy_053) ∉
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  simpa only [nb057_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      1

theorem nb057_distinct_066 : (nb057_alpha_dummy_052) ≠ (nb057_alpha_dummy_053) := by
  simpa only [nb057_alpha_dummy_052, nb057_alpha_dummy_053] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_067 :
    (nb057_alpha_dummy_088) ∉
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) :=
  by
  simpa only [nb057_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv)
      0

theorem nb057_fresh_068 :
    (nb057_alpha_dummy_089) ∉
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv) :=
  by
  simpa only [nb057_alpha_dummy_089] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv)
      1

theorem nb057_distinct_069 : (nb057_alpha_dummy_088) ≠ (nb057_alpha_dummy_089) := by
  simpa only [nb057_alpha_dummy_088, nb057_alpha_dummy_089] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_070 :
    (nb057_alpha_dummy_202) ∉
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  simpa only [nb057_alpha_dummy_202] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      0

theorem nb057_fresh_071 :
    (nb057_alpha_dummy_203) ∉
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv) :=
  by
  simpa only [nb057_alpha_dummy_203] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      1

theorem nb057_distinct_072 : (nb057_alpha_dummy_202) ≠ (nb057_alpha_dummy_203) := by
  simpa only [nb057_alpha_dummy_202, nb057_alpha_dummy_203] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_073 (f : Var) :
    (nb057_alpha_dummy_054 f) ∉
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv)
      0

theorem nb057_fresh_074 (f : Var) :
    (nb057_alpha_dummy_055 f) ∉
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv)
      1

theorem nb057_distinct_075 (f : Var) :
    (nb057_alpha_dummy_054 f) ≠ (nb057_alpha_dummy_055 f) := by
  simpa only [nb057_alpha_dummy_054, nb057_alpha_dummy_055] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_076 (f : Var) :
    (nb057_alpha_dummy_090 f) ∉
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_090] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv)
      0

theorem nb057_fresh_077 (f : Var) :
    (nb057_alpha_dummy_091 f) ∉
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_091] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_049 f))).fv)
      1

theorem nb057_distinct_078 (f : Var) :
    (nb057_alpha_dummy_090 f) ≠ (nb057_alpha_dummy_091 f) := by
  simpa only [nb057_alpha_dummy_090, nb057_alpha_dummy_091] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_049 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_079 (f : Var) :
    (nb057_alpha_dummy_204 f) ∉
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_204] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv)
      0

theorem nb057_fresh_080 (f : Var) :
    (nb057_alpha_dummy_205 f) ∉
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_205] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_048 f))).fv)
      1

theorem nb057_distinct_081 (f : Var) :
    (nb057_alpha_dummy_204 f) ≠ (nb057_alpha_dummy_205 f) := by
  simpa only [nb057_alpha_dummy_204, nb057_alpha_dummy_205] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_082 :
    (nb057_alpha_dummy_060) ∉ (((Class.cv (nb057_alpha_dummy_053))).fv) := by
  simpa only [nb057_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_053))).fv) 0

theorem nb057_fresh_083 :
    (nb057_alpha_dummy_061) ∉ (((Class.cv (nb057_alpha_dummy_053))).fv) := by
  simpa only [nb057_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_053))).fv) 1

theorem nb057_distinct_084 : (nb057_alpha_dummy_060) ≠ (nb057_alpha_dummy_061) := by
  simpa only [nb057_alpha_dummy_060, nb057_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_085 (f : Var) :
    (nb057_alpha_dummy_062 f) ∉ (((Class.cv (nb057_alpha_dummy_055 f))).fv) := by
  simpa only [nb057_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_055 f))).fv) 0

theorem nb057_fresh_086 (f : Var) :
    (nb057_alpha_dummy_063 f) ∉ (((Class.cv (nb057_alpha_dummy_055 f))).fv) := by
  simpa only [nb057_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_055 f))).fv) 1

theorem nb057_distinct_087 (f : Var) :
    (nb057_alpha_dummy_062 f) ≠ (nb057_alpha_dummy_063 f) := by
  simpa only [nb057_alpha_dummy_062, nb057_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_088 :
    (nb057_alpha_dummy_066) ∉
      (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_089 :
    (nb057_alpha_dummy_067) ∉
      (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_067] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_090 :
    (nb057_alpha_dummy_068) ∉
      (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_068] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_091 : (nb057_alpha_dummy_066) ≠ (nb057_alpha_dummy_067) := by
  simpa only [nb057_alpha_dummy_066, nb057_alpha_dummy_067] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_092 : (nb057_alpha_dummy_066) ≠ (nb057_alpha_dummy_068) := by
  simpa only [nb057_alpha_dummy_066, nb057_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_093 : (nb057_alpha_dummy_067) ≠ (nb057_alpha_dummy_068) := by
  simpa only [nb057_alpha_dummy_067, nb057_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_094 (f : Var) :
    (nb057_alpha_dummy_069 f) ∉
      (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_069] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_095 (f : Var) :
    (nb057_alpha_dummy_070 f) ∉
      (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_070] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_096 (f : Var) :
    (nb057_alpha_dummy_071 f) ∉
      (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_071] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_097 (f : Var) :
    (nb057_alpha_dummy_069 f) ≠ (nb057_alpha_dummy_070 f) := by
  simpa only [nb057_alpha_dummy_069, nb057_alpha_dummy_070] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_098 (f : Var) :
    (nb057_alpha_dummy_069 f) ≠ (nb057_alpha_dummy_071 f) := by
  simpa only [nb057_alpha_dummy_069, nb057_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_099 (f : Var) :
    (nb057_alpha_dummy_070 f) ≠ (nb057_alpha_dummy_071 f) := by
  simpa only [nb057_alpha_dummy_070, nb057_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_100 :
    (nb057_alpha_dummy_078) ∉
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv) :=
  by
  simpa only [nb057_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_067))).fv)
      0

theorem nb057_fresh_101 :
    (nb057_alpha_dummy_074) ∉
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) :=
  by
  simpa only [nb057_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_067))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv)
      0

theorem nb057_fresh_102 :
    (nb057_alpha_dummy_080) ∉
      (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv) :=
  by
  simpa only [nb057_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_068))).fv ∪ ((Class.cv (nb057_alpha_dummy_068))).fv)
      0

theorem nb057_fresh_103 (f : Var) :
    (nb057_alpha_dummy_079 f) ∉
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_070 f))).fv)
      0

theorem nb057_fresh_104 (f : Var) :
    (nb057_alpha_dummy_075 f) ∉
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_070 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv)
      0

theorem nb057_fresh_105 (f : Var) :
    (nb057_alpha_dummy_081 f) ∉
      (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_071 f))).fv)
      0

theorem nb057_fresh_106 :
    (nb057_alpha_dummy_096) ∉ (((Class.cv (nb057_alpha_dummy_089))).fv) := by
  simpa only [nb057_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_089))).fv) 0

theorem nb057_fresh_107 :
    (nb057_alpha_dummy_097) ∉ (((Class.cv (nb057_alpha_dummy_089))).fv) := by
  simpa only [nb057_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_089))).fv) 1

theorem nb057_distinct_108 : (nb057_alpha_dummy_096) ≠ (nb057_alpha_dummy_097) := by
  simpa only [nb057_alpha_dummy_096, nb057_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_109 (f : Var) :
    (nb057_alpha_dummy_098 f) ∉ (((Class.cv (nb057_alpha_dummy_091 f))).fv) := by
  simpa only [nb057_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_091 f))).fv) 0

theorem nb057_fresh_110 (f : Var) :
    (nb057_alpha_dummy_099 f) ∉ (((Class.cv (nb057_alpha_dummy_091 f))).fv) := by
  simpa only [nb057_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_091 f))).fv) 1

theorem nb057_distinct_111 (f : Var) :
    (nb057_alpha_dummy_098 f) ≠ (nb057_alpha_dummy_099 f) := by
  simpa only [nb057_alpha_dummy_098, nb057_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_112 :
    (nb057_alpha_dummy_102) ∉
      (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_102] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_113 :
    (nb057_alpha_dummy_103) ∉
      (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_114 :
    (nb057_alpha_dummy_104) ∉
      (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_104] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_115 : (nb057_alpha_dummy_102) ≠ (nb057_alpha_dummy_103) := by
  simpa only [nb057_alpha_dummy_102, nb057_alpha_dummy_103] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_116 : (nb057_alpha_dummy_102) ≠ (nb057_alpha_dummy_104) := by
  simpa only [nb057_alpha_dummy_102, nb057_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_117 : (nb057_alpha_dummy_103) ≠ (nb057_alpha_dummy_104) := by
  simpa only [nb057_alpha_dummy_103, nb057_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_118 (f : Var) :
    (nb057_alpha_dummy_105 f) ∉
      (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_119 (f : Var) :
    (nb057_alpha_dummy_106 f) ∉
      (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_120 (f : Var) :
    (nb057_alpha_dummy_107 f) ∉
      (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_121 (f : Var) :
    (nb057_alpha_dummy_105 f) ≠ (nb057_alpha_dummy_106 f) := by
  simpa only [nb057_alpha_dummy_105, nb057_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_122 (f : Var) :
    (nb057_alpha_dummy_105 f) ≠ (nb057_alpha_dummy_107 f) := by
  simpa only [nb057_alpha_dummy_105, nb057_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_123 (f : Var) :
    (nb057_alpha_dummy_106 f) ≠ (nb057_alpha_dummy_107 f) := by
  simpa only [nb057_alpha_dummy_106, nb057_alpha_dummy_107] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_124 :
    (nb057_alpha_dummy_114) ∉
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv) :=
  by
  simpa only [nb057_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_103))).fv)
      0

theorem nb057_fresh_125 :
    (nb057_alpha_dummy_110) ∉
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) :=
  by
  simpa only [nb057_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_103))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv)
      0

theorem nb057_fresh_126 :
    (nb057_alpha_dummy_116) ∉
      (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv) :=
  by
  simpa only [nb057_alpha_dummy_116] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_104))).fv ∪ ((Class.cv (nb057_alpha_dummy_104))).fv)
      0

theorem nb057_fresh_127 (f : Var) :
    (nb057_alpha_dummy_115 f) ∉
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_115] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_106 f))).fv)
      0

theorem nb057_fresh_128 (f : Var) :
    (nb057_alpha_dummy_111 f) ∉
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_106 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv)
      0

theorem nb057_fresh_129 (f : Var) :
    (nb057_alpha_dummy_117 f) ∉
      (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_117] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_107 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_107 f))).fv)
      0

theorem nb057_fresh_130 :
    (nb057_alpha_dummy_130) ∉
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) :=
  by
  simpa only [nb057_alpha_dummy_130] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv)
      0

theorem nb057_fresh_131 :
    (nb057_alpha_dummy_131) ∉
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv) :=
  by
  simpa only [nb057_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv)
      1

theorem nb057_distinct_132 : (nb057_alpha_dummy_130) ≠ (nb057_alpha_dummy_131) := by
  simpa only [nb057_alpha_dummy_130, nb057_alpha_dummy_131] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_124))).fv ∪ ((Class.cv (nb057_alpha_dummy_125))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_133 :
    (nb057_alpha_dummy_166) ∉
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) :=
  by
  simpa only [nb057_alpha_dummy_166] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv)
      0

theorem nb057_fresh_134 :
    (nb057_alpha_dummy_167) ∉
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv) :=
  by
  simpa only [nb057_alpha_dummy_167] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv)
      1

theorem nb057_distinct_135 : (nb057_alpha_dummy_166) ≠ (nb057_alpha_dummy_167) := by
  simpa only [nb057_alpha_dummy_166, nb057_alpha_dummy_167] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_125))).fv ∪ ((Class.cv (nb057_alpha_dummy_124))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_136 (f : Var) :
    (nb057_alpha_dummy_132 f) ∉
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_132] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv)
      0

theorem nb057_fresh_137 (f : Var) :
    (nb057_alpha_dummy_133 f) ∉
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_127 f))).fv)
      1

theorem nb057_distinct_138 (f : Var) :
    (nb057_alpha_dummy_132 f) ≠ (nb057_alpha_dummy_133 f) := by
  simpa only [nb057_alpha_dummy_132, nb057_alpha_dummy_133] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_127 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_139 (f : Var) :
    (nb057_alpha_dummy_168 f) ∉
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_168] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv)
      0

theorem nb057_fresh_140 (f : Var) :
    (nb057_alpha_dummy_169 f) ∉
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_126 f))).fv)
      1

theorem nb057_distinct_141 (f : Var) :
    (nb057_alpha_dummy_168 f) ≠ (nb057_alpha_dummy_169 f) := by
  simpa only [nb057_alpha_dummy_168, nb057_alpha_dummy_169] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_126 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_142 :
    (nb057_alpha_dummy_138) ∉ (((Class.cv (nb057_alpha_dummy_131))).fv) := by
  simpa only [nb057_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_131))).fv) 0

theorem nb057_fresh_143 :
    (nb057_alpha_dummy_139) ∉ (((Class.cv (nb057_alpha_dummy_131))).fv) := by
  simpa only [nb057_alpha_dummy_139] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_131))).fv) 1

theorem nb057_distinct_144 : (nb057_alpha_dummy_138) ≠ (nb057_alpha_dummy_139) := by
  simpa only [nb057_alpha_dummy_138, nb057_alpha_dummy_139] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_145 (f : Var) :
    (nb057_alpha_dummy_140 f) ∉ (((Class.cv (nb057_alpha_dummy_133 f))).fv) := by
  simpa only [nb057_alpha_dummy_140] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_133 f))).fv) 0

theorem nb057_fresh_146 (f : Var) :
    (nb057_alpha_dummy_141 f) ∉ (((Class.cv (nb057_alpha_dummy_133 f))).fv) := by
  simpa only [nb057_alpha_dummy_141] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_133 f))).fv) 1

theorem nb057_distinct_147 (f : Var) :
    (nb057_alpha_dummy_140 f) ≠ (nb057_alpha_dummy_141 f) := by
  simpa only [nb057_alpha_dummy_140, nb057_alpha_dummy_141] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_148 :
    (nb057_alpha_dummy_144) ∉
      (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_144] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_149 :
    (nb057_alpha_dummy_145) ∉
      (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_145] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_150 :
    (nb057_alpha_dummy_146) ∉
      (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_146] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_151 : (nb057_alpha_dummy_144) ≠ (nb057_alpha_dummy_145) := by
  simpa only [nb057_alpha_dummy_144, nb057_alpha_dummy_145] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_152 : (nb057_alpha_dummy_144) ≠ (nb057_alpha_dummy_146) := by
  simpa only [nb057_alpha_dummy_144, nb057_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_153 : (nb057_alpha_dummy_145) ≠ (nb057_alpha_dummy_146) := by
  simpa only [nb057_alpha_dummy_145, nb057_alpha_dummy_146] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_154 (f : Var) :
    (nb057_alpha_dummy_147 f) ∉
      (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_147] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_155 (f : Var) :
    (nb057_alpha_dummy_148 f) ∉
      (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_148] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_156 (f : Var) :
    (nb057_alpha_dummy_149 f) ∉
      (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_149] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_157 (f : Var) :
    (nb057_alpha_dummy_147 f) ≠ (nb057_alpha_dummy_148 f) := by
  simpa only [nb057_alpha_dummy_147, nb057_alpha_dummy_148] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_158 (f : Var) :
    (nb057_alpha_dummy_147 f) ≠ (nb057_alpha_dummy_149 f) := by
  simpa only [nb057_alpha_dummy_147, nb057_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_159 (f : Var) :
    (nb057_alpha_dummy_148 f) ≠ (nb057_alpha_dummy_149 f) := by
  simpa only [nb057_alpha_dummy_148, nb057_alpha_dummy_149] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_160 :
    (nb057_alpha_dummy_156) ∉
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv) :=
  by
  simpa only [nb057_alpha_dummy_156] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_145))).fv)
      0

theorem nb057_fresh_161 :
    (nb057_alpha_dummy_152) ∉
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) :=
  by
  simpa only [nb057_alpha_dummy_152] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_145))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv)
      0

theorem nb057_fresh_162 :
    (nb057_alpha_dummy_158) ∉
      (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv) :=
  by
  simpa only [nb057_alpha_dummy_158] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_146))).fv ∪ ((Class.cv (nb057_alpha_dummy_146))).fv)
      0

theorem nb057_fresh_163 (f : Var) :
    (nb057_alpha_dummy_157 f) ∉
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_157] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_148 f))).fv)
      0

theorem nb057_fresh_164 (f : Var) :
    (nb057_alpha_dummy_153 f) ∉
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_153] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_148 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv)
      0

theorem nb057_fresh_165 (f : Var) :
    (nb057_alpha_dummy_159 f) ∉
      (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_159] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_149 f))).fv)
      0

theorem nb057_fresh_166 :
    (nb057_alpha_dummy_174) ∉ (((Class.cv (nb057_alpha_dummy_167))).fv) := by
  simpa only [nb057_alpha_dummy_174] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_167))).fv) 0

theorem nb057_fresh_167 :
    (nb057_alpha_dummy_175) ∉ (((Class.cv (nb057_alpha_dummy_167))).fv) := by
  simpa only [nb057_alpha_dummy_175] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_167))).fv) 1

theorem nb057_distinct_168 : (nb057_alpha_dummy_174) ≠ (nb057_alpha_dummy_175) := by
  simpa only [nb057_alpha_dummy_174, nb057_alpha_dummy_175] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_169 (f : Var) :
    (nb057_alpha_dummy_176 f) ∉ (((Class.cv (nb057_alpha_dummy_169 f))).fv) := by
  simpa only [nb057_alpha_dummy_176] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_169 f))).fv) 0

theorem nb057_fresh_170 (f : Var) :
    (nb057_alpha_dummy_177 f) ∉ (((Class.cv (nb057_alpha_dummy_169 f))).fv) := by
  simpa only [nb057_alpha_dummy_177] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_169 f))).fv) 1

theorem nb057_distinct_171 (f : Var) :
    (nb057_alpha_dummy_176 f) ≠ (nb057_alpha_dummy_177 f) := by
  simpa only [nb057_alpha_dummy_176, nb057_alpha_dummy_177] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (i := 0) (j := 1)
      (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part004`. -/


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

theorem nb057_fresh_172 :
    (nb057_alpha_dummy_180) ∉
      (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_180] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_173 :
    (nb057_alpha_dummy_181) ∉
      (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_181] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_174 :
    (nb057_alpha_dummy_182) ∉
      (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_182] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_175 : (nb057_alpha_dummy_180) ≠ (nb057_alpha_dummy_181) := by
  simpa only [nb057_alpha_dummy_180, nb057_alpha_dummy_181] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_176 : (nb057_alpha_dummy_180) ≠ (nb057_alpha_dummy_182) := by
  simpa only [nb057_alpha_dummy_180, nb057_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_177 : (nb057_alpha_dummy_181) ≠ (nb057_alpha_dummy_182) := by
  simpa only [nb057_alpha_dummy_181, nb057_alpha_dummy_182] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_178 (f : Var) :
    (nb057_alpha_dummy_183 f) ∉
      (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_183] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_179 (f : Var) :
    (nb057_alpha_dummy_184 f) ∉
      (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_184] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_180 (f : Var) :
    (nb057_alpha_dummy_185 f) ∉
      (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_185] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_181 (f : Var) :
    (nb057_alpha_dummy_183 f) ≠ (nb057_alpha_dummy_184 f) := by
  simpa only [nb057_alpha_dummy_183, nb057_alpha_dummy_184] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_182 (f : Var) :
    (nb057_alpha_dummy_183 f) ≠ (nb057_alpha_dummy_185 f) := by
  simpa only [nb057_alpha_dummy_183, nb057_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_183 (f : Var) :
    (nb057_alpha_dummy_184 f) ≠ (nb057_alpha_dummy_185 f) := by
  simpa only [nb057_alpha_dummy_184, nb057_alpha_dummy_185] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_184 :
    (nb057_alpha_dummy_192) ∉
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv) :=
  by
  simpa only [nb057_alpha_dummy_192] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_181))).fv)
      0

theorem nb057_fresh_185 :
    (nb057_alpha_dummy_188) ∉
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) :=
  by
  simpa only [nb057_alpha_dummy_188] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_181))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv)
      0

theorem nb057_fresh_186 :
    (nb057_alpha_dummy_194) ∉
      (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv) :=
  by
  simpa only [nb057_alpha_dummy_194] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_182))).fv ∪ ((Class.cv (nb057_alpha_dummy_182))).fv)
      0

theorem nb057_fresh_187 (f : Var) :
    (nb057_alpha_dummy_193 f) ∉
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_193] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_184 f))).fv)
      0

theorem nb057_fresh_188 (f : Var) :
    (nb057_alpha_dummy_189 f) ∉
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_189] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_184 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv)
      0

theorem nb057_fresh_189 (f : Var) :
    (nb057_alpha_dummy_195 f) ∉
      (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_195] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_185 f))).fv)
      0

theorem nb057_fresh_190 :
    (nb057_alpha_dummy_210) ∉ (((Class.cv (nb057_alpha_dummy_203))).fv) := by
  simpa only [nb057_alpha_dummy_210] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_203))).fv) 0

theorem nb057_fresh_191 :
    (nb057_alpha_dummy_211) ∉ (((Class.cv (nb057_alpha_dummy_203))).fv) := by
  simpa only [nb057_alpha_dummy_211] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_203))).fv) 1

theorem nb057_distinct_192 : (nb057_alpha_dummy_210) ≠ (nb057_alpha_dummy_211) := by
  simpa only [nb057_alpha_dummy_210, nb057_alpha_dummy_211] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_203))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_193 (f : Var) :
    (nb057_alpha_dummy_212 f) ∉ (((Class.cv (nb057_alpha_dummy_205 f))).fv) := by
  simpa only [nb057_alpha_dummy_212] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_205 f))).fv) 0

theorem nb057_fresh_194 (f : Var) :
    (nb057_alpha_dummy_213 f) ∉ (((Class.cv (nb057_alpha_dummy_205 f))).fv) := by
  simpa only [nb057_alpha_dummy_213] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_205 f))).fv) 1

theorem nb057_distinct_195 (f : Var) :
    (nb057_alpha_dummy_212 f) ≠ (nb057_alpha_dummy_213 f) := by
  simpa only [nb057_alpha_dummy_212, nb057_alpha_dummy_213] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_205 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_196 :
    (nb057_alpha_dummy_216) ∉
      (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_216] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_197 :
    (nb057_alpha_dummy_217) ∉
      (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_217] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_198 :
    (nb057_alpha_dummy_218) ∉
      (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_218] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_199 : (nb057_alpha_dummy_216) ≠ (nb057_alpha_dummy_217) := by
  simpa only [nb057_alpha_dummy_216, nb057_alpha_dummy_217] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_200 : (nb057_alpha_dummy_216) ≠ (nb057_alpha_dummy_218) := by
  simpa only [nb057_alpha_dummy_216, nb057_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_201 : (nb057_alpha_dummy_217) ≠ (nb057_alpha_dummy_218) := by
  simpa only [nb057_alpha_dummy_217, nb057_alpha_dummy_218] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_202 (f : Var) :
    (nb057_alpha_dummy_219 f) ∉
      (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_219] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_203 (f : Var) :
    (nb057_alpha_dummy_220 f) ∉
      (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_220] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_204 (f : Var) :
    (nb057_alpha_dummy_221 f) ∉
      (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_221] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_205 (f : Var) :
    (nb057_alpha_dummy_219 f) ≠ (nb057_alpha_dummy_220 f) := by
  simpa only [nb057_alpha_dummy_219, nb057_alpha_dummy_220] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_206 (f : Var) :
    (nb057_alpha_dummy_219 f) ≠ (nb057_alpha_dummy_221 f) := by
  simpa only [nb057_alpha_dummy_219, nb057_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_207 (f : Var) :
    (nb057_alpha_dummy_220 f) ≠ (nb057_alpha_dummy_221 f) := by
  simpa only [nb057_alpha_dummy_220, nb057_alpha_dummy_221] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_208 :
    (nb057_alpha_dummy_228) ∉
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv) :=
  by
  simpa only [nb057_alpha_dummy_228] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_217))).fv)
      0

theorem nb057_fresh_209 :
    (nb057_alpha_dummy_224) ∉
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) :=
  by
  simpa only [nb057_alpha_dummy_224] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_217))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv)
      0

theorem nb057_fresh_210 :
    (nb057_alpha_dummy_230) ∉
      (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv) :=
  by
  simpa only [nb057_alpha_dummy_230] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_218))).fv ∪ ((Class.cv (nb057_alpha_dummy_218))).fv)
      0

theorem nb057_fresh_211 (f : Var) :
    (nb057_alpha_dummy_229 f) ∉
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_229] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_220 f))).fv)
      0

theorem nb057_fresh_212 (f : Var) :
    (nb057_alpha_dummy_225 f) ∉
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_225] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_220 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv)
      0

theorem nb057_fresh_213 (f : Var) :
    (nb057_alpha_dummy_231 f) ∉
      (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_231] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_221 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_221 f))).fv)
      0

theorem nb057_fresh_214 :
    (nb057_alpha_dummy_242) ∉
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) :=
  by
  simpa only [nb057_alpha_dummy_242] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv)
      0

theorem nb057_fresh_215 :
    (nb057_alpha_dummy_243) ∉
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv) :=
  by
  simpa only [nb057_alpha_dummy_243] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv)
      1

theorem nb057_distinct_216 : (nb057_alpha_dummy_242) ≠ (nb057_alpha_dummy_243) := by
  simpa only [nb057_alpha_dummy_242, nb057_alpha_dummy_243] using
    (freshVar_injective
      (((Class.cv (nb057_alpha_dummy_239))).fv ∪ ((Class.cv (nb057_alpha_dummy_238))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb057_fresh_217 (f : Var) :
    (nb057_alpha_dummy_244 f) ∉
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_244] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv)
      0

theorem nb057_fresh_218 (f : Var) :
    (nb057_alpha_dummy_245 f) ∉
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_245] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_240 f))).fv)
      1

theorem nb057_distinct_219 (f : Var) :
    (nb057_alpha_dummy_244 f) ≠ (nb057_alpha_dummy_245 f) := by
  simpa only [nb057_alpha_dummy_244, nb057_alpha_dummy_245] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
        ((Class.cv (nb057_alpha_dummy_240 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_220 :
    (nb057_alpha_dummy_250) ∉ (((Class.cv (nb057_alpha_dummy_243))).fv) := by
  simpa only [nb057_alpha_dummy_250] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_243))).fv) 0

theorem nb057_fresh_221 :
    (nb057_alpha_dummy_251) ∉ (((Class.cv (nb057_alpha_dummy_243))).fv) := by
  simpa only [nb057_alpha_dummy_251] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_243))).fv) 1

theorem nb057_distinct_222 : (nb057_alpha_dummy_250) ≠ (nb057_alpha_dummy_251) := by
  simpa only [nb057_alpha_dummy_250, nb057_alpha_dummy_251] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_243))).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_223 (f : Var) :
    (nb057_alpha_dummy_252 f) ∉ (((Class.cv (nb057_alpha_dummy_245 f))).fv) := by
  simpa only [nb057_alpha_dummy_252] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_245 f))).fv) 0

theorem nb057_fresh_224 (f : Var) :
    (nb057_alpha_dummy_253 f) ∉ (((Class.cv (nb057_alpha_dummy_245 f))).fv) := by
  simpa only [nb057_alpha_dummy_253] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_245 f))).fv) 1

theorem nb057_distinct_225 (f : Var) :
    (nb057_alpha_dummy_252 f) ≠ (nb057_alpha_dummy_253 f) := by
  simpa only [nb057_alpha_dummy_252, nb057_alpha_dummy_253] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_245 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_226 :
    (nb057_alpha_dummy_256) ∉
      (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_256] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_227 :
    (nb057_alpha_dummy_257) ∉
      (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_257] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_228 :
    (nb057_alpha_dummy_258) ∉
      (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_258] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_229 : (nb057_alpha_dummy_256) ≠ (nb057_alpha_dummy_257) := by
  simpa only [nb057_alpha_dummy_256, nb057_alpha_dummy_257] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_230 : (nb057_alpha_dummy_256) ≠ (nb057_alpha_dummy_258) := by
  simpa only [nb057_alpha_dummy_256, nb057_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_231 : (nb057_alpha_dummy_257) ≠ (nb057_alpha_dummy_258) := by
  simpa only [nb057_alpha_dummy_257, nb057_alpha_dummy_258] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_232 (f : Var) :
    (nb057_alpha_dummy_259 f) ∉
      (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_259] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb057_fresh_233 (f : Var) :
    (nb057_alpha_dummy_260 f) ∉
      (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_260] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb057_fresh_234 (f : Var) :
    (nb057_alpha_dummy_261 f) ∉
      (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb057_alpha_dummy_261] using
    freshVar_not_mem (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb057_distinct_235 (f : Var) :
    (nb057_alpha_dummy_259 f) ≠ (nb057_alpha_dummy_260 f) := by
  simpa only [nb057_alpha_dummy_259, nb057_alpha_dummy_260] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb057_distinct_236 (f : Var) :
    (nb057_alpha_dummy_259 f) ≠ (nb057_alpha_dummy_261 f) := by
  simpa only [nb057_alpha_dummy_259, nb057_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb057_distinct_237 (f : Var) :
    (nb057_alpha_dummy_260 f) ≠ (nb057_alpha_dummy_261 f) := by
  simpa only [nb057_alpha_dummy_260, nb057_alpha_dummy_261] using
    (freshVar_injective (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb057_fresh_238 :
    (nb057_alpha_dummy_268) ∉
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv) :=
  by
  simpa only [nb057_alpha_dummy_268] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_257))).fv)
      0

theorem nb057_fresh_239 :
    (nb057_alpha_dummy_264) ∉
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) :=
  by
  simpa only [nb057_alpha_dummy_264] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_257))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv)
      0

theorem nb057_fresh_240 :
    (nb057_alpha_dummy_270) ∉
      (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv) :=
  by
  simpa only [nb057_alpha_dummy_270] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_258))).fv ∪ ((Class.cv (nb057_alpha_dummy_258))).fv)
      0

theorem nb057_fresh_241 (f : Var) :
    (nb057_alpha_dummy_269 f) ∉
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_269] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_260 f))).fv)
      0

theorem nb057_fresh_242 (f : Var) :
    (nb057_alpha_dummy_265 f) ∉
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_265] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_260 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv)
      0

theorem nb057_fresh_243 (f : Var) :
    (nb057_alpha_dummy_271 f) ∉
      (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_271] using
    freshVar_not_mem
      (((Class.cv (nb057_alpha_dummy_261 f))).fv ∪ ((Class.cv (nb057_alpha_dummy_261 f))).fv)
      0

theorem nb057_fresh_244 (f : Var) : (nb057_alpha_dummy_126 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057_alpha_dummy_126] using freshVar_not_mem (((Class.cv f)).fv) 0

theorem nb057_fresh_245 (f : Var) : (nb057_alpha_dummy_127 f) ∉ (((Class.cv f)).fv) := by
  simpa only [nb057_alpha_dummy_127] using freshVar_not_mem (((Class.cv f)).fv) 1

theorem nb057_distinct_246 (f : Var) :
    (nb057_alpha_dummy_126 f) ≠ (nb057_alpha_dummy_127 f) := by
  simpa only [nb057_alpha_dummy_126, nb057_alpha_dummy_127] using
    (freshVar_injective (((Class.cv f)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_247 (f : Var) (a : Var) :
    (nb057_alpha_dummy_006 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057_alpha_dummy_006] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 0

theorem nb057_fresh_248 (f : Var) (a : Var) :
    (nb057_alpha_dummy_007 f a) ∉ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb057_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((Class.cv a)).fv) 1

theorem nb057_distinct_249 (f : Var) (a : Var) :
    (nb057_alpha_dummy_006 f a) ≠ (nb057_alpha_dummy_007 f a) := by
  simpa only [nb057_alpha_dummy_006, nb057_alpha_dummy_007] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb057_fresh_250 (f : Var) :
    (nb057_alpha_dummy_047 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_047] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 0

theorem nb057_fresh_251 (f : Var) :
    (nb057_alpha_dummy_048 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_048] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 1

theorem nb057_fresh_252 (f : Var) :
    (nb057_alpha_dummy_049 f) ∉ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) := by
  simpa only [nb057_alpha_dummy_049] using
    freshVar_not_mem (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) 2

theorem nb057_distinct_253 (f : Var) :
    (nb057_alpha_dummy_047 f) ≠ (nb057_alpha_dummy_048 f) := by
  simpa only [nb057_alpha_dummy_047, nb057_alpha_dummy_048] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb057_distinct_254 (f : Var) :
    (nb057_alpha_dummy_047 f) ≠ (nb057_alpha_dummy_049 f) := by
  simpa only [nb057_alpha_dummy_047, nb057_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 0) (j :=
      2) (by decide))

theorem nb057_distinct_255 (f : Var) :
    (nb057_alpha_dummy_048 f) ≠ (nb057_alpha_dummy_049 f) := by
  simpa only [nb057_alpha_dummy_048, nb057_alpha_dummy_049] using
    (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (i := 1) (j :=
      2) (by decide))

theorem nb057_fresh_256 :
    (nb057_alpha_dummy_016) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_012))).fv) :=
  by
  simpa only [nb057_alpha_dummy_016] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_012)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_012)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_012))).fv)
      0

theorem nb057_fresh_257 (f : Var) (a : Var) :
    (nb057_alpha_dummy_017 f a) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_014 f a))).fv) :=
  by
  simpa only [nb057_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_014 f a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_014 f a)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_014 f a))).fv)
      0

theorem nb057_fresh_258 :
    (nb057_alpha_dummy_064) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_060))).fv) :=
  by
  simpa only [nb057_alpha_dummy_064] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_060))).fv)
      0

theorem nb057_fresh_259 (f : Var) :
    (nb057_alpha_dummy_065 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_062 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_065] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_062 f))).fv)
      0

theorem nb057_fresh_260 :
    (nb057_alpha_dummy_100) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_096))).fv) :=
  by
  simpa only [nb057_alpha_dummy_100] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_096))).fv)
      0

theorem nb057_fresh_261 (f : Var) :
    (nb057_alpha_dummy_101 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_098 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_101] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_098 f))).fv)
      0

theorem nb057_fresh_262 :
    (nb057_alpha_dummy_142) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_138))).fv) :=
  by
  simpa only [nb057_alpha_dummy_142] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_138))).fv)
      0

theorem nb057_fresh_263 (f : Var) :
    (nb057_alpha_dummy_143 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_140 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_143] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_140 f))).fv)
      0

theorem nb057_fresh_264 :
    (nb057_alpha_dummy_178) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_174))).fv) :=
  by
  simpa only [nb057_alpha_dummy_178] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_174))).fv)
      0

theorem nb057_fresh_265 (f : Var) :
    (nb057_alpha_dummy_179 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_176 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_179] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_176 f))).fv)
      0

theorem nb057_fresh_266 :
    (nb057_alpha_dummy_214) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_210))).fv) :=
  by
  simpa only [nb057_alpha_dummy_214] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_210))).fv)
      0

theorem nb057_fresh_267 (f : Var) :
    (nb057_alpha_dummy_215 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_212 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_215] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_212 f))).fv)
      0

theorem nb057_fresh_268 :
    (nb057_alpha_dummy_254) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_250))).fv) :=
  by
  simpa only [nb057_alpha_dummy_254] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_250))).fv)
      0

theorem nb057_fresh_269 (f : Var) :
    (nb057_alpha_dummy_255 f) ∉
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_252 f))).fv) :=
  by
  simpa only [nb057_alpha_dummy_255] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb057_alpha_dummy_252 f))).fv)
      0

theorem nb057_fresh_270 :
    (nb057_alpha_dummy_238) ∉
      (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb057_alpha_dummy_238] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv)
      0

theorem nb057_fresh_271 :
    (nb057_alpha_dummy_239) ∉
      (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb057_alpha_dummy_239] using
    freshVar_not_mem (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv)
      1

theorem nb057_distinct_272 : (nb057_alpha_dummy_238) ≠ (nb057_alpha_dummy_239) := by
  simpa only [nb057_alpha_dummy_238, nb057_alpha_dummy_239] using
    (freshVar_injective
      (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb057_fresh_273 (f : Var) :
    (nb057_alpha_dummy_240 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_240] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 0

theorem nb057_fresh_274 (f : Var) :
    (nb057_alpha_dummy_241 f) ∉ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) := by
  simpa only [nb057_alpha_dummy_241] using
    freshVar_not_mem (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) 1

theorem nb057_distinct_275 (f : Var) :
    (nb057_alpha_dummy_240 f) ≠ (nb057_alpha_dummy_241 f) := by
  simpa only [nb057_alpha_dummy_240, nb057_alpha_dummy_241] using
    (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (i := 0) (j := 1)
      (by decide))

theorem nb057_fresh_276 :
    (nb057_alpha_dummy_042) ∉
      (((syn_ccom (Class.cv (nb057_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb057_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccom (Class.cv (nb057_alpha_dummy_001))
            (syn_ccnv (Class.cv (nb057_alpha_dummy_001))))).fv ∪ ((syn_cid)).fv)
      0

theorem nb057_fresh_277 (f : Var) :
    (nb057_alpha_dummy_043 f) ∉
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  simpa only [nb057_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) 0

theorem nb057_fresh_278 :
    (nb057_alpha_dummy_008) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_005)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_004)
              (syn_wrex (nb057_alpha_dummy_005) (Class.cv (nb057_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_004))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_005)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_279 (f : Var) (a : Var) :
    (nb057_alpha_dummy_009 f a) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_006 f a)
              (syn_wrex (nb057_alpha_dummy_007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057_alpha_dummy_006 f a))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_280 :
    (nb057_alpha_dummy_056) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_053)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_281 (f : Var) :
    (nb057_alpha_dummy_057 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_282 :
    (nb057_alpha_dummy_092) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_092] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_044))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_089)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_283 (f : Var) :
    (nb057_alpha_dummy_093 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_093] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_047 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_284 :
    (nb057_alpha_dummy_134) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_134] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_131)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_285 (f : Var) :
    (nb057_alpha_dummy_135 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_135] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_286 :
    (nb057_alpha_dummy_170) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_170] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_167)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_287 (f : Var) :
    (nb057_alpha_dummy_171 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_171] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_288 :
    (nb057_alpha_dummy_206) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_206] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_203)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_289 (f : Var) :
    (nb057_alpha_dummy_207 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_207] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_290 :
    (nb057_alpha_dummy_246) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_246] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_239))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_243)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_291 (f : Var) :
    (nb057_alpha_dummy_247 f) ∉
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb057_alpha_dummy_247] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_241 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb057_fresh_292 :
    (nb057_alpha_dummy_028) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_019)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_020)))).fv)
      0

theorem nb057_fresh_293 (f : Var) (a : Var) :
    (nb057_alpha_dummy_029 f a) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_022 f a)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_023 f a)))).fv)
      0

theorem nb057_fresh_294 :
    (nb057_alpha_dummy_076) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_067)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_068)))).fv)
      0

theorem nb057_fresh_295 (f : Var) :
    (nb057_alpha_dummy_077 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_070 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_071 f)))).fv)
      0

theorem nb057_fresh_296 :
    (nb057_alpha_dummy_112) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_112] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_103)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_104)))).fv)
      0

theorem nb057_fresh_297 (f : Var) :
    (nb057_alpha_dummy_113 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_113] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_106 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_107 f)))).fv)
      0

theorem nb057_fresh_298 :
    (nb057_alpha_dummy_154) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_154] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_145)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_146)))).fv)
      0

theorem nb057_fresh_299 (f : Var) :
    (nb057_alpha_dummy_155 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_148 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_149 f)))).fv)
      0

theorem nb057_fresh_300 :
    (nb057_alpha_dummy_190) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_190] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_181)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_182)))).fv)
      0

theorem nb057_fresh_301 (f : Var) :
    (nb057_alpha_dummy_191 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_191] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_184 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_185 f)))).fv)
      0

theorem nb057_fresh_302 :
    (nb057_alpha_dummy_226) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_226] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_217)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_218)))).fv)
      0

theorem nb057_fresh_303 (f : Var) :
    (nb057_alpha_dummy_227 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_227] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_220 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_221 f)))).fv)
      0

theorem nb057_fresh_304 :
    (nb057_alpha_dummy_266) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_266] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_257)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_258)))).fv)
      0

theorem nb057_fresh_305 (f : Var) :
    (nb057_alpha_dummy_267 f) ∉
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_267] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb057_alpha_dummy_260 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb057_alpha_dummy_261 f)))).fv)
      0

theorem nb057_fresh_306 :
    (nb057_alpha_dummy_036) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_036] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_005))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_307 (f : Var) (a : Var) :
    (nb057_alpha_dummy_037 f a) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_007 f a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_308 :
    (nb057_alpha_dummy_084) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_084] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_053))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_309 (f : Var) :
    (nb057_alpha_dummy_085 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_055 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_310 :
    (nb057_alpha_dummy_120) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_120] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_089))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_311 (f : Var) :
    (nb057_alpha_dummy_121 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_121] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_091 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_312 :
    (nb057_alpha_dummy_162) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_162] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_131))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_313 (f : Var) :
    (nb057_alpha_dummy_163 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_163] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_133 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_314 :
    (nb057_alpha_dummy_198) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_198] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_167))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_315 (f : Var) :
    (nb057_alpha_dummy_199 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_199] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_169 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_316 :
    (nb057_alpha_dummy_234) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_234] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_203))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_317 (f : Var) :
    (nb057_alpha_dummy_235 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_235] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_205 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_318 :
    (nb057_alpha_dummy_274) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_274] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_243))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_319 (f : Var) :
    (nb057_alpha_dummy_275 f) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_275] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb057_alpha_dummy_245 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb057_fresh_320 :
    (nb057_alpha_dummy_024) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_019))
            (Class.cv (nb057_alpha_dummy_020)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_024] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_019)) (Class.cv (nb057_alpha_dummy_020)))).fv)
      0

theorem nb057_fresh_321 (f : Var) (a : Var) :
    (nb057_alpha_dummy_025 f a) ∉
      (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv) :=
  by
  simpa only [nb057_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv ∪
        ((syn_cnin (Class.cv (nb057_alpha_dummy_022 f a))
            (Class.cv (nb057_alpha_dummy_023 f a)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
