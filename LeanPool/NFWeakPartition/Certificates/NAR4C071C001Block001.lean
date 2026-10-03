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

/-! Certificates from `NAR4C071C001Part001`. -/


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
noncomputable def nb071_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb071_alpha_dummy_001 : Var :=
  (freshVar (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
      ((syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_002 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_003 : Var :=
  (freshVar
    (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c))
          (Wff.classEq (Class.cv (nb071_alpha_dummy_001))
            (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_004 (x : Var) : Var :=
  (freshVar (({ x } : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
          (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x))
            (syn_ctc (syn_cuni (Class.cv x)))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_005 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_006 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_007 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_008 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_009 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_011 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_005)
          (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
              (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪
      ((Class.cab (nb071_alpha_dummy_005)
          (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
              (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_012 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_007 x)
          (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪
      ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
            (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
              (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_013 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_006))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_014 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_006))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_015 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_008 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_016 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_008 x))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_017 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_013)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb071_alpha_dummy_013)) (syn_c1c))).fv ∪
      ((Class.cv (nb071_alpha_dummy_013))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_018 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb071_alpha_dummy_015 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb071_alpha_dummy_015 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_019 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_020 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_021 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb071_alpha_dummy_022 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_024 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb071_alpha_dummy_025 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_020))
          (Class.cv (nb071_alpha_dummy_021)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_026 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
          (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x)) (Class.cv (nb071_alpha_dummy_024 x)))).fv)
    0)

@[expose]
noncomputable def nb071_alpha_dummy_027 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_028 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_029 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪
      ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_030 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_031 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_032 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_023 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_033 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_024 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_024 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_035 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_005)
          (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005)
          (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_036 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_007 x)
          (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x)
          (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_037 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_006))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_038 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_039 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv ∪
      ((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_040 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv ∪
      ((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_041 : Var :=
  (freshVar (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_042 : Var :=
  (freshVar (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_044 (x : Var) : Var :=
  (freshVar (((syn_cuni (Class.cv x))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_045 : Var :=
  (freshVar (({(nb071_alpha_dummy_041)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
          (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
              (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_046 (x : Var) : Var :=
  (freshVar (({(nb071_alpha_dummy_043 x)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
          (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
              (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_047 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
            (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
              (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                  (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
          (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_048 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
            (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
              (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                  (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
          (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_049 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq
          (Class.cab (nb071_alpha_dummy_043 x)
            (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
              (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                  (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
          (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_050 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq
          (Class.cab (nb071_alpha_dummy_043 x)
            (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
              (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                  (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
          (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_051 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_052 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_000))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_053 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_054 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_055 : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_056 : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_057 (x : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_058 (x : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_059 : Var :=
  (freshVar (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_060 (x : Var) : Var :=
  (freshVar (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_061 : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_062 (x : Var) : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_063 : Var :=
  (freshVar (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_064 (x : Var) : Var :=
  (freshVar (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_065 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_042))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_066 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_044 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_067 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_065))
          (Class.cv (nb071_alpha_dummy_042)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_068 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
          (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x)) (Class.cv (nb071_alpha_dummy_044 x)))).fv)
    0)

@[expose]
noncomputable def nb071_alpha_dummy_069 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_070 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_044 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_072 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_073 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_057 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_074 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_057 x))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_075 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_076 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_077 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_071)
          (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
              (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪
      ((Class.cab (nb071_alpha_dummy_071)
          (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
              (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_078 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_073 x)
          (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
              (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪
      ((Class.cab (nb071_alpha_dummy_073 x)
          (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
              (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_079 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_072))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_080 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_072))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_081 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_074 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_082 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_074 x))).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_083 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪
      ((Class.cv (nb071_alpha_dummy_079))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_084 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb071_alpha_dummy_081 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_085 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_086 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_087 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb071_alpha_dummy_088 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_089 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb071_alpha_dummy_090 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb071_alpha_dummy_091 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_086))
          (Class.cv (nb071_alpha_dummy_087)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_092 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
          (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪
      ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x)) (Class.cv (nb071_alpha_dummy_090 x)))).fv)
    0)

@[expose]
noncomputable def nb071_alpha_dummy_093 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_094 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_090 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_095 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪
      ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_096 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_097 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_098 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_089 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_099 : Var :=
  (freshVar
    (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_100 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪
      ((Class.cv (nb071_alpha_dummy_090 x))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_101 : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_071)
          (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071)
          (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_102 (x : Var) : Var :=
  (freshVar (((Class.cab (nb071_alpha_dummy_073 x)
          (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x)
          (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
              (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_103 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_104 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_105 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪
      ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_106 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪
      ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_107 : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_045))).fv) 0)

@[expose]
noncomputable def nb071_alpha_dummy_108 (x : Var) : Var :=
  (freshVar (((Class.cv (nb071_alpha_dummy_046 x))).fv) 0)

theorem nb071_fresh_000 :
    (nb071_alpha_dummy_011) ∉
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv)
      0

theorem nb071_fresh_001 :
    (nb071_alpha_dummy_035) ∉
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb071_fresh_002 (x : Var) :
    (nb071_alpha_dummy_036 x) ∉
      (((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb071_fresh_003 (x : Var) :
    (nb071_alpha_dummy_012 x) ∉
      (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv)
      0

theorem nb071_fresh_004 :
    (nb071_alpha_dummy_047) ∉
      (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv)
      0

theorem nb071_fresh_005 :
    (nb071_alpha_dummy_048) ∉
      (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv)
      1

theorem nb071_distinct_006 : (nb071_alpha_dummy_047) ≠ (nb071_alpha_dummy_048) := by
  simpa only [nb071_alpha_dummy_047, nb071_alpha_dummy_048] using
    (freshVar_injective (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq
            (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_007 (x : Var) :
    (nb071_alpha_dummy_049 x) ∉
      (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv)
      0

theorem nb071_fresh_008 (x : Var) :
    (nb071_alpha_dummy_050 x) ∉
      (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv)
      1

theorem nb071_distinct_009 (x : Var) :
    (nb071_alpha_dummy_049 x) ≠ (nb071_alpha_dummy_050 x) := by
  simpa only [nb071_alpha_dummy_049, nb071_alpha_dummy_050] using
    (freshVar_injective (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq
            (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_010 :
    (nb071_alpha_dummy_101) ∉
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb071_fresh_011 :
    (nb071_alpha_dummy_077) ∉
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_077] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv)
      0

theorem nb071_fresh_012 (x : Var) :
    (nb071_alpha_dummy_102 x) ∉
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb071_fresh_013 (x : Var) :
    (nb071_alpha_dummy_078 x) ∉
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv)
      0

theorem nb071_fresh_014 :
    (nb071_alpha_dummy_051) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv) := by
  simpa only [nb071_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv) 0

theorem nb071_fresh_015 :
    (nb071_alpha_dummy_052) ∉ (((Class.cv (nb071_alpha_dummy_000))).fv) := by
  simpa only [nb071_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_000))).fv) 1

theorem nb071_distinct_016 : (nb071_alpha_dummy_051) ≠ (nb071_alpha_dummy_052) := by
  simpa only [nb071_alpha_dummy_051, nb071_alpha_dummy_052] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_017 :
    (nb071_alpha_dummy_005) ∉
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) :=
  by
  simpa only [nb071_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv)
      0

theorem nb071_fresh_018 :
    (nb071_alpha_dummy_006) ∉
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) :=
  by
  simpa only [nb071_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv)
      1

theorem nb071_distinct_019 : (nb071_alpha_dummy_005) ≠ (nb071_alpha_dummy_006) := by
  simpa only [nb071_alpha_dummy_005, nb071_alpha_dummy_006] using
    (freshVar_injective
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_020 :
    (nb071_alpha_dummy_013) ∉ (((Class.cv (nb071_alpha_dummy_006))).fv) := by
  simpa only [nb071_alpha_dummy_013] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_006))).fv) 0

theorem nb071_fresh_021 :
    (nb071_alpha_dummy_014) ∉ (((Class.cv (nb071_alpha_dummy_006))).fv) := by
  simpa only [nb071_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_006))).fv) 1

theorem nb071_distinct_022 : (nb071_alpha_dummy_013) ≠ (nb071_alpha_dummy_014) := by
  simpa only [nb071_alpha_dummy_013, nb071_alpha_dummy_014] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_006))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_023 (x : Var) :
    (nb071_alpha_dummy_015 x) ∉ (((Class.cv (nb071_alpha_dummy_008 x))).fv) := by
  simpa only [nb071_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_008 x))).fv) 0

theorem nb071_fresh_024 (x : Var) :
    (nb071_alpha_dummy_016 x) ∉ (((Class.cv (nb071_alpha_dummy_008 x))).fv) := by
  simpa only [nb071_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_008 x))).fv) 1

theorem nb071_distinct_025 (x : Var) :
    (nb071_alpha_dummy_015 x) ≠ (nb071_alpha_dummy_016 x) := by
  simpa only [nb071_alpha_dummy_015, nb071_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_008 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb071_fresh_026 :
    (nb071_alpha_dummy_019) ∉
      (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_027 :
    (nb071_alpha_dummy_020) ∉
      (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_028 :
    (nb071_alpha_dummy_021) ∉
      (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_029 : (nb071_alpha_dummy_019) ≠ (nb071_alpha_dummy_020) := by
  simpa only [nb071_alpha_dummy_019, nb071_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_030 : (nb071_alpha_dummy_019) ≠ (nb071_alpha_dummy_021) := by
  simpa only [nb071_alpha_dummy_019, nb071_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_031 : (nb071_alpha_dummy_020) ≠ (nb071_alpha_dummy_021) := by
  simpa only [nb071_alpha_dummy_020, nb071_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_032 (x : Var) :
    (nb071_alpha_dummy_022 x) ∉
      (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_033 (x : Var) :
    (nb071_alpha_dummy_023 x) ∉
      (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_034 (x : Var) :
    (nb071_alpha_dummy_024 x) ∉
      (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_035 (x : Var) :
    (nb071_alpha_dummy_022 x) ≠ (nb071_alpha_dummy_023 x) := by
  simpa only [nb071_alpha_dummy_022, nb071_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_036 (x : Var) :
    (nb071_alpha_dummy_022 x) ≠ (nb071_alpha_dummy_024 x) := by
  simpa only [nb071_alpha_dummy_022, nb071_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_037 (x : Var) :
    (nb071_alpha_dummy_023 x) ≠ (nb071_alpha_dummy_024 x) := by
  simpa only [nb071_alpha_dummy_023, nb071_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_038 :
    (nb071_alpha_dummy_031) ∉
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) :=
  by
  simpa only [nb071_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv)
      0

theorem nb071_fresh_039 :
    (nb071_alpha_dummy_027) ∉
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) :=
  by
  simpa only [nb071_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv)
      0

theorem nb071_fresh_040 :
    (nb071_alpha_dummy_033) ∉
      (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) :=
  by
  simpa only [nb071_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C071C001Part002`. -/


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

theorem nb071_fresh_041 (x : Var) :
    (nb071_alpha_dummy_032 x) ∉
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_023 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_023 x))).fv)
      0

theorem nb071_fresh_042 (x : Var) :
    (nb071_alpha_dummy_028 x) ∉
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv)
      0

theorem nb071_fresh_043 (x : Var) :
    (nb071_alpha_dummy_034 x) ∉
      (((Class.cv (nb071_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv)
      0

theorem nb071_fresh_044 :
    (nb071_alpha_dummy_065) ∉ (((Class.cv (nb071_alpha_dummy_042))).fv) := by
  simpa only [nb071_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_042))).fv) 0

theorem nb071_fresh_045 (x : Var) :
    (nb071_alpha_dummy_066 x) ∉ (((Class.cv (nb071_alpha_dummy_044 x))).fv) := by
  simpa only [nb071_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_044 x))).fv) 0

theorem nb071_fresh_046 :
    (nb071_alpha_dummy_107) ∉ (((Class.cv (nb071_alpha_dummy_045))).fv) := by
  simpa only [nb071_alpha_dummy_107] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_045))).fv) 0

theorem nb071_fresh_047 (x : Var) :
    (nb071_alpha_dummy_108 x) ∉ (((Class.cv (nb071_alpha_dummy_046 x))).fv) := by
  simpa only [nb071_alpha_dummy_108] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_046 x))).fv) 0

theorem nb071_fresh_048 :
    (nb071_alpha_dummy_071) ∉
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) :=
  by
  simpa only [nb071_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv)
      0

theorem nb071_fresh_049 :
    (nb071_alpha_dummy_072) ∉
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) :=
  by
  simpa only [nb071_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv)
      1

theorem nb071_distinct_050 : (nb071_alpha_dummy_071) ≠ (nb071_alpha_dummy_072) := by
  simpa only [nb071_alpha_dummy_071, nb071_alpha_dummy_072] using
    (freshVar_injective
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_051 (x : Var) :
    (nb071_alpha_dummy_073 x) ∉
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv)
      0

theorem nb071_fresh_052 (x : Var) :
    (nb071_alpha_dummy_074 x) ∉
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv)
      1

theorem nb071_distinct_053 (x : Var) :
    (nb071_alpha_dummy_073 x) ≠ (nb071_alpha_dummy_074 x) := by
  simpa only [nb071_alpha_dummy_073, nb071_alpha_dummy_074] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪
        ((Class.cv (nb071_alpha_dummy_057 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_054 :
    (nb071_alpha_dummy_069) ∉
      (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) :=
  by
  simpa only [nb071_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv)
      0

theorem nb071_fresh_055 (x : Var) :
    (nb071_alpha_dummy_070 x) ∉
      (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv)
      0

theorem nb071_fresh_056 :
    (nb071_alpha_dummy_079) ∉ (((Class.cv (nb071_alpha_dummy_072))).fv) := by
  simpa only [nb071_alpha_dummy_079] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_072))).fv) 0

theorem nb071_fresh_057 :
    (nb071_alpha_dummy_080) ∉ (((Class.cv (nb071_alpha_dummy_072))).fv) := by
  simpa only [nb071_alpha_dummy_080] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_072))).fv) 1

theorem nb071_distinct_058 : (nb071_alpha_dummy_079) ≠ (nb071_alpha_dummy_080) := by
  simpa only [nb071_alpha_dummy_079, nb071_alpha_dummy_080] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_072))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_059 (x : Var) :
    (nb071_alpha_dummy_081 x) ∉ (((Class.cv (nb071_alpha_dummy_074 x))).fv) := by
  simpa only [nb071_alpha_dummy_081] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_074 x))).fv) 0

theorem nb071_fresh_060 (x : Var) :
    (nb071_alpha_dummy_082 x) ∉ (((Class.cv (nb071_alpha_dummy_074 x))).fv) := by
  simpa only [nb071_alpha_dummy_082] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_074 x))).fv) 1

theorem nb071_distinct_061 (x : Var) :
    (nb071_alpha_dummy_081 x) ≠ (nb071_alpha_dummy_082 x) := by
  simpa only [nb071_alpha_dummy_081, nb071_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_074 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb071_fresh_062 :
    (nb071_alpha_dummy_085) ∉
      (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_085] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_063 :
    (nb071_alpha_dummy_086) ∉
      (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_086] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_064 :
    (nb071_alpha_dummy_087) ∉
      (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_087] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_065 : (nb071_alpha_dummy_085) ≠ (nb071_alpha_dummy_086) := by
  simpa only [nb071_alpha_dummy_085, nb071_alpha_dummy_086] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_066 : (nb071_alpha_dummy_085) ≠ (nb071_alpha_dummy_087) := by
  simpa only [nb071_alpha_dummy_085, nb071_alpha_dummy_087] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_067 : (nb071_alpha_dummy_086) ≠ (nb071_alpha_dummy_087) := by
  simpa only [nb071_alpha_dummy_086, nb071_alpha_dummy_087] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_068 (x : Var) :
    (nb071_alpha_dummy_088 x) ∉
      (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_088] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_069 (x : Var) :
    (nb071_alpha_dummy_089 x) ∉
      (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb071_fresh_070 (x : Var) :
    (nb071_alpha_dummy_090 x) ∉
      (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb071_distinct_071 (x : Var) :
    (nb071_alpha_dummy_088 x) ≠ (nb071_alpha_dummy_089 x) := by
  simpa only [nb071_alpha_dummy_088, nb071_alpha_dummy_089] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb071_distinct_072 (x : Var) :
    (nb071_alpha_dummy_088 x) ≠ (nb071_alpha_dummy_090 x) := by
  simpa only [nb071_alpha_dummy_088, nb071_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb071_distinct_073 (x : Var) :
    (nb071_alpha_dummy_089 x) ≠ (nb071_alpha_dummy_090 x) := by
  simpa only [nb071_alpha_dummy_089, nb071_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb071_fresh_074 :
    (nb071_alpha_dummy_097) ∉
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv) :=
  by
  simpa only [nb071_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv)
      0

theorem nb071_fresh_075 :
    (nb071_alpha_dummy_093) ∉
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) :=
  by
  simpa only [nb071_alpha_dummy_093] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv)
      0

theorem nb071_fresh_076 :
    (nb071_alpha_dummy_099) ∉
      (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) :=
  by
  simpa only [nb071_alpha_dummy_099] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv)
      0

theorem nb071_fresh_077 (x : Var) :
    (nb071_alpha_dummy_098 x) ∉
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_089 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_089 x))).fv)
      0

theorem nb071_fresh_078 (x : Var) :
    (nb071_alpha_dummy_094 x) ∉
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_094] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv)
      0

theorem nb071_fresh_079 (x : Var) :
    (nb071_alpha_dummy_100 x) ∉
      (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_100] using
    freshVar_not_mem
      (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv)
      0

theorem nb071_fresh_080 (x : Var) : (nb071_alpha_dummy_053 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb071_alpha_dummy_053] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb071_fresh_081 (x : Var) : (nb071_alpha_dummy_054 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb071_alpha_dummy_054] using freshVar_not_mem (((Class.cv x)).fv) 1

theorem nb071_distinct_082 (x : Var) :
    (nb071_alpha_dummy_053 x) ≠ (nb071_alpha_dummy_054 x) := by
  simpa only [nb071_alpha_dummy_053, nb071_alpha_dummy_054] using
    (freshVar_injective (((Class.cv x)).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_083 (x : Var) :
    (nb071_alpha_dummy_007 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_007] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 0

theorem nb071_fresh_084 (x : Var) :
    (nb071_alpha_dummy_008 x) ∉
      (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) 1

theorem nb071_distinct_085 (x : Var) :
    (nb071_alpha_dummy_007 x) ≠ (nb071_alpha_dummy_008 x) := by
  simpa only [nb071_alpha_dummy_007, nb071_alpha_dummy_008] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_086 :
    (nb071_alpha_dummy_017) ∉
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_013))).fv) :=
  by
  simpa only [nb071_alpha_dummy_017] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_013))).fv)
      0

theorem nb071_fresh_087 (x : Var) :
    (nb071_alpha_dummy_018 x) ∉
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_015 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_015 x))).fv)
      0

theorem nb071_fresh_088 :
    (nb071_alpha_dummy_083) ∉
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_079))).fv) :=
  by
  simpa only [nb071_alpha_dummy_083] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_079))).fv)
      0

theorem nb071_fresh_089 (x : Var) :
    (nb071_alpha_dummy_084 x) ∉
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_081 x))).fv) :=
  by
  simpa only [nb071_alpha_dummy_084] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_081 x))).fv)
      0

theorem nb071_fresh_090 :
    (nb071_alpha_dummy_009) ∉
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb071_fresh_091 (x : Var) :
    (nb071_alpha_dummy_010 x) ∉
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb071_fresh_092 :
    (nb071_alpha_dummy_075) ∉
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb071_fresh_093 (x : Var) :
    (nb071_alpha_dummy_076 x) ∉
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb071_fresh_094 :
    (nb071_alpha_dummy_029) ∉
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv)
      0

theorem nb071_fresh_095 (x : Var) :
    (nb071_alpha_dummy_030 x) ∉
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv)
      0

theorem nb071_fresh_096 :
    (nb071_alpha_dummy_095) ∉
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_095] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv)
      0

theorem nb071_fresh_097 (x : Var) :
    (nb071_alpha_dummy_096 x) ∉
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_096] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv)
      0

theorem nb071_fresh_098 :
    (nb071_alpha_dummy_037) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb071_fresh_099 (x : Var) :
    (nb071_alpha_dummy_038 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb071_fresh_100 :
    (nb071_alpha_dummy_103) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_103] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb071_fresh_101 (x : Var) :
    (nb071_alpha_dummy_104 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_104] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb071_fresh_102 :
    (nb071_alpha_dummy_055) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_055] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 0

theorem nb071_fresh_103 :
    (nb071_alpha_dummy_056) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) 1

theorem nb071_distinct_104 : (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_056) := by
  simpa only [nb071_alpha_dummy_055, nb071_alpha_dummy_056] using
    (freshVar_injective
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_105 (x : Var) :
    (nb071_alpha_dummy_057 x) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 0

theorem nb071_fresh_106 (x : Var) :
    (nb071_alpha_dummy_058 x) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) 1

theorem nb071_distinct_107 (x : Var) :
    (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_058 x) := by
  simpa only [nb071_alpha_dummy_057, nb071_alpha_dummy_058] using
    (freshVar_injective
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb071_fresh_108 :
    (nb071_alpha_dummy_025) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_020))
            (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv)
      0

theorem nb071_fresh_109 (x : Var) :
    (nb071_alpha_dummy_026 x) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv)
      0

theorem nb071_fresh_110 :
    (nb071_alpha_dummy_067) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_065))
            (Class.cv (nb071_alpha_dummy_042)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv)
      0

theorem nb071_fresh_111 (x : Var) :
    (nb071_alpha_dummy_068 x) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_068] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv)
      0

theorem nb071_fresh_112 :
    (nb071_alpha_dummy_091) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_086))
            (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_091] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv)
      0

theorem nb071_fresh_113 (x : Var) :
    (nb071_alpha_dummy_092 x) ∉
      (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_092] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv)
      0

theorem nb071_fresh_114 :
    (nb071_alpha_dummy_061) ∉
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv) :=
  by
  simpa only [nb071_alpha_dummy_061] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv)
      0

theorem nb071_fresh_115 (x : Var) :
    (nb071_alpha_dummy_062 x) ∉
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv) :=
  by
  simpa only [nb071_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv)
      0

theorem nb071_fresh_116 :
    (nb071_alpha_dummy_039) ∉
      (((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv)
      0

theorem nb071_fresh_117 (x : Var) :
    (nb071_alpha_dummy_040 x) ∉
      (((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv)
      0

theorem nb071_fresh_118 :
    (nb071_alpha_dummy_105) ∉
      (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv)
      0

theorem nb071_fresh_119 (x : Var) :
    (nb071_alpha_dummy_106 x) ∉
      (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_106] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv)
      0

theorem nb071_fresh_120 :
    (nb071_alpha_dummy_063) ∉
      (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_063] using
    freshVar_not_mem (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv)
      0

theorem nb071_fresh_121 (x : Var) :
    (nb071_alpha_dummy_064 x) ∉
      (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb071_alpha_dummy_064] using
    freshVar_not_mem
      (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) 0

theorem nb071_fresh_122 :
    (nb071_alpha_dummy_059) ∉ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) := by
  simpa only [nb071_alpha_dummy_059] using
    freshVar_not_mem (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) 0

theorem nb071_fresh_123 (x : Var) :
    (nb071_alpha_dummy_060 x) ∉ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_060] using
    freshVar_not_mem (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) 0

theorem nb071_fresh_124 :
    (nb071_alpha_dummy_041) ∉ (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) := by
  simpa only [nb071_alpha_dummy_041] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 0

theorem nb071_fresh_125 :
    (nb071_alpha_dummy_042) ∉ (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) := by
  simpa only [nb071_alpha_dummy_042] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) 1

theorem nb071_distinct_126 : (nb071_alpha_dummy_041) ≠ (nb071_alpha_dummy_042) := by
  simpa only [nb071_alpha_dummy_041, nb071_alpha_dummy_042] using
    (freshVar_injective (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb071_fresh_127 (x : Var) :
    (nb071_alpha_dummy_043 x) ∉ (((syn_cuni (Class.cv x))).fv) := by
  simpa only [nb071_alpha_dummy_043] using
    freshVar_not_mem (((syn_cuni (Class.cv x))).fv) 0

theorem nb071_fresh_128 (x : Var) :
    (nb071_alpha_dummy_044 x) ∉ (((syn_cuni (Class.cv x))).fv) := by
  simpa only [nb071_alpha_dummy_044] using
    freshVar_not_mem (((syn_cuni (Class.cv x))).fv) 1

theorem nb071_distinct_129 (x : Var) :
    (nb071_alpha_dummy_043 x) ≠ (nb071_alpha_dummy_044 x) := by
  simpa only [nb071_alpha_dummy_043, nb071_alpha_dummy_044] using
    (freshVar_injective (((syn_cuni (Class.cv x))).fv) (i := 0) (j := 1) (by decide))

theorem nb071_fresh_130 :
    (nb071_alpha_dummy_001) ∉
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))).fv)
      0

theorem nb071_fresh_131 :
    (nb071_alpha_dummy_003) ∉
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_001))
              (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_001))
              (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv)
      0

theorem nb071_fresh_132 :
    (nb071_alpha_dummy_045) ∉
      (({(nb071_alpha_dummy_041)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_045] using
    freshVar_not_mem
      (({(nb071_alpha_dummy_041)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))).fv)
      0

theorem nb071_fresh_133 (x : Var) :
    (nb071_alpha_dummy_046 x) ∉
      (({(nb071_alpha_dummy_043 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_046] using
    freshVar_not_mem
      (({(nb071_alpha_dummy_043 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))).fv)
      0

theorem nb071_fresh_134 (x : Var) :
    (nb071_alpha_dummy_002 x) ∉
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv x)))).fv) :=
  by
  simpa only [nb071_alpha_dummy_002] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv x)))).fv) 0

theorem nb071_fresh_135 (x : Var) :
    (nb071_alpha_dummy_004 x) ∉
      (({ x } : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x))
              (syn_ctc (syn_cuni (Class.cv x)))))).fv) :=
  by
  simpa only [nb071_alpha_dummy_004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x))
              (syn_ctc (syn_cuni (Class.cv x)))))).fv)
      0

theorem nb071_fresh_136 : (nb071_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb071_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb071_support_mem_0000 :
    (nb071_alpha_dummy_000) ∈
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_001))
              (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0001 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x))
              (syn_ctc (syn_cuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0002 :
    (nb071_alpha_dummy_001) ∈
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ({(nb071_alpha_dummy_001)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_000)) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_001))
              (syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0003 (x : Var) :
    (nb071_alpha_dummy_002 x) ∈
      (({ x } : Finset Var) ∪ ({(nb071_alpha_dummy_002 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv x) (syn_c1c))
            (Wff.classEq (Class.cv (nb071_alpha_dummy_002 x))
              (syn_ctc (syn_cuni (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0004 :
    (nb071_alpha_dummy_000) ∈
      (({(nb071_alpha_dummy_000)} : Finset Var) ∪ ((syn_c1c)).fv ∪
        ((syn_ctc (syn_cuni (Class.cv (nb071_alpha_dummy_000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0005 (x : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((syn_c1c)).fv ∪ ((syn_ctc (syn_cuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0006 :
    (nb071_alpha_dummy_000) ∈
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0007 :
    (nb071_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_005) from (by
          unfold nb071_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_006) from (by
            unfold nb071_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0008 (x : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0009 (x : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071_alpha_dummy_007 x) from (by
          unfold nb071_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071_alpha_dummy_008 x) from (by
            unfold nb071_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0010 :
    (nb071_alpha_dummy_000) ∈
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cphi (Class.cv (nb071_alpha_dummy_006))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_005) from (by
          unfold nb071_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_006) from (by
            unfold nb071_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0006) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0011 (x : Var) :
    x ∈
      (((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_007 x) (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071_alpha_dummy_007 x) from (by
          unfold nb071_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071_alpha_dummy_008 x) from (by
            unfold nb071_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0008 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0012 :
    (nb071_alpha_dummy_006) ∈ (((Class.cv (nb071_alpha_dummy_006))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0013 (x : Var) :
    (nb071_alpha_dummy_008 x) ∈ (((Class.cv (nb071_alpha_dummy_008 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0014 :
    (nb071_alpha_dummy_013) ∈
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_013)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_013)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_013))).fv) :=
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

theorem nb071_support_mem_0015 (x : Var) :
    (nb071_alpha_dummy_015 x) ∈
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_015 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_015 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_015 x))).fv) :=
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

theorem nb071_support_mem_0016 :
    (nb071_alpha_dummy_013) ∈
      (((Class.cv (nb071_alpha_dummy_013))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0017 (x : Var) :
    (nb071_alpha_dummy_015 x) ∈
      (((Class.cv (nb071_alpha_dummy_015 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0018 :
    (nb071_alpha_dummy_020) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_020))
            (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0019 (x : Var) :
    (nb071_alpha_dummy_023 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0020 :
    (nb071_alpha_dummy_020) ∈
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0021 (x : Var) :
    (nb071_alpha_dummy_023 x) ∈
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0022 :
    (nb071_alpha_dummy_021) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_020)) (Class.cv (nb071_alpha_dummy_021)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_020))
            (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0023 (x : Var) :
    (nb071_alpha_dummy_024 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_023 x))
            (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0024 :
    (nb071_alpha_dummy_021) ∈
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0025 (x : Var) :
    (nb071_alpha_dummy_024 x) ∈
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0026 :
    (nb071_alpha_dummy_020) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0027 (x : Var) :
    (nb071_alpha_dummy_023 x) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0028 :
    (nb071_alpha_dummy_020) ∈
      (((Class.cv (nb071_alpha_dummy_020))).fv ∪ ((Class.cv (nb071_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0029 (x : Var) :
    (nb071_alpha_dummy_023 x) ∈
      (((Class.cv (nb071_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0030 :
    (nb071_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0031 (x : Var) :
    (nb071_alpha_dummy_024 x) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0032 :
    (nb071_alpha_dummy_021) ∈
      (((Class.cv (nb071_alpha_dummy_021))).fv ∪ ((Class.cv (nb071_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0033 (x : Var) :
    (nb071_alpha_dummy_024 x) ∈
      (((Class.cv (nb071_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0034 :
    (nb071_alpha_dummy_001) ∈
      (((Class.cv (nb071_alpha_dummy_000))).fv ∪ ((Class.cv (nb071_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0035 :
    (nb071_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_005)
              (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_005) from (by
          unfold nb071_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_006) from (by
            unfold nb071_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0036 (x : Var) :
    (nb071_alpha_dummy_002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb071_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0037 (x : Var) :
    (nb071_alpha_dummy_002 x) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_007 x)
              (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_007 x) from (by
          unfold nb071_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_008 x) from (by
            unfold nb071_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0038 :
    (nb071_alpha_dummy_001) ∈
      (((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_005)
            (syn_wrex (nb071_alpha_dummy_006) (Class.cv (nb071_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_005) from (by
          unfold nb071_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_001) ≠ (nb071_alpha_dummy_006) from (by
            unfold nb071_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0034) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0039 (x : Var) :
    (nb071_alpha_dummy_002 x) ∈
      (((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_007 x)
            (syn_wrex (nb071_alpha_dummy_008 x) (Class.cv (nb071_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_007 x) from (by
          unfold nb071_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_002 x) ≠ (nb071_alpha_dummy_008 x) from (by
            unfold nb071_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0036 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0040 :
    (nb071_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0041 (x : Var) :
    (nb071_alpha_dummy_008 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0042 :
    (nb071_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0043 (x : Var) :
    (nb071_alpha_dummy_008 x) ∈
      (((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0044 :
    (nb071_alpha_dummy_000) ∈ (((syn_cuni (Class.cv (nb071_alpha_dummy_000)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0045 :
    (nb071_alpha_dummy_000) ∈
      (({(nb071_alpha_dummy_041)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wrex]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_042) from (by
          unfold nb071_alpha_dummy_042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 1))))
  · rw [fv_syn_cuni]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb071_support_mem_0046 :
    (nb071_alpha_dummy_000) ∈
      (((Class.cab (nb071_alpha_dummy_045) (Wff.classEq (Class.cab (nb071_alpha_dummy_041)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_041)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_042) (syn_cuni (Class.cv (nb071_alpha_dummy_000)))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_041))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_045)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_045) from (by
          unfold nb071_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0045) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_041) from (by
            unfold nb071_alpha_dummy_041;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 0))))
    · rw [fv_syn_wa]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact
          (show (nb071_alpha_dummy_000) ≠ (nb071_alpha_dummy_042) from (by
              unfold nb071_alpha_dummy_042;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0044) 1))))
      · rw [fv_syn_cuni]
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _

theorem nb071_support_mem_0047 (x : Var) : x ∈ (((syn_cuni (Class.cv x))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0048 (x : Var) :
    x ∈
      (({(nb071_alpha_dummy_043 x)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
            (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wrex]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071_alpha_dummy_044 x) from (by
          unfold nb071_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
  · rw [fv_syn_cuni]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb071_support_mem_0049 (x : Var) :
    x ∈
      (((Class.cab (nb071_alpha_dummy_046 x) (Wff.classEq (Class.cab (nb071_alpha_dummy_043 x)
              (syn_wa (Wff.classMem (Class.cv (nb071_alpha_dummy_043 x)) (syn_cncs))
                (syn_wrex (nb071_alpha_dummy_044 x) (syn_cuni (Class.cv x))
                  (Wff.classEq (Class.cv (nb071_alpha_dummy_043 x))
                    (syn_cnc (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))))))
            (syn_csn (Class.cv (nb071_alpha_dummy_046 x)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb071_alpha_dummy_046 x) from (by
          unfold nb071_alpha_dummy_046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0048 x) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb071_alpha_dummy_043 x) from (by
            unfold nb071_alpha_dummy_043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 0))))
    · rw [fv_syn_wa]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_wrex]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_erase]
      constructor
      · exact
          (show x ≠ (nb071_alpha_dummy_044 x) from (by
              unfold nb071_alpha_dummy_044;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0047 x) 1))))
      · rw [fv_syn_cuni]
        rw [fv_class_cv]
        exact Finset.mem_singleton_self _

theorem nb071_support_mem_0050 :
    (nb071_alpha_dummy_000) ∈ (((Class.cv (nb071_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0051 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0052 :
    (nb071_alpha_dummy_065) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_065))
            (Class.cv (nb071_alpha_dummy_042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0053 (x : Var) :
    (nb071_alpha_dummy_066 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
