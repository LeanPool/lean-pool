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

/-! Certificates from `NAR4C076C001Part001`. -/


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
noncomputable def nb076_alpha_dummy_000 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
noncomputable def nb076_alpha_dummy_001 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
noncomputable def nb076_alpha_dummy_002 : Var :=
  (freshVar ((∅ : Finset Var)) 2)

@[expose]
noncomputable def nb076_alpha_dummy_003 : Var :=
  (freshVar ((∅ : Finset Var)) 3)

@[expose]
noncomputable def nb076_alpha_dummy_004 : Var :=
  (freshVar ((∅ : Finset Var)) 4)

@[expose]
noncomputable def nb076_alpha_dummy_005 : Var :=
  (freshVar (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪
          ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪
      ((Class.cab (nb076_alpha_dummy_000)
          (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
            (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
              (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                  (Class.cv (nb076_alpha_dummy_002)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_006 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ m } : Finset Var) ∪ ((syn_cncs)).fv ∪ ({ n } : Finset Var) ∪ ((syn_cncs)).fv ∪
      ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
              (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_007 : Var :=
  (freshVar
    (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
        ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
          (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
              (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                  (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                    (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                      (Class.cv (nb076_alpha_dummy_002)))))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_008 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
        ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
          (syn_wa (Wff.classMem (Class.cv m) (syn_cncs)) (Wff.classMem (Class.cv n) (syn_cncs)))
          (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
              (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n) (syn_wbr (Class.cv a) (syn_cen)
                    (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_009 : Var :=
  (freshVar (((syn_cop (Class.cv (nb076_alpha_dummy_003))
          (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_010 : Var :=
  (freshVar (((syn_cop (Class.cv (nb076_alpha_dummy_003))
          (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_011 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
      ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_012 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
      ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_013 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_014 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_015 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
            (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
              (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
            (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
              (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_016 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_011 g m n a b)
          (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_011 g m n a b)
          (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_017 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_018 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_019 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_020 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_021 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_022 (m : Var) (n : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_023 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_017)
          (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
              (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_017)
          (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
              (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_024 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_019 m n)
          (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
              (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_019 m n) (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
              (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_025 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_018))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_026 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_018))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_027 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_028 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_029 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_025))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_030 (m : Var) (n : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_027 m n))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_031 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_032 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_033 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_034 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_035 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_036 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_037 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_032))
          (Class.cv (nb076_alpha_dummy_033)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_038 (m : Var) (n : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
          (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
          (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_039 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_040 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
      ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_041 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_042 (m : Var) (n : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_043 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_044 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
      ((Class.cv (nb076_alpha_dummy_035 m n))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_045 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_046 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪
      ((Class.cv (nb076_alpha_dummy_036 m n))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_047 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_017)
          (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017)
          (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_048 (m : Var) (n : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_019 m n)
          (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n)
          (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_049 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_050 (m : Var) (n : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_051 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_052 (m : Var) (n : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_053 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_010))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_054 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_010))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_055 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_056 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_057 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_053))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_058 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_059 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_060 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_061 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_062 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_063 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_064 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_065 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_060))
          (Class.cv (nb076_alpha_dummy_061)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_066 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
          (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
          (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_067 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_068 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_069 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_070 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_071 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_072 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_073 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_074 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_075 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_009)
          (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009)
          (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_076 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_011 g m n a b)
          (syn_wrex (nb076_alpha_dummy_012 g m n a b)
            (Class.cv (nb076_alpha_dummy_006 g m n a b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b)
          (syn_wrex (nb076_alpha_dummy_012 g m n a b)
            (Class.cv (nb076_alpha_dummy_006 g m n a b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_077 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_078 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_079 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_080 (g : Var) (m : Var) (n : Var) (a : Var)
    (b : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_081 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_000))).fv ∪
      ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_082 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_000))).fv ∪
      ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_083 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_084 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_085 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
              (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_086 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_087 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_081)
          (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
              (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_081)
          (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
              (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_088 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_083 g a b)
          (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_083 g a b)
          (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_089 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_082))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_090 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_082))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_091 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_092 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_093 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_089))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_094 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_095 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_096 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_097 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_098 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_099 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_100 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_101 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_096))
          (Class.cv (nb076_alpha_dummy_097)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_102 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
          (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
          (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_103 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_104 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_105 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_106 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_107 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_108 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_109 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_110 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_111 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
            (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081)
          (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001))
              (Class.cv (nb076_alpha_dummy_002)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_112 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_083 g a b)
          (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b)
          (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_113 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_114 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_115 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_116 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_117 : Var :=
  (freshVar
    (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
            (Class.cv (nb076_alpha_dummy_001))) (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
            (Class.cv (nb076_alpha_dummy_002))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_118 (g : Var) (b : Var) : Var :=
  (freshVar (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
        ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
          (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_119 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_120 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_121 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_122 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_116 g b))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_123 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_124 (g : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_125 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_119)
          (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
              (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_119)
          (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
              (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_126 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_121 g b)
          (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪
      ((Class.cab (nb076_alpha_dummy_121 g b)
          (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
              (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_127 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_120))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_128 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_120))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_129 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_130 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_131 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_127))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_132 (g : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪
      ((Class.cv (nb076_alpha_dummy_129 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_133 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_134 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_135 : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_136 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_137 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb076_alpha_dummy_138 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb076_alpha_dummy_139 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_134))
          (Class.cv (nb076_alpha_dummy_135)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_140 (g : Var) (b : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
          (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪
      ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
          (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_141 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_142 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_143 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_144 (g : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪
      ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_145 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_146 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_137 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_147 : Var :=
  (freshVar
    (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_148 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪
      ((Class.cv (nb076_alpha_dummy_138 g b))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_149 : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_119)
          (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119)
          (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                (syn_csn (syn_c0c))))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part002`. -/


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
noncomputable def nb076_alpha_dummy_150 (g : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb076_alpha_dummy_121 g b)
          (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b)
          (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
              (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_151 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_152 (g : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_153 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_154 (g : Var) (b : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_155 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_156 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_157 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) 0)

@[expose]
noncomputable def nb076_alpha_dummy_158 (g : Var) (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪
      ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) 0)

theorem nb076_fresh_000 :
    (nb076_alpha_dummy_075) ∉
      (((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_001 :
    (nb076_alpha_dummy_015) ∉
      (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv)
      0

theorem nb076_fresh_002 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_076 g m n a b) ∉
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_016 g m n a b) ∉
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_016] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv)
      0

theorem nb076_fresh_004 :
    (nb076_alpha_dummy_023) ∉
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_023] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv)
      0

theorem nb076_fresh_005 :
    (nb076_alpha_dummy_047) ∉
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_006 (m : Var) (n : Var) :
    (nb076_alpha_dummy_024 m n) ∉
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv)
      0

theorem nb076_fresh_007 (m : Var) (n : Var) :
    (nb076_alpha_dummy_048 m n) ∉
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_008 :
    (nb076_alpha_dummy_087) ∉
      (((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_087] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv)
      0

theorem nb076_fresh_009 :
    (nb076_alpha_dummy_111) ∉
      (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
              (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_111] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
              (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_010 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_088 g a b) ∉
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_088] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv)
      0

theorem nb076_fresh_011 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_112 g a b) ∉
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_112] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_012 :
    (nb076_alpha_dummy_125) ∉
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv)
      0

theorem nb076_fresh_013 :
    (nb076_alpha_dummy_149) ∉
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_149] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_014 (g : Var) (b : Var) :
    (nb076_alpha_dummy_126 g b) ∉
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv)
      0

theorem nb076_fresh_015 (g : Var) (b : Var) :
    (nb076_alpha_dummy_150 g b) ∉
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_150] using
    freshVar_not_mem
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb076_fresh_016 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_083 g a b) ∉
      (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) :=
  by
  simpa only [nb076_alpha_dummy_083] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 0

theorem nb076_fresh_017 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_084 g a b) ∉
      (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) :=
  by
  simpa only [nb076_alpha_dummy_084] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) 1

theorem nb076_distinct_018 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_083 g a b) ≠ (nb076_alpha_dummy_084 g a b) := by
  simpa only [nb076_alpha_dummy_083, nb076_alpha_dummy_084] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_019 :
    (nb076_alpha_dummy_081) ∉
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv)
      0

theorem nb076_fresh_020 :
    (nb076_alpha_dummy_082) ∉
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv)
      1

theorem nb076_distinct_021 : (nb076_alpha_dummy_081) ≠ (nb076_alpha_dummy_082) := by
  simpa only [nb076_alpha_dummy_081, nb076_alpha_dummy_082] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_000))).fv ∪
        ((syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_022 :
    (nb076_alpha_dummy_113) ∉
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) :=
  by
  simpa only [nb076_alpha_dummy_113] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv)
      0

theorem nb076_fresh_023 :
    (nb076_alpha_dummy_114) ∉
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) :=
  by
  simpa only [nb076_alpha_dummy_114] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv)
      1

theorem nb076_distinct_024 : (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_114) := by
  simpa only [nb076_alpha_dummy_113, nb076_alpha_dummy_114] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_025 :
    (nb076_alpha_dummy_017) ∉
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) :=
  by
  simpa only [nb076_alpha_dummy_017] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv)
      0

theorem nb076_fresh_026 :
    (nb076_alpha_dummy_018) ∉
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) :=
  by
  simpa only [nb076_alpha_dummy_018] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv)
      1

theorem nb076_distinct_027 : (nb076_alpha_dummy_017) ≠ (nb076_alpha_dummy_018) := by
  simpa only [nb076_alpha_dummy_017, nb076_alpha_dummy_018] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_028 :
    (nb076_alpha_dummy_053) ∉ (((Class.cv (nb076_alpha_dummy_010))).fv) := by
  simpa only [nb076_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_010))).fv) 0

theorem nb076_fresh_029 :
    (nb076_alpha_dummy_054) ∉ (((Class.cv (nb076_alpha_dummy_010))).fv) := by
  simpa only [nb076_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_010))).fv) 1

theorem nb076_distinct_030 : (nb076_alpha_dummy_053) ≠ (nb076_alpha_dummy_054) := by
  simpa only [nb076_alpha_dummy_053, nb076_alpha_dummy_054] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_010))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_031 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_055 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 0

theorem nb076_fresh_032 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_056 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) 1

theorem nb076_distinct_033 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_055 g m n a b) ≠ (nb076_alpha_dummy_056 g m n a b) := by
  simpa only [nb076_alpha_dummy_055, nb076_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb076_fresh_034 :
    (nb076_alpha_dummy_025) ∉ (((Class.cv (nb076_alpha_dummy_018))).fv) := by
  simpa only [nb076_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_018))).fv) 0

theorem nb076_fresh_035 :
    (nb076_alpha_dummy_026) ∉ (((Class.cv (nb076_alpha_dummy_018))).fv) := by
  simpa only [nb076_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_018))).fv) 1

theorem nb076_distinct_036 : (nb076_alpha_dummy_025) ≠ (nb076_alpha_dummy_026) := by
  simpa only [nb076_alpha_dummy_025, nb076_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_018))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_037 (m : Var) (n : Var) :
    (nb076_alpha_dummy_027 m n) ∉ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) := by
  simpa only [nb076_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 0

theorem nb076_fresh_038 (m : Var) (n : Var) :
    (nb076_alpha_dummy_028 m n) ∉ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) := by
  simpa only [nb076_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_020 m n))).fv) 1

theorem nb076_distinct_039 (m : Var) (n : Var) :
    (nb076_alpha_dummy_027 m n) ≠ (nb076_alpha_dummy_028 m n) := by
  simpa only [nb076_alpha_dummy_027, nb076_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_020 m n))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_040 :
    (nb076_alpha_dummy_031) ∉
      (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_041 :
    (nb076_alpha_dummy_032) ∉
      (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_042 :
    (nb076_alpha_dummy_033) ∉
      (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_043 : (nb076_alpha_dummy_031) ≠ (nb076_alpha_dummy_032) := by
  simpa only [nb076_alpha_dummy_031, nb076_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_044 : (nb076_alpha_dummy_031) ≠ (nb076_alpha_dummy_033) := by
  simpa only [nb076_alpha_dummy_031, nb076_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_045 : (nb076_alpha_dummy_032) ≠ (nb076_alpha_dummy_033) := by
  simpa only [nb076_alpha_dummy_032, nb076_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_046 (m : Var) (n : Var) :
    (nb076_alpha_dummy_034 m n) ∉
      (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_047 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ∉
      (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_035] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_048 (m : Var) (n : Var) :
    (nb076_alpha_dummy_036 m n) ∉
      (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_036] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_049 (m : Var) (n : Var) :
    (nb076_alpha_dummy_034 m n) ≠ (nb076_alpha_dummy_035 m n) := by
  simpa only [nb076_alpha_dummy_034, nb076_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_050 (m : Var) (n : Var) :
    (nb076_alpha_dummy_034 m n) ≠ (nb076_alpha_dummy_036 m n) := by
  simpa only [nb076_alpha_dummy_034, nb076_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_051 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ≠ (nb076_alpha_dummy_036 m n) := by
  simpa only [nb076_alpha_dummy_035, nb076_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_052 :
    (nb076_alpha_dummy_043) ∉
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) :=
  by
  simpa only [nb076_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv)
      0

theorem nb076_fresh_053 :
    (nb076_alpha_dummy_039) ∉
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) :=
  by
  simpa only [nb076_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv)
      0

theorem nb076_fresh_054 :
    (nb076_alpha_dummy_045) ∉
      (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) :=
  by
  simpa only [nb076_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv)
      0

theorem nb076_fresh_055 (m : Var) (n : Var) :
    (nb076_alpha_dummy_044 m n) ∉
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_035 m n))).fv) :=
  by
  simpa only [nb076_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_035 m n))).fv)
      0

theorem nb076_fresh_056 (m : Var) (n : Var) :
    (nb076_alpha_dummy_040 m n) ∉
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv) :=
  by
  simpa only [nb076_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv)
      0

theorem nb076_fresh_057 (m : Var) (n : Var) :
    (nb076_alpha_dummy_046 m n) ∉
      (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv) :=
  by
  simpa only [nb076_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv)
      0

theorem nb076_fresh_058 :
    (nb076_alpha_dummy_059) ∉
      (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_059 :
    (nb076_alpha_dummy_060) ∉
      (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_060 :
    (nb076_alpha_dummy_061) ∉
      (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_061 : (nb076_alpha_dummy_059) ≠ (nb076_alpha_dummy_060) := by
  simpa only [nb076_alpha_dummy_059, nb076_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_062 : (nb076_alpha_dummy_059) ≠ (nb076_alpha_dummy_061) := by
  simpa only [nb076_alpha_dummy_059, nb076_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_063 : (nb076_alpha_dummy_060) ≠ (nb076_alpha_dummy_061) := by
  simpa only [nb076_alpha_dummy_060, nb076_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_064 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_062 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv)
      0

theorem nb076_fresh_065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv)
      1

theorem nb076_fresh_066 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_064 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv)
      2

theorem nb076_distinct_067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_062 g m n a b) ≠ (nb076_alpha_dummy_063 g m n a b) := by
  simpa only [nb076_alpha_dummy_062, nb076_alpha_dummy_063] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      1) (by decide))

theorem nb076_distinct_068 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_062 g m n a b) ≠ (nb076_alpha_dummy_064 g m n a b) := by
  simpa only [nb076_alpha_dummy_062, nb076_alpha_dummy_064] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 0) (j :=
      2) (by decide))

theorem nb076_distinct_069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ≠ (nb076_alpha_dummy_064 g m n a b) := by
  simpa only [nb076_alpha_dummy_063, nb076_alpha_dummy_064] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) (i := 1) (j :=
      2) (by decide))

theorem nb076_fresh_070 :
    (nb076_alpha_dummy_071) ∉
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) :=
  by
  simpa only [nb076_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv)
      0

theorem nb076_fresh_071 :
    (nb076_alpha_dummy_067) ∉
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) :=
  by
  simpa only [nb076_alpha_dummy_067] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv)
      0

theorem nb076_fresh_072 :
    (nb076_alpha_dummy_073) ∉
      (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) :=
  by
  simpa only [nb076_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv)
      0

theorem nb076_fresh_073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_072 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv)
      0

theorem nb076_fresh_074 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_068 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv)
      0

theorem nb076_fresh_075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_074 g m n a b) ∉
      (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv)
      0

theorem nb076_fresh_076 :
    (nb076_alpha_dummy_089) ∉ (((Class.cv (nb076_alpha_dummy_082))).fv) := by
  simpa only [nb076_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_082))).fv) 0

theorem nb076_fresh_077 :
    (nb076_alpha_dummy_090) ∉ (((Class.cv (nb076_alpha_dummy_082))).fv) := by
  simpa only [nb076_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_082))).fv) 1

theorem nb076_distinct_078 : (nb076_alpha_dummy_089) ≠ (nb076_alpha_dummy_090) := by
  simpa only [nb076_alpha_dummy_089, nb076_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_082))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_079 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_091 g a b) ∉ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_091] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 0

theorem nb076_fresh_080 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_092 g a b) ∉ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) := by
  simpa only [nb076_alpha_dummy_092] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) 1

theorem nb076_distinct_081 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_091 g a b) ≠ (nb076_alpha_dummy_092 g a b) := by
  simpa only [nb076_alpha_dummy_091, nb076_alpha_dummy_092] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_082 :
    (nb076_alpha_dummy_095) ∉
      (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_095] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_083 :
    (nb076_alpha_dummy_096) ∉
      (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_096] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_084 :
    (nb076_alpha_dummy_097) ∉
      (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_097] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_085 : (nb076_alpha_dummy_095) ≠ (nb076_alpha_dummy_096) := by
  simpa only [nb076_alpha_dummy_095, nb076_alpha_dummy_096] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_086 : (nb076_alpha_dummy_095) ≠ (nb076_alpha_dummy_097) := by
  simpa only [nb076_alpha_dummy_095, nb076_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_087 : (nb076_alpha_dummy_096) ≠ (nb076_alpha_dummy_097) := by
  simpa only [nb076_alpha_dummy_096, nb076_alpha_dummy_097] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_088 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_098 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_098] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_089 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_099] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_090 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_100 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_100] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_091 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_098 g a b) ≠ (nb076_alpha_dummy_099 g a b) := by
  simpa only [nb076_alpha_dummy_098, nb076_alpha_dummy_099] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_092 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_098 g a b) ≠ (nb076_alpha_dummy_100 g a b) := by
  simpa only [nb076_alpha_dummy_098, nb076_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_093 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ≠ (nb076_alpha_dummy_100 g a b) := by
  simpa only [nb076_alpha_dummy_099, nb076_alpha_dummy_100] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_094 :
    (nb076_alpha_dummy_107) ∉
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) :=
  by
  simpa only [nb076_alpha_dummy_107] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv)
      0

theorem nb076_fresh_095 :
    (nb076_alpha_dummy_103) ∉
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) :=
  by
  simpa only [nb076_alpha_dummy_103] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv)
      0

theorem nb076_fresh_096 :
    (nb076_alpha_dummy_109) ∉
      (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) :=
  by
  simpa only [nb076_alpha_dummy_109] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv)
      0

theorem nb076_fresh_097 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_108 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_108] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_099 g a b))).fv)
      0

theorem nb076_fresh_098 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_104 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_104] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv)
      0

theorem nb076_fresh_099 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_110 g a b) ∉
      (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_110] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv)
      0

theorem nb076_fresh_100 :
    (nb076_alpha_dummy_119) ∉
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) :=
  by
  simpa only [nb076_alpha_dummy_119] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv)
      0

theorem nb076_fresh_101 :
    (nb076_alpha_dummy_120) ∉
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) :=
  by
  simpa only [nb076_alpha_dummy_120] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv)
      1

theorem nb076_distinct_102 : (nb076_alpha_dummy_119) ≠ (nb076_alpha_dummy_120) := by
  simpa only [nb076_alpha_dummy_119, nb076_alpha_dummy_120] using
    (freshVar_injective
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_103 (g : Var) (b : Var) :
    (nb076_alpha_dummy_121 g b) ∉
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_121] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv)
      0

theorem nb076_fresh_104 (g : Var) (b : Var) :
    (nb076_alpha_dummy_122 g b) ∉
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_122] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv)
      1

theorem nb076_distinct_105 (g : Var) (b : Var) :
    (nb076_alpha_dummy_121 g b) ≠ (nb076_alpha_dummy_122 g b) := by
  simpa only [nb076_alpha_dummy_121, nb076_alpha_dummy_122] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_106 :
    (nb076_alpha_dummy_127) ∉ (((Class.cv (nb076_alpha_dummy_120))).fv) := by
  simpa only [nb076_alpha_dummy_127] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_120))).fv) 0

theorem nb076_fresh_107 :
    (nb076_alpha_dummy_128) ∉ (((Class.cv (nb076_alpha_dummy_120))).fv) := by
  simpa only [nb076_alpha_dummy_128] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_120))).fv) 1

theorem nb076_distinct_108 : (nb076_alpha_dummy_127) ≠ (nb076_alpha_dummy_128) := by
  simpa only [nb076_alpha_dummy_127, nb076_alpha_dummy_128] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_120))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_109 (g : Var) (b : Var) :
    (nb076_alpha_dummy_129 g b) ∉ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) := by
  simpa only [nb076_alpha_dummy_129] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 0

theorem nb076_fresh_110 (g : Var) (b : Var) :
    (nb076_alpha_dummy_130 g b) ∉ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) := by
  simpa only [nb076_alpha_dummy_130] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_122 g b))).fv) 1

theorem nb076_distinct_111 (g : Var) (b : Var) :
    (nb076_alpha_dummy_129 g b) ≠ (nb076_alpha_dummy_130 g b) := by
  simpa only [nb076_alpha_dummy_129, nb076_alpha_dummy_130] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_122 g b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb076_fresh_112 :
    (nb076_alpha_dummy_133) ∉
      (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_133] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_113 :
    (nb076_alpha_dummy_134) ∉
      (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_134] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_114 :
    (nb076_alpha_dummy_135) ∉
      (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_135] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_115 : (nb076_alpha_dummy_133) ≠ (nb076_alpha_dummy_134) := by
  simpa only [nb076_alpha_dummy_133, nb076_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb076_distinct_116 : (nb076_alpha_dummy_133) ≠ (nb076_alpha_dummy_135) := by
  simpa only [nb076_alpha_dummy_133, nb076_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb076_distinct_117 : (nb076_alpha_dummy_134) ≠ (nb076_alpha_dummy_135) := by
  simpa only [nb076_alpha_dummy_134, nb076_alpha_dummy_135] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb076_fresh_118 (g : Var) (b : Var) :
    (nb076_alpha_dummy_136 g b) ∉
      (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_136] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb076_fresh_119 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ∉
      (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_137] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb076_fresh_120 (g : Var) (b : Var) :
    (nb076_alpha_dummy_138 g b) ∉
      (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb076_alpha_dummy_138] using
    freshVar_not_mem (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb076_distinct_121 (g : Var) (b : Var) :
    (nb076_alpha_dummy_136 g b) ≠ (nb076_alpha_dummy_137 g b) := by
  simpa only [nb076_alpha_dummy_136, nb076_alpha_dummy_137] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_distinct_122 (g : Var) (b : Var) :
    (nb076_alpha_dummy_136 g b) ≠ (nb076_alpha_dummy_138 g b) := by
  simpa only [nb076_alpha_dummy_136, nb076_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb076_distinct_123 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ≠ (nb076_alpha_dummy_138 g b) := by
  simpa only [nb076_alpha_dummy_137, nb076_alpha_dummy_138] using
    (freshVar_injective (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb076_fresh_124 :
    (nb076_alpha_dummy_145) ∉
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) :=
  by
  simpa only [nb076_alpha_dummy_145] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv)
      0

theorem nb076_fresh_125 :
    (nb076_alpha_dummy_141) ∉
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) :=
  by
  simpa only [nb076_alpha_dummy_141] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv)
      0

theorem nb076_fresh_126 :
    (nb076_alpha_dummy_147) ∉
      (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) :=
  by
  simpa only [nb076_alpha_dummy_147] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv)
      0

theorem nb076_fresh_127 (g : Var) (b : Var) :
    (nb076_alpha_dummy_146 g b) ∉
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_137 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_146] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_137 g b))).fv)
      0

theorem nb076_fresh_128 (g : Var) (b : Var) :
    (nb076_alpha_dummy_142 g b) ∉
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_142] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv)
      0

theorem nb076_fresh_129 (g : Var) (b : Var) :
    (nb076_alpha_dummy_148 g b) ∉
      (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_148] using
    freshVar_not_mem
      (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv)
      0

theorem nb076_fresh_130 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076_alpha_dummy_115] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 0

theorem nb076_fresh_131 (g : Var) (b : Var) :
    (nb076_alpha_dummy_116 g b) ∉ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) := by
  simpa only [nb076_alpha_dummy_116] using
    freshVar_not_mem (((Class.cv b)).fv ∪ ((Class.cv g)).fv) 1

theorem nb076_distinct_132 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_116 g b) := by
  simpa only [nb076_alpha_dummy_115, nb076_alpha_dummy_116] using
    (freshVar_injective (((Class.cv b)).fv ∪ ((Class.cv g)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_133 (m : Var) (n : Var) :
    (nb076_alpha_dummy_019 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 0

theorem nb076_fresh_134 (m : Var) (n : Var) :
    (nb076_alpha_dummy_020 m n) ∉ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) := by
  simpa only [nb076_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv n)).fv) 1

theorem nb076_distinct_135 (m : Var) (n : Var) :
    (nb076_alpha_dummy_019 m n) ≠ (nb076_alpha_dummy_020 m n) := by
  simpa only [nb076_alpha_dummy_019, nb076_alpha_dummy_020] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv n)).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_136 :
    (nb076_alpha_dummy_029) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_025))).fv) :=
  by
  simpa only [nb076_alpha_dummy_029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_025))).fv)
      0

theorem nb076_fresh_137 (m : Var) (n : Var) :
    (nb076_alpha_dummy_030 m n) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_027 m n))).fv) :=
  by
  simpa only [nb076_alpha_dummy_030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_027 m n))).fv)
      0

theorem nb076_fresh_138 :
    (nb076_alpha_dummy_057) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_053))).fv) :=
  by
  simpa only [nb076_alpha_dummy_057] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_053))).fv)
      0

theorem nb076_fresh_139 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_058 g m n a b) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_058] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv)
      0

theorem nb076_fresh_140 :
    (nb076_alpha_dummy_093) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_089))).fv) :=
  by
  simpa only [nb076_alpha_dummy_093] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_089))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part003`. -/


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

theorem nb076_fresh_141 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_094 g a b) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_094] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_091 g a b))).fv)
      0

theorem nb076_fresh_142 :
    (nb076_alpha_dummy_131) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_127))).fv) :=
  by
  simpa only [nb076_alpha_dummy_131] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_127))).fv)
      0

theorem nb076_fresh_143 (g : Var) (b : Var) :
    (nb076_alpha_dummy_132 g b) ∉
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_129 g b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_132] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_129 g b))).fv)
      0

theorem nb076_fresh_144 :
    (nb076_alpha_dummy_013) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
                (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
                (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_145 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_014 g m n a b) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b)
                (Class.cv (nb076_alpha_dummy_006 g m n a b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_014] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b)
                (Class.cv (nb076_alpha_dummy_006 g m n a b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_146 :
    (nb076_alpha_dummy_021) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_021] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_147 (m : Var) (n : Var) :
    (nb076_alpha_dummy_022 m n) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_022] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_148 :
    (nb076_alpha_dummy_085) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_149 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_086 g a b) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_150 :
    (nb076_alpha_dummy_123) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_123] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_151 (g : Var) (b : Var) :
    (nb076_alpha_dummy_124 g b) ∉
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_124] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb076_fresh_152 :
    (nb076_alpha_dummy_041) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv)
      0

theorem nb076_fresh_153 (m : Var) (n : Var) :
    (nb076_alpha_dummy_042 m n) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv)
      0

theorem nb076_fresh_154 :
    (nb076_alpha_dummy_069) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_069] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv)
      0

theorem nb076_fresh_155 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_070 g m n a b) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_070] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv)
      0

theorem nb076_fresh_156 :
    (nb076_alpha_dummy_105) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_105] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv)
      0

theorem nb076_fresh_157 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_106 g a b) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_106] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv)
      0

theorem nb076_fresh_158 :
    (nb076_alpha_dummy_143) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_143] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv)
      0

theorem nb076_fresh_159 (g : Var) (b : Var) :
    (nb076_alpha_dummy_144 g b) ∉
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_144] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv)
      0

theorem nb076_fresh_160 :
    (nb076_alpha_dummy_077) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_161 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_078 g m n a b) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_078] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_162 :
    (nb076_alpha_dummy_049) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_163 (m : Var) (n : Var) :
    (nb076_alpha_dummy_050 m n) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_164 :
    (nb076_alpha_dummy_155) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_155] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_082))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_165 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_156 g a b) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_156] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_166 :
    (nb076_alpha_dummy_151) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_151] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_167 (g : Var) (b : Var) :
    (nb076_alpha_dummy_152 g b) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_152] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb076_fresh_168 :
    (nb076_alpha_dummy_037) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_032))
            (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv)
      0

theorem nb076_fresh_169 (m : Var) (n : Var) :
    (nb076_alpha_dummy_038 m n) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv)
      0

theorem nb076_fresh_170 :
    (nb076_alpha_dummy_065) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_060))
            (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_065] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv)
      0

theorem nb076_fresh_171 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_066 g m n a b) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv)
      0

theorem nb076_fresh_172 :
    (nb076_alpha_dummy_101) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_096))
            (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_101] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv)
      0

theorem nb076_fresh_173 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_102 g a b) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv)
      0

theorem nb076_fresh_174 :
    (nb076_alpha_dummy_139) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_134))
            (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv)
      0

theorem nb076_fresh_175 (g : Var) (b : Var) :
    (nb076_alpha_dummy_140 g b) ∉
      (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_140] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv)
      0

theorem nb076_fresh_176 :
    (nb076_alpha_dummy_009) ∉
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv) :=
  by
  simpa only [nb076_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv)
      0

theorem nb076_fresh_177 :
    (nb076_alpha_dummy_010) ∉
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv) :=
  by
  simpa only [nb076_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv)
      1

theorem nb076_distinct_178 : (nb076_alpha_dummy_009) ≠ (nb076_alpha_dummy_010) := by
  simpa only [nb076_alpha_dummy_009, nb076_alpha_dummy_010] using
    (freshVar_injective (((syn_cop (Class.cv (nb076_alpha_dummy_003))
            (Class.cv (nb076_alpha_dummy_004)))).fv ∪ ((Class.cv (nb076_alpha_dummy_005))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb076_fresh_179 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_011 g m n a b) ∉
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv)
      0

theorem nb076_fresh_180 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_012 g m n a b) ∉
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) :=
  by
  simpa only [nb076_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv)
      1

theorem nb076_distinct_181 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_011 g m n a b) ≠ (nb076_alpha_dummy_012 g m n a b) := by
  simpa only [nb076_alpha_dummy_011, nb076_alpha_dummy_012] using
    (freshVar_injective (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) (i := 0) (j := 1) (by decide))

theorem nb076_fresh_182 :
    (nb076_alpha_dummy_079) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv)
      0

theorem nb076_fresh_183 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_080 g m n a b) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv)
      0

theorem nb076_fresh_184 :
    (nb076_alpha_dummy_051) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv)
      0

theorem nb076_fresh_185 (m : Var) (n : Var) :
    (nb076_alpha_dummy_052 m n) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv)
      0

theorem nb076_fresh_186 :
    (nb076_alpha_dummy_157) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_157] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_082)))).fv)
      0

theorem nb076_fresh_187 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_158 g a b) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_158] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))).fv)
      0

theorem nb076_fresh_188 :
    (nb076_alpha_dummy_153) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_153] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv)
      0

theorem nb076_fresh_189 (g : Var) (b : Var) :
    (nb076_alpha_dummy_154 g b) ∉
      (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_154] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv)
      0

theorem nb076_fresh_190 :
    (nb076_alpha_dummy_005) ∉
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪
            ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab (nb076_alpha_dummy_000)
            (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
              (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                  (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                    (Class.cv (nb076_alpha_dummy_002)))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_005] using
    freshVar_not_mem
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪
            ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab (nb076_alpha_dummy_000)
            (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
              (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                  (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                    (Class.cv (nb076_alpha_dummy_002)))))))).fv)
      0

theorem nb076_fresh_191 :
    (nb076_alpha_dummy_007) ∉
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
          ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
              (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
                (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                  (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                    (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                      (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                        (Class.cv (nb076_alpha_dummy_002)))))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_007] using
    freshVar_not_mem
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
          ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
              (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
                (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                  (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                    (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                      (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                        (Class.cv (nb076_alpha_dummy_002)))))))))).fv)
      0

theorem nb076_fresh_192 :
    (nb076_alpha_dummy_117) ∉
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_117] using
    freshVar_not_mem
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv)
      0

theorem nb076_fresh_193 (g : Var) (b : Var) :
    (nb076_alpha_dummy_118 g b) ∉
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) :=
  by
  simpa only [nb076_alpha_dummy_118] using
    freshVar_not_mem
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv)
      0

theorem nb076_fresh_194 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∉
      (({ m } : Finset Var) ∪ ((syn_cncs)).fv ∪ ({ n } : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_006] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ((syn_cncs)).fv ∪ ({ n } : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv)
      0

theorem nb076_fresh_195 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_008 g m n a b) ∉
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv m) (syn_cncs))
              (Wff.classMem (Class.cv n) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
                (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                    (syn_wbr (Class.cv a) (syn_cen)
                      (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  simpa only [nb076_alpha_dummy_008] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv m) (syn_cncs))
              (Wff.classMem (Class.cv n) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
                (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                    (syn_wbr (Class.cv a) (syn_cen)
                      (syn_cxp (Class.cv b) (Class.cv g))))))))).fv)
      0

theorem nb076_fresh_196 : (nb076_alpha_dummy_000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb076_fresh_197 : (nb076_alpha_dummy_001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb076_fresh_198 : (nb076_alpha_dummy_002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb076_fresh_199 : (nb076_alpha_dummy_003) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_003] using freshVar_not_mem ((∅ : Finset Var)) 3

theorem nb076_fresh_200 : (nb076_alpha_dummy_004) ∉ ((∅ : Finset Var)) := by
  simpa only [nb076_alpha_dummy_004] using freshVar_not_mem ((∅ : Finset Var)) 4

theorem nb076_distinct_201 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_001) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb076_distinct_202 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_002) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb076_distinct_203 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 3) (by decide))

theorem nb076_distinct_204 : (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_000, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 4) (by decide))

theorem nb076_distinct_205 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_002) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb076_distinct_206 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 3) (by decide))

theorem nb076_distinct_207 : (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_001, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 4) (by decide))

theorem nb076_distinct_208 : (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_003) := by
  simpa only [nb076_alpha_dummy_002, nb076_alpha_dummy_003] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 3) (by decide))

theorem nb076_distinct_209 : (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_002, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 2) (j := 4) (by decide))

theorem nb076_distinct_210 : (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_004) := by
  simpa only [nb076_alpha_dummy_003, nb076_alpha_dummy_004] using
    (freshVar_injective ((∅ : Finset Var)) (i := 3) (j := 4) (by decide))

theorem nb076_support_mem_0000 :
    (nb076_alpha_dummy_003) ∈
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
          ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
              (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
                (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                  (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                    (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                      (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                        (Class.cv (nb076_alpha_dummy_002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0001 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv m) (syn_cncs))
              (Wff.classMem (Class.cv n) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
                (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                    (syn_wbr (Class.cv a) (syn_cen)
                      (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0002 :
    (nb076_alpha_dummy_004) ∈
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
          ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
              (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
                (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                  (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                    (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                      (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                        (Class.cv (nb076_alpha_dummy_002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0003 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv m) (syn_cncs))
              (Wff.classMem (Class.cv n) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
                (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                    (syn_wbr (Class.cv a) (syn_cen)
                      (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0004 :
    (nb076_alpha_dummy_005) ∈
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ({(nb076_alpha_dummy_004)} : Finset Var) ∪
          ({(nb076_alpha_dummy_005)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_003)) (syn_cncs))
              (Wff.classMem (Class.cv (nb076_alpha_dummy_004)) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_005)) (Class.cab (nb076_alpha_dummy_000)
                (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
                  (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                    (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                      (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                        (Class.cv (nb076_alpha_dummy_002)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0005 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∈
      (({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪
          ({(nb076_alpha_dummy_006 g m n a b)} : Finset Var) ∪ ((syn_wa
            (syn_wa (Wff.classMem (Class.cv m) (syn_cncs))
              (Wff.classMem (Class.cv n) (syn_cncs)))
            (Wff.classEq (Class.cv (nb076_alpha_dummy_006 g m n a b)) (Class.cab a
                (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                    (syn_wbr (Class.cv a) (syn_cen)
                      (syn_cxp (Class.cv b) (Class.cv g))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0006 :
    (nb076_alpha_dummy_003) ∈
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪
            ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab (nb076_alpha_dummy_000)
            (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
              (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                  (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                    (Class.cv (nb076_alpha_dummy_002)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0007 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (({ m } : Finset Var) ∪ ((syn_cncs)).fv ∪ ({ n } : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0008 :
    (nb076_alpha_dummy_003) ∈
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0009 :
    (nb076_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
                (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0010 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0011 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b)
                (Class.cv (nb076_alpha_dummy_006 g m n a b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0012 :
    (nb076_alpha_dummy_003) ∈
      (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0008) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0013 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    m ∈
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0010 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0014 :
    (nb076_alpha_dummy_003) ∈
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0015 :
    (nb076_alpha_dummy_003) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_018) from (by
            unfold nb076_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0016 (m : Var) (n : Var) :
    m ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0017 (m : Var) (n : Var) :
    m ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076_alpha_dummy_020 m n) from (by
            unfold nb076_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0018 :
    (nb076_alpha_dummy_003) ∈
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cphi (Class.cv (nb076_alpha_dummy_018))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_003) ≠ (nb076_alpha_dummy_018) from (by
            unfold nb076_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0014) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0019 (m : Var) (n : Var) :
    m ∈
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb076_alpha_dummy_020 m n) from (by
            unfold nb076_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0016 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0020 :
    (nb076_alpha_dummy_018) ∈ (((Class.cv (nb076_alpha_dummy_018))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0021 (m : Var) (n : Var) :
    (nb076_alpha_dummy_020 m n) ∈ (((Class.cv (nb076_alpha_dummy_020 m n))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0022 :
    (nb076_alpha_dummy_025) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_025)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_025)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_025))).fv) :=
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

theorem nb076_support_mem_0023 (m : Var) (n : Var) :
    (nb076_alpha_dummy_027 m n) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_027 m n)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_027 m n)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_027 m n))).fv) :=
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

theorem nb076_support_mem_0024 :
    (nb076_alpha_dummy_025) ∈
      (((Class.cv (nb076_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0025 (m : Var) (n : Var) :
    (nb076_alpha_dummy_027 m n) ∈
      (((Class.cv (nb076_alpha_dummy_027 m n))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0026 :
    (nb076_alpha_dummy_032) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_032))
            (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0027 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0028 :
    (nb076_alpha_dummy_032) ∈
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0029 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ∈
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0030 :
    (nb076_alpha_dummy_033) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_032)) (Class.cv (nb076_alpha_dummy_033)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_032))
            (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0031 (m : Var) (n : Var) :
    (nb076_alpha_dummy_036 m n) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_035 m n))
            (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0032 :
    (nb076_alpha_dummy_033) ∈
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0033 (m : Var) (n : Var) :
    (nb076_alpha_dummy_036 m n) ∈
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0034 :
    (nb076_alpha_dummy_032) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0035 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0036 :
    (nb076_alpha_dummy_032) ∈
      (((Class.cv (nb076_alpha_dummy_032))).fv ∪ ((Class.cv (nb076_alpha_dummy_032))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0037 (m : Var) (n : Var) :
    (nb076_alpha_dummy_035 m n) ∈
      (((Class.cv (nb076_alpha_dummy_035 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_035 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0038 :
    (nb076_alpha_dummy_033) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_032)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_033)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0039 (m : Var) (n : Var) :
    (nb076_alpha_dummy_036 m n) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_035 m n)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_036 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0040 :
    (nb076_alpha_dummy_033) ∈
      (((Class.cv (nb076_alpha_dummy_033))).fv ∪ ((Class.cv (nb076_alpha_dummy_033))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0041 (m : Var) (n : Var) :
    (nb076_alpha_dummy_036 m n) ∈
      (((Class.cv (nb076_alpha_dummy_036 m n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_036 m n))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0042 :
    (nb076_alpha_dummy_004) ∈
      (({(nb076_alpha_dummy_003)} : Finset Var) ∪ ((syn_cncs)).fv ∪
            ({(nb076_alpha_dummy_004)} : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab (nb076_alpha_dummy_000)
            (syn_wrex (nb076_alpha_dummy_001) (Class.cv (nb076_alpha_dummy_003))
              (syn_wrex (nb076_alpha_dummy_002) (Class.cv (nb076_alpha_dummy_004))
                (syn_wbr (Class.cv (nb076_alpha_dummy_000)) (syn_cen)
                  (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                    (Class.cv (nb076_alpha_dummy_002)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0043 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (({ m } : Finset Var) ∪ ((syn_cncs)).fv ∪ ({ n } : Finset Var) ∪ ((syn_cncs)).fv ∪
        ((Class.cab a (syn_wrex b (Class.cv m) (syn_wrex g (Class.cv n)
                (syn_wbr (Class.cv a) (syn_cen) (syn_cxp (Class.cv b) (Class.cv g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0044 :
    (nb076_alpha_dummy_004) ∈
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0045 :
    (nb076_alpha_dummy_004) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
                (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0046 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0047 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b)
                (Class.cv (nb076_alpha_dummy_006 g m n a b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C076C001Part004`. -/


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

theorem nb076_support_mem_0048 :
    (nb076_alpha_dummy_004) ∈
      (((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
              (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cphi (Class.cv (nb076_alpha_dummy_010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0044) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0049 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    n ∈
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0046 g m n a b) 1))))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0050 :
    (nb076_alpha_dummy_004) ∈
      (((Class.cv (nb076_alpha_dummy_003))).fv ∪ ((Class.cv (nb076_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0051 :
    (nb076_alpha_dummy_004) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_003))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_017)
              (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_018) from (by
            unfold nb076_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0052 (m : Var) (n : Var) :
    n ∈ (((Class.cv m)).fv ∪ ((Class.cv n)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0053 (m : Var) (n : Var) :
    n ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv m)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_019 m n)
              (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076_alpha_dummy_020 m n) from (by
            unfold nb076_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0054 :
    (nb076_alpha_dummy_004) ∈
      (((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_017)
            (syn_wrex (nb076_alpha_dummy_018) (Class.cv (nb076_alpha_dummy_004))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_017) from (by
          unfold nb076_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_004) ≠ (nb076_alpha_dummy_018) from (by
            unfold nb076_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0050) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0055 (m : Var) (n : Var) :
    n ∈
      (((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_019 m n)
            (syn_wrex (nb076_alpha_dummy_020 m n) (Class.cv n)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_019 m n))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show n ≠ (nb076_alpha_dummy_019 m n) from (by
          unfold nb076_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show n ≠ (nb076_alpha_dummy_020 m n) from (by
            unfold nb076_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0052 m n) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0056 :
    (nb076_alpha_dummy_018) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0057 (m : Var) (n : Var) :
    (nb076_alpha_dummy_020 m n) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_020 m n))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0058 :
    (nb076_alpha_dummy_018) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_018)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0059 (m : Var) (n : Var) :
    (nb076_alpha_dummy_020 m n) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_020 m n)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0060 :
    (nb076_alpha_dummy_010) ∈ (((Class.cv (nb076_alpha_dummy_010))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0061 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_012 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_012 g m n a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0062 :
    (nb076_alpha_dummy_053) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_053)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_053)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_053))).fv) :=
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

theorem nb076_support_mem_0063 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_055 g m n a b) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_055 g m n a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv) :=
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

theorem nb076_support_mem_0064 :
    (nb076_alpha_dummy_053) ∈
      (((Class.cv (nb076_alpha_dummy_053))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0065 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_055 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_055 g m n a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0066 :
    (nb076_alpha_dummy_060) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_060))
            (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0067 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0068 :
    (nb076_alpha_dummy_060) ∈
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0069 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0070 :
    (nb076_alpha_dummy_061) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_060)) (Class.cv (nb076_alpha_dummy_061)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_060))
            (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0071 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_064 g m n a b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_063 g m n a b))
            (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0072 :
    (nb076_alpha_dummy_061) ∈
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0073 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_064 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0074 :
    (nb076_alpha_dummy_060) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0075 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0076 :
    (nb076_alpha_dummy_060) ∈
      (((Class.cv (nb076_alpha_dummy_060))).fv ∪ ((Class.cv (nb076_alpha_dummy_060))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0077 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_063 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_063 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0078 :
    (nb076_alpha_dummy_061) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_060)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_061)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0079 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_064 g m n a b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_063 g m n a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_064 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0080 :
    (nb076_alpha_dummy_061) ∈
      (((Class.cv (nb076_alpha_dummy_061))).fv ∪ ((Class.cv (nb076_alpha_dummy_061))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0081 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_064 g m n a b) ∈
      (((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_064 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0082 :
    (nb076_alpha_dummy_005) ∈
      (((syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))).fv ∪
        ((Class.cv (nb076_alpha_dummy_005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0083 :
    (nb076_alpha_dummy_005) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_009) (syn_wrex (nb076_alpha_dummy_010)
                (syn_cop (Class.cv (nb076_alpha_dummy_003)) (Class.cv (nb076_alpha_dummy_004)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_009)
              (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0084 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∈
      (((syn_cop (Class.cv m) (Class.cv n))).fv ∪
        ((Class.cv (nb076_alpha_dummy_006 g m n a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0085 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b) (syn_cop (Class.cv m) (Class.cv n))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_011 g m n a b)
              (syn_wrex (nb076_alpha_dummy_012 g m n a b)
                (Class.cv (nb076_alpha_dummy_006 g m n a b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0086 :
    (nb076_alpha_dummy_005) ∈
      (((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_009)
            (syn_wrex (nb076_alpha_dummy_010) (Class.cv (nb076_alpha_dummy_005))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_009))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_010)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_009) from (by
          unfold nb076_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_005) ≠ (nb076_alpha_dummy_010) from (by
            unfold nb076_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0082) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0087 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_006 g m n a b) ∈
      (((Class.cab (nb076_alpha_dummy_011 g m n a b) (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_011 g m n a b)
            (syn_wrex (nb076_alpha_dummy_012 g m n a b)
              (Class.cv (nb076_alpha_dummy_006 g m n a b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_011 g m n a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_011 g m n a b) from (by
          unfold nb076_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_006 g m n a b) ≠ (nb076_alpha_dummy_012 g m n a b) from (by
            unfold nb076_alpha_dummy_012;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0084 g m n a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0088 :
    (nb076_alpha_dummy_010) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0089 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_012 g m n a b) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0090 :
    (nb076_alpha_dummy_010) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_010)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0091 (g : Var) (m : Var) (n : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_012 g m n a b) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_012 g m n a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0092 :
    (nb076_alpha_dummy_000) ∈
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0093 :
    (nb076_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0094 (g : Var) (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0095 (g : Var) (a : Var) (b : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0096 :
    (nb076_alpha_dummy_000) ∈
      (((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cphi (Class.cv (nb076_alpha_dummy_082))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_000) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0092) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0097 (g : Var) (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0094 g a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0098 :
    (nb076_alpha_dummy_082) ∈ (((Class.cv (nb076_alpha_dummy_082))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0099 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_084 g a b) ∈ (((Class.cv (nb076_alpha_dummy_084 g a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0100 :
    (nb076_alpha_dummy_089) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_089)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_089)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_089))).fv) :=
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

theorem nb076_support_mem_0101 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_091 g a b) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_091 g a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_091 g a b))).fv) :=
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

theorem nb076_support_mem_0102 :
    (nb076_alpha_dummy_089) ∈
      (((Class.cv (nb076_alpha_dummy_089))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0103 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_091 g a b) ∈
      (((Class.cv (nb076_alpha_dummy_091 g a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0104 :
    (nb076_alpha_dummy_096) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_096))
            (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0105 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0106 :
    (nb076_alpha_dummy_096) ∈
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0107 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ∈
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0108 :
    (nb076_alpha_dummy_097) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_096)) (Class.cv (nb076_alpha_dummy_097)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_096))
            (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0109 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_100 g a b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_099 g a b))
            (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0110 :
    (nb076_alpha_dummy_097) ∈
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0111 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_100 g a b) ∈
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0112 :
    (nb076_alpha_dummy_096) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0113 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0114 :
    (nb076_alpha_dummy_096) ∈
      (((Class.cv (nb076_alpha_dummy_096))).fv ∪ ((Class.cv (nb076_alpha_dummy_096))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0115 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_099 g a b) ∈
      (((Class.cv (nb076_alpha_dummy_099 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_099 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0116 :
    (nb076_alpha_dummy_097) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_096)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_097)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0117 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_100 g a b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_099 g a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_100 g a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0118 :
    (nb076_alpha_dummy_097) ∈
      (((Class.cv (nb076_alpha_dummy_097))).fv ∪ ((Class.cv (nb076_alpha_dummy_097))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0119 (g : Var) (a : Var) (b : Var) :
    (nb076_alpha_dummy_100 g a b) ∈
      (((Class.cv (nb076_alpha_dummy_100 g a b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_100 g a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0120 :
    (nb076_alpha_dummy_113) ∈
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0121 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ∈
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0122 :
    (nb076_alpha_dummy_114) ∈
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0123 (g : Var) (b : Var) :
    (nb076_alpha_dummy_116 g b) ∈
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0124 :
    (nb076_alpha_dummy_113) ∈
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0125 :
    (nb076_alpha_dummy_113) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_119) from (by
          unfold nb076_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_120) from (by
            unfold nb076_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0126 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ∈
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0127 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold nb076_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
            unfold nb076_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0128 :
    (nb076_alpha_dummy_113) ∈
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cphi (Class.cv (nb076_alpha_dummy_120))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_119) from (by
          unfold nb076_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_113) ≠ (nb076_alpha_dummy_120) from (by
            unfold nb076_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0124) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0129 (g : Var) (b : Var) :
    (nb076_alpha_dummy_115 g b) ∈
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv ∪
        ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold nb076_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_115 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
            unfold nb076_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0126 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0130 :
    (nb076_alpha_dummy_120) ∈ (((Class.cv (nb076_alpha_dummy_120))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0131 (g : Var) (b : Var) :
    (nb076_alpha_dummy_122 g b) ∈ (((Class.cv (nb076_alpha_dummy_122 g b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0132 :
    (nb076_alpha_dummy_127) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_127)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_127)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_127))).fv) :=
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

theorem nb076_support_mem_0133 (g : Var) (b : Var) :
    (nb076_alpha_dummy_129 g b) ∈
      (((Wff.classMem (Class.cv (nb076_alpha_dummy_129 g b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb076_alpha_dummy_129 g b)) (syn_c1c))).fv ∪
        ((Class.cv (nb076_alpha_dummy_129 g b))).fv) :=
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

theorem nb076_support_mem_0134 :
    (nb076_alpha_dummy_127) ∈
      (((Class.cv (nb076_alpha_dummy_127))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0135 (g : Var) (b : Var) :
    (nb076_alpha_dummy_129 g b) ∈
      (((Class.cv (nb076_alpha_dummy_129 g b))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0136 :
    (nb076_alpha_dummy_134) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_134))
            (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0137 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0138 :
    (nb076_alpha_dummy_134) ∈
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0139 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ∈
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0140 :
    (nb076_alpha_dummy_135) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_134)) (Class.cv (nb076_alpha_dummy_135)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_134))
            (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0141 (g : Var) (b : Var) :
    (nb076_alpha_dummy_138 g b) ∈
      (((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv ∪
        ((syn_cnin (Class.cv (nb076_alpha_dummy_137 g b))
            (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0142 :
    (nb076_alpha_dummy_135) ∈
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0143 (g : Var) (b : Var) :
    (nb076_alpha_dummy_138 g b) ∈
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0144 :
    (nb076_alpha_dummy_134) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0145 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0146 :
    (nb076_alpha_dummy_134) ∈
      (((Class.cv (nb076_alpha_dummy_134))).fv ∪ ((Class.cv (nb076_alpha_dummy_134))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0147 (g : Var) (b : Var) :
    (nb076_alpha_dummy_137 g b) ∈
      (((Class.cv (nb076_alpha_dummy_137 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_137 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0148 :
    (nb076_alpha_dummy_135) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_134)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_135)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0149 (g : Var) (b : Var) :
    (nb076_alpha_dummy_138 g b) ∈
      (((syn_ccompl (Class.cv (nb076_alpha_dummy_137 g b)))).fv ∪
        ((syn_ccompl (Class.cv (nb076_alpha_dummy_138 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0150 :
    (nb076_alpha_dummy_135) ∈
      (((Class.cv (nb076_alpha_dummy_135))).fv ∪ ((Class.cv (nb076_alpha_dummy_135))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0151 (g : Var) (b : Var) :
    (nb076_alpha_dummy_138 g b) ∈
      (((Class.cv (nb076_alpha_dummy_138 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_138 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0152 :
    (nb076_alpha_dummy_114) ∈
      (((Class.cv (nb076_alpha_dummy_113))).fv ∪ ((Class.cv (nb076_alpha_dummy_114))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0153 :
    (nb076_alpha_dummy_114) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_113))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_120)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_119)
              (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119) from (by
          unfold nb076_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_120) from (by
            unfold nb076_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0154 (g : Var) (b : Var) :
    (nb076_alpha_dummy_116 g b) ∈
      (((Class.cv (nb076_alpha_dummy_115 g b))).fv ∪
        ((Class.cv (nb076_alpha_dummy_116 g b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0155 (g : Var) (b : Var) :
    (nb076_alpha_dummy_116 g b) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_115 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_121 g b)
              (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold nb076_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
            unfold nb076_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0156 :
    (nb076_alpha_dummy_114) ∈
      (((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_119)
            (syn_wrex (nb076_alpha_dummy_120) (Class.cv (nb076_alpha_dummy_114))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_119))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_120)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_119) from (by
          unfold nb076_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_114) ≠ (nb076_alpha_dummy_120) from (by
            unfold nb076_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0152) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0157 (g : Var) (b : Var) :
    (nb076_alpha_dummy_116 g b) ∈
      (((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_121 g b)
            (syn_wrex (nb076_alpha_dummy_122 g b) (Class.cv (nb076_alpha_dummy_116 g b))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_121 g b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_121 g b) from (by
          unfold nb076_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_116 g b) ≠ (nb076_alpha_dummy_122 g b) from (by
            unfold nb076_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0154 g b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0158 :
    (nb076_alpha_dummy_120) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_120))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0159 (g : Var) (b : Var) :
    (nb076_alpha_dummy_122 g b) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb076_alpha_dummy_122 g b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0160 :
    (nb076_alpha_dummy_120) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_120)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0161 (g : Var) (b : Var) :
    (nb076_alpha_dummy_122 g b) ∈
      (((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv ∪
        ((syn_cphi (Class.cv (nb076_alpha_dummy_122 g b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0162 :
    (nb076_alpha_dummy_001) ∈
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0163 :
    (nb076_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0164 (g : Var) (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0165 (g : Var) (a : Var) (b : Var) :
    b ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0166 :
    (nb076_alpha_dummy_001) ∈
      (((Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
              (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_081)
            (syn_wrex (nb076_alpha_dummy_082) (syn_cxp (Class.cv (nb076_alpha_dummy_001))
                (Class.cv (nb076_alpha_dummy_002)))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_001) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0162) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0167 (g : Var) (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb076_alpha_dummy_083 g a b)
            (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
              (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0164 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0168 :
    (nb076_alpha_dummy_001) ∈
      (({(nb076_alpha_dummy_113)} : Finset Var) ∪ ({(nb076_alpha_dummy_114)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_113))
              (Class.cv (nb076_alpha_dummy_001)))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_114))
              (Class.cv (nb076_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0169 (g : Var) (b : Var) :
    b ∈
      (({(nb076_alpha_dummy_115 g b)} : Finset Var) ∪
          ({(nb076_alpha_dummy_116 g b)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb076_alpha_dummy_115 g b)) (Class.cv b))
            (Wff.classMem (Class.cv (nb076_alpha_dummy_116 g b)) (Class.cv g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0170 :
    (nb076_alpha_dummy_001) ∈
      (((Class.cv (nb076_alpha_dummy_001))).fv ∪ ((Class.cv (nb076_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0171 (g : Var) (b : Var) :
    b ∈ (((Class.cv b)).fv ∪ ((Class.cv g)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0172 :
    (nb076_alpha_dummy_002) ∈
      (((Class.cv (nb076_alpha_dummy_000))).fv ∪ ((syn_cxp (Class.cv (nb076_alpha_dummy_001))
            (Class.cv (nb076_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0173 :
    (nb076_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_081)
              (syn_wrex (nb076_alpha_dummy_082) (Class.cv (nb076_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_082)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_081) (syn_wrex (nb076_alpha_dummy_082)
                (syn_cxp (Class.cv (nb076_alpha_dummy_001)) (Class.cv (nb076_alpha_dummy_002)))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_081))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_082)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_081) from (by
          unfold nb076_alpha_dummy_081;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb076_alpha_dummy_002) ≠ (nb076_alpha_dummy_082) from (by
            unfold nb076_alpha_dummy_082;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0172) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb076_support_mem_0174 (g : Var) (a : Var) (b : Var) :
    g ∈ (((Class.cv a)).fv ∪ ((syn_cxp (Class.cv b) (Class.cv g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb076_support_mem_0175 (g : Var) (a : Var) (b : Var) :
    g ∈
      (((syn_ccompl (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb076_alpha_dummy_083 g a b)
              (syn_wrex (nb076_alpha_dummy_084 g a b) (syn_cxp (Class.cv b) (Class.cv g))
                (Wff.classEq (Class.cv (nb076_alpha_dummy_083 g a b))
                  (syn_cun (syn_cphi (Class.cv (nb076_alpha_dummy_084 g a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show g ≠ (nb076_alpha_dummy_083 g a b) from (by
          unfold nb076_alpha_dummy_083;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show g ≠ (nb076_alpha_dummy_084 g a b) from (by
            unfold nb076_alpha_dummy_084;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb076_support_mem_0174 g a b) 1))))
    · rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
