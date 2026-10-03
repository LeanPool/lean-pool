/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4H5C092M3Part001. -/


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
noncomputable def nb092_alpha_dummy_000 (R : Class) : Var :=
  (freshVar ((R).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_001 (R : Class) : Var :=
  (freshVar ((R).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_002 (R : Class) : Var :=
  (freshVar ((R).fv) 2)

@[expose]
noncomputable def nb092_alpha_dummy_003 (R : Class) : Var :=
  (freshVar ((R).fv) 3)

@[expose]
noncomputable def nb092_alpha_dummy_004 (R : Class) : Var :=
  (freshVar (({(nb092_alpha_dummy_000 R)} : Finset Var) ∪
        ({(nb092_alpha_dummy_001 R)} : Finset Var) ∪
      ((syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
          (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
            (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
              (Class.cv (nb092_alpha_dummy_003 R)))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_005 (x : Var) (y : Var) (R : Class) (a : Var)
    (b : Var) : Var :=
  (freshVar (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
          (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_006 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_001 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_007 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_001 R))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_008 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_009 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_010 (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_011 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_012 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_006 R)
          (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
              (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv ∪
      ((Class.cab (nb092_alpha_dummy_006 R)
          (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
              (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_013 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_008 a b)
          (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
              (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv ∪
      ((Class.cab (nb092_alpha_dummy_008 a b) (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
              (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_014 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_007 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_015 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_007 R))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_016 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_009 a b))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_017 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_009 a b))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_018 (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092_alpha_dummy_014 R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb092_alpha_dummy_014 R)) (syn_c1c))).fv ∪
      ((Class.cv (nb092_alpha_dummy_014 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_019 (a : Var) (b : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb092_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
      ((Class.cv (nb092_alpha_dummy_016 a b))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_020 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_021 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_022 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb092_alpha_dummy_023 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_024 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_025 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb092_alpha_dummy_026 (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
          (Class.cv (nb092_alpha_dummy_022 R)))).fv ∪
      ((syn_cnin (Class.cv (nb092_alpha_dummy_021 R)) (Class.cv (nb092_alpha_dummy_022 R)))).fv)
    0)

@[expose]
noncomputable def nb092_alpha_dummy_027 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
          (Class.cv (nb092_alpha_dummy_025 a b)))).fv ∪
      ((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
          (Class.cv (nb092_alpha_dummy_025 a b)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_028 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_022 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_029 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
      ((Class.cv (nb092_alpha_dummy_025 a b))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_030 (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb092_alpha_dummy_021 R)))).fv ∪
      ((syn_ccompl (Class.cv (nb092_alpha_dummy_022 R)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_031 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb092_alpha_dummy_024 a b)))).fv ∪
      ((syn_ccompl (Class.cv (nb092_alpha_dummy_025 a b)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_032 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_021 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_033 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
      ((Class.cv (nb092_alpha_dummy_024 a b))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_034 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_022 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_022 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_035 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_025 a b))).fv ∪
      ((Class.cv (nb092_alpha_dummy_025 a b))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_036 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_006 R)
          (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_006 R)
          (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_037 (a : Var) (b : Var) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_008 a b)
          (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_008 a b)
          (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_038 (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_039 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_040 (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv ∪
      ((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_041 (a : Var) (b : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv ∪
      ((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_042 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_003 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_043 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_003 R))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_044 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_045 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_046 (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_047 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_048 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_042 R)
          (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
              (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv ∪
      ((Class.cab (nb092_alpha_dummy_042 R)
          (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
              (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_049 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_044 x y)
          (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
              (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv ∪
      ((Class.cab (nb092_alpha_dummy_044 x y) (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
              (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_050 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_043 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_051 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_043 R))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_052 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_045 x y))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_053 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_045 x y))).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_054 (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092_alpha_dummy_050 R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb092_alpha_dummy_050 R)) (syn_c1c))).fv ∪
      ((Class.cv (nb092_alpha_dummy_050 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_055 (x : Var) (y : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb092_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb092_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
      ((Class.cv (nb092_alpha_dummy_052 x y))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_056 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_057 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_058 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb092_alpha_dummy_059 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_060 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb092_alpha_dummy_061 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb092_alpha_dummy_062 (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
          (Class.cv (nb092_alpha_dummy_058 R)))).fv ∪
      ((syn_cnin (Class.cv (nb092_alpha_dummy_057 R)) (Class.cv (nb092_alpha_dummy_058 R)))).fv)
    0)

@[expose]
noncomputable def nb092_alpha_dummy_063 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
          (Class.cv (nb092_alpha_dummy_061 x y)))).fv ∪
      ((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
          (Class.cv (nb092_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_064 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_058 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_065 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb092_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_066 (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb092_alpha_dummy_057 R)))).fv ∪
      ((syn_ccompl (Class.cv (nb092_alpha_dummy_058 R)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_067 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb092_alpha_dummy_060 x y)))).fv ∪
      ((syn_ccompl (Class.cv (nb092_alpha_dummy_061 x y)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_068 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_057 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_069 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
      ((Class.cv (nb092_alpha_dummy_060 x y))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_070 (R : Class) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_058 R))).fv ∪
      ((Class.cv (nb092_alpha_dummy_058 R))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_071 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cv (nb092_alpha_dummy_061 x y))).fv ∪
      ((Class.cv (nb092_alpha_dummy_061 x y))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_072 (R : Class) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_042 R)
          (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_042 R)
          (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
            (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_073 (x : Var) (y : Var) : Var :=
  (freshVar (((Class.cab (nb092_alpha_dummy_044 x y)
          (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_044 x y)
          (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
            (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
              (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_074 (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_075 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_076 (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv ∪
      ((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv) 0)

@[expose]
noncomputable def nb092_alpha_dummy_077 (x : Var) (y : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv ∪
      ((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv) 0)

theorem nb092_fresh_000 (R : Class) :
    (nb092_alpha_dummy_012 R) ∉
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_012] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv)
      0

theorem nb092_fresh_001 (R : Class) :
    (nb092_alpha_dummy_036 R) ∉
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb092_fresh_002 (a : Var) (b : Var) :
    (nb092_alpha_dummy_013 a b) ∉
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv)
      0

theorem nb092_fresh_003 (a : Var) (b : Var) :
    (nb092_alpha_dummy_037 a b) ∉
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb092_fresh_004 (R : Class) :
    (nb092_alpha_dummy_048 R) ∉
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv)
      0

theorem nb092_fresh_005 (R : Class) :
    (nb092_alpha_dummy_072 R) ∉
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_072] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb092_fresh_006 (x : Var) (y : Var) :
    (nb092_alpha_dummy_049 x y) ∉
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_049] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv)
      0

theorem nb092_fresh_007 (x : Var) (y : Var) :
    (nb092_alpha_dummy_073 x y) ∉
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb092_fresh_008 (a : Var) (b : Var) :
    (nb092_alpha_dummy_008 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb092_alpha_dummy_008] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 0

theorem nb092_fresh_009 (a : Var) (b : Var) :
    (nb092_alpha_dummy_009 a b) ∉ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) := by
  simpa only [nb092_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv a)).fv ∪ ((Class.cv b)).fv) 1

theorem nb092_distinct_010 (a : Var) (b : Var) :
    (nb092_alpha_dummy_008 a b) ≠ (nb092_alpha_dummy_009 a b) := by
  simpa only [nb092_alpha_dummy_008, nb092_alpha_dummy_009] using
    (freshVar_injective (((Class.cv a)).fv ∪ ((Class.cv b)).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_011 (R : Class) :
    (nb092_alpha_dummy_006 R) ∉
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv)
      0

theorem nb092_fresh_012 (R : Class) :
    (nb092_alpha_dummy_007 R) ∉
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv)
      1

theorem nb092_distinct_013 (R : Class) :
    (nb092_alpha_dummy_006 R) ≠ (nb092_alpha_dummy_007 R) := by
  simpa only [nb092_alpha_dummy_006, nb092_alpha_dummy_007] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪
        ((Class.cv (nb092_alpha_dummy_001 R))).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_014 (R : Class) :
    (nb092_alpha_dummy_042 R) ∉
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_042] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv)
      0

theorem nb092_fresh_015 (R : Class) :
    (nb092_alpha_dummy_043 R) ∉
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv)
      1

theorem nb092_distinct_016 (R : Class) :
    (nb092_alpha_dummy_042 R) ≠ (nb092_alpha_dummy_043 R) := by
  simpa only [nb092_alpha_dummy_042, nb092_alpha_dummy_043] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪
        ((Class.cv (nb092_alpha_dummy_003 R))).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_017 (R : Class) :
    (nb092_alpha_dummy_014 R) ∉ (((Class.cv (nb092_alpha_dummy_007 R))).fv) := by
  simpa only [nb092_alpha_dummy_014] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_007 R))).fv) 0

theorem nb092_fresh_018 (R : Class) :
    (nb092_alpha_dummy_015 R) ∉ (((Class.cv (nb092_alpha_dummy_007 R))).fv) := by
  simpa only [nb092_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_007 R))).fv) 1

theorem nb092_distinct_019 (R : Class) :
    (nb092_alpha_dummy_014 R) ≠ (nb092_alpha_dummy_015 R) := by
  simpa only [nb092_alpha_dummy_014, nb092_alpha_dummy_015] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_007 R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_020 (a : Var) (b : Var) :
    (nb092_alpha_dummy_016 a b) ∉ (((Class.cv (nb092_alpha_dummy_009 a b))).fv) := by
  simpa only [nb092_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_009 a b))).fv) 0

theorem nb092_fresh_021 (a : Var) (b : Var) :
    (nb092_alpha_dummy_017 a b) ∉ (((Class.cv (nb092_alpha_dummy_009 a b))).fv) := by
  simpa only [nb092_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_009 a b))).fv) 1

theorem nb092_distinct_022 (a : Var) (b : Var) :
    (nb092_alpha_dummy_016 a b) ≠ (nb092_alpha_dummy_017 a b) := by
  simpa only [nb092_alpha_dummy_016, nb092_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_009 a b))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_023 (R : Class) :
    (nb092_alpha_dummy_020 R) ∉
      (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_020] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb092_fresh_024 (R : Class) :
    (nb092_alpha_dummy_021 R) ∉
      (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb092_fresh_025 (R : Class) :
    (nb092_alpha_dummy_022 R) ∉
      (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb092_distinct_026 (R : Class) :
    (nb092_alpha_dummy_020 R) ≠ (nb092_alpha_dummy_021 R) := by
  simpa only [nb092_alpha_dummy_020, nb092_alpha_dummy_021] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb092_distinct_027 (R : Class) :
    (nb092_alpha_dummy_020 R) ≠ (nb092_alpha_dummy_022 R) := by
  simpa only [nb092_alpha_dummy_020, nb092_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb092_distinct_028 (R : Class) :
    (nb092_alpha_dummy_021 R) ≠ (nb092_alpha_dummy_022 R) := by
  simpa only [nb092_alpha_dummy_021, nb092_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb092_fresh_029 (a : Var) (b : Var) :
    (nb092_alpha_dummy_023 a b) ∉
      (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 0

theorem nb092_fresh_030 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ∉
      (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 1

theorem nb092_fresh_031 (a : Var) (b : Var) :
    (nb092_alpha_dummy_025 a b) ∉
      (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) 2

theorem nb092_distinct_032 (a : Var) (b : Var) :
    (nb092_alpha_dummy_023 a b) ≠ (nb092_alpha_dummy_024 a b) := by
  simpa only [nb092_alpha_dummy_023, nb092_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb092_distinct_033 (a : Var) (b : Var) :
    (nb092_alpha_dummy_023 a b) ≠ (nb092_alpha_dummy_025 a b) := by
  simpa only [nb092_alpha_dummy_023, nb092_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb092_distinct_034 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ≠ (nb092_alpha_dummy_025 a b) := by
  simpa only [nb092_alpha_dummy_024, nb092_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb092_fresh_035 (R : Class) :
    (nb092_alpha_dummy_032 R) ∉
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_021 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_032] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_021 R))).fv)
      0

theorem nb092_fresh_036 (R : Class) :
    (nb092_alpha_dummy_028 R) ∉
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_028] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv)
      0

theorem nb092_fresh_037 (R : Class) :
    (nb092_alpha_dummy_034 R) ∉
      (((Class.cv (nb092_alpha_dummy_022 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_022 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv)
      0

theorem nb092_fresh_038 (a : Var) (b : Var) :
    (nb092_alpha_dummy_033 a b) ∉
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_024 a b))).fv) :=
  by
  simpa only [nb092_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_024 a b))).fv)
      0

theorem nb092_fresh_039 (a : Var) (b : Var) :
    (nb092_alpha_dummy_029 a b) ∉
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv) :=
  by
  simpa only [nb092_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv)
      0

theorem nb092_fresh_040 (a : Var) (b : Var) :
    (nb092_alpha_dummy_035 a b) ∉
      (((Class.cv (nb092_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv) :=
  by
  simpa only [nb092_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv)
      0

theorem nb092_fresh_041 (R : Class) :
    (nb092_alpha_dummy_050 R) ∉ (((Class.cv (nb092_alpha_dummy_043 R))).fv) := by
  simpa only [nb092_alpha_dummy_050] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_043 R))).fv) 0

theorem nb092_fresh_042 (R : Class) :
    (nb092_alpha_dummy_051 R) ∉ (((Class.cv (nb092_alpha_dummy_043 R))).fv) := by
  simpa only [nb092_alpha_dummy_051] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_043 R))).fv) 1

theorem nb092_distinct_043 (R : Class) :
    (nb092_alpha_dummy_050 R) ≠ (nb092_alpha_dummy_051 R) := by
  simpa only [nb092_alpha_dummy_050, nb092_alpha_dummy_051] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_043 R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_044 (x : Var) (y : Var) :
    (nb092_alpha_dummy_052 x y) ∉ (((Class.cv (nb092_alpha_dummy_045 x y))).fv) := by
  simpa only [nb092_alpha_dummy_052] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_045 x y))).fv) 0

theorem nb092_fresh_045 (x : Var) (y : Var) :
    (nb092_alpha_dummy_053 x y) ∉ (((Class.cv (nb092_alpha_dummy_045 x y))).fv) := by
  simpa only [nb092_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_045 x y))).fv) 1

theorem nb092_distinct_046 (x : Var) (y : Var) :
    (nb092_alpha_dummy_052 x y) ≠ (nb092_alpha_dummy_053 x y) := by
  simpa only [nb092_alpha_dummy_052, nb092_alpha_dummy_053] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_045 x y))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb092_fresh_047 (R : Class) :
    (nb092_alpha_dummy_056 R) ∉
      (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb092_fresh_048 (R : Class) :
    (nb092_alpha_dummy_057 R) ∉
      (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb092_fresh_049 (R : Class) :
    (nb092_alpha_dummy_058 R) ∉
      (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb092_distinct_050 (R : Class) :
    (nb092_alpha_dummy_056 R) ≠ (nb092_alpha_dummy_057 R) := by
  simpa only [nb092_alpha_dummy_056, nb092_alpha_dummy_057] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb092_distinct_051 (R : Class) :
    (nb092_alpha_dummy_056 R) ≠ (nb092_alpha_dummy_058 R) := by
  simpa only [nb092_alpha_dummy_056, nb092_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb092_distinct_052 (R : Class) :
    (nb092_alpha_dummy_057 R) ≠ (nb092_alpha_dummy_058 R) := by
  simpa only [nb092_alpha_dummy_057, nb092_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb092_fresh_053 (x : Var) (y : Var) :
    (nb092_alpha_dummy_059 x y) ∉
      (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_059] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 0

theorem nb092_fresh_054 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ∉
      (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 1

theorem nb092_fresh_055 (x : Var) (y : Var) :
    (nb092_alpha_dummy_061 x y) ∉
      (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb092_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) 2

theorem nb092_distinct_056 (x : Var) (y : Var) :
    (nb092_alpha_dummy_059 x y) ≠ (nb092_alpha_dummy_060 x y) := by
  simpa only [nb092_alpha_dummy_059, nb092_alpha_dummy_060] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb092_distinct_057 (x : Var) (y : Var) :
    (nb092_alpha_dummy_059 x y) ≠ (nb092_alpha_dummy_061 x y) := by
  simpa only [nb092_alpha_dummy_059, nb092_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb092_distinct_058 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ≠ (nb092_alpha_dummy_061 x y) := by
  simpa only [nb092_alpha_dummy_060, nb092_alpha_dummy_061] using
    (freshVar_injective (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb092_fresh_059 (R : Class) :
    (nb092_alpha_dummy_068 R) ∉
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_057 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_068] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_057 R))).fv)
      0

theorem nb092_fresh_060 (R : Class) :
    (nb092_alpha_dummy_064 R) ∉
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_064] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv)
      0

theorem nb092_fresh_061 (R : Class) :
    (nb092_alpha_dummy_070 R) ∉
      (((Class.cv (nb092_alpha_dummy_058 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_058 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv)
      0

theorem nb092_fresh_062 (x : Var) (y : Var) :
    (nb092_alpha_dummy_069 x y) ∉
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_060 x y))).fv) :=
  by
  simpa only [nb092_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_060 x y))).fv)
      0

theorem nb092_fresh_063 (x : Var) (y : Var) :
    (nb092_alpha_dummy_065 x y) ∉
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb092_alpha_dummy_065] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv)
      0

theorem nb092_fresh_064 (x : Var) (y : Var) :
    (nb092_alpha_dummy_071 x y) ∉
      (((Class.cv (nb092_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv) :=
  by
  simpa only [nb092_alpha_dummy_071] using
    freshVar_not_mem
      (((Class.cv (nb092_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv)
      0

theorem nb092_fresh_065 (x : Var) (y : Var) :
    (nb092_alpha_dummy_044 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb092_alpha_dummy_044] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0

theorem nb092_fresh_066 (x : Var) (y : Var) :
    (nb092_alpha_dummy_045 x y) ∉ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) := by
  simpa only [nb092_alpha_dummy_045] using
    freshVar_not_mem (((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1

theorem nb092_distinct_067 (x : Var) (y : Var) :
    (nb092_alpha_dummy_044 x y) ≠ (nb092_alpha_dummy_045 x y) := by
  simpa only [nb092_alpha_dummy_044, nb092_alpha_dummy_045] using
    (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (i := 0) (j := 1) (by decide))

theorem nb092_fresh_068 (R : Class) :
    (nb092_alpha_dummy_018 R) ∉
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_014 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_014 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_014 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_018] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_014 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_014 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_014 R))).fv)
      0

theorem nb092_fresh_069 (a : Var) (b : Var) :
    (nb092_alpha_dummy_019 a b) ∉
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_016 a b))).fv) :=
  by
  simpa only [nb092_alpha_dummy_019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_016 a b))).fv)
      0

theorem nb092_fresh_070 (R : Class) :
    (nb092_alpha_dummy_054 R) ∉
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_050 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_050 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_050 R))).fv) :=
  by
  simpa only [nb092_alpha_dummy_054] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_050 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_050 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_050 R))).fv)
      0

theorem nb092_fresh_071 (x : Var) (y : Var) :
    (nb092_alpha_dummy_055 x y) ∉
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_052 x y))).fv) :=
  by
  simpa only [nb092_alpha_dummy_055] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_052 x y))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb092_fresh_072 (R : Class) :
    (nb092_alpha_dummy_010 R) ∉
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb092_fresh_073 (a : Var) (b : Var) :
    (nb092_alpha_dummy_011 a b) ∉
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb092_fresh_074 (R : Class) :
    (nb092_alpha_dummy_046 R) ∉
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb092_fresh_075 (x : Var) (y : Var) :
    (nb092_alpha_dummy_047 x y) ∉
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb092_fresh_076 (R : Class) :
    (nb092_alpha_dummy_030 R) ∉
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_021 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_030] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_021 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_022 R)))).fv)
      0

theorem nb092_fresh_077 (a : Var) (b : Var) :
    (nb092_alpha_dummy_031 a b) ∉
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_031] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_025 a b)))).fv)
      0

theorem nb092_fresh_078 (R : Class) :
    (nb092_alpha_dummy_066 R) ∉
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_057 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_066] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_057 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_058 R)))).fv)
      0

theorem nb092_fresh_079 (x : Var) (y : Var) :
    (nb092_alpha_dummy_067 x y) ∉
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_061 x y)))).fv)
      0

theorem nb092_fresh_080 (R : Class) :
    (nb092_alpha_dummy_038 R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb092_fresh_081 (a : Var) (b : Var) :
    (nb092_alpha_dummy_039 a b) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb092_fresh_082 (R : Class) :
    (nb092_alpha_dummy_074 R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_074] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb092_fresh_083 (x : Var) (y : Var) :
    (nb092_alpha_dummy_075 x y) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_075] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb092_fresh_084 (R : Class) :
    (nb092_alpha_dummy_026 R) ∉
      (((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv)
      0

theorem nb092_fresh_085 (a : Var) (b : Var) :
    (nb092_alpha_dummy_027 a b) ∉
      (((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv)
      0

theorem nb092_fresh_086 (R : Class) :
    (nb092_alpha_dummy_062 R) ∉
      (((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv)
      0

theorem nb092_fresh_087 (x : Var) (y : Var) :
    (nb092_alpha_dummy_063 x y) ∉
      (((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_063] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv)
      0

theorem nb092_fresh_088 (R : Class) :
    (nb092_alpha_dummy_040 R) ∉
      (((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv)
      0

theorem nb092_fresh_089 (a : Var) (b : Var) :
    (nb092_alpha_dummy_041 a b) ∉
      (((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv)
      0

theorem nb092_fresh_090 (R : Class) :
    (nb092_alpha_dummy_076 R) ∉
      (((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_076] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv)
      0

theorem nb092_fresh_091 (x : Var) (y : Var) :
    (nb092_alpha_dummy_077 x y) ∉
      (((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv) :=
  by
  simpa only [nb092_alpha_dummy_077] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv)
      0

theorem nb092_fresh_092 (R : Class) : (nb092_alpha_dummy_000 R) ∉ ((R).fv) := by
  simpa only [nb092_alpha_dummy_000] using freshVar_not_mem ((R).fv) 0

theorem nb092_fresh_093 (R : Class) : (nb092_alpha_dummy_001 R) ∉ ((R).fv) := by
  simpa only [nb092_alpha_dummy_001] using freshVar_not_mem ((R).fv) 1

theorem nb092_fresh_094 (R : Class) : (nb092_alpha_dummy_002 R) ∉ ((R).fv) := by
  simpa only [nb092_alpha_dummy_002] using freshVar_not_mem ((R).fv) 2

theorem nb092_fresh_095 (R : Class) : (nb092_alpha_dummy_003 R) ∉ ((R).fv) := by
  simpa only [nb092_alpha_dummy_003] using freshVar_not_mem ((R).fv) 3

theorem nb092_distinct_096 (R : Class) :
    (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_001 R) := by
  simpa only [nb092_alpha_dummy_000, nb092_alpha_dummy_001] using
    (freshVar_injective ((R).fv) (i := 0) (j := 1) (by decide))

theorem nb092_distinct_097 (R : Class) :
    (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_002 R) := by
  simpa only [nb092_alpha_dummy_000, nb092_alpha_dummy_002] using
    (freshVar_injective ((R).fv) (i := 0) (j := 2) (by decide))

theorem nb092_distinct_098 (R : Class) :
    (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_003 R) := by
  simpa only [nb092_alpha_dummy_000, nb092_alpha_dummy_003] using
    (freshVar_injective ((R).fv) (i := 0) (j := 3) (by decide))

theorem nb092_distinct_099 (R : Class) :
    (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_002 R) := by
  simpa only [nb092_alpha_dummy_001, nb092_alpha_dummy_002] using
    (freshVar_injective ((R).fv) (i := 1) (j := 2) (by decide))

theorem nb092_distinct_100 (R : Class) :
    (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_003 R) := by
  simpa only [nb092_alpha_dummy_001, nb092_alpha_dummy_003] using
    (freshVar_injective ((R).fv) (i := 1) (j := 3) (by decide))

theorem nb092_distinct_101 (R : Class) :
    (nb092_alpha_dummy_002 R) ≠ (nb092_alpha_dummy_003 R) := by
  simpa only [nb092_alpha_dummy_002, nb092_alpha_dummy_003] using
    (freshVar_injective ((R).fv) (i := 2) (j := 3) (by decide))

theorem nb092_fresh_102 (R : Class) :
    (nb092_alpha_dummy_004 R) ∉
      (({(nb092_alpha_dummy_000 R)} : Finset Var) ∪ ({(nb092_alpha_dummy_001 R)} : Finset Var) ∪
        ((syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
            (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
              (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
                (Class.cv (nb092_alpha_dummy_003 R)))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_004] using
    freshVar_not_mem
      (({(nb092_alpha_dummy_000 R)} : Finset Var) ∪ ({(nb092_alpha_dummy_001 R)} : Finset Var) ∪
        ((syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
            (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
              (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
                (Class.cv (nb092_alpha_dummy_003 R)))))).fv)
      0

theorem nb092_fresh_103 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    (nb092_alpha_dummy_005 x y R a b) ∉
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  simpa only [nb092_alpha_dummy_005] using
    freshVar_not_mem
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y))))).fv)
      0

theorem nb092_support_mem_0000 (R : Class) :
    (nb092_alpha_dummy_000 R) ∈
      (({(nb092_alpha_dummy_000 R)} : Finset Var) ∪ ({(nb092_alpha_dummy_001 R)} : Finset Var) ∪
        ((syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
            (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
              (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
                (Class.cv (nb092_alpha_dummy_003 R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0001 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    a ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0002 (R : Class) :
    (nb092_alpha_dummy_001 R) ∈
      (({(nb092_alpha_dummy_000 R)} : Finset Var) ∪ ({(nb092_alpha_dummy_001 R)} : Finset Var) ∪
        ((syn_wrex (nb092_alpha_dummy_002 R) (Class.cv (nb092_alpha_dummy_000 R))
            (syn_wrex (nb092_alpha_dummy_003 R) (Class.cv (nb092_alpha_dummy_001 R))
              (syn_wbr (Class.cv (nb092_alpha_dummy_002 R)) R
                (Class.cv (nb092_alpha_dummy_003 R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0003 (x : Var) (y : Var) (R : Class) (a : Var) (b : Var) :
    b ∈
      (({ a } : Finset Var) ∪ ({ b } : Finset Var) ∪ ((syn_wrex x (Class.cv a)
            (syn_wrex y (Class.cv b) (syn_wbr (Class.cv x) R (Class.cv y))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0004 (R : Class) :
    (nb092_alpha_dummy_000 R) ∈
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0005 (R : Class) :
    (nb092_alpha_dummy_000 R) ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_006 R) from (by
          unfold nb092_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_007 R) from (by
            unfold nb092_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0006 (a : Var) (b : Var) :
    a ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0007 (a : Var) (b : Var) :
    a ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb092_alpha_dummy_008 a b) from (by
          unfold nb092_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb092_alpha_dummy_009 a b) from (by
            unfold nb092_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0008 (R : Class) :
    (nb092_alpha_dummy_000 R) ∈
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_006 R) from (by
          unfold nb092_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_000 R) ≠ (nb092_alpha_dummy_007 R) from (by
            unfold nb092_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0004 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0009 (a : Var) (b : Var) :
    a ∈
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show a ≠ (nb092_alpha_dummy_008 a b) from (by
          unfold nb092_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show a ≠ (nb092_alpha_dummy_009 a b) from (by
            unfold nb092_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0006 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0010 (R : Class) :
    (nb092_alpha_dummy_007 R) ∈ (((Class.cv (nb092_alpha_dummy_007 R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0011 (a : Var) (b : Var) :
    (nb092_alpha_dummy_009 a b) ∈ (((Class.cv (nb092_alpha_dummy_009 a b))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0012 (R : Class) :
    (nb092_alpha_dummy_014 R) ∈
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_014 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_014 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_014 R))).fv) :=
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

theorem nb092_support_mem_0013 (a : Var) (b : Var) :
    (nb092_alpha_dummy_016 a b) ∈
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_016 a b)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_016 a b)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_016 a b))).fv) :=
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

theorem nb092_support_mem_0014 (R : Class) :
    (nb092_alpha_dummy_014 R) ∈
      (((Class.cv (nb092_alpha_dummy_014 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0015 (a : Var) (b : Var) :
    (nb092_alpha_dummy_016 a b) ∈
      (((Class.cv (nb092_alpha_dummy_016 a b))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0016 (R : Class) :
    (nb092_alpha_dummy_021 R) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0017 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0018 (R : Class) :
    (nb092_alpha_dummy_021 R) ∈
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0019 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ∈
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0020 (R : Class) :
    (nb092_alpha_dummy_022 R) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_021 R))
            (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0021 (a : Var) (b : Var) :
    (nb092_alpha_dummy_025 a b) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_024 a b))
            (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0022 (R : Class) :
    (nb092_alpha_dummy_022 R) ∈
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0023 (a : Var) (b : Var) :
    (nb092_alpha_dummy_025 a b) ∈
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0024 (R : Class) :
    (nb092_alpha_dummy_021 R) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_021 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0025 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0026 (R : Class) :
    (nb092_alpha_dummy_021 R) ∈
      (((Class.cv (nb092_alpha_dummy_021 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_021 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0027 (a : Var) (b : Var) :
    (nb092_alpha_dummy_024 a b) ∈
      (((Class.cv (nb092_alpha_dummy_024 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_024 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0028 (R : Class) :
    (nb092_alpha_dummy_022 R) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_021 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_022 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0029 (a : Var) (b : Var) :
    (nb092_alpha_dummy_025 a b) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_024 a b)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_025 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0030 (R : Class) :
    (nb092_alpha_dummy_022 R) ∈
      (((Class.cv (nb092_alpha_dummy_022 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_022 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0031 (a : Var) (b : Var) :
    (nb092_alpha_dummy_025 a b) ∈
      (((Class.cv (nb092_alpha_dummy_025 a b))).fv ∪
        ((Class.cv (nb092_alpha_dummy_025 a b))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0032 (R : Class) :
    (nb092_alpha_dummy_001 R) ∈
      (((Class.cv (nb092_alpha_dummy_000 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_001 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0033 (R : Class) :
    (nb092_alpha_dummy_001 R) ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_000 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_006 R)
              (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_006 R) from (by
          unfold nb092_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_007 R) from (by
            unfold nb092_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0034 (a : Var) (b : Var) :
    b ∈ (((Class.cv a)).fv ∪ ((Class.cv b)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0035 (a : Var) (b : Var) :
    b ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv a)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_008 a b)
              (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb092_alpha_dummy_008 a b) from (by
          unfold nb092_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb092_alpha_dummy_009 a b) from (by
            unfold nb092_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0036 (R : Class) :
    (nb092_alpha_dummy_001 R) ∈
      (((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_006 R)
            (syn_wrex (nb092_alpha_dummy_007 R) (Class.cv (nb092_alpha_dummy_001 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_006 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_006 R) from (by
          unfold nb092_alpha_dummy_006;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_001 R) ≠ (nb092_alpha_dummy_007 R) from (by
            unfold nb092_alpha_dummy_007;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0032 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0037 (a : Var) (b : Var) :
    b ∈
      (((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_008 a b)
            (syn_wrex (nb092_alpha_dummy_009 a b) (Class.cv b)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_008 a b))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show b ≠ (nb092_alpha_dummy_008 a b) from (by
          unfold nb092_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show b ≠ (nb092_alpha_dummy_009 a b) from (by
            unfold nb092_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0034 a b) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0038 (R : Class) :
    (nb092_alpha_dummy_007 R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_007 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0039 (a : Var) (b : Var) :
    (nb092_alpha_dummy_009 a b) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_009 a b))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0040 (R : Class) :
    (nb092_alpha_dummy_007 R) ∈
      (((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_007 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0041 (a : Var) (b : Var) :
    (nb092_alpha_dummy_009 a b) ∈
      (((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_009 a b)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0042 (R : Class) :
    (nb092_alpha_dummy_002 R) ∈
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0043 (R : Class) :
    (nb092_alpha_dummy_002 R) ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_002 R) ≠ (nb092_alpha_dummy_042 R) from (by
          unfold nb092_alpha_dummy_042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_002 R) ≠ (nb092_alpha_dummy_043 R) from (by
            unfold nb092_alpha_dummy_043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0044 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0045 (x : Var) (y : Var) :
    x ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb092_alpha_dummy_044 x y) from (by
          unfold nb092_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb092_alpha_dummy_045 x y) from (by
            unfold nb092_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0046 (R : Class) :
    (nb092_alpha_dummy_002 R) ∈
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_002 R) ≠ (nb092_alpha_dummy_042 R) from (by
          unfold nb092_alpha_dummy_042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_002 R) ≠ (nb092_alpha_dummy_043 R) from (by
            unfold nb092_alpha_dummy_043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0042 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0047 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv ∪
        ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show x ≠ (nb092_alpha_dummy_044 x y) from (by
          unfold nb092_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show x ≠ (nb092_alpha_dummy_045 x y) from (by
            unfold nb092_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0044 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0048 (R : Class) :
    (nb092_alpha_dummy_043 R) ∈ (((Class.cv (nb092_alpha_dummy_043 R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0049 (x : Var) (y : Var) :
    (nb092_alpha_dummy_045 x y) ∈ (((Class.cv (nb092_alpha_dummy_045 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0050 (R : Class) :
    (nb092_alpha_dummy_050 R) ∈
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_050 R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_050 R)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_050 R))).fv) :=
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

theorem nb092_support_mem_0051 (x : Var) (y : Var) :
    (nb092_alpha_dummy_052 x y) ∈
      (((Wff.classMem (Class.cv (nb092_alpha_dummy_052 x y)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb092_alpha_dummy_052 x y)) (syn_c1c))).fv ∪
        ((Class.cv (nb092_alpha_dummy_052 x y))).fv) :=
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

theorem nb092_support_mem_0052 (R : Class) :
    (nb092_alpha_dummy_050 R) ∈
      (((Class.cv (nb092_alpha_dummy_050 R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0053 (x : Var) (y : Var) :
    (nb092_alpha_dummy_052 x y) ∈
      (((Class.cv (nb092_alpha_dummy_052 x y))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0054 (R : Class) :
    (nb092_alpha_dummy_057 R) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0055 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0056 (R : Class) :
    (nb092_alpha_dummy_057 R) ∈
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0057 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ∈
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0058 (R : Class) :
    (nb092_alpha_dummy_058 R) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_057 R))
            (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0059 (x : Var) (y : Var) :
    (nb092_alpha_dummy_061 x y) ∈
      (((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb092_alpha_dummy_060 x y))
            (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0060 (R : Class) :
    (nb092_alpha_dummy_058 R) ∈
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0061 (x : Var) (y : Var) :
    (nb092_alpha_dummy_061 x y) ∈
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0062 (R : Class) :
    (nb092_alpha_dummy_057 R) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_057 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0063 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0064 (R : Class) :
    (nb092_alpha_dummy_057 R) ∈
      (((Class.cv (nb092_alpha_dummy_057 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_057 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0065 (x : Var) (y : Var) :
    (nb092_alpha_dummy_060 x y) ∈
      (((Class.cv (nb092_alpha_dummy_060 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_060 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0066 (R : Class) :
    (nb092_alpha_dummy_058 R) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_057 R)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_058 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0067 (x : Var) (y : Var) :
    (nb092_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb092_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb092_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0068 (R : Class) :
    (nb092_alpha_dummy_058 R) ∈
      (((Class.cv (nb092_alpha_dummy_058 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_058 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0069 (x : Var) (y : Var) :
    (nb092_alpha_dummy_061 x y) ∈
      (((Class.cv (nb092_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb092_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0070 (R : Class) :
    (nb092_alpha_dummy_003 R) ∈
      (((Class.cv (nb092_alpha_dummy_002 R))).fv ∪ ((Class.cv (nb092_alpha_dummy_003 R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0071 (R : Class) :
    (nb092_alpha_dummy_003 R) ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_002 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_042 R)
              (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
                (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_003 R) ≠ (nb092_alpha_dummy_042 R) from (by
          unfold nb092_alpha_dummy_042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_003 R) ≠ (nb092_alpha_dummy_043 R) from (by
            unfold nb092_alpha_dummy_043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0072 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0073 (x : Var) (y : Var) :
    y ∈
      (((syn_ccompl (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb092_alpha_dummy_044 x y)
              (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                  (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb092_alpha_dummy_044 x y) from (by
          unfold nb092_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb092_alpha_dummy_045 x y) from (by
            unfold nb092_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0074 (R : Class) :
    (nb092_alpha_dummy_003 R) ∈
      (((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_042 R)
            (syn_wrex (nb092_alpha_dummy_043 R) (Class.cv (nb092_alpha_dummy_003 R))
              (Wff.classEq (Class.cv (nb092_alpha_dummy_042 R))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb092_alpha_dummy_003 R) ≠ (nb092_alpha_dummy_042 R) from (by
          unfold nb092_alpha_dummy_042;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb092_alpha_dummy_003 R) ≠ (nb092_alpha_dummy_043 R) from (by
            unfold nb092_alpha_dummy_043;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0070 R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0075 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb092_alpha_dummy_044 x y)
            (syn_wrex (nb092_alpha_dummy_045 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb092_alpha_dummy_044 x y))
                (syn_cun (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show y ≠ (nb092_alpha_dummy_044 x y) from (by
          unfold nb092_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show y ≠ (nb092_alpha_dummy_045 x y) from (by
            unfold nb092_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb092_support_mem_0072 x y) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb092_support_mem_0076 (R : Class) :
    (nb092_alpha_dummy_043 R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_043 R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0077 (x : Var) (y : Var) :
    (nb092_alpha_dummy_045 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb092_alpha_dummy_045 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0078 (R : Class) :
    (nb092_alpha_dummy_043 R) ∈
      (((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_043 R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb092_support_mem_0079 (x : Var) (y : Var) :
    (nb092_alpha_dummy_045 x y) ∈
      (((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb092_alpha_dummy_045 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
