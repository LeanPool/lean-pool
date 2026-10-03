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

/-! Certificates from `NAR4C089C001Part001`. -/


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
noncomputable def nb089_alpha_dummy_000 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_001 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_wbr R (syn_cwe) A)).fv ∪
        ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
            (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪ ((syn_c0)).fv)
    0)

@[expose]
noncomputable def nb089_alpha_dummy_002 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
            (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_003 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
        ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
      ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_004 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
      ((syn_cfdrowfib R A B (Class.cv u))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_005 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
        ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
          (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
            (syn_cpw1 (syn_cpw1 (syn_cuni A))))
          (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
            (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_006 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
          (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
            (syn_cfdrowfib R A B (Class.cv u))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_007 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_008 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_009 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_010 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_011 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R)
            (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_012 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
              (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_013 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_007 A B R)
          (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪
      ((Class.cab (nb089_alpha_dummy_007 A B R)
          (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_014 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_009 u A B R)
          (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪
      ((Class.cab (nb089_alpha_dummy_009 u A B R)
          (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_015 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_016 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_017 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_018 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_019 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪
      ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_020 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪
      ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_021 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_022 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_023 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb089_alpha_dummy_024 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_025 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_026 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb089_alpha_dummy_027 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
          (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪
      ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
          (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_028 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
          (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪
      ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
          (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_029 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_030 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_031 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪
      ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_032 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪
      ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_033 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_034 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_035 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_036 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_037 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_007 A B R)
          (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R)
          (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_038 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_009 u A B R)
          (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R)
          (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_039 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_040 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_041 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪
      ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_042 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪
      ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_043 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_044 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_045 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
      ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_046 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
      ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_047 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_048 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_049 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R)
            (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_050 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_051 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
            (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪
      ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
            (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_052 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_047 u A B R)
          (syn_wrex (nb089_alpha_dummy_048 u A B R)
            (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪
      ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
            (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
              (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_053 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_054 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_055 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_056 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_057 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_058 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_059 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪
      ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_060 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪
      ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_061 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_062 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_063 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb089_alpha_dummy_064 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_065 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb089_alpha_dummy_066 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb089_alpha_dummy_067 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
          (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪
      ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
          (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_068 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
          (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪
      ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
          (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_069 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_070 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_071 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪
      ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_072 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪
      ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_073 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_074 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_075 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_076 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪
      ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_077 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_045 A B R)
          (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R)
          (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_078 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((Class.cab (nb089_alpha_dummy_047 u A B R)
          (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R)
          (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
            (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
              (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_079 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_080 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_081 (A : Class) (B : Class) (R : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪
      ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) 0)

@[expose]
noncomputable def nb089_alpha_dummy_082 (u : Var) (A : Class) (B : Class) (R : Class) :
    Var :=
  (freshVar (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪
      ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) 0)

theorem nb089_fresh_000 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_013 A B R) ∉
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_013] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv)
      0

theorem nb089_fresh_001 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_037 A B R) ∉
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R)
            (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R)
            (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb089_fresh_002 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_038 u A B R) ∉
      (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
              (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
              (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb089_fresh_003 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_014 u A B R) ∉
      (((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv)
      0

theorem nb089_fresh_004 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_077 A B R) ∉
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R)
            (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_077] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R)
            (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb089_fresh_005 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_051 A B R) ∉
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv)
      0

theorem nb089_fresh_006 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_078 u A B R) ∉
      (((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_078] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb089_fresh_007 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_052 u A B R) ∉
      (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv)
      0

theorem nb089_fresh_008 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_007 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv)
      0

theorem nb089_fresh_009 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_008 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv)
      1

theorem nb089_distinct_010 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_007 A B R) ≠ (nb089_alpha_dummy_008 A B R) := by
  simpa only [nb089_alpha_dummy_007, nb089_alpha_dummy_008] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_011 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_015 A B R) ∉ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_015] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 0

theorem nb089_fresh_012 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_016 A B R) ∉ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) 1

theorem nb089_distinct_013 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_015 A B R) ≠ (nb089_alpha_dummy_016 A B R) := by
  simpa only [nb089_alpha_dummy_015, nb089_alpha_dummy_016] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb089_fresh_014 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_017 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 0

theorem nb089_fresh_015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_018 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) 1

theorem nb089_distinct_016 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_017 u A B R) ≠ (nb089_alpha_dummy_018 u A B R) := by
  simpa only [nb089_alpha_dummy_017, nb089_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_017 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_021 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_021] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_018 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_019 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_023 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_020 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_021 A B R) ≠ (nb089_alpha_dummy_022 A B R) := by
  simpa only [nb089_alpha_dummy_021, nb089_alpha_dummy_022] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_021 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_021 A B R) ≠ (nb089_alpha_dummy_023 A B R) := by
  simpa only [nb089_alpha_dummy_021, nb089_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_022 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ≠ (nb089_alpha_dummy_023 A B R) := by
  simpa only [nb089_alpha_dummy_022, nb089_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_023 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_024 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_024 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_025 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_026 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_026 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_024 u A B R) ≠ (nb089_alpha_dummy_025 u A B R) := by
  simpa only [nb089_alpha_dummy_024, nb089_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_024 u A B R) ≠ (nb089_alpha_dummy_026 u A B R) := by
  simpa only [nb089_alpha_dummy_024, nb089_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_028 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ≠ (nb089_alpha_dummy_026 u A B R) := by
  simpa only [nb089_alpha_dummy_025, nb089_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_029 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_033 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_033] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_022 A B R))).fv)
      0

theorem nb089_fresh_030 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_029 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_029] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv)
      0

theorem nb089_fresh_031 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_035 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv)
      0

theorem nb089_fresh_032 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_034 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv)
      0

theorem nb089_fresh_033 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_030 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv)
      0

theorem nb089_fresh_034 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_036 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv)
      0

theorem nb089_fresh_035 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_053 A B R) ∉ (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_053] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) 0

theorem nb089_fresh_036 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_054 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_054] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) 0

theorem nb089_fresh_037 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_055 A B R) ∉ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_055] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 0

theorem nb089_fresh_038 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_056 A B R) ∉ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) := by
  simpa only [nb089_alpha_dummy_056] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) 1

theorem nb089_distinct_039 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_055 A B R) ≠ (nb089_alpha_dummy_056 A B R) := by
  simpa only [nb089_alpha_dummy_055, nb089_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb089_fresh_040 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_057 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_057] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 0

theorem nb089_fresh_041 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_058 u A B R) ∉ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_058] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) 1

theorem nb089_distinct_042 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_057 u A B R) ≠ (nb089_alpha_dummy_058 u A B R) := by
  simpa only [nb089_alpha_dummy_057, nb089_alpha_dummy_058] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_043 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_061 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_044 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_045 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_063 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_046 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_061 A B R) ≠ (nb089_alpha_dummy_062 A B R) := by
  simpa only [nb089_alpha_dummy_061, nb089_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_047 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_061 A B R) ≠ (nb089_alpha_dummy_063 A B R) := by
  simpa only [nb089_alpha_dummy_061, nb089_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_048 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ≠ (nb089_alpha_dummy_063 A B R) := by
  simpa only [nb089_alpha_dummy_062, nb089_alpha_dummy_063] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_064 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 0

theorem nb089_fresh_050 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_065] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 1

theorem nb089_fresh_051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_066 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb089_alpha_dummy_066] using
    freshVar_not_mem (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) 2

theorem nb089_distinct_052 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_064 u A B R) ≠ (nb089_alpha_dummy_065 u A B R) := by
  simpa only [nb089_alpha_dummy_064, nb089_alpha_dummy_065] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_distinct_053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_064 u A B R) ≠ (nb089_alpha_dummy_066 u A B R) := by
  simpa only [nb089_alpha_dummy_064, nb089_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb089_distinct_054 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ≠ (nb089_alpha_dummy_066 u A B R) := by
  simpa only [nb089_alpha_dummy_065, nb089_alpha_dummy_066] using
    (freshVar_injective (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb089_fresh_055 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_073 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_073] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_062 A B R))).fv)
      0

theorem nb089_fresh_056 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_069 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_069] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv)
      0

theorem nb089_fresh_057 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_075 A B R) ∉
      (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv)
      0

theorem nb089_fresh_058 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_074 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_074] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv)
      0

theorem nb089_fresh_059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_070 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_070] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv)
      0

theorem nb089_fresh_060 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_076 u A B R) ∉
      (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv)
      0

theorem nb089_fresh_061 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_009 u A B R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_009] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv)
      0

theorem nb089_fresh_062 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_010 u A B R) ∉
      (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv)
      1

theorem nb089_distinct_063 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_009 u A B R) ≠ (nb089_alpha_dummy_010 u A B R) := by
  simpa only [nb089_alpha_dummy_009, nb089_alpha_dummy_010] using
    (freshVar_injective
      (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb089_fresh_064 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_019 A B R) ∉
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_019] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_015 A B R))).fv)
      0

theorem nb089_fresh_065 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_020 u A B R) ∉
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv)
      0

theorem nb089_fresh_066 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_059 A B R) ∉
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_059] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_055 A B R))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part002`. -/


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

theorem nb089_fresh_067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_060 u A B R) ∉
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_060] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv)
      0

theorem nb089_fresh_068 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_011 A B R) ∉
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R)
              (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                (Class.cv (nb089_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R)
              (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                (Class.cv (nb089_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb089_fresh_069 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_012 u A B R) ∉
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R)
              (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
                (Class.cv (nb089_alpha_dummy_004 u A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R)
              (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
                (Class.cv (nb089_alpha_dummy_004 u A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb089_fresh_070 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_049 A B R) ∉
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R)
              (syn_wrex (nb089_alpha_dummy_046 A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
                (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R)
              (syn_wrex (nb089_alpha_dummy_046 A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
                (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb089_fresh_071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_050 u A B R) ∉
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb089_fresh_072 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_031 A B R) ∉
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_031] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv)
      0

theorem nb089_fresh_073 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_032 u A B R) ∉
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_032] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv)
      0

theorem nb089_fresh_074 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_071 A B R) ∉
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_071] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv)
      0

theorem nb089_fresh_075 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_072 u A B R) ∉
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_072] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv)
      0

theorem nb089_fresh_076 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_039 A B R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb089_fresh_077 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_040 u A B R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb089_fresh_078 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_079 A B R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_079] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb089_fresh_079 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_080 u A B R) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_080] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb089_fresh_080 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_027 A B R) ∉
      (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_027] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv)
      0

theorem nb089_fresh_081 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_028 u A B R) ∉
      (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv)
      0

theorem nb089_fresh_082 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_067 A B R) ∉
      (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_067] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv)
      0

theorem nb089_fresh_083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_068 u A B R) ∉
      (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_068] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv)
      0

theorem nb089_fresh_084 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_041 A B R) ∉
      (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv)
      0

theorem nb089_fresh_085 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_042 u A B R) ∉
      (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv)
      0

theorem nb089_fresh_086 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_081 A B R) ∉
      (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_081] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv)
      0

theorem nb089_fresh_087 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_082 u A B R) ∉
      (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_082] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv)
      0

theorem nb089_fresh_088 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_045 A B R) ∉
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv)
      0

theorem nb089_fresh_089 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_046 A B R) ∉
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_046] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv)
      1

theorem nb089_distinct_090 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_045 A B R) ≠ (nb089_alpha_dummy_046 A B R) := by
  simpa only [nb089_alpha_dummy_045, nb089_alpha_dummy_046] using
    (freshVar_injective (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) (i := 0) (j := 1) (by decide))

theorem nb089_fresh_091 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_047 u A B R) ∉
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb089_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_092 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_048 u A B R) ∉
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  simpa only [nb089_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) 1

theorem nb089_distinct_093 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_047 u A B R) ≠ (nb089_alpha_dummy_048 u A B R) := by
  simpa only [nb089_alpha_dummy_047, nb089_alpha_dummy_048] using
    (freshVar_injective
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb089_fresh_094 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉
      (((syn_wbr R (syn_cwe) A)).fv ∪
          ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪
        ((syn_c0)).fv) :=
  by
  simpa only [nb089_alpha_dummy_001] using
    freshVar_not_mem
      (((syn_wbr R (syn_cwe) A)).fv ∪
          ((syn_cmpt (nb089_alpha_dummy_000 A B R) (syn_cpw1 (syn_cpw1 (syn_cuni A)))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R))))).fv ∪
        ((syn_c0)).fv)
      0

theorem nb089_fresh_095 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉
      (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
              (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv) :=
  by
  simpa only [nb089_alpha_dummy_002] using
    freshVar_not_mem
      (((syn_wbr R (syn_cwe) A)).fv ∪ ((syn_cmpt u (syn_cpw1 (syn_cpw1 (syn_cuni A)))
              (syn_cfdrowfib R A B (Class.cv u)))).fv ∪ ((syn_c0)).fv)
      0

theorem nb089_fresh_096 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv) := by
  simpa only [nb089_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv) 0

theorem nb089_fresh_097 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∉
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  simpa only [nb089_alpha_dummy_043] using
    freshVar_not_mem
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) 0

theorem nb089_fresh_098 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) := by
  simpa only [nb089_alpha_dummy_044] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) 0

theorem nb089_fresh_099 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∉
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) :=
  by
  simpa only [nb089_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv)
      0

theorem nb089_fresh_100 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_005 A B R) ∉
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
              (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_005] using
    freshVar_not_mem
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
              (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv)
      0

theorem nb089_fresh_101 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∉
      (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv u))).fv) :=
  by
  simpa only [nb089_alpha_dummy_004] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv u))).fv)
      0

theorem nb089_fresh_102 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_006 u A B R) ∉
      (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
              (syn_cfdrowfib R A B (Class.cv u))))).fv) :=
  by
  simpa only [nb089_alpha_dummy_006] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
              (syn_cfdrowfib R A B (Class.cv u))))).fv)
      0

theorem nb089_support_mem_0000 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
              (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0001 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
              (syn_cfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0002 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∈
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ({(nb089_alpha_dummy_003 A B R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb089_alpha_dummy_000 A B R))
              (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_003 A B R))
              (syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0003 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∈
      (({ u } : Finset Var) ∪ ({(nb089_alpha_dummy_004 u A B R)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv u) (syn_cpw1 (syn_cpw1 (syn_cuni A))))
            (Wff.classEq (Class.cv (nb089_alpha_dummy_004 u A B R))
              (syn_cfdrowfib R A B (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0004 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (({(nb089_alpha_dummy_000 A B R)} : Finset Var) ∪
          ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv (nb089_alpha_dummy_000 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0005 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (({ u } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 (syn_cuni A)))).fv ∪
        ((syn_cfdrowfib R A B (Class.cv u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0006 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0007 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R)
              (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                (Class.cv (nb089_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_007 A B R) from (by
          unfold nb089_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_008 A B R) from (by
            unfold nb089_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0008 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0009 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R)
              (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
                (Class.cv (nb089_alpha_dummy_004 u A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089_alpha_dummy_009 u A B R) from (by
          unfold nb089_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089_alpha_dummy_010 u A B R) from (by
            unfold nb089_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0010 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_007 A B R) from (by
          unfold nb089_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_008 A B R) from (by
            unfold nb089_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0006 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0011 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089_alpha_dummy_009 u A B R) from (by
          unfold nb089_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089_alpha_dummy_010 u A B R) from (by
            unfold nb089_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0008 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0012 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_008 A B R) ∈ (((Class.cv (nb089_alpha_dummy_008 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0013 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_010 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_010 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0014 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_015 A B R) ∈
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_015 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_015 A B R))).fv) :=
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

theorem nb089_support_mem_0015 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_017 u A B R) ∈
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_017 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_017 u A B R))).fv) :=
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

theorem nb089_support_mem_0016 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_015 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_015 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0017 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_017 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_017 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0018 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0019 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0020 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0021 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0022 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_023 A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_022 A B R))
            (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0023 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_026 u A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_025 u A B R))
            (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0024 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_023 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0025 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_026 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0026 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0028 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_022 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_022 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_022 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0029 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_025 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_025 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_025 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0030 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_023 A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_022 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_023 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0031 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_026 u A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_025 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_026 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0032 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_023 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_023 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_023 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0033 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_026 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_026 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_026 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0034 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_000 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_003 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0035 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_007 A B R)
              (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
                (Class.cv (nb089_alpha_dummy_003 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_007 A B R) from (by
          unfold nb089_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_008 A B R) from (by
            unfold nb089_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0036 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb089_alpha_dummy_004 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0037 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_009 u A B R)
              (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
                (Class.cv (nb089_alpha_dummy_004 u A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_009 u A B R) from (by
          unfold nb089_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_010 u A B R) from (by
            unfold nb089_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0038 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_003 A B R) ∈
      (((Class.cab (nb089_alpha_dummy_007 A B R) (syn_wrex (nb089_alpha_dummy_008 A B R)
              (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_007 A B R)
            (syn_wrex (nb089_alpha_dummy_008 A B R) (Class.cv (nb089_alpha_dummy_003 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_007 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_007 A B R) from (by
          unfold nb089_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_003 A B R) ≠ (nb089_alpha_dummy_008 A B R) from (by
            unfold nb089_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0034 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0039 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_004 u A B R) ∈
      (((Class.cab (nb089_alpha_dummy_009 u A B R) (syn_wrex (nb089_alpha_dummy_010 u A B R)
              (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_009 u A B R)
            (syn_wrex (nb089_alpha_dummy_010 u A B R) (Class.cv (nb089_alpha_dummy_004 u A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_009 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_009 u A B R) from (by
          unfold nb089_alpha_dummy_009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_004 u A B R) ≠ (nb089_alpha_dummy_010 u A B R) from (by
            unfold nb089_alpha_dummy_010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0036 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0040 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_008 A B R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0041 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_010 u A B R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0042 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_008 A B R) ∈
      (((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_008 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0043 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_010 u A B R) ∈
      (((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_010 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0044 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∈
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0045 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R)
              (syn_wrex (nb089_alpha_dummy_046 A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
                (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_045 A B R) from (by
          unfold nb089_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
            unfold nb089_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0046 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∈
      (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0047 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_047 u A B R) from (by
          unfold nb089_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_048 u A B R) from (by
            unfold nb089_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0048 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∈
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_045 A B R) from (by
          unfold nb089_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_043 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
            unfold nb089_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0044 A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0049 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∈
      (((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv ∪
        ((Class.cab (nb089_alpha_dummy_047 u A B R) (syn_wrex (nb089_alpha_dummy_048 u A B R)
              (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_047 u A B R) from (by
          unfold nb089_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_044 u A B R) ≠ (nb089_alpha_dummy_048 u A B R) from (by
            unfold nb089_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0046 u A B R) 1))))
    · rw [fv_syn_csn]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0050 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_043 A B R) ∈ (((Class.cv (nb089_alpha_dummy_043 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0051 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_044 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_044 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0052 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_046 A B R) ∈ (((Class.cv (nb089_alpha_dummy_046 A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0053 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_048 u A B R) ∈ (((Class.cv (nb089_alpha_dummy_048 u A B R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0054 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_055 A B R) ∈
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_055 A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_055 A B R))).fv) :=
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

theorem nb089_support_mem_0055 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_057 u A B R) ∈
      (((Wff.classMem (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb089_alpha_dummy_057 u A B R)) (syn_c1c))).fv ∪
        ((Class.cv (nb089_alpha_dummy_057 u A B R))).fv) :=
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

theorem nb089_support_mem_0056 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_055 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_055 A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0057 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_057 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_057 u A B R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0058 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0059 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0060 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0061 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0062 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_063 A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_062 A B R))
            (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0063 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_066 u A B R) ∈
      (((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv ∪
        ((syn_cnin (Class.cv (nb089_alpha_dummy_065 u A B R))
            (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0064 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_063 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0065 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_066 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0066 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0067 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0068 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_062 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_062 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_062 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0069 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_065 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_065 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_065 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0070 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_063 A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_062 A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_063 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0071 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_066 u A B R) ∈
      (((syn_ccompl (Class.cv (nb089_alpha_dummy_065 u A B R)))).fv ∪
        ((syn_ccompl (Class.cv (nb089_alpha_dummy_066 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0072 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_063 A B R) ∈
      (((Class.cv (nb089_alpha_dummy_063 A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_063 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0073 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_066 u A B R) ∈
      (((Class.cv (nb089_alpha_dummy_066 u A B R))).fv ∪
        ((Class.cv (nb089_alpha_dummy_066 u A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0074 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0075 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ ((R).fv ∪ (A).fv ∪ (B).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0076 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))).fv ∪
        ((Class.cv (nb089_alpha_dummy_000 A B R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0077 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_045 A B R)
              (syn_wrex (nb089_alpha_dummy_046 A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_043 A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
                (Class.cv (nb089_alpha_dummy_000 A B R))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_045 A B R) from (by
          unfold nb089_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
            unfold nb089_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0078 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈ (((syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0079 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((syn_ccompl (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R)
                (syn_csn (Class.cv (nb089_alpha_dummy_044 u A B R)))
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb089_alpha_dummy_047 u A B R)
              (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
                (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                  (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089_alpha_dummy_047 u A B R) from (by
          unfold nb089_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089_alpha_dummy_048 u A B R) from (by
            unfold nb089_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0080 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_000 A B R) ∈
      (((Class.cab (nb089_alpha_dummy_045 A B R) (syn_wrex (nb089_alpha_dummy_046 A B R)
              (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_045 A B R)
            (syn_wrex (nb089_alpha_dummy_046 A B R) (Class.cv (nb089_alpha_dummy_000 A B R))
              (Wff.classEq (Class.cv (nb089_alpha_dummy_045 A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_045 A B R) from (by
          unfold nb089_alpha_dummy_045;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb089_alpha_dummy_000 A B R) ≠ (nb089_alpha_dummy_046 A B R) from (by
            unfold nb089_alpha_dummy_046;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0076 A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0081 (u : Var) (A : Class) (B : Class) (R : Class) :
    u ∈
      (((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb089_alpha_dummy_047 u A B R)
            (syn_wrex (nb089_alpha_dummy_048 u A B R) (Class.cv u)
              (Wff.classEq (Class.cv (nb089_alpha_dummy_047 u A B R))
                (syn_cun (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb089_alpha_dummy_047 u A B R) from (by
          unfold nb089_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb089_alpha_dummy_048 u A B R) from (by
            unfold nb089_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb089_support_mem_0078 u A B R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb089_support_mem_0082 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_046 A B R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0083 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_048 u A B R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0084 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_046 A B R) ∈
      (((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_046 A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb089_support_mem_0085 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_048 u A B R) ∈
      (((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv ∪
        ((syn_cphi (Class.cv (nb089_alpha_dummy_048 u A B R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C089C001Part003`. -/


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

theorem nb089_compact_fv_empty_0026 (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_001 A B R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb089_compact_fv_empty_0027 (u : Var) (A : Class) (B : Class) (R : Class) :
    (nb089_alpha_dummy_002 u A B R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
