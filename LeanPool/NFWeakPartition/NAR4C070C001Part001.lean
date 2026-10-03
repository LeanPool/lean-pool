/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C070C001Part001. -/


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
noncomputable def nb070_alpha_dummy_000 (A : Class) : Var :=
  (freshVar ((A).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_001 (A : Class) : Var :=
  (freshVar ((A).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_002 (A : Class) : Var :=
  (freshVar (({(nb070_alpha_dummy_000 A)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
          (syn_wrex (nb070_alpha_dummy_001 A) A
            (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
              (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_003 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (({ b } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv b) (syn_cncs))
          (syn_wrex x A (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_004 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq
          (Class.cab (nb070_alpha_dummy_000 A)
            (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
              (syn_wrex (nb070_alpha_dummy_001 A) A
                (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                  (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
          (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_005 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq
          (Class.cab (nb070_alpha_dummy_000 A)
            (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
              (syn_wrex (nb070_alpha_dummy_001 A) A
                (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                  (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
          (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_006 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
            (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
          (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_007 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
            (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
          (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_008 (A : Class) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_009 (A : Class) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_010 (x : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_011 (x : Var) : Var :=
  (freshVar (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_012 (A : Class) : Var :=
  (freshVar (((syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_013 (x : Var) : Var :=
  (freshVar (((syn_cpw1 (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_014 (A : Class) : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_015 (x : Var) : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_016 (A : Class) : Var :=
  (freshVar (((syn_cpw (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_017 (x : Var) : Var :=
  (freshVar (((syn_cpw (Class.cv x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_018 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_019 (x : Var) : Var :=
  (freshVar (((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_020 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
          (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪
      ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A)) (Class.cv (nb070_alpha_dummy_001 A)))).fv)
    0)

@[expose]
noncomputable def nb070_alpha_dummy_021 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪
      ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_022 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_001 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_023 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_024 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_008 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_025 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_008 A))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_026 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
      ((Class.cv (nb070_alpha_dummy_010 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_027 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
      ((Class.cv (nb070_alpha_dummy_010 x))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_028 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_029 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_030 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_024 A)
          (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
              (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv ∪
      ((Class.cab (nb070_alpha_dummy_024 A)
          (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
              (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_031 (x : Var) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_026 x)
          (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
              (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv ∪
      ((Class.cab (nb070_alpha_dummy_026 x)
          (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
              (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_032 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_025 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_033 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_025 A))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_034 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_027 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_035 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_027 x))).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_036 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))).fv ∪
      ((Class.cv (nb070_alpha_dummy_032 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_037 (x : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))).fv ∪
      ((Class.cv (nb070_alpha_dummy_034 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_038 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_039 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_040 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb070_alpha_dummy_041 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_042 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb070_alpha_dummy_043 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb070_alpha_dummy_044 (A : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
          (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪
      ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A)) (Class.cv (nb070_alpha_dummy_040 A)))).fv)
    0)

@[expose]
noncomputable def nb070_alpha_dummy_045 (x : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
          (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪
      ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x)) (Class.cv (nb070_alpha_dummy_043 x)))).fv)
    0)

@[expose]
noncomputable def nb070_alpha_dummy_046 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_040 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_047 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪
      ((Class.cv (nb070_alpha_dummy_043 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_048 (A : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪
      ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_049 (x : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪
      ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_050 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_039 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_051 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪
      ((Class.cv (nb070_alpha_dummy_042 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_052 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_040 A))).fv ∪
      ((Class.cv (nb070_alpha_dummy_040 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_053 (x : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_043 x))).fv ∪
      ((Class.cv (nb070_alpha_dummy_043 x))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_054 (A : Class) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_024 A)
          (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
              (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A)
          (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
              (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_055 (x : Var) : Var :=
  (freshVar (((Class.cab (nb070_alpha_dummy_026 x)
          (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
              (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x)
          (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
            (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
              (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_056 (A : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_057 (x : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_058 (A : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv ∪
      ((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_059 (x : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv ∪
      ((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_060 (A : Class) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_002 A))).fv) 0)

@[expose]
noncomputable def nb070_alpha_dummy_061 (x : Var) (A : Class) (b : Var) : Var :=
  (freshVar (((Class.cv (nb070_alpha_dummy_003 x A b))).fv) 0)

theorem nb070_fresh_000 (A : Class) :
    (nb070_alpha_dummy_004 A) ∉
      (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A)
              (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                (syn_wrex (nb070_alpha_dummy_001 A) A
                  (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                    (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A)
              (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                (syn_wrex (nb070_alpha_dummy_001 A) A
                  (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                    (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv)
      0

theorem nb070_fresh_001 (A : Class) :
    (nb070_alpha_dummy_005 A) ∉
      (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A)
              (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                (syn_wrex (nb070_alpha_dummy_001 A) A
                  (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                    (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq (Class.cab (nb070_alpha_dummy_000 A)
              (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                (syn_wrex (nb070_alpha_dummy_001 A) A
                  (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                    (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv)
      1

theorem nb070_distinct_002 (A : Class) :
    (nb070_alpha_dummy_004 A) ≠ (nb070_alpha_dummy_005 A) := by
  simpa only [nb070_alpha_dummy_004, nb070_alpha_dummy_005] using
    (freshVar_injective (((Class.cab (nb070_alpha_dummy_002 A) (Wff.classEq
            (Class.cab (nb070_alpha_dummy_000 A)
              (syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
                (syn_wrex (nb070_alpha_dummy_001 A) A
                  (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                    (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_002 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_003 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_006 x A b) ∉
      (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
              (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                  (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
              (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                  (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv)
      0

theorem nb070_fresh_004 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_007 x A b) ∉
      (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
              (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                  (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
              (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                  (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv)
      1

theorem nb070_distinct_005 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_006 x A b) ≠ (nb070_alpha_dummy_007 x A b) := by
  simpa only [nb070_alpha_dummy_006, nb070_alpha_dummy_007] using
    (freshVar_injective (((Class.cab (nb070_alpha_dummy_003 x A b) (Wff.classEq (Class.cab b
              (syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
                  (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x)))))))
            (syn_csn (Class.cv (nb070_alpha_dummy_003 x A b)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb070_fresh_006 (A : Class) :
    (nb070_alpha_dummy_054 A) ∉
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb070_fresh_007 (A : Class) :
    (nb070_alpha_dummy_030 A) ∉
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_024 A)
            (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))))).fv)
      0

theorem nb070_fresh_008 (x : Var) :
    (nb070_alpha_dummy_055 x) ∉
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb070_fresh_009 (x : Var) :
    (nb070_alpha_dummy_031 x) ∉
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv ∪
        ((Class.cab (nb070_alpha_dummy_026 x)
            (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
              (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))))).fv)
      0

theorem nb070_fresh_010 (A : Class) :
    (nb070_alpha_dummy_018 A) ∉ (((Class.cv (nb070_alpha_dummy_001 A))).fv) := by
  simpa only [nb070_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_001 A))).fv) 0

theorem nb070_fresh_011 (A : Class) :
    (nb070_alpha_dummy_060 A) ∉ (((Class.cv (nb070_alpha_dummy_002 A))).fv) := by
  simpa only [nb070_alpha_dummy_060] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_002 A))).fv) 0

theorem nb070_fresh_012 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_061 x A b) ∉ (((Class.cv (nb070_alpha_dummy_003 x A b))).fv) := by
  simpa only [nb070_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_003 x A b))).fv) 0

theorem nb070_fresh_013 (A : Class) :
    (nb070_alpha_dummy_024 A) ∉
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv)
      0

theorem nb070_fresh_014 (A : Class) :
    (nb070_alpha_dummy_025 A) ∉
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_025] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_008 A))).fv)
      1

theorem nb070_distinct_015 (A : Class) :
    (nb070_alpha_dummy_024 A) ≠ (nb070_alpha_dummy_025 A) := by
  simpa only [nb070_alpha_dummy_024, nb070_alpha_dummy_025] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_009 A))).fv ∪
        ((Class.cv (nb070_alpha_dummy_008 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_016 (x : Var) :
    (nb070_alpha_dummy_026 x) ∉
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_026] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv)
      0

theorem nb070_fresh_017 (x : Var) :
    (nb070_alpha_dummy_027 x) ∉
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_027] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_010 x))).fv)
      1

theorem nb070_distinct_018 (x : Var) :
    (nb070_alpha_dummy_026 x) ≠ (nb070_alpha_dummy_027 x) := by
  simpa only [nb070_alpha_dummy_026, nb070_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_011 x))).fv ∪
        ((Class.cv (nb070_alpha_dummy_010 x))).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_019 (A : Class) :
    (nb070_alpha_dummy_022 A) ∉
      (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_001 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_022] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_001 A))).fv)
      0

theorem nb070_fresh_020 (x : Var) :
    (nb070_alpha_dummy_023 x) ∉
      (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  simpa only [nb070_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) 0

theorem nb070_fresh_021 (A : Class) :
    (nb070_alpha_dummy_032 A) ∉ (((Class.cv (nb070_alpha_dummy_025 A))).fv) := by
  simpa only [nb070_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_025 A))).fv) 0

theorem nb070_fresh_022 (A : Class) :
    (nb070_alpha_dummy_033 A) ∉ (((Class.cv (nb070_alpha_dummy_025 A))).fv) := by
  simpa only [nb070_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_025 A))).fv) 1

theorem nb070_distinct_023 (A : Class) :
    (nb070_alpha_dummy_032 A) ≠ (nb070_alpha_dummy_033 A) := by
  simpa only [nb070_alpha_dummy_032, nb070_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_025 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb070_fresh_024 (x : Var) :
    (nb070_alpha_dummy_034 x) ∉ (((Class.cv (nb070_alpha_dummy_027 x))).fv) := by
  simpa only [nb070_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_027 x))).fv) 0

theorem nb070_fresh_025 (x : Var) :
    (nb070_alpha_dummy_035 x) ∉ (((Class.cv (nb070_alpha_dummy_027 x))).fv) := by
  simpa only [nb070_alpha_dummy_035] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_027 x))).fv) 1

theorem nb070_distinct_026 (x : Var) :
    (nb070_alpha_dummy_034 x) ≠ (nb070_alpha_dummy_035 x) := by
  simpa only [nb070_alpha_dummy_034, nb070_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_027 x))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb070_fresh_027 (A : Class) :
    (nb070_alpha_dummy_038 A) ∉
      (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_038] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 0

theorem nb070_fresh_028 (A : Class) :
    (nb070_alpha_dummy_039 A) ∉
      (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_039] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 1

theorem nb070_fresh_029 (A : Class) :
    (nb070_alpha_dummy_040 A) ∉
      (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_040] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) 2

theorem nb070_distinct_030 (A : Class) :
    (nb070_alpha_dummy_038 A) ≠ (nb070_alpha_dummy_039 A) := by
  simpa only [nb070_alpha_dummy_038, nb070_alpha_dummy_039] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb070_distinct_031 (A : Class) :
    (nb070_alpha_dummy_038 A) ≠ (nb070_alpha_dummy_040 A) := by
  simpa only [nb070_alpha_dummy_038, nb070_alpha_dummy_040] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb070_distinct_032 (A : Class) :
    (nb070_alpha_dummy_039 A) ≠ (nb070_alpha_dummy_040 A) := by
  simpa only [nb070_alpha_dummy_039, nb070_alpha_dummy_040] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_032 A))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb070_fresh_033 (x : Var) :
    (nb070_alpha_dummy_041 x) ∉
      (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_041] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb070_fresh_034 (x : Var) :
    (nb070_alpha_dummy_042 x) ∉
      (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_042] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 1

theorem nb070_fresh_035 (x : Var) :
    (nb070_alpha_dummy_043 x) ∉
      (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_043] using
    freshVar_not_mem (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) 2

theorem nb070_distinct_036 (x : Var) :
    (nb070_alpha_dummy_041 x) ≠ (nb070_alpha_dummy_042 x) := by
  simpa only [nb070_alpha_dummy_041, nb070_alpha_dummy_042] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb070_distinct_037 (x : Var) :
    (nb070_alpha_dummy_041 x) ≠ (nb070_alpha_dummy_043 x) := by
  simpa only [nb070_alpha_dummy_041, nb070_alpha_dummy_043] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb070_distinct_038 (x : Var) :
    (nb070_alpha_dummy_042 x) ≠ (nb070_alpha_dummy_043 x) := by
  simpa only [nb070_alpha_dummy_042, nb070_alpha_dummy_043] using
    (freshVar_injective (((Class.cv (nb070_alpha_dummy_034 x))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb070_fresh_039 (A : Class) :
    (nb070_alpha_dummy_050 A) ∉
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_039 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_050] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_039 A))).fv)
      0

theorem nb070_fresh_040 (A : Class) :
    (nb070_alpha_dummy_046 A) ∉
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_039 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv)
      0

theorem nb070_fresh_041 (A : Class) :
    (nb070_alpha_dummy_052 A) ∉
      (((Class.cv (nb070_alpha_dummy_040 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_052] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_040 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_040 A))).fv)
      0

theorem nb070_fresh_042 (x : Var) :
    (nb070_alpha_dummy_051 x) ∉
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_042 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_051] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_042 x))).fv)
      0

theorem nb070_fresh_043 (x : Var) :
    (nb070_alpha_dummy_047 x) ∉
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_042 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv)
      0

theorem nb070_fresh_044 (x : Var) :
    (nb070_alpha_dummy_053 x) ∉
      (((Class.cv (nb070_alpha_dummy_043 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cv (nb070_alpha_dummy_043 x))).fv ∪ ((Class.cv (nb070_alpha_dummy_043 x))).fv)
      0

theorem nb070_fresh_045 (x : Var) : (nb070_alpha_dummy_019 x) ∉ (((Class.cv x)).fv) := by
  simpa only [nb070_alpha_dummy_019] using freshVar_not_mem (((Class.cv x)).fv) 0

theorem nb070_fresh_046 (A : Class) :
    (nb070_alpha_dummy_036 A) ∉
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_032 A))).fv) :=
  by
  simpa only [nb070_alpha_dummy_036] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_032 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_032 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_032 A))).fv)
      0

theorem nb070_fresh_047 (x : Var) :
    (nb070_alpha_dummy_037 x) ∉
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_034 x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_037] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb070_alpha_dummy_034 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb070_alpha_dummy_034 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb070_alpha_dummy_034 x))).fv)
      0

theorem nb070_fresh_048 (A : Class) :
    (nb070_alpha_dummy_028 A) ∉
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_009 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_024 A)
              (syn_wrex (nb070_alpha_dummy_025 A) (Class.cv (nb070_alpha_dummy_008 A))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_024 A))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb070_fresh_049 (x : Var) :
    (nb070_alpha_dummy_029 x) ∉
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_011 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb070_alpha_dummy_026 x)
              (syn_wrex (nb070_alpha_dummy_027 x) (Class.cv (nb070_alpha_dummy_010 x))
                (Wff.classEq (Class.cv (nb070_alpha_dummy_026 x))
                  (syn_cun (syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb070_fresh_050 (A : Class) :
    (nb070_alpha_dummy_048 A) ∉
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_039 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_040 A)))).fv)
      0

theorem nb070_fresh_051 (x : Var) :
    (nb070_alpha_dummy_049 x) ∉
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb070_alpha_dummy_042 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb070_alpha_dummy_043 x)))).fv)
      0

theorem nb070_fresh_052 (A : Class) :
    (nb070_alpha_dummy_056 A) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_025 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb070_fresh_053 (x : Var) :
    (nb070_alpha_dummy_057 x) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_057] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb070_alpha_dummy_027 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb070_fresh_054 (A : Class) :
    (nb070_alpha_dummy_008 A) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_008] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) 0

theorem nb070_fresh_055 (A : Class) :
    (nb070_alpha_dummy_009 A) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) 1

theorem nb070_distinct_056 (A : Class) :
    (nb070_alpha_dummy_008 A) ≠ (nb070_alpha_dummy_009 A) := by
  simpa only [nb070_alpha_dummy_008, nb070_alpha_dummy_009] using
    (freshVar_injective
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb070_fresh_057 (x : Var) :
    (nb070_alpha_dummy_010 x) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_010] using
    freshVar_not_mem (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) 0

theorem nb070_fresh_058 (x : Var) :
    (nb070_alpha_dummy_011 x) ∉
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_011] using
    freshVar_not_mem (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) 1

theorem nb070_distinct_059 (x : Var) :
    (nb070_alpha_dummy_010 x) ≠ (nb070_alpha_dummy_011 x) := by
  simpa only [nb070_alpha_dummy_010, nb070_alpha_dummy_011] using
    (freshVar_injective (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb070_fresh_060 (A : Class) :
    (nb070_alpha_dummy_020 A) ∉
      (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_020] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv)
      0

theorem nb070_fresh_061 (x : Var) :
    (nb070_alpha_dummy_021 x) ∉
      (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv) :=
  by
  simpa only [nb070_alpha_dummy_021] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv)
      0

theorem nb070_fresh_062 (A : Class) :
    (nb070_alpha_dummy_044 A) ∉
      (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_044] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_039 A))
            (Class.cv (nb070_alpha_dummy_040 A)))).fv)
      0

theorem nb070_fresh_063 (x : Var) :
    (nb070_alpha_dummy_045 x) ∉
      (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_045] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_042 x))
            (Class.cv (nb070_alpha_dummy_043 x)))).fv)
      0

theorem nb070_fresh_064 (A : Class) :
    (nb070_alpha_dummy_014 A) ∉
      (((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv) :=
  by
  simpa only [nb070_alpha_dummy_014] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv)
      0

theorem nb070_fresh_065 (x : Var) :
    (nb070_alpha_dummy_015 x) ∉
      (((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv) :=
  by
  simpa only [nb070_alpha_dummy_015] using
    freshVar_not_mem
      (((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv)
      0

theorem nb070_fresh_066 (A : Class) :
    (nb070_alpha_dummy_058 A) ∉
      (((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_058] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_025 A)))).fv)
      0

theorem nb070_fresh_067 (x : Var) :
    (nb070_alpha_dummy_059 x) ∉
      (((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_059] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv ∪
        ((syn_cphi (Class.cv (nb070_alpha_dummy_027 x)))).fv)
      0

theorem nb070_fresh_068 (A : Class) :
    (nb070_alpha_dummy_016 A) ∉
      (((syn_cpw (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb070_alpha_dummy_016] using
    freshVar_not_mem
      (((syn_cpw (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪ ((syn_c1c)).fv) 0

theorem nb070_fresh_069 (x : Var) :
    (nb070_alpha_dummy_017 x) ∉ (((syn_cpw (Class.cv x))).fv ∪ ((syn_c1c)).fv) := by
  simpa only [nb070_alpha_dummy_017] using
    freshVar_not_mem (((syn_cpw (Class.cv x))).fv ∪ ((syn_c1c)).fv) 0

theorem nb070_fresh_070 (A : Class) :
    (nb070_alpha_dummy_012 A) ∉ (((syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))).fv) :=
  by
  simpa only [nb070_alpha_dummy_012] using
    freshVar_not_mem (((syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))).fv) 0

theorem nb070_fresh_071 (x : Var) :
    (nb070_alpha_dummy_013 x) ∉ (((syn_cpw1 (Class.cv x))).fv) := by
  simpa only [nb070_alpha_dummy_013] using
    freshVar_not_mem (((syn_cpw1 (Class.cv x))).fv) 0

theorem nb070_fresh_072 (A : Class) : (nb070_alpha_dummy_000 A) ∉ ((A).fv) := by
  simpa only [nb070_alpha_dummy_000] using freshVar_not_mem ((A).fv) 0

theorem nb070_fresh_073 (A : Class) : (nb070_alpha_dummy_001 A) ∉ ((A).fv) := by
  simpa only [nb070_alpha_dummy_001] using freshVar_not_mem ((A).fv) 1

theorem nb070_distinct_074 (A : Class) :
    (nb070_alpha_dummy_000 A) ≠ (nb070_alpha_dummy_001 A) := by
  simpa only [nb070_alpha_dummy_000, nb070_alpha_dummy_001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb070_fresh_075 (A : Class) :
    (nb070_alpha_dummy_002 A) ∉
      (({(nb070_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
            (syn_wrex (nb070_alpha_dummy_001 A) A
              (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb070_alpha_dummy_000 A)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb070_alpha_dummy_000 A)) (syn_cncs))
            (syn_wrex (nb070_alpha_dummy_001 A) A
              (Wff.classEq (Class.cv (nb070_alpha_dummy_000 A))
                (syn_cnc (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))))))).fv)
      0

theorem nb070_fresh_076 (x : Var) (A : Class) (b : Var) :
    (nb070_alpha_dummy_003 x A b) ∉
      (({ b } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
              (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).fv) :=
  by
  simpa only [nb070_alpha_dummy_003] using
    freshVar_not_mem
      (({ b } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv b) (syn_cncs)) (syn_wrex x A
              (Wff.classEq (Class.cv b) (syn_cnc (syn_cpw1 (Class.cv x))))))).fv)
      0

theorem nb070_support_mem_0000 (A : Class) :
    (nb070_alpha_dummy_018 A) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_018 A))
            (Class.cv (nb070_alpha_dummy_001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0001 (x : Var) :
    (nb070_alpha_dummy_019 x) ∈
      (((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv ∪
        ((syn_cnin (Class.cv (nb070_alpha_dummy_019 x)) (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0002 (A : Class) :
    (nb070_alpha_dummy_018 A) ∈
      (((Class.cv (nb070_alpha_dummy_018 A))).fv ∪ ((Class.cv (nb070_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0003 (x : Var) :
    (nb070_alpha_dummy_019 x) ∈
      (((Class.cv (nb070_alpha_dummy_019 x))).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0004 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0005 (x : Var) :
    x ∈ (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0006 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈ (((syn_cpw1 (Class.cv (nb070_alpha_dummy_001 A)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0007 (x : Var) : x ∈ (((syn_cpw1 (Class.cv x))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0008 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈
      (((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb070_alpha_dummy_001 A))) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0009 (x : Var) :
    x ∈
      (((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv x)) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb070_support_mem_0010 (A : Class) :
    (nb070_alpha_dummy_001 A) ∈
      (((syn_cpw (Class.cv (nb070_alpha_dummy_001 A)))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
