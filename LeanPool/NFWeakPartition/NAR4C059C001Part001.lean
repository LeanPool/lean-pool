/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C059C001Part001. -/


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
noncomputable def nb059_alpha_dummy_000 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((S_cls).fv ∪ (R).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_001 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_000 R S_cls)
        (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_002 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_000 R S_cls)
        (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_003 (R : Class) (S_cls : Class) (a : Var) : Var :=
  (freshVar (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
          (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_004 (R : Class) (S_cls : Class) (a : Var) : Var :=
  (freshVar (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
          (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_005 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
      ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_006 (S_cls : Class) (a : Var) : Var :=
  (freshVar (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_007 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_008 (S_cls : Class) (a : Var) : Var :=
  (freshVar ((S_cls).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_009 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
      ((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
          (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_010 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv ∪
      ((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_011 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
      ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_012 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_cima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_013 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_014 (R : Class) (S_cls : Class) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_015 (R : Class) (a : Var) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_016 (R : Class) (a : Var) : Var :=
  (freshVar ((R).fv ∪ ((Class.cv a)).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_017 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
      ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_018 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
      ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_019 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
      ((Class.cv (nb059_alpha_dummy_015 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_020 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
      ((Class.cv (nb059_alpha_dummy_015 R a))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_021 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls)
            (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_022 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_023 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_017 R S_cls)
          (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_014 R S_cls))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
              (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv ∪
      ((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
            (Class.cv (nb059_alpha_dummy_014 R S_cls))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
              (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_024 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_019 R a)
          (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
              (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv ∪
      ((Class.cab (nb059_alpha_dummy_019 R a)
          (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
              (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_025 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_026 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_027 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_020 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_028 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_020 R a))).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_029 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_c1c))).fv ∪
      ((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_030 (R : Class) (a : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb059_alpha_dummy_027 R a)) (syn_c1c))).fv ∪
      ((Class.cv (nb059_alpha_dummy_027 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_031 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_032 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_033 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb059_alpha_dummy_034 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_035 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb059_alpha_dummy_036 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb059_alpha_dummy_037 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
          (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv ∪
      ((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
          (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_038 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
          (Class.cv (nb059_alpha_dummy_036 R a)))).fv ∪
      ((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
          (Class.cv (nb059_alpha_dummy_036 R a)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_039 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
      ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_040 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
      ((Class.cv (nb059_alpha_dummy_036 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_041 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪
      ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_042 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪
      ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_043 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
      ((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_044 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
      ((Class.cv (nb059_alpha_dummy_035 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_045 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv ∪
      ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_046 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (nb059_alpha_dummy_036 R a))).fv ∪
      ((Class.cv (nb059_alpha_dummy_036 R a))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_047 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_017 R S_cls)
          (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
              (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_017 R S_cls)
          (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
              (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_048 (R : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (nb059_alpha_dummy_019 R a)
          (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
              (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_019 R a)
          (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
            (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
              (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_049 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_050 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_051 (R : Class) (S_cls : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv ∪
      ((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv) 0)

@[expose]
noncomputable def nb059_alpha_dummy_052 (R : Class) (a : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv ∪
      ((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv) 0)

theorem nb059_fresh_000 (R : Class) (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_003 R S_cls a) ∉
      (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
            (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_003] using
    freshVar_not_mem
      (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
            (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv)
      0

theorem nb059_fresh_001 (R : Class) (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_004 R S_cls a) ∉
      (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
            (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
            (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv)
      1

theorem nb059_distinct_002 (R : Class) (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_003 R S_cls a) ≠ (nb059_alpha_dummy_004 R S_cls a) := by
  simpa only [nb059_alpha_dummy_003, nb059_alpha_dummy_004] using
    (freshVar_injective (((Class.cab a (syn_wa (syn_wss S_cls (Class.cv a))
            (syn_wss (syn_cima R (Class.cv a)) (Class.cv a))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_fresh_003 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_001 R S_cls) ∉
      (((Class.cab (nb059_alpha_dummy_000 R S_cls)
          (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_001] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_000 R S_cls)
          (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv)
      0

theorem nb059_fresh_004 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_002 R S_cls) ∉
      (((Class.cab (nb059_alpha_dummy_000 R S_cls)
          (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_002] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_000 R S_cls)
          (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv)
      1

theorem nb059_distinct_005 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_001 R S_cls) ≠ (nb059_alpha_dummy_002 R S_cls) := by
  simpa only [nb059_alpha_dummy_001, nb059_alpha_dummy_002] using
    (freshVar_injective (((Class.cab (nb059_alpha_dummy_000 R S_cls)
          (syn_wa (syn_wss S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (syn_wss (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
              (Class.cv (nb059_alpha_dummy_000 R S_cls)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_006 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_047 R S_cls) ∉
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_017 R S_cls)
            (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_017 R S_cls)
            (syn_wrex (nb059_alpha_dummy_018 R S_cls) (Class.cv (nb059_alpha_dummy_013 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb059_fresh_007 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_023 R S_cls) ∉
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_023] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv)
      0

theorem nb059_fresh_008 (R : Class) (a : Var) :
    (nb059_alpha_dummy_048 R a) ∉
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb059_fresh_009 (R : Class) (a : Var) :
    (nb059_alpha_dummy_024 R a) ∉
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv)
      0

theorem nb059_fresh_010 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_017 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_017] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv)
      0

theorem nb059_fresh_011 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_018 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_018] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv)
      1

theorem nb059_distinct_012 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_017 R S_cls) ≠ (nb059_alpha_dummy_018 R S_cls) := by
  simpa only [nb059_alpha_dummy_017, nb059_alpha_dummy_018] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_013 (R : Class) (a : Var) :
    (nb059_alpha_dummy_019 R a) ∉
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_019] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv)
      0

theorem nb059_fresh_014 (R : Class) (a : Var) :
    (nb059_alpha_dummy_020 R a) ∉
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv)
      1

theorem nb059_distinct_015 (R : Class) (a : Var) :
    (nb059_alpha_dummy_019 R a) ≠ (nb059_alpha_dummy_020 R a) := by
  simpa only [nb059_alpha_dummy_019, nb059_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_016 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_025 R S_cls) ∉ (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) 0

theorem nb059_fresh_017 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_026 R S_cls) ∉ (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) 1

theorem nb059_distinct_018 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_025 R S_cls) ≠ (nb059_alpha_dummy_026 R S_cls) := by
  simpa only [nb059_alpha_dummy_025, nb059_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) (i := 0) (j :=
      1) (by decide))

theorem nb059_fresh_019 (R : Class) (a : Var) :
    (nb059_alpha_dummy_027 R a) ∉ (((Class.cv (nb059_alpha_dummy_020 R a))).fv) := by
  simpa only [nb059_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_020 R a))).fv) 0

theorem nb059_fresh_020 (R : Class) (a : Var) :
    (nb059_alpha_dummy_028 R a) ∉ (((Class.cv (nb059_alpha_dummy_020 R a))).fv) := by
  simpa only [nb059_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_020 R a))).fv) 1

theorem nb059_distinct_021 (R : Class) (a : Var) :
    (nb059_alpha_dummy_027 R a) ≠ (nb059_alpha_dummy_028 R a) := by
  simpa only [nb059_alpha_dummy_027, nb059_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_020 R a))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb059_fresh_022 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_031 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 0

theorem nb059_fresh_023 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 1

theorem nb059_fresh_024 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_033 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) 2

theorem nb059_distinct_025 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_031 R S_cls) ≠ (nb059_alpha_dummy_032 R S_cls) := by
  simpa only [nb059_alpha_dummy_031, nb059_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_distinct_026 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_031 R S_cls) ≠ (nb059_alpha_dummy_033 R S_cls) := by
  simpa only [nb059_alpha_dummy_031, nb059_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb059_distinct_027 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ≠ (nb059_alpha_dummy_033 R S_cls) := by
  simpa only [nb059_alpha_dummy_032, nb059_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb059_fresh_028 (R : Class) (a : Var) :
    (nb059_alpha_dummy_034 R a) ∉
      (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 0

theorem nb059_fresh_029 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ∉
      (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_035] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 1

theorem nb059_fresh_030 (R : Class) (a : Var) :
    (nb059_alpha_dummy_036 R a) ∉
      (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb059_alpha_dummy_036] using
    freshVar_not_mem (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) 2

theorem nb059_distinct_031 (R : Class) (a : Var) :
    (nb059_alpha_dummy_034 R a) ≠ (nb059_alpha_dummy_035 R a) := by
  simpa only [nb059_alpha_dummy_034, nb059_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb059_distinct_032 (R : Class) (a : Var) :
    (nb059_alpha_dummy_034 R a) ≠ (nb059_alpha_dummy_036 R a) := by
  simpa only [nb059_alpha_dummy_034, nb059_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb059_distinct_033 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ≠ (nb059_alpha_dummy_036 R a) := by
  simpa only [nb059_alpha_dummy_035, nb059_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb059_fresh_034 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_043 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv)
      0

theorem nb059_fresh_035 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_039 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv)
      0

theorem nb059_fresh_036 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_045 R S_cls) ∉
      (((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv)
      0

theorem nb059_fresh_037 (R : Class) (a : Var) :
    (nb059_alpha_dummy_044 R a) ∉
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_035 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_035 R a))).fv)
      0

theorem nb059_fresh_038 (R : Class) (a : Var) :
    (nb059_alpha_dummy_040 R a) ∉
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv)
      0

theorem nb059_fresh_039 (R : Class) (a : Var) :
    (nb059_alpha_dummy_046 R a) ∉
      (((Class.cv (nb059_alpha_dummy_036 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb059_alpha_dummy_036 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv)
      0

theorem nb059_fresh_040 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_029 R S_cls) ∉
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_029] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv)
      0

theorem nb059_fresh_041 (R : Class) (a : Var) :
    (nb059_alpha_dummy_030 R a) ∉
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_027 R a)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_027 R a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_030] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_027 R a)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_027 R a))).fv)
      0

theorem nb059_fresh_042 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_021 R S_cls) ∉
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls)
              (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_014 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_013 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_021] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls)
              (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_014 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_013 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb059_fresh_043 (R : Class) (a : Var) :
    (nb059_alpha_dummy_022 R a) ∉
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb059_alpha_dummy_022] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb059_fresh_044 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_041 R S_cls) ∉
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_032 R S_cls)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv)
      0

theorem nb059_fresh_045 (R : Class) (a : Var) :
    (nb059_alpha_dummy_042 R a) ∉
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb059_alpha_dummy_035 R a)))).fv ∪
        ((syn_ccompl (Class.cv (nb059_alpha_dummy_036 R a)))).fv)
      0

theorem nb059_fresh_046 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_049 R S_cls) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb059_fresh_047 (R : Class) (a : Var) :
    (nb059_alpha_dummy_050 R a) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb059_fresh_048 (R : Class) (a : Var) :
    (nb059_alpha_dummy_012 R a) ∉ (((syn_cima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) :=
  by
  simpa only [nb059_alpha_dummy_012] using
    freshVar_not_mem (((syn_cima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_049 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_011 R S_cls) ∉
      (((syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_011] using
    freshVar_not_mem
      (((syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv)
      0

theorem nb059_fresh_050 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_037 R S_cls) ∉
      (((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_037] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv)
      0

theorem nb059_fresh_051 (R : Class) (a : Var) :
    (nb059_alpha_dummy_038 R a) ∉
      (((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_038] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv)
      0

theorem nb059_fresh_052 (R : Class) (a : Var) :
    (nb059_alpha_dummy_010 R a) ∉
      (((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_010] using
    freshVar_not_mem
      (((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv)
      0

theorem nb059_fresh_053 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_009 R S_cls) ∉
      (((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_009] using
    freshVar_not_mem
      (((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv)
      0

theorem nb059_fresh_054 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_006 S_cls a) ∉
      (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) :=
  by
  simpa only [nb059_alpha_dummy_006] using
    freshVar_not_mem
      (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) 0

theorem nb059_fresh_055 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_005 R S_cls) ∉
      (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_005] using
    freshVar_not_mem
      (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv)
      0

theorem nb059_fresh_056 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_051 R S_cls) ∉
      (((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_051] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))).fv)
      0

theorem nb059_fresh_057 (R : Class) (a : Var) :
    (nb059_alpha_dummy_052 R a) ∉
      (((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv) :=
  by
  simpa only [nb059_alpha_dummy_052] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv ∪
        ((syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))).fv)
      0

theorem nb059_fresh_058 (R : Class) (a : Var) :
    (nb059_alpha_dummy_015 R a) ∉ ((R).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059_alpha_dummy_015] using freshVar_not_mem ((R).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_059 (R : Class) (a : Var) :
    (nb059_alpha_dummy_016 R a) ∉ ((R).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059_alpha_dummy_016] using freshVar_not_mem ((R).fv ∪ ((Class.cv a)).fv) 1

theorem nb059_distinct_060 (R : Class) (a : Var) :
    (nb059_alpha_dummy_015 R a) ≠ (nb059_alpha_dummy_016 R a) := by
  simpa only [nb059_alpha_dummy_015, nb059_alpha_dummy_016] using
    (freshVar_injective ((R).fv ∪ ((Class.cv a)).fv) (i := 0) (j := 1) (by decide))

theorem nb059_fresh_061 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_013 R S_cls) ∉
      ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_013] using
    freshVar_not_mem ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0

theorem nb059_fresh_062 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_014 R S_cls) ∉
      ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_014] using
    freshVar_not_mem ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 1

theorem nb059_distinct_063 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_013 R S_cls) ≠ (nb059_alpha_dummy_014 R S_cls) := by
  simpa only [nb059_alpha_dummy_013, nb059_alpha_dummy_014] using
    (freshVar_injective ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) (i :=
      0) (j := 1) (by decide))

theorem nb059_fresh_064 (S_cls : Class) (a : Var) :
    (nb059_alpha_dummy_008 S_cls a) ∉ ((S_cls).fv ∪ ((Class.cv a)).fv) := by
  simpa only [nb059_alpha_dummy_008] using
    freshVar_not_mem ((S_cls).fv ∪ ((Class.cv a)).fv) 0

theorem nb059_fresh_065 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_007 R S_cls) ∉
      ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  simpa only [nb059_alpha_dummy_007] using
    freshVar_not_mem ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) 0

theorem nb059_fresh_066 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∉ ((S_cls).fv ∪ (R).fv) := by
  simpa only [nb059_alpha_dummy_000] using freshVar_not_mem ((S_cls).fv ∪ (R).fv) 0

theorem nb059_support_mem_0000 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∈
      (((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin S_cls (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0001 (S_cls : Class) (a : Var) :
    a ∈ (((syn_cnin S_cls (Class.cv a))).fv ∪ ((syn_cnin S_cls (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0002 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∈
      ((S_cls).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0003 (S_cls : Class) (a : Var) :
    a ∈ ((S_cls).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0004 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∈
      (((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))
            (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0005 (R : Class) (a : Var) :
    a ∈
      (((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv ∪
        ((syn_cnin (syn_cima R (Class.cv a)) (Class.cv a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0006 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∈
      (((syn_cima R (Class.cv (nb059_alpha_dummy_000 R S_cls)))).fv ∪
        ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0007 (R : Class) (a : Var) :
    a ∈ (((syn_cima R (Class.cv a))).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0008 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_000 R S_cls) ∈
      ((R).fv ∪ ((Class.cv (nb059_alpha_dummy_000 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0009 (R : Class) (a : Var) : a ∈ ((R).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0010 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_014 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_014 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_013 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0011 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_014 R S_cls) ∈
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_017 R S_cls)
              (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_014 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
                (Class.cv (nb059_alpha_dummy_013 R S_cls))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0012 (R : Class) (a : Var) :
    (nb059_alpha_dummy_016 R a) ∈
      (((Class.cv (nb059_alpha_dummy_016 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_015 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0013 (R : Class) (a : Var) :
    (nb059_alpha_dummy_016 R a) ∈
      (((syn_ccompl (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb059_alpha_dummy_019 R a)
              (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_015 R a))
                (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                  (syn_cun (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0014 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_014 R S_cls) ∈
      (((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_017 R S_cls) (syn_wrex (nb059_alpha_dummy_018 R S_cls)
              (Class.cv (nb059_alpha_dummy_014 R S_cls))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_017 R S_cls))
                (syn_cphi (Class.cv (nb059_alpha_dummy_018 R S_cls))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0010 R S_cls) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0015 (R : Class) (a : Var) :
    (nb059_alpha_dummy_016 R a) ∈
      (((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv ∪
        ((Class.cab (nb059_alpha_dummy_019 R a)
            (syn_wrex (nb059_alpha_dummy_020 R a) (Class.cv (nb059_alpha_dummy_016 R a))
              (Wff.classEq (Class.cv (nb059_alpha_dummy_019 R a))
                (syn_cphi (Class.cv (nb059_alpha_dummy_020 R a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb059_support_mem_0012 R a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb059_support_mem_0016 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_018 R S_cls) ∈ (((Class.cv (nb059_alpha_dummy_018 R S_cls))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0017 (R : Class) (a : Var) :
    (nb059_alpha_dummy_020 R a) ∈ (((Class.cv (nb059_alpha_dummy_020 R a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0018 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_025 R S_cls) ∈
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_025 R S_cls)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv) :=
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

theorem nb059_support_mem_0019 (R : Class) (a : Var) :
    (nb059_alpha_dummy_027 R a) ∈
      (((Wff.classMem (Class.cv (nb059_alpha_dummy_027 R a)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb059_alpha_dummy_027 R a)) (syn_c1c))).fv ∪
        ((Class.cv (nb059_alpha_dummy_027 R a))).fv) :=
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

theorem nb059_support_mem_0020 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_025 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_025 R S_cls))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0021 (R : Class) (a : Var) :
    (nb059_alpha_dummy_027 R a) ∈
      (((Class.cv (nb059_alpha_dummy_027 R a))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0022 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ∈
      (((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0023 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ∈
      (((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0024 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_032 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0025 (R : Class) (a : Var) :
    (nb059_alpha_dummy_035 R a) ∈
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0026 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_033 R S_cls) ∈
      (((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_032 R S_cls))
            (Class.cv (nb059_alpha_dummy_033 R S_cls)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0027 (R : Class) (a : Var) :
    (nb059_alpha_dummy_036 R a) ∈
      (((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv ∪
        ((syn_cnin (Class.cv (nb059_alpha_dummy_035 R a))
            (Class.cv (nb059_alpha_dummy_036 R a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0028 (R : Class) (S_cls : Class) :
    (nb059_alpha_dummy_033 R S_cls) ∈
      (((Class.cv (nb059_alpha_dummy_032 R S_cls))).fv ∪
        ((Class.cv (nb059_alpha_dummy_033 R S_cls))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb059_support_mem_0029 (R : Class) (a : Var) :
    (nb059_alpha_dummy_036 R a) ∈
      (((Class.cv (nb059_alpha_dummy_035 R a))).fv ∪
        ((Class.cv (nb059_alpha_dummy_036 R a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
