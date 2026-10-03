/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part007`. -/


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
noncomputable def nb078_alpha_dummy_900 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_892 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_901 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_897))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_902 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_899 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_903 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_904 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_905 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_906 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_907 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_908 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_909 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_904))
          (Class.cv (nb078_alpha_dummy_905)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_910 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
          (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h)) (Class.cv (nb078_alpha_dummy_908 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_911 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_912 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_913 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_914 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_915 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_916 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_907 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_917 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_918 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_908 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_919 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_889)
          (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889)
          (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_920 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_891 h)
          (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h)
          (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_921 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_922 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_923 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_924 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_925 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_926 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_927 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_771 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_928 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_771 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_929 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_930 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_931 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_925)
          (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
              (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_925)
          (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
              (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_932 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_927 h)
          (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_927 h)
          (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_933 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_926))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_934 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_926))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_935 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_928 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_936 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_928 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_937 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_933))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_938 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_935 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_939 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_940 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_941 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_942 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_943 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_944 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_945 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_940))
          (Class.cv (nb078_alpha_dummy_941)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_946 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
          (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h)) (Class.cv (nb078_alpha_dummy_944 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_947 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_948 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_949 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_950 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_951 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_952 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_943 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_953 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_954 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_944 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_955 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_925)
          (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925)
          (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_956 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_927 h)
          (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h)
          (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_957 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_958 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_959 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_960 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_961 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_962 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_963 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_964 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_965 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_966 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_967 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_963 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_968 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_963 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_969 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_970 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_971 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_965)
          (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
              (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_965)
          (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
              (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_972 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_967 h)
          (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_967 h)
          (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_973 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_966))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_974 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_966))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_975 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_968 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_976 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_968 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_977 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_973))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_978 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_975 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_979 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_980 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_981 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_982 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_983 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_984 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_985 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_980))
          (Class.cv (nb078_alpha_dummy_981)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_986 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
          (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h)) (Class.cv (nb078_alpha_dummy_984 h)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_987 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_988 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_989 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_990 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_991 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_992 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_983 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_993 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_994 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_984 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_995 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_965)
          (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965)
          (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_996 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_967 h)
          (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h)
          (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_997 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_998 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_999 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1000 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1001 : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
          (Class.cv (nb078_alpha_dummy_004)))).fv ∪
      ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
          (Class.cv (nb078_alpha_dummy_004)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1002 (y : Var) (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪
      ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1003 : Var :=
  (freshVar (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪
      ((Class.cv (nb078_alpha_dummy_004))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1004 (y : Var) (h : Var) : Var :=
  (freshVar (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1005 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1006 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1007 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1008 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((syn_cvv)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1009 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1010 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1011 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1012 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1007 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1013 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1014 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1015 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1009)
          (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1009)
          (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1016 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1011 h)
          (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1011 h)
          (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1017 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1010))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1018 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1010))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1019 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1020 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1021 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1017))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1022 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1019 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1023 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1024 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1025 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1026 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1027 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1028 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1029 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1024))
          (Class.cv (nb078_alpha_dummy_1025)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1030 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
          (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
          (Class.cv (nb078_alpha_dummy_1028 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1031 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1032 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1033 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1034 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1035 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1036 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1027 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1037 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1038 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1028 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1039 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1009)
          (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009)
          (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1040 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1011 h)
          (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h)
          (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1041 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1042 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1043 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1044 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1045 : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1046 (h : Var) : Var :=
  (freshVar (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
          (syn_cid))).fv ∪
      ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
          (syn_cid))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1047 : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
          (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1048 (h : Var) : Var :=
  (freshVar (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
      ((syn_cid)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1049 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part008`. -/


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
noncomputable def nb078_alpha_dummy_1050 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1051 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
      ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1052 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1053 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1054 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1055 : Var :=
  (freshVar (({(nb078_alpha_dummy_1049)} : Finset Var) ∪
        ({(nb078_alpha_dummy_1050)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1051) (syn_wa
            (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
              (Class.cv (nb078_alpha_dummy_1051))) (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (Class.cv (nb078_alpha_dummy_1050)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1056 (h : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
        ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
          (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
              (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
            (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
              (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1057 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1058 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1059 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1060 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1061 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1062 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1063 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1057)
          (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1057)
          (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1064 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1059 h)
          (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1059 h)
          (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1065 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1058))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1066 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1058))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1067 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1068 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1060 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1069 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1065))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1070 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1067 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1071 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1072 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1073 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1074 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1075 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1076 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1077 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1072))
          (Class.cv (nb078_alpha_dummy_1073)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1078 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
          (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
          (Class.cv (nb078_alpha_dummy_1076 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1079 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1080 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1081 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1082 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1083 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1084 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1075 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1085 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1086 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1076 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1087 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1057)
          (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057)
          (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1088 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1059 h)
          (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h)
          (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1089 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1090 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1091 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1092 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1093 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1094 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1095 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1096 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1054 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1097 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1098 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1099 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1093)
          (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1093)
          (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1100 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1095 h)
          (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1095 h)
          (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1101 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1094))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1102 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1094))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1103 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1104 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1096 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1105 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1101))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1106 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1103 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1107 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1108 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1109 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1110 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1111 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1112 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1113 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1108))
          (Class.cv (nb078_alpha_dummy_1109)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1114 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
          (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
          (Class.cv (nb078_alpha_dummy_1112 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1115 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1116 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1117 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1118 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1119 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1120 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1111 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1121 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1122 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1112 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1123 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1093)
          (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093)
          (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1124 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1095 h)
          (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h)
          (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1125 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1126 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1127 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1128 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1129 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1130 : Var :=
  (freshVar (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1131 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1132 (h : Var) : Var :=
  (freshVar (((syn_ccnv (Class.cv h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1133 : Var :=
  (freshVar (({(nb078_alpha_dummy_1129)} : Finset Var) ∪
        ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
          (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
          (Class.cv (nb078_alpha_dummy_1129)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1134 (h : Var) : Var :=
  (freshVar (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
        ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
      ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
          (Class.cv (nb078_alpha_dummy_1131 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1135 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1136 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1137 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1138 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1132 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1139 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1140 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1141 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1135)
          (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1135)
          (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1142 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1137 h)
          (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1137 h)
          (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1143 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1136))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1144 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1136))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1145 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1146 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1138 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1147 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1143))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1148 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1145 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1149 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1150 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1151 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1152 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1153 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1154 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1155 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1150))
          (Class.cv (nb078_alpha_dummy_1151)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1156 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
          (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
          (Class.cv (nb078_alpha_dummy_1154 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1157 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1158 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1159 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1160 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1161 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1162 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1153 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1163 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1164 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1154 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1165 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1135)
          (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135)
          (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1166 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1137 h)
          (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h)
          (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1167 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1168 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1169 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1170 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1171 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1172 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1173 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1174 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1131 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1175 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1176 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1177 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1171)
          (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1171)
          (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1178 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1173 h)
          (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1173 h)
          (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1179 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1172))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1180 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1172))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1181 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1182 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1174 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1183 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1179))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1184 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1181 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1185 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1186 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1187 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1188 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1189 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1190 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1191 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1186))
          (Class.cv (nb078_alpha_dummy_1187)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1192 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
          (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
          (Class.cv (nb078_alpha_dummy_1190 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1193 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1194 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1190 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1195 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1196 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1197 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1198 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1189 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1199 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) 0)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part009`. -/


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
noncomputable def nb078_alpha_dummy_1200 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1190 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1201 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1171)
          (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1171)
          (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1202 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1173 h)
          (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1173 h)
          (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1203 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1204 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1205 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1206 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1207 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1208 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1209 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1210 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1053 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1211 : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1212 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1213 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1207)
          (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1207)
          (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1214 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1209 h)
          (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv ∪
      ((Class.cab (nb078_alpha_dummy_1209 h)
          (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
              (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1215 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1208))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1216 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1208))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1217 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1218 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1210 h))).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1219 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1215))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1220 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1217 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1221 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1222 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1223 : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1224 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1225 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb078_alpha_dummy_1226 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb078_alpha_dummy_1227 : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1222))
          (Class.cv (nb078_alpha_dummy_1223)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv)
    0)

@[expose]
noncomputable def nb078_alpha_dummy_1228 (h : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
          (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪
      ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
          (Class.cv (nb078_alpha_dummy_1226 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1229 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1230 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1226 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1231 : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1222)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1223)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1232 (h : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb078_alpha_dummy_1225 h)))).fv ∪
      ((syn_ccompl (Class.cv (nb078_alpha_dummy_1226 h)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1233 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1234 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1225 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1235 : Var :=
  (freshVar
    (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1236 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪
      ((Class.cv (nb078_alpha_dummy_1226 h))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1237 : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1207)
          (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1207)
          (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1238 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078_alpha_dummy_1209 h)
          (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1209 h)
          (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
            (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
              (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1239 : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1240 (h : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1241 : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) 0)

@[expose]
noncomputable def nb078_alpha_dummy_1242 (h : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪
      ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) 0)

theorem nb078_fresh_000 :
    (nb078_alpha_dummy_023) ∉
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_023] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cphi (Class.cv (nb078_alpha_dummy_018))))))).fv)
      0

theorem nb078_fresh_001 :
    (nb078_alpha_dummy_047) ∉
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_047] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_002 (f : Var) :
    (nb078_alpha_dummy_024 f) ∉
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_024] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))))).fv)
      0

theorem nb078_fresh_003 (f : Var) :
    (nb078_alpha_dummy_048 f) ∉
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_048] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_004 :
    (nb078_alpha_dummy_059) ∉
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_059] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv)
      0

theorem nb078_fresh_005 :
    (nb078_alpha_dummy_083) ∉
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_083] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_006 (f : Var) :
    (nb078_alpha_dummy_060 f) ∉
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_060] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv)
      0

theorem nb078_fresh_007 (f : Var) :
    (nb078_alpha_dummy_084 f) ∉
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_084] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_008 :
    (nb078_alpha_dummy_101) ∉
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_101] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv)
      0

theorem nb078_fresh_009 :
    (nb078_alpha_dummy_125) ∉
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_125] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_010 (f : Var) :
    (nb078_alpha_dummy_102 f) ∉
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_102] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv)
      0

theorem nb078_fresh_011 (f : Var) :
    (nb078_alpha_dummy_126 f) ∉
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_126] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_012 :
    (nb078_alpha_dummy_1039) ∉
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1039] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_013 :
    (nb078_alpha_dummy_1015) ∉
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1015] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv)
      0

theorem nb078_fresh_014 (h : Var) :
    (nb078_alpha_dummy_1040 h) ∉
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1040] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_015 (h : Var) :
    (nb078_alpha_dummy_1016 h) ∉
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1016] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv)
      0

theorem nb078_fresh_016 :
    (nb078_alpha_dummy_1063) ∉
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1063] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv)
      0

theorem nb078_fresh_017 :
    (nb078_alpha_dummy_1087) ∉
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1087] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_018 (h : Var) :
    (nb078_alpha_dummy_1064 h) ∉
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1064] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv)
      0

theorem nb078_fresh_019 (h : Var) :
    (nb078_alpha_dummy_1088 h) ∉
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1088] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_020 :
    (nb078_alpha_dummy_1099) ∉
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1099] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv)
      0

theorem nb078_fresh_021 :
    (nb078_alpha_dummy_1123) ∉
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1123] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_022 (h : Var) :
    (nb078_alpha_dummy_1100 h) ∉
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1100] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv)
      0

theorem nb078_fresh_023 (h : Var) :
    (nb078_alpha_dummy_1124 h) ∉
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1124] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_024 :
    (nb078_alpha_dummy_1141) ∉
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1141] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv)
      0

theorem nb078_fresh_025 :
    (nb078_alpha_dummy_1165) ∉
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1165] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_026 (h : Var) :
    (nb078_alpha_dummy_1142 h) ∉
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1142] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv)
      0

theorem nb078_fresh_027 (h : Var) :
    (nb078_alpha_dummy_1166 h) ∉
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1166] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_028 :
    (nb078_alpha_dummy_1201) ∉
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1201] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_029 :
    (nb078_alpha_dummy_1177) ∉
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1177] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv)
      0

theorem nb078_fresh_030 (h : Var) :
    (nb078_alpha_dummy_1202 h) ∉
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1202] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_031 (h : Var) :
    (nb078_alpha_dummy_1178 h) ∉
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1178] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv)
      0

theorem nb078_fresh_032 :
    (nb078_alpha_dummy_1237) ∉
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1237] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_033 :
    (nb078_alpha_dummy_1213) ∉
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1213] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv)
      0

theorem nb078_fresh_034 (h : Var) :
    (nb078_alpha_dummy_1238 h) ∉
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1238] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_035 (h : Var) :
    (nb078_alpha_dummy_1214 h) ∉
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1214] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv)
      0

theorem nb078_fresh_036 :
    (nb078_alpha_dummy_161) ∉
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_161] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_037 :
    (nb078_alpha_dummy_137) ∉
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_137] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv)
      0

theorem nb078_fresh_038 (f : Var) :
    (nb078_alpha_dummy_162 f) ∉
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_162] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_039 (f : Var) :
    (nb078_alpha_dummy_138 f) ∉
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_138] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv)
      0

theorem nb078_fresh_040 :
    (nb078_alpha_dummy_197) ∉
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_197] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_041 :
    (nb078_alpha_dummy_173) ∉
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_173] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv)
      0

theorem nb078_fresh_042 (f : Var) :
    (nb078_alpha_dummy_198 f) ∉
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_198] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_043 (f : Var) :
    (nb078_alpha_dummy_174 f) ∉
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_174] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv)
      0

theorem nb078_fresh_044 :
    (nb078_alpha_dummy_237) ∉
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_237] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_045 :
    (nb078_alpha_dummy_213) ∉
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_213] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv)
      0

theorem nb078_fresh_046 (f : Var) :
    (nb078_alpha_dummy_238 f) ∉
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_238] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part010`. -/


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

theorem nb078_fresh_047 (f : Var) :
    (nb078_alpha_dummy_214 f) ∉
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_214] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv)
      0

theorem nb078_fresh_048 :
    (nb078_alpha_dummy_277) ∉
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_277] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_049 :
    (nb078_alpha_dummy_253) ∉
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_253] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv)
      0

theorem nb078_fresh_050 (f : Var) :
    (nb078_alpha_dummy_278 f) ∉
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_278] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_051 (f : Var) :
    (nb078_alpha_dummy_254 f) ∉
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_254] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv)
      0

theorem nb078_fresh_052 :
    (nb078_alpha_dummy_301) ∉
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_301] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv)
      0

theorem nb078_fresh_053 :
    (nb078_alpha_dummy_325) ∉
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_325] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_054 (g : Var) :
    (nb078_alpha_dummy_302 g) ∉
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_302] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv)
      0

theorem nb078_fresh_055 (g : Var) :
    (nb078_alpha_dummy_326 g) ∉
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_326] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_056 :
    (nb078_alpha_dummy_337) ∉
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_337] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cphi (Class.cv (nb078_alpha_dummy_332))))))).fv)
      0

theorem nb078_fresh_057 :
    (nb078_alpha_dummy_361) ∉
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_361] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_331)
            (syn_wrex (nb078_alpha_dummy_332) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_331))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_332)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_058 (g : Var) :
    (nb078_alpha_dummy_338 g) ∉
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_338] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_334 g))))))).fv)
      0

theorem nb078_fresh_059 (g : Var) :
    (nb078_alpha_dummy_362 g) ∉
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_362] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_333 g)
            (syn_wrex (nb078_alpha_dummy_334 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_333 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_334 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_060 :
    (nb078_alpha_dummy_379) ∉
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_379] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))).fv)
      0

theorem nb078_fresh_061 :
    (nb078_alpha_dummy_403) ∉
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_403] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_374)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_062 (g : Var) :
    (nb078_alpha_dummy_380 g) ∉
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_380] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))).fv)
      0

theorem nb078_fresh_063 (g : Var) :
    (nb078_alpha_dummy_404 g) ∉
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_404] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_376 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_064 :
    (nb078_alpha_dummy_439) ∉
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_439] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_410)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_065 :
    (nb078_alpha_dummy_415) ∉
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_415] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))).fv)
      0

theorem nb078_fresh_066 (g : Var) :
    (nb078_alpha_dummy_440 g) ∉
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_440] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_067 (g : Var) :
    (nb078_alpha_dummy_416 g) ∉
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_416] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))).fv)
      0

theorem nb078_fresh_068 :
    (nb078_alpha_dummy_475) ∉
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_475] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_288))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_446)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_069 :
    (nb078_alpha_dummy_451) ∉
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_451] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))).fv)
      0

theorem nb078_fresh_070 (g : Var) :
    (nb078_alpha_dummy_476 g) ∉
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_476] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_291 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_071 (g : Var) :
    (nb078_alpha_dummy_452 g) ∉
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_452] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))).fv)
      0

theorem nb078_fresh_072 :
    (nb078_alpha_dummy_515) ∉
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_515] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_073 :
    (nb078_alpha_dummy_491) ∉
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_491] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_485)
            (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                (syn_cphi (Class.cv (nb078_alpha_dummy_486))))))).fv)
      0

theorem nb078_fresh_074 (g : Var) :
    (nb078_alpha_dummy_516 g) ∉
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_516] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_075 (g : Var) :
    (nb078_alpha_dummy_492 g) ∉
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_492] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_487 g)
            (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))))))).fv)
      0

theorem nb078_fresh_076 :
    (nb078_alpha_dummy_559) ∉
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_559] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_077 :
    (nb078_alpha_dummy_535) ∉
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_535] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))).fv)
      0

theorem nb078_fresh_078 (g : Var) :
    (nb078_alpha_dummy_560 g) ∉
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_560] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_079 (g : Var) :
    (nb078_alpha_dummy_536 g) ∉
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_536] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))).fv)
      0

theorem nb078_fresh_080 :
    (nb078_alpha_dummy_583) ∉
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_583] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))).fv)
      0

theorem nb078_fresh_081 :
    (nb078_alpha_dummy_607) ∉
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_607] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_082 (g : Var) :
    (nb078_alpha_dummy_584 g) ∉
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_584] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))).fv)
      0

theorem nb078_fresh_083 (g : Var) :
    (nb078_alpha_dummy_608 g) ∉
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_608] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_084 :
    (nb078_alpha_dummy_619) ∉
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_619] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))).fv)
      0

theorem nb078_fresh_085 :
    (nb078_alpha_dummy_643) ∉
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_643] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_614)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_086 (g : Var) :
    (nb078_alpha_dummy_620 g) ∉
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_620] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))).fv)
      0

theorem nb078_fresh_087 (g : Var) :
    (nb078_alpha_dummy_644 g) ∉
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_644] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_616 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_088 :
    (nb078_alpha_dummy_661) ∉
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_661] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cphi (Class.cv (nb078_alpha_dummy_656))))))).fv)
      0

theorem nb078_fresh_089 :
    (nb078_alpha_dummy_685) ∉
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_685] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_655)
            (syn_wrex (nb078_alpha_dummy_656) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_655))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_656)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_090 (g : Var) :
    (nb078_alpha_dummy_662 g) ∉
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_662] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_658 g))))))).fv)
      0

theorem nb078_fresh_091 (g : Var) :
    (nb078_alpha_dummy_686 g) ∉
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_686] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_657 g)
            (syn_wrex (nb078_alpha_dummy_658 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_657 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_658 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_092 :
    (nb078_alpha_dummy_721) ∉
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_721] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_649))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_692)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_093 :
    (nb078_alpha_dummy_697) ∉
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_697] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))).fv)
      0

theorem nb078_fresh_094 (g : Var) :
    (nb078_alpha_dummy_722 g) ∉
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_722] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_651 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_095 (g : Var) :
    (nb078_alpha_dummy_698 g) ∉
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_698] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))).fv)
      0

theorem nb078_fresh_096 :
    (nb078_alpha_dummy_757) ∉
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_757] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_570))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_728)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_097 :
    (nb078_alpha_dummy_733) ∉
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_733] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))).fv)
      0

theorem nb078_fresh_098 (g : Var) :
    (nb078_alpha_dummy_758 g) ∉
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_758] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_573 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_730 g)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_099 (g : Var) :
    (nb078_alpha_dummy_734 g) ∉
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_734] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))).fv)
      0

theorem nb078_fresh_100 :
    (nb078_alpha_dummy_781) ∉
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_781] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))).fv)
      0

theorem nb078_fresh_101 :
    (nb078_alpha_dummy_805) ∉
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_805] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_102 (h : Var) :
    (nb078_alpha_dummy_782 h) ∉
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_782] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))).fv)
      0

theorem nb078_fresh_103 (h : Var) :
    (nb078_alpha_dummy_806 h) ∉
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_806] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part011`. -/


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

theorem nb078_fresh_104 :
    (nb078_alpha_dummy_817) ∉
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_817] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))).fv)
      0

theorem nb078_fresh_105 :
    (nb078_alpha_dummy_841) ∉
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_841] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_812)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_106 (h : Var) :
    (nb078_alpha_dummy_818 h) ∉
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_818] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))).fv)
      0

theorem nb078_fresh_107 (h : Var) :
    (nb078_alpha_dummy_842 h) ∉
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_842] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_814 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_108 :
    (nb078_alpha_dummy_859) ∉
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_859] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv)
      0

theorem nb078_fresh_109 :
    (nb078_alpha_dummy_883) ∉
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_883] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_110 (h : Var) :
    (nb078_alpha_dummy_860 h) ∉
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_860] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv)
      0

theorem nb078_fresh_111 (h : Var) :
    (nb078_alpha_dummy_884 h) ∉
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_884] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_112 :
    (nb078_alpha_dummy_919) ∉
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_919] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_113 :
    (nb078_alpha_dummy_895) ∉
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_895] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv)
      0

theorem nb078_fresh_114 (h : Var) :
    (nb078_alpha_dummy_920 h) ∉
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_920] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_115 (h : Var) :
    (nb078_alpha_dummy_896 h) ∉
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_896] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv)
      0

theorem nb078_fresh_116 :
    (nb078_alpha_dummy_955) ∉
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_955] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_117 :
    (nb078_alpha_dummy_931) ∉
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_931] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv)
      0

theorem nb078_fresh_118 (h : Var) :
    (nb078_alpha_dummy_956 h) ∉
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_956] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_119 (h : Var) :
    (nb078_alpha_dummy_932 h) ∉
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_932] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv)
      0

theorem nb078_fresh_120 :
    (nb078_alpha_dummy_995) ∉
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_995] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_121 :
    (nb078_alpha_dummy_971) ∉
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_971] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv)
      0

theorem nb078_fresh_122 (h : Var) :
    (nb078_alpha_dummy_996 h) ∉
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_996] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb078_fresh_123 (h : Var) :
    (nb078_alpha_dummy_972 h) ∉
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) :=
  by
  simpa only [nb078_alpha_dummy_972] using
    freshVar_not_mem
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv)
      0

theorem nb078_fresh_124 :
    (nb078_alpha_dummy_089) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv) := by
  simpa only [nb078_alpha_dummy_089] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv) 0

theorem nb078_fresh_125 :
    (nb078_alpha_dummy_090) ∉ (((Class.cv (nb078_alpha_dummy_000))).fv) := by
  simpa only [nb078_alpha_dummy_090] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv) 1

theorem nb078_distinct_126 : (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_090) := by
  simpa only [nb078_alpha_dummy_089, nb078_alpha_dummy_090] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_127 :
    (nb078_alpha_dummy_009) ∉
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
      0

theorem nb078_fresh_128 :
    (nb078_alpha_dummy_010) ∉
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_010] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
      1

theorem nb078_fresh_129 :
    (nb078_alpha_dummy_011) ∉
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_011] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv)
      2

theorem nb078_distinct_130 : (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_010) := by
  simpa only [nb078_alpha_dummy_009, nb078_alpha_dummy_010] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_131 : (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_011) := by
  simpa only [nb078_alpha_dummy_009, nb078_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_132 : (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_011) := by
  simpa only [nb078_alpha_dummy_010, nb078_alpha_dummy_011] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_133 :
    (nb078_alpha_dummy_243) ∉
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_243] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_134 :
    (nb078_alpha_dummy_244) ∉
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_244] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_135 : (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_244) := by
  simpa only [nb078_alpha_dummy_243, nb078_alpha_dummy_244] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_136 :
    (nb078_alpha_dummy_367) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv) := by
  simpa only [nb078_alpha_dummy_367] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv) 0

theorem nb078_fresh_137 :
    (nb078_alpha_dummy_368) ∉ (((Class.cv (nb078_alpha_dummy_001))).fv) := by
  simpa only [nb078_alpha_dummy_368] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv) 1

theorem nb078_distinct_138 : (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_368) := by
  simpa only [nb078_alpha_dummy_367, nb078_alpha_dummy_368] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_139 :
    (nb078_alpha_dummy_287) ∉
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_287] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
      0

theorem nb078_fresh_140 :
    (nb078_alpha_dummy_288) ∉
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_288] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
      1

theorem nb078_fresh_141 :
    (nb078_alpha_dummy_289) ∉
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_289] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
      2

theorem nb078_distinct_142 : (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_288) := by
  simpa only [nb078_alpha_dummy_287, nb078_alpha_dummy_288] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_143 : (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_289) := by
  simpa only [nb078_alpha_dummy_287, nb078_alpha_dummy_289] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_144 : (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_289) := by
  simpa only [nb078_alpha_dummy_288, nb078_alpha_dummy_289] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_145 :
    (nb078_alpha_dummy_525) ∉
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_525] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_146 :
    (nb078_alpha_dummy_526) ∉
      (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_526] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_147 : (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_526) := by
  simpa only [nb078_alpha_dummy_525, nb078_alpha_dummy_526] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_148 :
    (nb078_alpha_dummy_847) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv) := by
  simpa only [nb078_alpha_dummy_847] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv) 0

theorem nb078_fresh_149 :
    (nb078_alpha_dummy_848) ∉ (((Class.cv (nb078_alpha_dummy_002))).fv) := by
  simpa only [nb078_alpha_dummy_848] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv) 1

theorem nb078_distinct_150 : (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_848) := by
  simpa only [nb078_alpha_dummy_847, nb078_alpha_dummy_848] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_151 :
    (nb078_alpha_dummy_767) ∉
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_767] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
      0

theorem nb078_fresh_152 :
    (nb078_alpha_dummy_768) ∉
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_768] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
      1

theorem nb078_fresh_153 :
    (nb078_alpha_dummy_769) ∉
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) :=
  by
  simpa only [nb078_alpha_dummy_769] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
      2

theorem nb078_distinct_154 : (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_768) := by
  simpa only [nb078_alpha_dummy_767, nb078_alpha_dummy_768] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_155 : (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_769) := by
  simpa only [nb078_alpha_dummy_767, nb078_alpha_dummy_769] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_156 : (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_769) := by
  simpa only [nb078_alpha_dummy_768, nb078_alpha_dummy_769] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_157 :
    (nb078_alpha_dummy_1005) ∉
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1005] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 0

theorem nb078_fresh_158 :
    (nb078_alpha_dummy_1006) ∉
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) :=
  by
  simpa only [nb078_alpha_dummy_1006] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) 1

theorem nb078_distinct_159 : (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1006) := by
  simpa only [nb078_alpha_dummy_1005, nb078_alpha_dummy_1006] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_160 :
    (nb078_alpha_dummy_017) ∉
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  simpa only [nb078_alpha_dummy_017] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      0

theorem nb078_fresh_161 :
    (nb078_alpha_dummy_018) ∉
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  simpa only [nb078_alpha_dummy_018] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      1

theorem nb078_distinct_162 : (nb078_alpha_dummy_017) ≠ (nb078_alpha_dummy_018) := by
  simpa only [nb078_alpha_dummy_017, nb078_alpha_dummy_018] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_163 :
    (nb078_alpha_dummy_053) ∉
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) :=
  by
  simpa only [nb078_alpha_dummy_053] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv)
      0

theorem nb078_fresh_164 :
    (nb078_alpha_dummy_054) ∉
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) :=
  by
  simpa only [nb078_alpha_dummy_054] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv)
      1

theorem nb078_distinct_165 : (nb078_alpha_dummy_053) ≠ (nb078_alpha_dummy_054) := by
  simpa only [nb078_alpha_dummy_053, nb078_alpha_dummy_054] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_166 :
    (nb078_alpha_dummy_167) ∉
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  simpa only [nb078_alpha_dummy_167] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      0

theorem nb078_fresh_167 :
    (nb078_alpha_dummy_168) ∉
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  simpa only [nb078_alpha_dummy_168] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      1

theorem nb078_distinct_168 : (nb078_alpha_dummy_167) ≠ (nb078_alpha_dummy_168) := by
  simpa only [nb078_alpha_dummy_167, nb078_alpha_dummy_168] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_169 (f : Var) :
    (nb078_alpha_dummy_019 f) ∉
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_019] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv)
      0

theorem nb078_fresh_170 (f : Var) :
    (nb078_alpha_dummy_020 f) ∉
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_020] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv)
      1

theorem nb078_distinct_171 (f : Var) :
    (nb078_alpha_dummy_019 f) ≠ (nb078_alpha_dummy_020 f) := by
  simpa only [nb078_alpha_dummy_019, nb078_alpha_dummy_020] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_172 (f : Var) :
    (nb078_alpha_dummy_055 f) ∉
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_055] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv)
      0

theorem nb078_fresh_173 (f : Var) :
    (nb078_alpha_dummy_056 f) ∉
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_056] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv)
      1

theorem nb078_distinct_174 (f : Var) :
    (nb078_alpha_dummy_055 f) ≠ (nb078_alpha_dummy_056 f) := by
  simpa only [nb078_alpha_dummy_055, nb078_alpha_dummy_056] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_014 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_175 (f : Var) :
    (nb078_alpha_dummy_169 f) ∉
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_169] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv)
      0

theorem nb078_fresh_176 (f : Var) :
    (nb078_alpha_dummy_170 f) ∉
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_170] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv)
      1

theorem nb078_distinct_177 (f : Var) :
    (nb078_alpha_dummy_169 f) ≠ (nb078_alpha_dummy_170 f) := by
  simpa only [nb078_alpha_dummy_169, nb078_alpha_dummy_170] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_178 :
    (nb078_alpha_dummy_025) ∉ (((Class.cv (nb078_alpha_dummy_018))).fv) := by
  simpa only [nb078_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_018))).fv) 0

theorem nb078_fresh_179 :
    (nb078_alpha_dummy_026) ∉ (((Class.cv (nb078_alpha_dummy_018))).fv) := by
  simpa only [nb078_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_018))).fv) 1

theorem nb078_distinct_180 : (nb078_alpha_dummy_025) ≠ (nb078_alpha_dummy_026) := by
  simpa only [nb078_alpha_dummy_025, nb078_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_018))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_181 (f : Var) :
    (nb078_alpha_dummy_027 f) ∉ (((Class.cv (nb078_alpha_dummy_020 f))).fv) := by
  simpa only [nb078_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_020 f))).fv) 0

theorem nb078_fresh_182 (f : Var) :
    (nb078_alpha_dummy_028 f) ∉ (((Class.cv (nb078_alpha_dummy_020 f))).fv) := by
  simpa only [nb078_alpha_dummy_028] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_020 f))).fv) 1

theorem nb078_distinct_183 (f : Var) :
    (nb078_alpha_dummy_027 f) ≠ (nb078_alpha_dummy_028 f) := by
  simpa only [nb078_alpha_dummy_027, nb078_alpha_dummy_028] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_020 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_184 :
    (nb078_alpha_dummy_031) ∉
      (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_031] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_185 :
    (nb078_alpha_dummy_032) ∉
      (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_032] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_186 :
    (nb078_alpha_dummy_033) ∉
      (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_033] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_187 : (nb078_alpha_dummy_031) ≠ (nb078_alpha_dummy_032) := by
  simpa only [nb078_alpha_dummy_031, nb078_alpha_dummy_032] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_188 : (nb078_alpha_dummy_031) ≠ (nb078_alpha_dummy_033) := by
  simpa only [nb078_alpha_dummy_031, nb078_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_189 : (nb078_alpha_dummy_032) ≠ (nb078_alpha_dummy_033) := by
  simpa only [nb078_alpha_dummy_032, nb078_alpha_dummy_033] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_025))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_190 (f : Var) :
    (nb078_alpha_dummy_034 f) ∉
      (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_034] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_191 (f : Var) :
    (nb078_alpha_dummy_035 f) ∉
      (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_035] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_192 (f : Var) :
    (nb078_alpha_dummy_036 f) ∉
      (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_036] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_193 (f : Var) :
    (nb078_alpha_dummy_034 f) ≠ (nb078_alpha_dummy_035 f) := by
  simpa only [nb078_alpha_dummy_034, nb078_alpha_dummy_035] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_194 (f : Var) :
    (nb078_alpha_dummy_034 f) ≠ (nb078_alpha_dummy_036 f) := by
  simpa only [nb078_alpha_dummy_034, nb078_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_195 (f : Var) :
    (nb078_alpha_dummy_035 f) ≠ (nb078_alpha_dummy_036 f) := by
  simpa only [nb078_alpha_dummy_035, nb078_alpha_dummy_036] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_027 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_196 :
    (nb078_alpha_dummy_043) ∉
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv) :=
  by
  simpa only [nb078_alpha_dummy_043] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_032))).fv)
      0

theorem nb078_fresh_197 :
    (nb078_alpha_dummy_039) ∉
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) :=
  by
  simpa only [nb078_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_032))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv)
      0

theorem nb078_fresh_198 :
    (nb078_alpha_dummy_045) ∉
      (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv) :=
  by
  simpa only [nb078_alpha_dummy_045] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_033))).fv ∪ ((Class.cv (nb078_alpha_dummy_033))).fv)
      0

theorem nb078_fresh_199 (f : Var) :
    (nb078_alpha_dummy_044 f) ∉
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_044] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_035 f))).fv)
      0

theorem nb078_fresh_200 (f : Var) :
    (nb078_alpha_dummy_040 f) ∉
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_040] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_035 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv)
      0

theorem nb078_fresh_201 (f : Var) :
    (nb078_alpha_dummy_046 f) ∉
      (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_046] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_036 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_036 f))).fv)
      0

theorem nb078_fresh_202 :
    (nb078_alpha_dummy_061) ∉ (((Class.cv (nb078_alpha_dummy_054))).fv) := by
  simpa only [nb078_alpha_dummy_061] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_054))).fv) 0

theorem nb078_fresh_203 :
    (nb078_alpha_dummy_062) ∉ (((Class.cv (nb078_alpha_dummy_054))).fv) := by
  simpa only [nb078_alpha_dummy_062] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_054))).fv) 1

theorem nb078_distinct_204 : (nb078_alpha_dummy_061) ≠ (nb078_alpha_dummy_062) := by
  simpa only [nb078_alpha_dummy_061, nb078_alpha_dummy_062] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_054))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_205 (f : Var) :
    (nb078_alpha_dummy_063 f) ∉ (((Class.cv (nb078_alpha_dummy_056 f))).fv) := by
  simpa only [nb078_alpha_dummy_063] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_056 f))).fv) 0

theorem nb078_fresh_206 (f : Var) :
    (nb078_alpha_dummy_064 f) ∉ (((Class.cv (nb078_alpha_dummy_056 f))).fv) := by
  simpa only [nb078_alpha_dummy_064] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_056 f))).fv) 1

theorem nb078_distinct_207 (f : Var) :
    (nb078_alpha_dummy_063 f) ≠ (nb078_alpha_dummy_064 f) := by
  simpa only [nb078_alpha_dummy_063, nb078_alpha_dummy_064] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_056 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_208 :
    (nb078_alpha_dummy_067) ∉
      (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_067] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_209 :
    (nb078_alpha_dummy_068) ∉
      (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_068] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_210 :
    (nb078_alpha_dummy_069) ∉
      (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_069] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_211 : (nb078_alpha_dummy_067) ≠ (nb078_alpha_dummy_068) := by
  simpa only [nb078_alpha_dummy_067, nb078_alpha_dummy_068] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_212 : (nb078_alpha_dummy_067) ≠ (nb078_alpha_dummy_069) := by
  simpa only [nb078_alpha_dummy_067, nb078_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_213 : (nb078_alpha_dummy_068) ≠ (nb078_alpha_dummy_069) := by
  simpa only [nb078_alpha_dummy_068, nb078_alpha_dummy_069] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_214 (f : Var) :
    (nb078_alpha_dummy_070 f) ∉
      (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_070] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 0

theorem nb078_fresh_215 (f : Var) :
    (nb078_alpha_dummy_071 f) ∉
      (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_071] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 1

theorem nb078_fresh_216 (f : Var) :
    (nb078_alpha_dummy_072 f) ∉
      (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb078_alpha_dummy_072] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) 2

theorem nb078_distinct_217 (f : Var) :
    (nb078_alpha_dummy_070 f) ≠ (nb078_alpha_dummy_071 f) := by
  simpa only [nb078_alpha_dummy_070, nb078_alpha_dummy_071] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_218 (f : Var) :
    (nb078_alpha_dummy_070 f) ≠ (nb078_alpha_dummy_072 f) := by
  simpa only [nb078_alpha_dummy_070, nb078_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_219 (f : Var) :
    (nb078_alpha_dummy_071 f) ≠ (nb078_alpha_dummy_072 f) := by
  simpa only [nb078_alpha_dummy_071, nb078_alpha_dummy_072] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_220 :
    (nb078_alpha_dummy_079) ∉
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) :=
  by
  simpa only [nb078_alpha_dummy_079] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv)
      0

theorem nb078_fresh_221 :
    (nb078_alpha_dummy_075) ∉
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) :=
  by
  simpa only [nb078_alpha_dummy_075] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv)
      0

theorem nb078_fresh_222 :
    (nb078_alpha_dummy_081) ∉
      (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) :=
  by
  simpa only [nb078_alpha_dummy_081] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv)
      0

theorem nb078_fresh_223 (f : Var) :
    (nb078_alpha_dummy_080 f) ∉
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_080] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv)
      0

theorem nb078_fresh_224 (f : Var) :
    (nb078_alpha_dummy_076 f) ∉
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_076] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv)
      0

theorem nb078_fresh_225 (f : Var) :
    (nb078_alpha_dummy_082 f) ∉
      (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_082] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv)
      0

theorem nb078_fresh_226 :
    (nb078_alpha_dummy_095) ∉
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) :=
  by
  simpa only [nb078_alpha_dummy_095] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv)
      0

theorem nb078_fresh_227 :
    (nb078_alpha_dummy_096) ∉
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) :=
  by
  simpa only [nb078_alpha_dummy_096] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv)
      1

theorem nb078_distinct_228 : (nb078_alpha_dummy_095) ≠ (nb078_alpha_dummy_096) := by
  simpa only [nb078_alpha_dummy_095, nb078_alpha_dummy_096] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_229 :
    (nb078_alpha_dummy_131) ∉
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) :=
  by
  simpa only [nb078_alpha_dummy_131] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv)
      0

theorem nb078_fresh_230 :
    (nb078_alpha_dummy_132) ∉
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) :=
  by
  simpa only [nb078_alpha_dummy_132] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv)
      1

theorem nb078_distinct_231 : (nb078_alpha_dummy_131) ≠ (nb078_alpha_dummy_132) := by
  simpa only [nb078_alpha_dummy_131, nb078_alpha_dummy_132] using
    (freshVar_injective
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_232 (f : Var) :
    (nb078_alpha_dummy_097 f) ∉
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_097] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv)
      0

theorem nb078_fresh_233 (f : Var) :
    (nb078_alpha_dummy_098 f) ∉
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_098] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv)
      1

theorem nb078_distinct_234 (f : Var) :
    (nb078_alpha_dummy_097 f) ≠ (nb078_alpha_dummy_098 f) := by
  simpa only [nb078_alpha_dummy_097, nb078_alpha_dummy_098] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_092 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_235 (f : Var) :
    (nb078_alpha_dummy_133 f) ∉
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_133] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv)
      0

theorem nb078_fresh_236 (f : Var) :
    (nb078_alpha_dummy_134 f) ∉
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) :=
  by
  simpa only [nb078_alpha_dummy_134] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv)
      1

theorem nb078_distinct_237 (f : Var) :
    (nb078_alpha_dummy_133 f) ≠ (nb078_alpha_dummy_134 f) := by
  simpa only [nb078_alpha_dummy_133, nb078_alpha_dummy_134] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪
        ((Class.cv (nb078_alpha_dummy_091 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_238 :
    (nb078_alpha_dummy_103) ∉ (((Class.cv (nb078_alpha_dummy_096))).fv) := by
  simpa only [nb078_alpha_dummy_103] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_096))).fv) 0

theorem nb078_fresh_239 :
    (nb078_alpha_dummy_104) ∉ (((Class.cv (nb078_alpha_dummy_096))).fv) := by
  simpa only [nb078_alpha_dummy_104] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_096))).fv) 1

theorem nb078_distinct_240 : (nb078_alpha_dummy_103) ≠ (nb078_alpha_dummy_104) := by
  simpa only [nb078_alpha_dummy_103, nb078_alpha_dummy_104] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_096))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_241 (f : Var) :
    (nb078_alpha_dummy_105 f) ∉ (((Class.cv (nb078_alpha_dummy_098 f))).fv) := by
  simpa only [nb078_alpha_dummy_105] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_098 f))).fv) 0

theorem nb078_fresh_242 (f : Var) :
    (nb078_alpha_dummy_106 f) ∉ (((Class.cv (nb078_alpha_dummy_098 f))).fv) := by
  simpa only [nb078_alpha_dummy_106] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_098 f))).fv) 1

theorem nb078_distinct_243 (f : Var) :
    (nb078_alpha_dummy_105 f) ≠ (nb078_alpha_dummy_106 f) := by
  simpa only [nb078_alpha_dummy_105, nb078_alpha_dummy_106] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_098 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_244 :
    (nb078_alpha_dummy_1009) ∉
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1009] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv)
      0

theorem nb078_fresh_245 :
    (nb078_alpha_dummy_1010) ∉
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1010] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv)
      1

theorem nb078_distinct_246 : (nb078_alpha_dummy_1009) ≠ (nb078_alpha_dummy_1010) := by
  simpa only [nb078_alpha_dummy_1009, nb078_alpha_dummy_1010] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1006))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1005))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_247 (h : Var) :
    (nb078_alpha_dummy_1011 h) ∉
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1011] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv)
      0

theorem nb078_fresh_248 (h : Var) :
    (nb078_alpha_dummy_1012 h) ∉
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) :=
  by
  simpa only [nb078_alpha_dummy_1012] using
    freshVar_not_mem
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_1007 h))).fv)
      1

theorem nb078_distinct_249 (h : Var) :
    (nb078_alpha_dummy_1011 h) ≠ (nb078_alpha_dummy_1012 h) := by
  simpa only [nb078_alpha_dummy_1011, nb078_alpha_dummy_1012] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_250 :
    (nb078_alpha_dummy_1017) ∉ (((Class.cv (nb078_alpha_dummy_1010))).fv) := by
  simpa only [nb078_alpha_dummy_1017] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1010))).fv) 0

theorem nb078_fresh_251 :
    (nb078_alpha_dummy_1018) ∉ (((Class.cv (nb078_alpha_dummy_1010))).fv) := by
  simpa only [nb078_alpha_dummy_1018] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1010))).fv) 1

theorem nb078_distinct_252 : (nb078_alpha_dummy_1017) ≠ (nb078_alpha_dummy_1018) := by
  simpa only [nb078_alpha_dummy_1017, nb078_alpha_dummy_1018] using
    (freshVar_injective (((Class.cv (nb078_alpha_dummy_1010))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_253 (h : Var) :
    (nb078_alpha_dummy_1019 h) ∉ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) := by
  simpa only [nb078_alpha_dummy_1019] using
    freshVar_not_mem (((Class.cv (nb078_alpha_dummy_1012 h))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
