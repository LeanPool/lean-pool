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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_900`. -/
@[expose]
noncomputable def nb078AlphaDummy900 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy892 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_901`. -/
@[expose]
noncomputable def nb078AlphaDummy901 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy897)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy897)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy897))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_902`. -/
@[expose]
noncomputable def nb078AlphaDummy902 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy899 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy899 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy899 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_903`. -/
@[expose]
noncomputable def nb078AlphaDummy903 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_904`. -/
@[expose]
noncomputable def nb078AlphaDummy904 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_905`. -/
@[expose]
noncomputable def nb078AlphaDummy905 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_906`. -/
@[expose]
noncomputable def nb078AlphaDummy906 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_907`. -/
@[expose]
noncomputable def nb078AlphaDummy907 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_908`. -/
@[expose]
noncomputable def nb078AlphaDummy908 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_909`. -/
@[expose]
noncomputable def nb078AlphaDummy909 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy904))
          (Class.cv (nb078AlphaDummy905)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_910`. -/
@[expose]
noncomputable def nb078AlphaDummy910 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy907 h))
          (Class.cv (nb078AlphaDummy908 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy907 h)) (Class.cv (nb078AlphaDummy908 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_911`. -/
@[expose]
noncomputable def nb078AlphaDummy911 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_912`. -/
@[expose]
noncomputable def nb078AlphaDummy912 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy907 h))).fv ∪
      ((Class.cv (nb078AlphaDummy908 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_913`. -/
@[expose]
noncomputable def nb078AlphaDummy913 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy904)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy905)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_914`. -/
@[expose]
noncomputable def nb078AlphaDummy914 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy907 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy908 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_915`. -/
@[expose]
noncomputable def nb078AlphaDummy915 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy904))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_916`. -/
@[expose]
noncomputable def nb078AlphaDummy916 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy907 h))).fv ∪
      ((Class.cv (nb078AlphaDummy907 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_917`. -/
@[expose]
noncomputable def nb078AlphaDummy917 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy905))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_918`. -/
@[expose]
noncomputable def nb078AlphaDummy918 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy908 h))).fv ∪
      ((Class.cv (nb078AlphaDummy908 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_919`. -/
@[expose]
noncomputable def nb078AlphaDummy919 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy889)
          (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
            (Wff.classEq (Class.cv (nb078AlphaDummy889))
              (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy889)
          (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
            (Wff.classEq (Class.cv (nb078AlphaDummy889))
              (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_920`. -/
@[expose]
noncomputable def nb078AlphaDummy920 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy891 h)
          (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy891 h)
          (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_921`. -/
@[expose]
noncomputable def nb078AlphaDummy921 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy890))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_922`. -/
@[expose]
noncomputable def nb078AlphaDummy922 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy892 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_923`. -/
@[expose]
noncomputable def nb078AlphaDummy923 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy890)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy890)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_924`. -/
@[expose]
noncomputable def nb078AlphaDummy924 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_925`. -/
@[expose]
noncomputable def nb078AlphaDummy925 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_926`. -/
@[expose]
noncomputable def nb078AlphaDummy926 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_927`. -/
@[expose]
noncomputable def nb078AlphaDummy927 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy772 h))).fv ∪
      ((Class.cv (nb078AlphaDummy771 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_928`. -/
@[expose]
noncomputable def nb078AlphaDummy928 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy772 h))).fv ∪
      ((Class.cv (nb078AlphaDummy771 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_929`. -/
@[expose]
noncomputable def nb078AlphaDummy929 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_930`. -/
@[expose]
noncomputable def nb078AlphaDummy930 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_931`. -/
@[expose]
noncomputable def nb078AlphaDummy931 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy925)
          (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
            (Wff.classEq (Class.cv (nb078AlphaDummy925))
              (synCphi (Class.cv (nb078AlphaDummy926))))))).fv ∪
      ((Class.cab (nb078AlphaDummy925)
          (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
            (Wff.classEq (Class.cv (nb078AlphaDummy925))
              (synCphi (Class.cv (nb078AlphaDummy926))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_932`. -/
@[expose]
noncomputable def nb078AlphaDummy932 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy927 h)
          (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
              (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy927 h)
          (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
              (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_933`. -/
@[expose]
noncomputable def nb078AlphaDummy933 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy926))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_934`. -/
@[expose]
noncomputable def nb078AlphaDummy934 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy926))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_935`. -/
@[expose]
noncomputable def nb078AlphaDummy935 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy928 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_936`. -/
@[expose]
noncomputable def nb078AlphaDummy936 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy928 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_937`. -/
@[expose]
noncomputable def nb078AlphaDummy937 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy933)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy933)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy933))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_938`. -/
@[expose]
noncomputable def nb078AlphaDummy938 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy935 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy935 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy935 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_939`. -/
@[expose]
noncomputable def nb078AlphaDummy939 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_940`. -/
@[expose]
noncomputable def nb078AlphaDummy940 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_941`. -/
@[expose]
noncomputable def nb078AlphaDummy941 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_942`. -/
@[expose]
noncomputable def nb078AlphaDummy942 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_943`. -/
@[expose]
noncomputable def nb078AlphaDummy943 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_944`. -/
@[expose]
noncomputable def nb078AlphaDummy944 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_945`. -/
@[expose]
noncomputable def nb078AlphaDummy945 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy940))
          (Class.cv (nb078AlphaDummy941)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_946`. -/
@[expose]
noncomputable def nb078AlphaDummy946 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy943 h))
          (Class.cv (nb078AlphaDummy944 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy943 h)) (Class.cv (nb078AlphaDummy944 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_947`. -/
@[expose]
noncomputable def nb078AlphaDummy947 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_948`. -/
@[expose]
noncomputable def nb078AlphaDummy948 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy943 h))).fv ∪
      ((Class.cv (nb078AlphaDummy944 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_949`. -/
@[expose]
noncomputable def nb078AlphaDummy949 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy940)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy941)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_950`. -/
@[expose]
noncomputable def nb078AlphaDummy950 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy943 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy944 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_951`. -/
@[expose]
noncomputable def nb078AlphaDummy951 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy940))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_952`. -/
@[expose]
noncomputable def nb078AlphaDummy952 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy943 h))).fv ∪
      ((Class.cv (nb078AlphaDummy943 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_953`. -/
@[expose]
noncomputable def nb078AlphaDummy953 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy941))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_954`. -/
@[expose]
noncomputable def nb078AlphaDummy954 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy944 h))).fv ∪
      ((Class.cv (nb078AlphaDummy944 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_955`. -/
@[expose]
noncomputable def nb078AlphaDummy955 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy925)
          (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
            (Wff.classEq (Class.cv (nb078AlphaDummy925))
              (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy925)
          (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
            (Wff.classEq (Class.cv (nb078AlphaDummy925))
              (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_956`. -/
@[expose]
noncomputable def nb078AlphaDummy956 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy927 h)
          (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy927 h)
          (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_957`. -/
@[expose]
noncomputable def nb078AlphaDummy957 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy926))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_958`. -/
@[expose]
noncomputable def nb078AlphaDummy958 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_959`. -/
@[expose]
noncomputable def nb078AlphaDummy959 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy926)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy926)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_960`. -/
@[expose]
noncomputable def nb078AlphaDummy960 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_961`. -/
@[expose]
noncomputable def nb078AlphaDummy961 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_962`. -/
@[expose]
noncomputable def nb078AlphaDummy962 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_963`. -/
@[expose]
noncomputable def nb078AlphaDummy963 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_964`. -/
@[expose]
noncomputable def nb078AlphaDummy964 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_965`. -/
@[expose]
noncomputable def nb078AlphaDummy965 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_966`. -/
@[expose]
noncomputable def nb078AlphaDummy966 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_967`. -/
@[expose]
noncomputable def nb078AlphaDummy967 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy964 h))).fv ∪
      ((Class.cv (nb078AlphaDummy963 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_968`. -/
@[expose]
noncomputable def nb078AlphaDummy968 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy964 h))).fv ∪
      ((Class.cv (nb078AlphaDummy963 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_969`. -/
@[expose]
noncomputable def nb078AlphaDummy969 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_970`. -/
@[expose]
noncomputable def nb078AlphaDummy970 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_971`. -/
@[expose]
noncomputable def nb078AlphaDummy971 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy965)
          (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
            (Wff.classEq (Class.cv (nb078AlphaDummy965))
              (synCphi (Class.cv (nb078AlphaDummy966))))))).fv ∪
      ((Class.cab (nb078AlphaDummy965)
          (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
            (Wff.classEq (Class.cv (nb078AlphaDummy965))
              (synCphi (Class.cv (nb078AlphaDummy966))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_972`. -/
@[expose]
noncomputable def nb078AlphaDummy972 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy967 h)
          (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
              (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy967 h)
          (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
              (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_973`. -/
@[expose]
noncomputable def nb078AlphaDummy973 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy966))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_974`. -/
@[expose]
noncomputable def nb078AlphaDummy974 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy966))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_975`. -/
@[expose]
noncomputable def nb078AlphaDummy975 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy968 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_976`. -/
@[expose]
noncomputable def nb078AlphaDummy976 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy968 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_977`. -/
@[expose]
noncomputable def nb078AlphaDummy977 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy973)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy973)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy973))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_978`. -/
@[expose]
noncomputable def nb078AlphaDummy978 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy975 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy975 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy975 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_979`. -/
@[expose]
noncomputable def nb078AlphaDummy979 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_980`. -/
@[expose]
noncomputable def nb078AlphaDummy980 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_981`. -/
@[expose]
noncomputable def nb078AlphaDummy981 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_982`. -/
@[expose]
noncomputable def nb078AlphaDummy982 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_983`. -/
@[expose]
noncomputable def nb078AlphaDummy983 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_984`. -/
@[expose]
noncomputable def nb078AlphaDummy984 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_985`. -/
@[expose]
noncomputable def nb078AlphaDummy985 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy980))
          (Class.cv (nb078AlphaDummy981)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_986`. -/
@[expose]
noncomputable def nb078AlphaDummy986 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy983 h))
          (Class.cv (nb078AlphaDummy984 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy983 h)) (Class.cv (nb078AlphaDummy984 h)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_987`. -/
@[expose]
noncomputable def nb078AlphaDummy987 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_988`. -/
@[expose]
noncomputable def nb078AlphaDummy988 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy983 h))).fv ∪
      ((Class.cv (nb078AlphaDummy984 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_989`. -/
@[expose]
noncomputable def nb078AlphaDummy989 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy980)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy981)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_990`. -/
@[expose]
noncomputable def nb078AlphaDummy990 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy983 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy984 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_991`. -/
@[expose]
noncomputable def nb078AlphaDummy991 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy980))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_992`. -/
@[expose]
noncomputable def nb078AlphaDummy992 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy983 h))).fv ∪
      ((Class.cv (nb078AlphaDummy983 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_993`. -/
@[expose]
noncomputable def nb078AlphaDummy993 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy981))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_994`. -/
@[expose]
noncomputable def nb078AlphaDummy994 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy984 h))).fv ∪
      ((Class.cv (nb078AlphaDummy984 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_995`. -/
@[expose]
noncomputable def nb078AlphaDummy995 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy965)
          (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
            (Wff.classEq (Class.cv (nb078AlphaDummy965))
              (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy965)
          (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
            (Wff.classEq (Class.cv (nb078AlphaDummy965))
              (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_996`. -/
@[expose]
noncomputable def nb078AlphaDummy996 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy967 h)
          (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy967 h)
          (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_997`. -/
@[expose]
noncomputable def nb078AlphaDummy997 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy966))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_998`. -/
@[expose]
noncomputable def nb078AlphaDummy998 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy968 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_999`. -/
@[expose]
noncomputable def nb078AlphaDummy999 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy966)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy966)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1000`. -/
@[expose]
noncomputable def nb078AlphaDummy1000 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1001`. -/
@[expose]
noncomputable def nb078AlphaDummy1001 : Var :=
  (freshVar (((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
          (Class.cv (nb078AlphaDummy004)))).fv ∪
      ((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
          (Class.cv (nb078AlphaDummy004)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1002`. -/
@[expose]
noncomputable def nb078AlphaDummy1002 (y : Var) (h : Var) : Var :=
  (freshVar (((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv ∪
      ((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1003`. -/
@[expose]
noncomputable def nb078AlphaDummy1003 : Var :=
  (freshVar (((synCrn (Class.cv (nb078AlphaDummy002)))).fv ∪
      ((Class.cv (nb078AlphaDummy004))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1004`. -/
@[expose]
noncomputable def nb078AlphaDummy1004 (y : Var) (h : Var) : Var :=
  (freshVar (((synCrn (Class.cv h))).fv ∪ ((Class.cv y)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1005`. -/
@[expose]
noncomputable def nb078AlphaDummy1005 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1006`. -/
@[expose]
noncomputable def nb078AlphaDummy1006 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1007`. -/
@[expose]
noncomputable def nb078AlphaDummy1007 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCvv)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1008`. -/
@[expose]
noncomputable def nb078AlphaDummy1008 (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((synCvv)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1009`. -/
@[expose]
noncomputable def nb078AlphaDummy1009 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1010`. -/
@[expose]
noncomputable def nb078AlphaDummy1010 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1011`. -/
@[expose]
noncomputable def nb078AlphaDummy1011 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1007 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1012`. -/
@[expose]
noncomputable def nb078AlphaDummy1012 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1007 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1013`. -/
@[expose]
noncomputable def nb078AlphaDummy1013 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1014`. -/
@[expose]
noncomputable def nb078AlphaDummy1014 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1015`. -/
@[expose]
noncomputable def nb078AlphaDummy1015 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1009)
          (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
            (Wff.classEq (Class.cv (nb078AlphaDummy1009))
              (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1009)
          (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
            (Wff.classEq (Class.cv (nb078AlphaDummy1009))
              (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1016`. -/
@[expose]
noncomputable def nb078AlphaDummy1016 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1011 h)
          (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
              (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1011 h)
          (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
              (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1017`. -/
@[expose]
noncomputable def nb078AlphaDummy1017 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1010))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1018`. -/
@[expose]
noncomputable def nb078AlphaDummy1018 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1010))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1019`. -/
@[expose]
noncomputable def nb078AlphaDummy1019 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1012 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1020`. -/
@[expose]
noncomputable def nb078AlphaDummy1020 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1012 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1021`. -/
@[expose]
noncomputable def nb078AlphaDummy1021 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1017)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1017)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1017))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1022`. -/
@[expose]
noncomputable def nb078AlphaDummy1022 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1019 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1019 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1019 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1023`. -/
@[expose]
noncomputable def nb078AlphaDummy1023 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1024`. -/
@[expose]
noncomputable def nb078AlphaDummy1024 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1025`. -/
@[expose]
noncomputable def nb078AlphaDummy1025 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1026`. -/
@[expose]
noncomputable def nb078AlphaDummy1026 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1027`. -/
@[expose]
noncomputable def nb078AlphaDummy1027 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1028`. -/
@[expose]
noncomputable def nb078AlphaDummy1028 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1029`. -/
@[expose]
noncomputable def nb078AlphaDummy1029 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1024))
          (Class.cv (nb078AlphaDummy1025)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1030`. -/
@[expose]
noncomputable def nb078AlphaDummy1030 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1027 h))
          (Class.cv (nb078AlphaDummy1028 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1027 h))
          (Class.cv (nb078AlphaDummy1028 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1031`. -/
@[expose]
noncomputable def nb078AlphaDummy1031 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1032`. -/
@[expose]
noncomputable def nb078AlphaDummy1032 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1028 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1033`. -/
@[expose]
noncomputable def nb078AlphaDummy1033 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1024)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1025)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1034`. -/
@[expose]
noncomputable def nb078AlphaDummy1034 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1027 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1028 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1035`. -/
@[expose]
noncomputable def nb078AlphaDummy1035 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1024))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1036`. -/
@[expose]
noncomputable def nb078AlphaDummy1036 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1027 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1037`. -/
@[expose]
noncomputable def nb078AlphaDummy1037 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1025))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1038`. -/
@[expose]
noncomputable def nb078AlphaDummy1038 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1028 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1028 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1039`. -/
@[expose]
noncomputable def nb078AlphaDummy1039 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1009)
          (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
            (Wff.classEq (Class.cv (nb078AlphaDummy1009))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1009)
          (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
            (Wff.classEq (Class.cv (nb078AlphaDummy1009))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1040`. -/
@[expose]
noncomputable def nb078AlphaDummy1040 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1011 h)
          (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1011 h)
          (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1041`. -/
@[expose]
noncomputable def nb078AlphaDummy1041 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1010))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1042`. -/
@[expose]
noncomputable def nb078AlphaDummy1042 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1012 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1043`. -/
@[expose]
noncomputable def nb078AlphaDummy1043 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1010)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1010)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1044`. -/
@[expose]
noncomputable def nb078AlphaDummy1044 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1045`. -/
@[expose]
noncomputable def nb078AlphaDummy1045 : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1046`. -/
@[expose]
noncomputable def nb078AlphaDummy1046 (h : Var) : Var :=
  (freshVar (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
          (synCid))).fv ∪
      ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
          (synCid))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1047`. -/
@[expose]
noncomputable def nb078AlphaDummy1047 : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
          (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002)))))).fv ∪ ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1048`. -/
@[expose]
noncomputable def nb078AlphaDummy1048 (h : Var) : Var :=
  (freshVar (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
      ((synCid)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1049`. -/
@[expose]
noncomputable def nb078AlphaDummy1049 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1050`. -/
@[expose]
noncomputable def nb078AlphaDummy1050 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1051`. -/
@[expose]
noncomputable def nb078AlphaDummy1051 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
      ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1052`. -/
@[expose]
noncomputable def nb078AlphaDummy1052 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1053`. -/
@[expose]
noncomputable def nb078AlphaDummy1053 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1054`. -/
@[expose]
noncomputable def nb078AlphaDummy1054 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1055`. -/
@[expose]
noncomputable def nb078AlphaDummy1055 : Var :=
  (freshVar (({(nb078AlphaDummy1049)} : Finset Var) ∪
        ({(nb078AlphaDummy1050)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1051) (synWa
            (synWbr (Class.cv (nb078AlphaDummy1049))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
              (Class.cv (nb078AlphaDummy1051))) (synWbr (Class.cv (nb078AlphaDummy1051))
              (synCcnv (Class.cv (nb078AlphaDummy002)))
              (Class.cv (nb078AlphaDummy1050)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1056`. -/
@[expose]
noncomputable def nb078AlphaDummy1056 (h : Var) : Var :=
  (freshVar (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
        ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
          (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
              (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
            (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
              (Class.cv (nb078AlphaDummy1053 h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1057`. -/
@[expose]
noncomputable def nb078AlphaDummy1057 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1058`. -/
@[expose]
noncomputable def nb078AlphaDummy1058 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1059`. -/
@[expose]
noncomputable def nb078AlphaDummy1059 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1053 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1060`. -/
@[expose]
noncomputable def nb078AlphaDummy1060 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1053 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1061`. -/
@[expose]
noncomputable def nb078AlphaDummy1061 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1062`. -/
@[expose]
noncomputable def nb078AlphaDummy1062 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1063`. -/
@[expose]
noncomputable def nb078AlphaDummy1063 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1057)
          (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
            (Wff.classEq (Class.cv (nb078AlphaDummy1057))
              (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1057)
          (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
            (Wff.classEq (Class.cv (nb078AlphaDummy1057))
              (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1064`. -/
@[expose]
noncomputable def nb078AlphaDummy1064 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1059 h)
          (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
              (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1059 h)
          (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
              (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1065`. -/
@[expose]
noncomputable def nb078AlphaDummy1065 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1058))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1066`. -/
@[expose]
noncomputable def nb078AlphaDummy1066 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1058))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1067`. -/
@[expose]
noncomputable def nb078AlphaDummy1067 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1060 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1068`. -/
@[expose]
noncomputable def nb078AlphaDummy1068 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1060 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1069`. -/
@[expose]
noncomputable def nb078AlphaDummy1069 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1065)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1065)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1065))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1070`. -/
@[expose]
noncomputable def nb078AlphaDummy1070 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1067 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1067 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1067 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1071`. -/
@[expose]
noncomputable def nb078AlphaDummy1071 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1072`. -/
@[expose]
noncomputable def nb078AlphaDummy1072 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1073`. -/
@[expose]
noncomputable def nb078AlphaDummy1073 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1074`. -/
@[expose]
noncomputable def nb078AlphaDummy1074 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1075`. -/
@[expose]
noncomputable def nb078AlphaDummy1075 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1076`. -/
@[expose]
noncomputable def nb078AlphaDummy1076 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1077`. -/
@[expose]
noncomputable def nb078AlphaDummy1077 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1072))
          (Class.cv (nb078AlphaDummy1073)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1078`. -/
@[expose]
noncomputable def nb078AlphaDummy1078 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1075 h))
          (Class.cv (nb078AlphaDummy1076 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1075 h))
          (Class.cv (nb078AlphaDummy1076 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1079`. -/
@[expose]
noncomputable def nb078AlphaDummy1079 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1080`. -/
@[expose]
noncomputable def nb078AlphaDummy1080 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1076 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1081`. -/
@[expose]
noncomputable def nb078AlphaDummy1081 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1072)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1073)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1082`. -/
@[expose]
noncomputable def nb078AlphaDummy1082 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1075 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1076 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1083`. -/
@[expose]
noncomputable def nb078AlphaDummy1083 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1072))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1084`. -/
@[expose]
noncomputable def nb078AlphaDummy1084 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1075 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1085`. -/
@[expose]
noncomputable def nb078AlphaDummy1085 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1073))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1086`. -/
@[expose]
noncomputable def nb078AlphaDummy1086 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1076 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1076 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1087`. -/
@[expose]
noncomputable def nb078AlphaDummy1087 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1057)
          (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
            (Wff.classEq (Class.cv (nb078AlphaDummy1057))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1057)
          (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
            (Wff.classEq (Class.cv (nb078AlphaDummy1057))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1088`. -/
@[expose]
noncomputable def nb078AlphaDummy1088 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1059 h)
          (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1059 h)
          (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1089`. -/
@[expose]
noncomputable def nb078AlphaDummy1089 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1058))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1090`. -/
@[expose]
noncomputable def nb078AlphaDummy1090 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1060 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1091`. -/
@[expose]
noncomputable def nb078AlphaDummy1091 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1058)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1058)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1092`. -/
@[expose]
noncomputable def nb078AlphaDummy1092 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1093`. -/
@[expose]
noncomputable def nb078AlphaDummy1093 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1094`. -/
@[expose]
noncomputable def nb078AlphaDummy1094 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1095`. -/
@[expose]
noncomputable def nb078AlphaDummy1095 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1054 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1096`. -/
@[expose]
noncomputable def nb078AlphaDummy1096 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1054 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1097`. -/
@[expose]
noncomputable def nb078AlphaDummy1097 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1098`. -/
@[expose]
noncomputable def nb078AlphaDummy1098 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1099`. -/
@[expose]
noncomputable def nb078AlphaDummy1099 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1093)
          (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
            (Wff.classEq (Class.cv (nb078AlphaDummy1093))
              (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1093)
          (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
            (Wff.classEq (Class.cv (nb078AlphaDummy1093))
              (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1100`. -/
@[expose]
noncomputable def nb078AlphaDummy1100 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1095 h)
          (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
              (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1095 h)
          (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
              (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1101`. -/
@[expose]
noncomputable def nb078AlphaDummy1101 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1094))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1102`. -/
@[expose]
noncomputable def nb078AlphaDummy1102 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1094))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1103`. -/
@[expose]
noncomputable def nb078AlphaDummy1103 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1096 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1104`. -/
@[expose]
noncomputable def nb078AlphaDummy1104 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1096 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1105`. -/
@[expose]
noncomputable def nb078AlphaDummy1105 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1101)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1101)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1101))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1106`. -/
@[expose]
noncomputable def nb078AlphaDummy1106 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1103 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1103 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1103 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1107`. -/
@[expose]
noncomputable def nb078AlphaDummy1107 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1108`. -/
@[expose]
noncomputable def nb078AlphaDummy1108 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1109`. -/
@[expose]
noncomputable def nb078AlphaDummy1109 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1110`. -/
@[expose]
noncomputable def nb078AlphaDummy1110 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1111`. -/
@[expose]
noncomputable def nb078AlphaDummy1111 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1112`. -/
@[expose]
noncomputable def nb078AlphaDummy1112 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1113`. -/
@[expose]
noncomputable def nb078AlphaDummy1113 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1108))
          (Class.cv (nb078AlphaDummy1109)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1114`. -/
@[expose]
noncomputable def nb078AlphaDummy1114 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1111 h))
          (Class.cv (nb078AlphaDummy1112 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1111 h))
          (Class.cv (nb078AlphaDummy1112 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1115`. -/
@[expose]
noncomputable def nb078AlphaDummy1115 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1116`. -/
@[expose]
noncomputable def nb078AlphaDummy1116 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1112 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1117`. -/
@[expose]
noncomputable def nb078AlphaDummy1117 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1108)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1109)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1118`. -/
@[expose]
noncomputable def nb078AlphaDummy1118 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1111 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1112 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1119`. -/
@[expose]
noncomputable def nb078AlphaDummy1119 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1108))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1120`. -/
@[expose]
noncomputable def nb078AlphaDummy1120 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1111 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1121`. -/
@[expose]
noncomputable def nb078AlphaDummy1121 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1109))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1122`. -/
@[expose]
noncomputable def nb078AlphaDummy1122 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1112 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1112 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1123`. -/
@[expose]
noncomputable def nb078AlphaDummy1123 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1093)
          (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
            (Wff.classEq (Class.cv (nb078AlphaDummy1093))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1093)
          (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
            (Wff.classEq (Class.cv (nb078AlphaDummy1093))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1124`. -/
@[expose]
noncomputable def nb078AlphaDummy1124 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1095 h)
          (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1095 h)
          (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1125`. -/
@[expose]
noncomputable def nb078AlphaDummy1125 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1094))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1126`. -/
@[expose]
noncomputable def nb078AlphaDummy1126 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1096 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1127`. -/
@[expose]
noncomputable def nb078AlphaDummy1127 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1094)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1094)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1128`. -/
@[expose]
noncomputable def nb078AlphaDummy1128 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1129`. -/
@[expose]
noncomputable def nb078AlphaDummy1129 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1130`. -/
@[expose]
noncomputable def nb078AlphaDummy1130 : Var :=
  (freshVar (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1131`. -/
@[expose]
noncomputable def nb078AlphaDummy1131 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1132`. -/
@[expose]
noncomputable def nb078AlphaDummy1132 (h : Var) : Var :=
  (freshVar (((synCcnv (Class.cv h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1133`. -/
@[expose]
noncomputable def nb078AlphaDummy1133 : Var :=
  (freshVar (({(nb078AlphaDummy1129)} : Finset Var) ∪
        ({(nb078AlphaDummy1130)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy1130))
          (synCcnv (Class.cv (nb078AlphaDummy002)))
          (Class.cv (nb078AlphaDummy1129)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1134`. -/
@[expose]
noncomputable def nb078AlphaDummy1134 (h : Var) : Var :=
  (freshVar (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
        ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
          (Class.cv (nb078AlphaDummy1131 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1135`. -/
@[expose]
noncomputable def nb078AlphaDummy1135 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1136`. -/
@[expose]
noncomputable def nb078AlphaDummy1136 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1137`. -/
@[expose]
noncomputable def nb078AlphaDummy1137 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1132 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1138`. -/
@[expose]
noncomputable def nb078AlphaDummy1138 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1132 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1139`. -/
@[expose]
noncomputable def nb078AlphaDummy1139 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1140`. -/
@[expose]
noncomputable def nb078AlphaDummy1140 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1141`. -/
@[expose]
noncomputable def nb078AlphaDummy1141 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1135)
          (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
            (Wff.classEq (Class.cv (nb078AlphaDummy1135))
              (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1135)
          (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
            (Wff.classEq (Class.cv (nb078AlphaDummy1135))
              (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1142`. -/
@[expose]
noncomputable def nb078AlphaDummy1142 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1137 h)
          (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
              (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1137 h)
          (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
              (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1143`. -/
@[expose]
noncomputable def nb078AlphaDummy1143 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1136))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1144`. -/
@[expose]
noncomputable def nb078AlphaDummy1144 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1136))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1145`. -/
@[expose]
noncomputable def nb078AlphaDummy1145 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1138 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1146`. -/
@[expose]
noncomputable def nb078AlphaDummy1146 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1138 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1147`. -/
@[expose]
noncomputable def nb078AlphaDummy1147 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1143)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1143)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1143))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1148`. -/
@[expose]
noncomputable def nb078AlphaDummy1148 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1145 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1145 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1145 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1149`. -/
@[expose]
noncomputable def nb078AlphaDummy1149 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1150`. -/
@[expose]
noncomputable def nb078AlphaDummy1150 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1151`. -/
@[expose]
noncomputable def nb078AlphaDummy1151 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1152`. -/
@[expose]
noncomputable def nb078AlphaDummy1152 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1153`. -/
@[expose]
noncomputable def nb078AlphaDummy1153 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1154`. -/
@[expose]
noncomputable def nb078AlphaDummy1154 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1155`. -/
@[expose]
noncomputable def nb078AlphaDummy1155 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1150))
          (Class.cv (nb078AlphaDummy1151)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1156`. -/
@[expose]
noncomputable def nb078AlphaDummy1156 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1153 h))
          (Class.cv (nb078AlphaDummy1154 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1153 h))
          (Class.cv (nb078AlphaDummy1154 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1157`. -/
@[expose]
noncomputable def nb078AlphaDummy1157 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1158`. -/
@[expose]
noncomputable def nb078AlphaDummy1158 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1154 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1159`. -/
@[expose]
noncomputable def nb078AlphaDummy1159 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1150)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1151)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1160`. -/
@[expose]
noncomputable def nb078AlphaDummy1160 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1153 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1154 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1161`. -/
@[expose]
noncomputable def nb078AlphaDummy1161 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1150))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1162`. -/
@[expose]
noncomputable def nb078AlphaDummy1162 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1153 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1163`. -/
@[expose]
noncomputable def nb078AlphaDummy1163 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1151))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1164`. -/
@[expose]
noncomputable def nb078AlphaDummy1164 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1154 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1154 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1165`. -/
@[expose]
noncomputable def nb078AlphaDummy1165 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1135)
          (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
            (Wff.classEq (Class.cv (nb078AlphaDummy1135))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1135)
          (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
            (Wff.classEq (Class.cv (nb078AlphaDummy1135))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1166`. -/
@[expose]
noncomputable def nb078AlphaDummy1166 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1137 h)
          (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1137 h)
          (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1167`. -/
@[expose]
noncomputable def nb078AlphaDummy1167 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1136))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1168`. -/
@[expose]
noncomputable def nb078AlphaDummy1168 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1138 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1169`. -/
@[expose]
noncomputable def nb078AlphaDummy1169 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1136)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1136)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1170`. -/
@[expose]
noncomputable def nb078AlphaDummy1170 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1171`. -/
@[expose]
noncomputable def nb078AlphaDummy1171 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1172`. -/
@[expose]
noncomputable def nb078AlphaDummy1172 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1173`. -/
@[expose]
noncomputable def nb078AlphaDummy1173 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1131 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1174`. -/
@[expose]
noncomputable def nb078AlphaDummy1174 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1131 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1175`. -/
@[expose]
noncomputable def nb078AlphaDummy1175 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1176`. -/
@[expose]
noncomputable def nb078AlphaDummy1176 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1177`. -/
@[expose]
noncomputable def nb078AlphaDummy1177 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1171)
          (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
            (Wff.classEq (Class.cv (nb078AlphaDummy1171))
              (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1171)
          (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
            (Wff.classEq (Class.cv (nb078AlphaDummy1171))
              (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1178`. -/
@[expose]
noncomputable def nb078AlphaDummy1178 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1173 h)
          (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
              (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1173 h)
          (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
              (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1179`. -/
@[expose]
noncomputable def nb078AlphaDummy1179 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1172))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1180`. -/
@[expose]
noncomputable def nb078AlphaDummy1180 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1172))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1181`. -/
@[expose]
noncomputable def nb078AlphaDummy1181 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1174 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1182`. -/
@[expose]
noncomputable def nb078AlphaDummy1182 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1174 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1183`. -/
@[expose]
noncomputable def nb078AlphaDummy1183 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1179)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1179)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1179))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1184`. -/
@[expose]
noncomputable def nb078AlphaDummy1184 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1181 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1181 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1181 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1185`. -/
@[expose]
noncomputable def nb078AlphaDummy1185 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1186`. -/
@[expose]
noncomputable def nb078AlphaDummy1186 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1187`. -/
@[expose]
noncomputable def nb078AlphaDummy1187 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1188`. -/
@[expose]
noncomputable def nb078AlphaDummy1188 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1189`. -/
@[expose]
noncomputable def nb078AlphaDummy1189 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1190`. -/
@[expose]
noncomputable def nb078AlphaDummy1190 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1191`. -/
@[expose]
noncomputable def nb078AlphaDummy1191 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1186))
          (Class.cv (nb078AlphaDummy1187)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1192`. -/
@[expose]
noncomputable def nb078AlphaDummy1192 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1189 h))
          (Class.cv (nb078AlphaDummy1190 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1189 h))
          (Class.cv (nb078AlphaDummy1190 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1193`. -/
@[expose]
noncomputable def nb078AlphaDummy1193 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1194`. -/
@[expose]
noncomputable def nb078AlphaDummy1194 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1190 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1195`. -/
@[expose]
noncomputable def nb078AlphaDummy1195 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1186)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1187)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1196`. -/
@[expose]
noncomputable def nb078AlphaDummy1196 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1189 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1190 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1197`. -/
@[expose]
noncomputable def nb078AlphaDummy1197 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1186))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1198`. -/
@[expose]
noncomputable def nb078AlphaDummy1198 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1189 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1199`. -/
@[expose]
noncomputable def nb078AlphaDummy1199 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1187))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) 0)

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

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1200`. -/
@[expose]
noncomputable def nb078AlphaDummy1200 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1190 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1190 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1201`. -/
@[expose]
noncomputable def nb078AlphaDummy1201 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1171)
          (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
            (Wff.classEq (Class.cv (nb078AlphaDummy1171))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1171)
          (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
            (Wff.classEq (Class.cv (nb078AlphaDummy1171))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1202`. -/
@[expose]
noncomputable def nb078AlphaDummy1202 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1173 h)
          (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1173 h)
          (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1203`. -/
@[expose]
noncomputable def nb078AlphaDummy1203 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1172))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1204`. -/
@[expose]
noncomputable def nb078AlphaDummy1204 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1174 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1205`. -/
@[expose]
noncomputable def nb078AlphaDummy1205 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1172)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1172)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1206`. -/
@[expose]
noncomputable def nb078AlphaDummy1206 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1207`. -/
@[expose]
noncomputable def nb078AlphaDummy1207 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1208`. -/
@[expose]
noncomputable def nb078AlphaDummy1208 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1209`. -/
@[expose]
noncomputable def nb078AlphaDummy1209 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1053 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1210`. -/
@[expose]
noncomputable def nb078AlphaDummy1210 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1053 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1211`. -/
@[expose]
noncomputable def nb078AlphaDummy1211 : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1212`. -/
@[expose]
noncomputable def nb078AlphaDummy1212 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1213`. -/
@[expose]
noncomputable def nb078AlphaDummy1213 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1207)
          (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
            (Wff.classEq (Class.cv (nb078AlphaDummy1207))
              (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1207)
          (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
            (Wff.classEq (Class.cv (nb078AlphaDummy1207))
              (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1214`. -/
@[expose]
noncomputable def nb078AlphaDummy1214 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1209 h)
          (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
              (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv ∪
      ((Class.cab (nb078AlphaDummy1209 h)
          (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
              (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1215`. -/
@[expose]
noncomputable def nb078AlphaDummy1215 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1208))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1216`. -/
@[expose]
noncomputable def nb078AlphaDummy1216 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1208))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1217`. -/
@[expose]
noncomputable def nb078AlphaDummy1217 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1210 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1218`. -/
@[expose]
noncomputable def nb078AlphaDummy1218 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1210 h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1219`. -/
@[expose]
noncomputable def nb078AlphaDummy1219 : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1215)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1215)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1215))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1220`. -/
@[expose]
noncomputable def nb078AlphaDummy1220 (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb078AlphaDummy1217 h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb078AlphaDummy1217 h)) (synC1c))).fv ∪
      ((Class.cv (nb078AlphaDummy1217 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1221`. -/
@[expose]
noncomputable def nb078AlphaDummy1221 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1222`. -/
@[expose]
noncomputable def nb078AlphaDummy1222 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1223`. -/
@[expose]
noncomputable def nb078AlphaDummy1223 : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1224`. -/
@[expose]
noncomputable def nb078AlphaDummy1224 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1225`. -/
@[expose]
noncomputable def nb078AlphaDummy1225 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1226`. -/
@[expose]
noncomputable def nb078AlphaDummy1226 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1227`. -/
@[expose]
noncomputable def nb078AlphaDummy1227 : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1222))
          (Class.cv (nb078AlphaDummy1223)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1228`. -/
@[expose]
noncomputable def nb078AlphaDummy1228 (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb078AlphaDummy1225 h))
          (Class.cv (nb078AlphaDummy1226 h)))).fv ∪
      ((synCnin (Class.cv (nb078AlphaDummy1225 h))
          (Class.cv (nb078AlphaDummy1226 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1229`. -/
@[expose]
noncomputable def nb078AlphaDummy1229 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1230`. -/
@[expose]
noncomputable def nb078AlphaDummy1230 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1226 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1231`. -/
@[expose]
noncomputable def nb078AlphaDummy1231 : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1222)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1223)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1232`. -/
@[expose]
noncomputable def nb078AlphaDummy1232 (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb078AlphaDummy1225 h)))).fv ∪
      ((synCcompl (Class.cv (nb078AlphaDummy1226 h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1233`. -/
@[expose]
noncomputable def nb078AlphaDummy1233 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1222))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1234`. -/
@[expose]
noncomputable def nb078AlphaDummy1234 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1225 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1235`. -/
@[expose]
noncomputable def nb078AlphaDummy1235 : Var :=
  (freshVar
    (((Class.cv (nb078AlphaDummy1223))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1236`. -/
@[expose]
noncomputable def nb078AlphaDummy1236 (h : Var) : Var :=
  (freshVar (((Class.cv (nb078AlphaDummy1226 h))).fv ∪
      ((Class.cv (nb078AlphaDummy1226 h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1237`. -/
@[expose]
noncomputable def nb078AlphaDummy1237 : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1207)
          (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
            (Wff.classEq (Class.cv (nb078AlphaDummy1207))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1207)
          (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
            (Wff.classEq (Class.cv (nb078AlphaDummy1207))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1238`. -/
@[expose]
noncomputable def nb078AlphaDummy1238 (h : Var) : Var :=
  (freshVar (((Class.cab (nb078AlphaDummy1209 h)
          (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1209 h)
          (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
            (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
              (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1239`. -/
@[expose]
noncomputable def nb078AlphaDummy1239 : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1208))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1240`. -/
@[expose]
noncomputable def nb078AlphaDummy1240 (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1210 h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1241`. -/
@[expose]
noncomputable def nb078AlphaDummy1241 : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1208)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1208)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb078_alpha_dummy_1242`. -/
@[expose]
noncomputable def nb078AlphaDummy1242 (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv ∪
      ((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv) 0)

theorem nb078_fresh_000 :
    (nb078AlphaDummy023) ∉
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv ∪
        ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv) :=
  by
  simpa only [nb078AlphaDummy023] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv ∪
        ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCphi (Class.cv (nb078AlphaDummy018))))))).fv)
      0

theorem nb078_fresh_001 :
    (nb078AlphaDummy047) ∉
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy047] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy017)
            (synWrex (nb078AlphaDummy018) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy017))
                (synCun (synCphi (Class.cv (nb078AlphaDummy018)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_002 (f : Var) :
    (nb078AlphaDummy024 f) ∉
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy024] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCphi (Class.cv (nb078AlphaDummy020 f))))))).fv)
      0

theorem nb078_fresh_003 (f : Var) :
    (nb078AlphaDummy048 f) ∉
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy048] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy019 f)
            (synWrex (nb078AlphaDummy020 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy019 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy020 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_004 :
    (nb078AlphaDummy059) ∉
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv ∪
        ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv) :=
  by
  simpa only [nb078AlphaDummy059] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv ∪
        ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy009))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCphi (Class.cv (nb078AlphaDummy054))))))).fv)
      0

theorem nb078_fresh_005 :
    (nb078AlphaDummy083) ∉
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy083] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy053)
            (synWrex (nb078AlphaDummy054) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy053))
                (synCun (synCphi (Class.cv (nb078AlphaDummy054)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_006 (f : Var) :
    (nb078AlphaDummy060 f) ∉
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy060] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy012 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCphi (Class.cv (nb078AlphaDummy056 f))))))).fv)
      0

theorem nb078_fresh_007 (f : Var) :
    (nb078AlphaDummy084 f) ∉
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy084] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy055 f)
            (synWrex (nb078AlphaDummy056 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_008 :
    (nb078AlphaDummy101) ∉
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv ∪
        ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv) :=
  by
  simpa only [nb078AlphaDummy101] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv ∪
        ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCphi (Class.cv (nb078AlphaDummy096))))))).fv)
      0

theorem nb078_fresh_009 :
    (nb078AlphaDummy125) ∉
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy125] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy095)
            (synWrex (nb078AlphaDummy096) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy095))
                (synCun (synCphi (Class.cv (nb078AlphaDummy096)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_010 (f : Var) :
    (nb078AlphaDummy102 f) ∉
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy102] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCphi (Class.cv (nb078AlphaDummy098 f))))))).fv)
      0

theorem nb078_fresh_011 (f : Var) :
    (nb078AlphaDummy126 f) ∉
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy126] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy097 f)
            (synWrex (nb078AlphaDummy098 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy097 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy098 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_012 :
    (nb078AlphaDummy1039) ∉
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1039] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_013 :
    (nb078AlphaDummy1015) ∉
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1015] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv)
      0

theorem nb078_fresh_014 (h : Var) :
    (nb078AlphaDummy1040 h) ∉
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1040] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_015 (h : Var) :
    (nb078AlphaDummy1016 h) ∉
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1016] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv)
      0

theorem nb078_fresh_016 :
    (nb078AlphaDummy1063) ∉
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1063] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv)
      0

theorem nb078_fresh_017 :
    (nb078AlphaDummy1087) ∉
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1087] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_018 (h : Var) :
    (nb078AlphaDummy1064 h) ∉
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1064] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv)
      0

theorem nb078_fresh_019 (h : Var) :
    (nb078AlphaDummy1088 h) ∉
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1088] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_020 :
    (nb078AlphaDummy1099) ∉
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1099] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv)
      0

theorem nb078_fresh_021 :
    (nb078AlphaDummy1123) ∉
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1123] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_022 (h : Var) :
    (nb078AlphaDummy1100 h) ∉
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1100] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv)
      0

theorem nb078_fresh_023 (h : Var) :
    (nb078AlphaDummy1124 h) ∉
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1124] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_024 :
    (nb078AlphaDummy1141) ∉
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1141] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv)
      0

theorem nb078_fresh_025 :
    (nb078AlphaDummy1165) ∉
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1165] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_026 (h : Var) :
    (nb078AlphaDummy1142 h) ∉
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1142] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv)
      0

theorem nb078_fresh_027 (h : Var) :
    (nb078AlphaDummy1166 h) ∉
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1166] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_028 :
    (nb078AlphaDummy1201) ∉
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1201] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_029 :
    (nb078AlphaDummy1177) ∉
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1177] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv)
      0

theorem nb078_fresh_030 (h : Var) :
    (nb078AlphaDummy1202 h) ∉
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1202] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_031 (h : Var) :
    (nb078AlphaDummy1178 h) ∉
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1178] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv)
      0

theorem nb078_fresh_032 :
    (nb078AlphaDummy1237) ∉
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1237] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_033 :
    (nb078AlphaDummy1213) ∉
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1213] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv)
      0

theorem nb078_fresh_034 (h : Var) :
    (nb078AlphaDummy1238 h) ∉
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1238] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_035 (h : Var) :
    (nb078AlphaDummy1214 h) ∉
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy1214] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv)
      0

theorem nb078_fresh_036 :
    (nb078AlphaDummy161) ∉
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy161] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy089))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCun (synCphi (Class.cv (nb078AlphaDummy132)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_037 :
    (nb078AlphaDummy137) ∉
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv ∪
        ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv) :=
  by
  simpa only [nb078AlphaDummy137] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv ∪
        ((Class.cab (nb078AlphaDummy131)
            (synWrex (nb078AlphaDummy132) (Class.cv (nb078AlphaDummy090))
              (Wff.classEq (Class.cv (nb078AlphaDummy131))
                (synCphi (Class.cv (nb078AlphaDummy132))))))).fv)
      0

theorem nb078_fresh_038 (f : Var) :
    (nb078AlphaDummy162 f) ∉
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy162] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy091 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_039 (f : Var) :
    (nb078AlphaDummy138 f) ∉
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy138] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy133 f)
            (synWrex (nb078AlphaDummy134 f) (Class.cv (nb078AlphaDummy092 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy133 f))
                (synCphi (Class.cv (nb078AlphaDummy134 f))))))).fv)
      0

theorem nb078_fresh_040 :
    (nb078AlphaDummy197) ∉
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy197] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy010))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCun (synCphi (Class.cv (nb078AlphaDummy168)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_041 :
    (nb078AlphaDummy173) ∉
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv ∪
        ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv) :=
  by
  simpa only [nb078AlphaDummy173] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv ∪
        ((Class.cab (nb078AlphaDummy167)
            (synWrex (nb078AlphaDummy168) (Class.cv (nb078AlphaDummy011))
              (Wff.classEq (Class.cv (nb078AlphaDummy167))
                (synCphi (Class.cv (nb078AlphaDummy168))))))).fv)
      0

theorem nb078_fresh_042 (f : Var) :
    (nb078AlphaDummy198 f) ∉
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy198] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy013 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_043 (f : Var) :
    (nb078AlphaDummy174 f) ∉
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy174] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy169 f)
            (synWrex (nb078AlphaDummy170 f) (Class.cv (nb078AlphaDummy014 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy169 f))
                (synCphi (Class.cv (nb078AlphaDummy170 f))))))).fv)
      0

theorem nb078_fresh_044 :
    (nb078AlphaDummy237) ∉
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy237] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy203))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy208)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_045 :
    (nb078AlphaDummy213) ∉
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv) :=
  by
  simpa only [nb078AlphaDummy213] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy207)
            (synWrex (nb078AlphaDummy208) (Class.cv (nb078AlphaDummy204))
              (Wff.classEq (Class.cv (nb078AlphaDummy207))
                (synCphi (Class.cv (nb078AlphaDummy208))))))).fv)
      0

theorem nb078_fresh_046 (f : Var) :
    (nb078AlphaDummy238 f) ∉
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy238] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy205 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy210 f)))
                  (synCsn (synC0c))))))).fv)
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
    (nb078AlphaDummy214 f) ∉
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy214] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy209 f)
            (synWrex (nb078AlphaDummy210 f) (Class.cv (nb078AlphaDummy206 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy209 f))
                (synCphi (Class.cv (nb078AlphaDummy210 f))))))).fv)
      0

theorem nb078_fresh_048 :
    (nb078AlphaDummy277) ∉
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy277] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy243))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCun (synCphi (Class.cv (nb078AlphaDummy248)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_049 :
    (nb078AlphaDummy253) ∉
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv ∪
        ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv) :=
  by
  simpa only [nb078AlphaDummy253] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv ∪
        ((Class.cab (nb078AlphaDummy247)
            (synWrex (nb078AlphaDummy248) (Class.cv (nb078AlphaDummy244))
              (Wff.classEq (Class.cv (nb078AlphaDummy247))
                (synCphi (Class.cv (nb078AlphaDummy248))))))).fv)
      0

theorem nb078_fresh_050 (f : Var) :
    (nb078AlphaDummy278 f) ∉
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy278] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy245 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCun (synCphi (Class.cv (nb078AlphaDummy250 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_051 (f : Var) :
    (nb078AlphaDummy254 f) ∉
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv) :=
  by
  simpa only [nb078AlphaDummy254] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv ∪
        ((Class.cab (nb078AlphaDummy249 f)
            (synWrex (nb078AlphaDummy250 f) (Class.cv (nb078AlphaDummy246 f))
              (Wff.classEq (Class.cv (nb078AlphaDummy249 f))
                (synCphi (Class.cv (nb078AlphaDummy250 f))))))).fv)
      0

theorem nb078_fresh_052 :
    (nb078AlphaDummy301) ∉
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv ∪
        ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv) :=
  by
  simpa only [nb078AlphaDummy301] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv ∪
        ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCphi (Class.cv (nb078AlphaDummy296))))))).fv)
      0

theorem nb078_fresh_053 :
    (nb078AlphaDummy325) ∉
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy325] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy295)
            (synWrex (nb078AlphaDummy296) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy295))
                (synCun (synCphi (Class.cv (nb078AlphaDummy296)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_054 (g : Var) :
    (nb078AlphaDummy302 g) ∉
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy302] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCphi (Class.cv (nb078AlphaDummy298 g))))))).fv)
      0

theorem nb078_fresh_055 (g : Var) :
    (nb078AlphaDummy326 g) ∉
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy326] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy297 g)
            (synWrex (nb078AlphaDummy298 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy297 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy298 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_056 :
    (nb078AlphaDummy337) ∉
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv ∪
        ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv) :=
  by
  simpa only [nb078AlphaDummy337] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv ∪
        ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy287))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCphi (Class.cv (nb078AlphaDummy332))))))).fv)
      0

theorem nb078_fresh_057 :
    (nb078AlphaDummy361) ∉
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy361] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy331)
            (synWrex (nb078AlphaDummy332) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy331))
                (synCun (synCphi (Class.cv (nb078AlphaDummy332)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_058 (g : Var) :
    (nb078AlphaDummy338 g) ∉
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy338] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy290 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCphi (Class.cv (nb078AlphaDummy334 g))))))).fv)
      0

theorem nb078_fresh_059 (g : Var) :
    (nb078AlphaDummy362 g) ∉
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy362] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy333 g)
            (synWrex (nb078AlphaDummy334 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy333 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy334 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_060 :
    (nb078AlphaDummy379) ∉
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv ∪
        ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv) :=
  by
  simpa only [nb078AlphaDummy379] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv ∪
        ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))).fv)
      0

theorem nb078_fresh_061 :
    (nb078AlphaDummy403) ∉
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy403] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCun (synCphi (Class.cv (nb078AlphaDummy374)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_062 (g : Var) :
    (nb078AlphaDummy380 g) ∉
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy380] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))).fv)
      0

theorem nb078_fresh_063 (g : Var) :
    (nb078AlphaDummy404 g) ∉
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy404] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy376 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_064 :
    (nb078AlphaDummy439) ∉
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy439] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCun (synCphi (Class.cv (nb078AlphaDummy410)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_065 :
    (nb078AlphaDummy415) ∉
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv ∪
        ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv) :=
  by
  simpa only [nb078AlphaDummy415] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv ∪
        ((Class.cab (nb078AlphaDummy409)
            (synWrex (nb078AlphaDummy410) (Class.cv (nb078AlphaDummy368))
              (Wff.classEq (Class.cv (nb078AlphaDummy409))
                (synCphi (Class.cv (nb078AlphaDummy410))))))).fv)
      0

theorem nb078_fresh_066 (g : Var) :
    (nb078AlphaDummy440 g) ∉
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy440] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy412 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_067 (g : Var) :
    (nb078AlphaDummy416 g) ∉
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy416] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy411 g)
            (synWrex (nb078AlphaDummy412 g) (Class.cv (nb078AlphaDummy370 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy411 g))
                (synCphi (Class.cv (nb078AlphaDummy412 g))))))).fv)
      0

theorem nb078_fresh_068 :
    (nb078AlphaDummy475) ∉
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy475] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy288))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCun (synCphi (Class.cv (nb078AlphaDummy446)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_069 :
    (nb078AlphaDummy451) ∉
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv ∪
        ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv) :=
  by
  simpa only [nb078AlphaDummy451] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv ∪
        ((Class.cab (nb078AlphaDummy445)
            (synWrex (nb078AlphaDummy446) (Class.cv (nb078AlphaDummy289))
              (Wff.classEq (Class.cv (nb078AlphaDummy445))
                (synCphi (Class.cv (nb078AlphaDummy446))))))).fv)
      0

theorem nb078_fresh_070 (g : Var) :
    (nb078AlphaDummy476 g) ∉
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy476] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy291 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy448 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_071 (g : Var) :
    (nb078AlphaDummy452 g) ∉
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy452] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy447 g)
            (synWrex (nb078AlphaDummy448 g) (Class.cv (nb078AlphaDummy292 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy447 g))
                (synCphi (Class.cv (nb078AlphaDummy448 g))))))).fv)
      0

theorem nb078_fresh_072 :
    (nb078AlphaDummy515) ∉
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy515] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_073 :
    (nb078AlphaDummy491) ∉
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv ∪
        ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv) :=
  by
  simpa only [nb078AlphaDummy491] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv ∪
        ((Class.cab (nb078AlphaDummy485)
            (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
              (Wff.classEq (Class.cv (nb078AlphaDummy485))
                (synCphi (Class.cv (nb078AlphaDummy486))))))).fv)
      0

theorem nb078_fresh_074 (g : Var) :
    (nb078AlphaDummy516 g) ∉
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy516] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_075 (g : Var) :
    (nb078AlphaDummy492 g) ∉
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy492] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy487 g)
            (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                (synCphi (Class.cv (nb078AlphaDummy488 g))))))).fv)
      0

theorem nb078_fresh_076 :
    (nb078AlphaDummy559) ∉
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy559] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy525))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCun (synCphi (Class.cv (nb078AlphaDummy530)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_077 :
    (nb078AlphaDummy535) ∉
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv ∪
        ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv) :=
  by
  simpa only [nb078AlphaDummy535] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv ∪
        ((Class.cab (nb078AlphaDummy529)
            (synWrex (nb078AlphaDummy530) (Class.cv (nb078AlphaDummy526))
              (Wff.classEq (Class.cv (nb078AlphaDummy529))
                (synCphi (Class.cv (nb078AlphaDummy530))))))).fv)
      0

theorem nb078_fresh_078 (g : Var) :
    (nb078AlphaDummy560 g) ∉
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy560] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy527 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy532 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_079 (g : Var) :
    (nb078AlphaDummy536 g) ∉
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy536] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy531 g)
            (synWrex (nb078AlphaDummy532 g) (Class.cv (nb078AlphaDummy528 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy531 g))
                (synCphi (Class.cv (nb078AlphaDummy532 g))))))).fv)
      0

theorem nb078_fresh_080 :
    (nb078AlphaDummy583) ∉
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv ∪
        ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv) :=
  by
  simpa only [nb078AlphaDummy583] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv ∪
        ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))).fv)
      0

theorem nb078_fresh_081 :
    (nb078AlphaDummy607) ∉
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy607] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCun (synCphi (Class.cv (nb078AlphaDummy578)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_082 (g : Var) :
    (nb078AlphaDummy584 g) ∉
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy584] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))).fv)
      0

theorem nb078_fresh_083 (g : Var) :
    (nb078AlphaDummy608 g) ∉
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy608] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy580 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_084 :
    (nb078AlphaDummy619) ∉
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv ∪
        ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv) :=
  by
  simpa only [nb078AlphaDummy619] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv ∪
        ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))).fv)
      0

theorem nb078_fresh_085 :
    (nb078AlphaDummy643) ∉
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy643] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCun (synCphi (Class.cv (nb078AlphaDummy614)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_086 (g : Var) :
    (nb078AlphaDummy620 g) ∉
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy620] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))).fv)
      0

theorem nb078_fresh_087 (g : Var) :
    (nb078AlphaDummy644 g) ∉
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy644] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy616 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_088 :
    (nb078AlphaDummy661) ∉
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv ∪
        ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv) :=
  by
  simpa only [nb078AlphaDummy661] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv ∪
        ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCphi (Class.cv (nb078AlphaDummy656))))))).fv)
      0

theorem nb078_fresh_089 :
    (nb078AlphaDummy685) ∉
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy685] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy655)
            (synWrex (nb078AlphaDummy656) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy655))
                (synCun (synCphi (Class.cv (nb078AlphaDummy656)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_090 (g : Var) :
    (nb078AlphaDummy662 g) ∉
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy662] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCphi (Class.cv (nb078AlphaDummy658 g))))))).fv)
      0

theorem nb078_fresh_091 (g : Var) :
    (nb078AlphaDummy686 g) ∉
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy686] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy657 g)
            (synWrex (nb078AlphaDummy658 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy657 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy658 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_092 :
    (nb078AlphaDummy721) ∉
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy721] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy649))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCun (synCphi (Class.cv (nb078AlphaDummy692)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_093 :
    (nb078AlphaDummy697) ∉
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv ∪
        ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv) :=
  by
  simpa only [nb078AlphaDummy697] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv ∪
        ((Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))).fv)
      0

theorem nb078_fresh_094 (g : Var) :
    (nb078AlphaDummy722 g) ∉
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy722] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy651 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy694 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_095 (g : Var) :
    (nb078AlphaDummy698 g) ∉
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy698] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))).fv)
      0

theorem nb078_fresh_096 :
    (nb078AlphaDummy757) ∉
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy757] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy570))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCun (synCphi (Class.cv (nb078AlphaDummy728)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_097 :
    (nb078AlphaDummy733) ∉
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv ∪
        ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv) :=
  by
  simpa only [nb078AlphaDummy733] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv ∪
        ((Class.cab (nb078AlphaDummy727)
            (synWrex (nb078AlphaDummy728) (Class.cv (nb078AlphaDummy571))
              (Wff.classEq (Class.cv (nb078AlphaDummy727))
                (synCphi (Class.cv (nb078AlphaDummy728))))))).fv)
      0

theorem nb078_fresh_098 (g : Var) :
    (nb078AlphaDummy758 g) ∉
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy758] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy573 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCun (synCphi (Class.cv (nb078AlphaDummy730 g)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_099 (g : Var) :
    (nb078AlphaDummy734 g) ∉
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv) :=
  by
  simpa only [nb078AlphaDummy734] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv ∪
        ((Class.cab (nb078AlphaDummy729 g)
            (synWrex (nb078AlphaDummy730 g) (Class.cv (nb078AlphaDummy574 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy729 g))
                (synCphi (Class.cv (nb078AlphaDummy730 g))))))).fv)
      0

theorem nb078_fresh_100 :
    (nb078AlphaDummy781) ∉
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv ∪
        ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv) :=
  by
  simpa only [nb078AlphaDummy781] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv ∪
        ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCphi (Class.cv (nb078AlphaDummy776))))))).fv)
      0

theorem nb078_fresh_101 :
    (nb078AlphaDummy805) ∉
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy805] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy775)
            (synWrex (nb078AlphaDummy776) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy775))
                (synCun (synCphi (Class.cv (nb078AlphaDummy776)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_102 (h : Var) :
    (nb078AlphaDummy782 h) ∉
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy782] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCphi (Class.cv (nb078AlphaDummy778 h))))))).fv)
      0

theorem nb078_fresh_103 (h : Var) :
    (nb078AlphaDummy806 h) ∉
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy806] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy777 h)
            (synWrex (nb078AlphaDummy778 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy777 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy778 h)))
                  (synCsn (synC0c))))))).fv)
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
    (nb078AlphaDummy817) ∉
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv ∪
        ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv) :=
  by
  simpa only [nb078AlphaDummy817] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv ∪
        ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy767))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCphi (Class.cv (nb078AlphaDummy812))))))).fv)
      0

theorem nb078_fresh_105 :
    (nb078AlphaDummy841) ∉
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy841] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy811)
            (synWrex (nb078AlphaDummy812) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy811))
                (synCun (synCphi (Class.cv (nb078AlphaDummy812)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_106 (h : Var) :
    (nb078AlphaDummy818 h) ∉
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy818] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy770 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCphi (Class.cv (nb078AlphaDummy814 h))))))).fv)
      0

theorem nb078_fresh_107 (h : Var) :
    (nb078AlphaDummy842 h) ∉
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy842] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy813 h)
            (synWrex (nb078AlphaDummy814 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy813 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy814 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_108 :
    (nb078AlphaDummy859) ∉
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv ∪
        ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv) :=
  by
  simpa only [nb078AlphaDummy859] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv ∪
        ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv)
      0

theorem nb078_fresh_109 :
    (nb078AlphaDummy883) ∉
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy883] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_110 (h : Var) :
    (nb078AlphaDummy860 h) ∉
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy860] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv)
      0

theorem nb078_fresh_111 (h : Var) :
    (nb078AlphaDummy884 h) ∉
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy884] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_112 :
    (nb078AlphaDummy919) ∉
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy919] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_113 :
    (nb078AlphaDummy895) ∉
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv ∪
        ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv) :=
  by
  simpa only [nb078AlphaDummy895] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv ∪
        ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv)
      0

theorem nb078_fresh_114 (h : Var) :
    (nb078AlphaDummy920 h) ∉
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy920] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_115 (h : Var) :
    (nb078AlphaDummy896 h) ∉
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy896] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv)
      0

theorem nb078_fresh_116 :
    (nb078AlphaDummy955) ∉
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy955] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_117 :
    (nb078AlphaDummy931) ∉
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv ∪
        ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv) :=
  by
  simpa only [nb078AlphaDummy931] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv ∪
        ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv)
      0

theorem nb078_fresh_118 (h : Var) :
    (nb078AlphaDummy956 h) ∉
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy956] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_119 (h : Var) :
    (nb078AlphaDummy932 h) ∉
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy932] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv)
      0

theorem nb078_fresh_120 :
    (nb078AlphaDummy995) ∉
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy995] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_121 :
    (nb078AlphaDummy971) ∉
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv ∪
        ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv) :=
  by
  simpa only [nb078AlphaDummy971] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv ∪
        ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv)
      0

theorem nb078_fresh_122 (h : Var) :
    (nb078AlphaDummy996 h) ∉
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb078AlphaDummy996] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb078_fresh_123 (h : Var) :
    (nb078AlphaDummy972 h) ∉
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv) :=
  by
  simpa only [nb078AlphaDummy972] using
    freshVar_not_mem
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv)
      0

theorem nb078_fresh_124 :
    (nb078AlphaDummy089) ∉ (((Class.cv (nb078AlphaDummy000))).fv) := by
  simpa only [nb078AlphaDummy089] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy000))).fv) 0

theorem nb078_fresh_125 :
    (nb078AlphaDummy090) ∉ (((Class.cv (nb078AlphaDummy000))).fv) := by
  simpa only [nb078AlphaDummy090] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy000))).fv) 1

theorem nb078_distinct_126 : (nb078AlphaDummy089) ≠ (nb078AlphaDummy090) := by
  simpa only [nb078AlphaDummy089, nb078AlphaDummy090] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_127 :
    (nb078AlphaDummy009) ∉
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) :=
  by
  simpa only [nb078AlphaDummy009] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
      0

theorem nb078_fresh_128 :
    (nb078AlphaDummy010) ∉
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) :=
  by
  simpa only [nb078AlphaDummy010] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
      1

theorem nb078_fresh_129 :
    (nb078AlphaDummy011) ∉
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) :=
  by
  simpa only [nb078AlphaDummy011] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv)
      2

theorem nb078_distinct_130 : (nb078AlphaDummy009) ≠ (nb078AlphaDummy010) := by
  simpa only [nb078AlphaDummy009, nb078AlphaDummy010] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_131 : (nb078AlphaDummy009) ≠ (nb078AlphaDummy011) := by
  simpa only [nb078AlphaDummy009, nb078AlphaDummy011] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_132 : (nb078AlphaDummy010) ≠ (nb078AlphaDummy011) := by
  simpa only [nb078AlphaDummy010, nb078AlphaDummy011] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy000)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_133 :
    (nb078AlphaDummy243) ∉
      (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy243] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_134 :
    (nb078AlphaDummy244) ∉
      (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy244] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_135 : (nb078AlphaDummy243) ≠ (nb078AlphaDummy244) := by
  simpa only [nb078AlphaDummy243, nb078AlphaDummy244] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy000))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_136 :
    (nb078AlphaDummy367) ∉ (((Class.cv (nb078AlphaDummy001))).fv) := by
  simpa only [nb078AlphaDummy367] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy001))).fv) 0

theorem nb078_fresh_137 :
    (nb078AlphaDummy368) ∉ (((Class.cv (nb078AlphaDummy001))).fv) := by
  simpa only [nb078AlphaDummy368] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy001))).fv) 1

theorem nb078_distinct_138 : (nb078AlphaDummy367) ≠ (nb078AlphaDummy368) := by
  simpa only [nb078AlphaDummy367, nb078AlphaDummy368] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_139 :
    (nb078AlphaDummy287) ∉
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) :=
  by
  simpa only [nb078AlphaDummy287] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
      0

theorem nb078_fresh_140 :
    (nb078AlphaDummy288) ∉
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) :=
  by
  simpa only [nb078AlphaDummy288] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
      1

theorem nb078_fresh_141 :
    (nb078AlphaDummy289) ∉
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) :=
  by
  simpa only [nb078AlphaDummy289] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv)
      2

theorem nb078_distinct_142 : (nb078AlphaDummy287) ≠ (nb078AlphaDummy288) := by
  simpa only [nb078AlphaDummy287, nb078AlphaDummy288] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_143 : (nb078AlphaDummy287) ≠ (nb078AlphaDummy289) := by
  simpa only [nb078AlphaDummy287, nb078AlphaDummy289] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_144 : (nb078AlphaDummy288) ≠ (nb078AlphaDummy289) := by
  simpa only [nb078AlphaDummy288, nb078AlphaDummy289] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy001)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_145 :
    (nb078AlphaDummy525) ∉
      (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy525] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_146 :
    (nb078AlphaDummy526) ∉
      (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy526] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_147 : (nb078AlphaDummy525) ≠ (nb078AlphaDummy526) := by
  simpa only [nb078AlphaDummy525, nb078AlphaDummy526] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_148 :
    (nb078AlphaDummy847) ∉ (((Class.cv (nb078AlphaDummy002))).fv) := by
  simpa only [nb078AlphaDummy847] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy002))).fv) 0

theorem nb078_fresh_149 :
    (nb078AlphaDummy848) ∉ (((Class.cv (nb078AlphaDummy002))).fv) := by
  simpa only [nb078AlphaDummy848] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy002))).fv) 1

theorem nb078_distinct_150 : (nb078AlphaDummy847) ≠ (nb078AlphaDummy848) := by
  simpa only [nb078AlphaDummy847, nb078AlphaDummy848] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_151 :
    (nb078AlphaDummy767) ∉
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) :=
  by
  simpa only [nb078AlphaDummy767] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
      0

theorem nb078_fresh_152 :
    (nb078AlphaDummy768) ∉
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) :=
  by
  simpa only [nb078AlphaDummy768] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
      1

theorem nb078_fresh_153 :
    (nb078AlphaDummy769) ∉
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) :=
  by
  simpa only [nb078AlphaDummy769] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv)
      2

theorem nb078_distinct_154 : (nb078AlphaDummy767) ≠ (nb078AlphaDummy768) := by
  simpa only [nb078AlphaDummy767, nb078AlphaDummy768] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_distinct_155 : (nb078AlphaDummy767) ≠ (nb078AlphaDummy769) := by
  simpa only [nb078AlphaDummy767, nb078AlphaDummy769] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (i := 0) (j := 2) (by decide))

theorem nb078_distinct_156 : (nb078AlphaDummy768) ≠ (nb078AlphaDummy769) := by
  simpa only [nb078AlphaDummy768, nb078AlphaDummy769] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) (i := 1) (j := 2) (by decide))

theorem nb078_fresh_157 :
    (nb078AlphaDummy1005) ∉
      (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy1005] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) 0

theorem nb078_fresh_158 :
    (nb078AlphaDummy1006) ∉
      (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb078AlphaDummy1006] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) 1

theorem nb078_distinct_159 : (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1006) := by
  simpa only [nb078AlphaDummy1005, nb078AlphaDummy1006] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_fresh_160 :
    (nb078AlphaDummy017) ∉
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  simpa only [nb078AlphaDummy017] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      0

theorem nb078_fresh_161 :
    (nb078AlphaDummy018) ∉
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  simpa only [nb078AlphaDummy018] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      1

theorem nb078_distinct_162 : (nb078AlphaDummy017) ≠ (nb078AlphaDummy018) := by
  simpa only [nb078AlphaDummy017, nb078AlphaDummy018] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_163 :
    (nb078AlphaDummy053) ∉
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) :=
  by
  simpa only [nb078AlphaDummy053] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv)
      0

theorem nb078_fresh_164 :
    (nb078AlphaDummy054) ∉
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv) :=
  by
  simpa only [nb078AlphaDummy054] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv)
      1

theorem nb078_distinct_165 : (nb078AlphaDummy053) ≠ (nb078AlphaDummy054) := by
  simpa only [nb078AlphaDummy053, nb078AlphaDummy054] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy009))).fv ∪ ((Class.cv (nb078AlphaDummy011))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_166 :
    (nb078AlphaDummy167) ∉
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  simpa only [nb078AlphaDummy167] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      0

theorem nb078_fresh_167 :
    (nb078AlphaDummy168) ∉
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv) :=
  by
  simpa only [nb078AlphaDummy168] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      1

theorem nb078_distinct_168 : (nb078AlphaDummy167) ≠ (nb078AlphaDummy168) := by
  simpa only [nb078AlphaDummy167, nb078AlphaDummy168] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy011))).fv ∪ ((Class.cv (nb078AlphaDummy010))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_169 (f : Var) :
    (nb078AlphaDummy019 f) ∉
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  simpa only [nb078AlphaDummy019] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv)
      0

theorem nb078_fresh_170 (f : Var) :
    (nb078AlphaDummy020 f) ∉
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  simpa only [nb078AlphaDummy020] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv)
      1

theorem nb078_distinct_171 (f : Var) :
    (nb078AlphaDummy019 f) ≠ (nb078AlphaDummy020 f) := by
  simpa only [nb078AlphaDummy019, nb078AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
        ((Class.cv (nb078AlphaDummy013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_172 (f : Var) :
    (nb078AlphaDummy055 f) ∉
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) :=
  by
  simpa only [nb078AlphaDummy055] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv)
      0

theorem nb078_fresh_173 (f : Var) :
    (nb078AlphaDummy056 f) ∉
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv) :=
  by
  simpa only [nb078AlphaDummy056] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy012 f))).fv ∪ ((Class.cv (nb078AlphaDummy014 f))).fv)
      1

theorem nb078_distinct_174 (f : Var) :
    (nb078AlphaDummy055 f) ≠ (nb078AlphaDummy056 f) := by
  simpa only [nb078AlphaDummy055, nb078AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy012 f))).fv ∪
        ((Class.cv (nb078AlphaDummy014 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_175 (f : Var) :
    (nb078AlphaDummy169 f) ∉
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  simpa only [nb078AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv)
      0

theorem nb078_fresh_176 (f : Var) :
    (nb078AlphaDummy170 f) ∉
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv) :=
  by
  simpa only [nb078AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy014 f))).fv ∪ ((Class.cv (nb078AlphaDummy013 f))).fv)
      1

theorem nb078_distinct_177 (f : Var) :
    (nb078AlphaDummy169 f) ≠ (nb078AlphaDummy170 f) := by
  simpa only [nb078AlphaDummy169, nb078AlphaDummy170] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy014 f))).fv ∪
        ((Class.cv (nb078AlphaDummy013 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_178 :
    (nb078AlphaDummy025) ∉ (((Class.cv (nb078AlphaDummy018))).fv) := by
  simpa only [nb078AlphaDummy025] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy018))).fv) 0

theorem nb078_fresh_179 :
    (nb078AlphaDummy026) ∉ (((Class.cv (nb078AlphaDummy018))).fv) := by
  simpa only [nb078AlphaDummy026] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy018))).fv) 1

theorem nb078_distinct_180 : (nb078AlphaDummy025) ≠ (nb078AlphaDummy026) := by
  simpa only [nb078AlphaDummy025, nb078AlphaDummy026] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy018))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_181 (f : Var) :
    (nb078AlphaDummy027 f) ∉ (((Class.cv (nb078AlphaDummy020 f))).fv) := by
  simpa only [nb078AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy020 f))).fv) 0

theorem nb078_fresh_182 (f : Var) :
    (nb078AlphaDummy028 f) ∉ (((Class.cv (nb078AlphaDummy020 f))).fv) := by
  simpa only [nb078AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy020 f))).fv) 1

theorem nb078_distinct_183 (f : Var) :
    (nb078AlphaDummy027 f) ≠ (nb078AlphaDummy028 f) := by
  simpa only [nb078AlphaDummy027, nb078AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy020 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_184 :
    (nb078AlphaDummy031) ∉
      (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy031] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_185 :
    (nb078AlphaDummy032) ∉
      (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy032] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_186 :
    (nb078AlphaDummy033) ∉
      (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy033] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_187 : (nb078AlphaDummy031) ≠ (nb078AlphaDummy032) := by
  simpa only [nb078AlphaDummy031, nb078AlphaDummy032] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_188 : (nb078AlphaDummy031) ≠ (nb078AlphaDummy033) := by
  simpa only [nb078AlphaDummy031, nb078AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_189 : (nb078AlphaDummy032) ≠ (nb078AlphaDummy033) := by
  simpa only [nb078AlphaDummy032, nb078AlphaDummy033] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy025))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_190 (f : Var) :
    (nb078AlphaDummy034 f) ∉
      (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy034] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_191 (f : Var) :
    (nb078AlphaDummy035 f) ∉
      (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy035] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_192 (f : Var) :
    (nb078AlphaDummy036 f) ∉
      (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy036] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_193 (f : Var) :
    (nb078AlphaDummy034 f) ≠ (nb078AlphaDummy035 f) := by
  simpa only [nb078AlphaDummy034, nb078AlphaDummy035] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_194 (f : Var) :
    (nb078AlphaDummy034 f) ≠ (nb078AlphaDummy036 f) := by
  simpa only [nb078AlphaDummy034, nb078AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_195 (f : Var) :
    (nb078AlphaDummy035 f) ≠ (nb078AlphaDummy036 f) := by
  simpa only [nb078AlphaDummy035, nb078AlphaDummy036] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy027 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_196 :
    (nb078AlphaDummy043) ∉
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy032))).fv) :=
  by
  simpa only [nb078AlphaDummy043] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy032))).fv)
      0

theorem nb078_fresh_197 :
    (nb078AlphaDummy039) ∉
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) :=
  by
  simpa only [nb078AlphaDummy039] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy032))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv)
      0

theorem nb078_fresh_198 :
    (nb078AlphaDummy045) ∉
      (((Class.cv (nb078AlphaDummy033))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv) :=
  by
  simpa only [nb078AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy033))).fv ∪ ((Class.cv (nb078AlphaDummy033))).fv)
      0

theorem nb078_fresh_199 (f : Var) :
    (nb078AlphaDummy044 f) ∉
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy035 f))).fv) :=
  by
  simpa only [nb078AlphaDummy044] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy035 f))).fv)
      0

theorem nb078_fresh_200 (f : Var) :
    (nb078AlphaDummy040 f) ∉
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv) :=
  by
  simpa only [nb078AlphaDummy040] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy035 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv)
      0

theorem nb078_fresh_201 (f : Var) :
    (nb078AlphaDummy046 f) ∉
      (((Class.cv (nb078AlphaDummy036 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv) :=
  by
  simpa only [nb078AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy036 f))).fv ∪ ((Class.cv (nb078AlphaDummy036 f))).fv)
      0

theorem nb078_fresh_202 :
    (nb078AlphaDummy061) ∉ (((Class.cv (nb078AlphaDummy054))).fv) := by
  simpa only [nb078AlphaDummy061] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy054))).fv) 0

theorem nb078_fresh_203 :
    (nb078AlphaDummy062) ∉ (((Class.cv (nb078AlphaDummy054))).fv) := by
  simpa only [nb078AlphaDummy062] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy054))).fv) 1

theorem nb078_distinct_204 : (nb078AlphaDummy061) ≠ (nb078AlphaDummy062) := by
  simpa only [nb078AlphaDummy061, nb078AlphaDummy062] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy054))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_205 (f : Var) :
    (nb078AlphaDummy063 f) ∉ (((Class.cv (nb078AlphaDummy056 f))).fv) := by
  simpa only [nb078AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy056 f))).fv) 0

theorem nb078_fresh_206 (f : Var) :
    (nb078AlphaDummy064 f) ∉ (((Class.cv (nb078AlphaDummy056 f))).fv) := by
  simpa only [nb078AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy056 f))).fv) 1

theorem nb078_distinct_207 (f : Var) :
    (nb078AlphaDummy063 f) ≠ (nb078AlphaDummy064 f) := by
  simpa only [nb078AlphaDummy063, nb078AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy056 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_208 :
    (nb078AlphaDummy067) ∉
      (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy067] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_209 :
    (nb078AlphaDummy068) ∉
      (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy068] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_210 :
    (nb078AlphaDummy069) ∉
      (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy069] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_211 : (nb078AlphaDummy067) ≠ (nb078AlphaDummy068) := by
  simpa only [nb078AlphaDummy067, nb078AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_212 : (nb078AlphaDummy067) ≠ (nb078AlphaDummy069) := by
  simpa only [nb078AlphaDummy067, nb078AlphaDummy069] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_213 : (nb078AlphaDummy068) ≠ (nb078AlphaDummy069) := by
  simpa only [nb078AlphaDummy068, nb078AlphaDummy069] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy061))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_214 (f : Var) :
    (nb078AlphaDummy070 f) ∉
      (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy070] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 0

theorem nb078_fresh_215 (f : Var) :
    (nb078AlphaDummy071 f) ∉
      (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy071] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 1

theorem nb078_fresh_216 (f : Var) :
    (nb078AlphaDummy072 f) ∉
      (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb078AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) 2

theorem nb078_distinct_217 (f : Var) :
    (nb078AlphaDummy070 f) ≠ (nb078AlphaDummy071 f) := by
  simpa only [nb078AlphaDummy070, nb078AlphaDummy071] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb078_distinct_218 (f : Var) :
    (nb078AlphaDummy070 f) ≠ (nb078AlphaDummy072 f) := by
  simpa only [nb078AlphaDummy070, nb078AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb078_distinct_219 (f : Var) :
    (nb078AlphaDummy071 f) ≠ (nb078AlphaDummy072 f) := by
  simpa only [nb078AlphaDummy071, nb078AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy063 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb078_fresh_220 :
    (nb078AlphaDummy079) ∉
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy068))).fv) :=
  by
  simpa only [nb078AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy068))).fv)
      0

theorem nb078_fresh_221 :
    (nb078AlphaDummy075) ∉
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) :=
  by
  simpa only [nb078AlphaDummy075] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy068))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv)
      0

theorem nb078_fresh_222 :
    (nb078AlphaDummy081) ∉
      (((Class.cv (nb078AlphaDummy069))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv) :=
  by
  simpa only [nb078AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy069))).fv ∪ ((Class.cv (nb078AlphaDummy069))).fv)
      0

theorem nb078_fresh_223 (f : Var) :
    (nb078AlphaDummy080 f) ∉
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy071 f))).fv) :=
  by
  simpa only [nb078AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy071 f))).fv)
      0

theorem nb078_fresh_224 (f : Var) :
    (nb078AlphaDummy076 f) ∉
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv) :=
  by
  simpa only [nb078AlphaDummy076] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy071 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv)
      0

theorem nb078_fresh_225 (f : Var) :
    (nb078AlphaDummy082 f) ∉
      (((Class.cv (nb078AlphaDummy072 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv) :=
  by
  simpa only [nb078AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy072 f))).fv ∪ ((Class.cv (nb078AlphaDummy072 f))).fv)
      0

theorem nb078_fresh_226 :
    (nb078AlphaDummy095) ∉
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) :=
  by
  simpa only [nb078AlphaDummy095] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv)
      0

theorem nb078_fresh_227 :
    (nb078AlphaDummy096) ∉
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv) :=
  by
  simpa only [nb078AlphaDummy096] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv)
      1

theorem nb078_distinct_228 : (nb078AlphaDummy095) ≠ (nb078AlphaDummy096) := by
  simpa only [nb078AlphaDummy095, nb078AlphaDummy096] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy089))).fv ∪ ((Class.cv (nb078AlphaDummy090))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_229 :
    (nb078AlphaDummy131) ∉
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) :=
  by
  simpa only [nb078AlphaDummy131] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv)
      0

theorem nb078_fresh_230 :
    (nb078AlphaDummy132) ∉
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv) :=
  by
  simpa only [nb078AlphaDummy132] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv)
      1

theorem nb078_distinct_231 : (nb078AlphaDummy131) ≠ (nb078AlphaDummy132) := by
  simpa only [nb078AlphaDummy131, nb078AlphaDummy132] using
    (freshVar_injective
      (((Class.cv (nb078AlphaDummy090))).fv ∪ ((Class.cv (nb078AlphaDummy089))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb078_fresh_232 (f : Var) :
    (nb078AlphaDummy097 f) ∉
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) :=
  by
  simpa only [nb078AlphaDummy097] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv)
      0

theorem nb078_fresh_233 (f : Var) :
    (nb078AlphaDummy098 f) ∉
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv) :=
  by
  simpa only [nb078AlphaDummy098] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy091 f))).fv ∪ ((Class.cv (nb078AlphaDummy092 f))).fv)
      1

theorem nb078_distinct_234 (f : Var) :
    (nb078AlphaDummy097 f) ≠ (nb078AlphaDummy098 f) := by
  simpa only [nb078AlphaDummy097, nb078AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy091 f))).fv ∪
        ((Class.cv (nb078AlphaDummy092 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_235 (f : Var) :
    (nb078AlphaDummy133 f) ∉
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) :=
  by
  simpa only [nb078AlphaDummy133] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv)
      0

theorem nb078_fresh_236 (f : Var) :
    (nb078AlphaDummy134 f) ∉
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv) :=
  by
  simpa only [nb078AlphaDummy134] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy092 f))).fv ∪ ((Class.cv (nb078AlphaDummy091 f))).fv)
      1

theorem nb078_distinct_237 (f : Var) :
    (nb078AlphaDummy133 f) ≠ (nb078AlphaDummy134 f) := by
  simpa only [nb078AlphaDummy133, nb078AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy092 f))).fv ∪
        ((Class.cv (nb078AlphaDummy091 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_238 :
    (nb078AlphaDummy103) ∉ (((Class.cv (nb078AlphaDummy096))).fv) := by
  simpa only [nb078AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy096))).fv) 0

theorem nb078_fresh_239 :
    (nb078AlphaDummy104) ∉ (((Class.cv (nb078AlphaDummy096))).fv) := by
  simpa only [nb078AlphaDummy104] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy096))).fv) 1

theorem nb078_distinct_240 : (nb078AlphaDummy103) ≠ (nb078AlphaDummy104) := by
  simpa only [nb078AlphaDummy103, nb078AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy096))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_241 (f : Var) :
    (nb078AlphaDummy105 f) ∉ (((Class.cv (nb078AlphaDummy098 f))).fv) := by
  simpa only [nb078AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy098 f))).fv) 0

theorem nb078_fresh_242 (f : Var) :
    (nb078AlphaDummy106 f) ∉ (((Class.cv (nb078AlphaDummy098 f))).fv) := by
  simpa only [nb078AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy098 f))).fv) 1

theorem nb078_distinct_243 (f : Var) :
    (nb078AlphaDummy105 f) ≠ (nb078AlphaDummy106 f) := by
  simpa only [nb078AlphaDummy105, nb078AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy098 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_244 :
    (nb078AlphaDummy1009) ∉
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) :=
  by
  simpa only [nb078AlphaDummy1009] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv)
      0

theorem nb078_fresh_245 :
    (nb078AlphaDummy1010) ∉
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) :=
  by
  simpa only [nb078AlphaDummy1010] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv)
      1

theorem nb078_distinct_246 : (nb078AlphaDummy1009) ≠ (nb078AlphaDummy1010) := by
  simpa only [nb078AlphaDummy1009, nb078AlphaDummy1010] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1006))).fv ∪
        ((Class.cv (nb078AlphaDummy1005))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_247 (h : Var) :
    (nb078AlphaDummy1011 h) ∉
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1007 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1011] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪ ((Class.cv (nb078AlphaDummy1007 h))).fv)
      0

theorem nb078_fresh_248 (h : Var) :
    (nb078AlphaDummy1012 h) ∉
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1007 h))).fv) :=
  by
  simpa only [nb078AlphaDummy1012] using
    freshVar_not_mem
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪ ((Class.cv (nb078AlphaDummy1007 h))).fv)
      1

theorem nb078_distinct_249 (h : Var) :
    (nb078AlphaDummy1011 h) ≠ (nb078AlphaDummy1012 h) := by
  simpa only [nb078AlphaDummy1011, nb078AlphaDummy1012] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1007 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb078_fresh_250 :
    (nb078AlphaDummy1017) ∉ (((Class.cv (nb078AlphaDummy1010))).fv) := by
  simpa only [nb078AlphaDummy1017] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1010))).fv) 0

theorem nb078_fresh_251 :
    (nb078AlphaDummy1018) ∉ (((Class.cv (nb078AlphaDummy1010))).fv) := by
  simpa only [nb078AlphaDummy1018] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1010))).fv) 1

theorem nb078_distinct_252 : (nb078AlphaDummy1017) ≠ (nb078AlphaDummy1018) := by
  simpa only [nb078AlphaDummy1017, nb078AlphaDummy1018] using
    (freshVar_injective (((Class.cv (nb078AlphaDummy1010))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb078_fresh_253 (h : Var) :
    (nb078AlphaDummy1019 h) ∉ (((Class.cv (nb078AlphaDummy1012 h))).fv) := by
  simpa only [nb078AlphaDummy1019] using
    freshVar_not_mem (((Class.cv (nb078AlphaDummy1012 h))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
