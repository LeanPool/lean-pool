/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part006`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_750`. -/
@[expose]
noncomputable def nb090AlphaDummy750 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_751`. -/
@[expose]
noncomputable def nb090AlphaDummy751 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy709 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_752`. -/
@[expose]
noncomputable def nb090AlphaDummy752 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy710 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_753`. -/
@[expose]
noncomputable def nb090AlphaDummy753 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy700 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_754`. -/
@[expose]
noncomputable def nb090AlphaDummy754 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy700 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_755`. -/
@[expose]
noncomputable def nb090AlphaDummy755 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy702 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_756`. -/
@[expose]
noncomputable def nb090AlphaDummy756 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy702 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_757`. -/
@[expose]
noncomputable def nb090AlphaDummy757 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy753 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy753 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy753 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_758`. -/
@[expose]
noncomputable def nb090AlphaDummy758 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy755 v u h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy755 v u h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy755 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_759`. -/
@[expose]
noncomputable def nb090AlphaDummy759 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_760`. -/
@[expose]
noncomputable def nb090AlphaDummy760 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_761`. -/
@[expose]
noncomputable def nb090AlphaDummy761 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_762`. -/
@[expose]
noncomputable def nb090AlphaDummy762 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_763`. -/
@[expose]
noncomputable def nb090AlphaDummy763 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_764`. -/
@[expose]
noncomputable def nb090AlphaDummy764 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_765`. -/
@[expose]
noncomputable def nb090AlphaDummy765 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy760 A))
          (Class.cv (nb090AlphaDummy761 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy760 A)) (Class.cv (nb090AlphaDummy761 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_766`. -/
@[expose]
noncomputable def nb090AlphaDummy766 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy763 v u h))
          (Class.cv (nb090AlphaDummy764 v u h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy763 v u h))
          (Class.cv (nb090AlphaDummy764 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_767`. -/
@[expose]
noncomputable def nb090AlphaDummy767 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy760 A))).fv ∪
      ((Class.cv (nb090AlphaDummy761 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_768`. -/
@[expose]
noncomputable def nb090AlphaDummy768 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy764 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_769`. -/
@[expose]
noncomputable def nb090AlphaDummy769 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy760 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy761 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_770`. -/
@[expose]
noncomputable def nb090AlphaDummy770 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy763 v u h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy764 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_771`. -/
@[expose]
noncomputable def nb090AlphaDummy771 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy760 A))).fv ∪
      ((Class.cv (nb090AlphaDummy760 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_772`. -/
@[expose]
noncomputable def nb090AlphaDummy772 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy763 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_773`. -/
@[expose]
noncomputable def nb090AlphaDummy773 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy761 A))).fv ∪
      ((Class.cv (nb090AlphaDummy761 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_774`. -/
@[expose]
noncomputable def nb090AlphaDummy774 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy764 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy764 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_775`. -/
@[expose]
noncomputable def nb090AlphaDummy775 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
            (synCfv (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy042 A)))
            (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy699 A)
          (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
              (Class.cv (nb090AlphaDummy042 A)))
            (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_776`. -/
@[expose]
noncomputable def nb090AlphaDummy776 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
            (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
            (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy701 v u h)
          (synWrex (nb090AlphaDummy702 v u h)
            (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
            (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_777`. -/
@[expose]
noncomputable def nb090AlphaDummy777 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy000 A))).fv ∪
      ((Class.cv (nb090AlphaDummy042 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_778`. -/
@[expose]
noncomputable def nb090AlphaDummy778 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy044 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_779`. -/
@[expose]
noncomputable def nb090AlphaDummy779 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy777 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
          (Class.cv (nb090AlphaDummy777 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_780`. -/
@[expose]
noncomputable def nb090AlphaDummy780 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (({(nb090AlphaDummy778 v u h)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
          (Class.cv (nb090AlphaDummy778 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_781`. -/
@[expose]
noncomputable def nb090AlphaDummy781 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy777 A) (synWbr (Class.cv (nb090AlphaDummy042 A))
              (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy777 A))))
          (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_782`. -/
@[expose]
noncomputable def nb090AlphaDummy782 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy777 A) (synWbr (Class.cv (nb090AlphaDummy042 A))
              (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy777 A))))
          (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_783`. -/
@[expose]
noncomputable def nb090AlphaDummy783 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
          (Class.cab (nb090AlphaDummy778 v u h)
            (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
              (Class.cv (nb090AlphaDummy778 v u h))))
          (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_784`. -/
@[expose]
noncomputable def nb090AlphaDummy784 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
          (Class.cab (nb090AlphaDummy778 v u h)
            (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
              (Class.cv (nb090AlphaDummy778 v u h))))
          (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_785`. -/
@[expose]
noncomputable def nb090AlphaDummy785 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy042 A))).fv ∪
      ((Class.cv (nb090AlphaDummy777 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_786`. -/
@[expose]
noncomputable def nb090AlphaDummy786 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy042 A))).fv ∪
      ((Class.cv (nb090AlphaDummy777 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_787`. -/
@[expose]
noncomputable def nb090AlphaDummy787 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy778 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_788`. -/
@[expose]
noncomputable def nb090AlphaDummy788 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy778 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_789`. -/
@[expose]
noncomputable def nb090AlphaDummy789 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_790`. -/
@[expose]
noncomputable def nb090AlphaDummy790 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy787 v u h)
            (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_791`. -/
@[expose]
noncomputable def nb090AlphaDummy791 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy785 A)
          (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
              (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy785 A)
          (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
              (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_792`. -/
@[expose]
noncomputable def nb090AlphaDummy792 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy787 v u h)
          (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
              (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv ∪
      ((Class.cab (nb090AlphaDummy787 v u h)
          (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
              (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_793`. -/
@[expose]
noncomputable def nb090AlphaDummy793 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy786 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_794`. -/
@[expose]
noncomputable def nb090AlphaDummy794 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy786 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_795`. -/
@[expose]
noncomputable def nb090AlphaDummy795 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy788 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_796`. -/
@[expose]
noncomputable def nb090AlphaDummy796 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy788 v u h))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_797`. -/
@[expose]
noncomputable def nb090AlphaDummy797 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy793 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy793 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy793 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_798`. -/
@[expose]
noncomputable def nb090AlphaDummy798 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy795 v u h)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy795 v u h)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy795 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_799`. -/
@[expose]
noncomputable def nb090AlphaDummy799 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_800`. -/
@[expose]
noncomputable def nb090AlphaDummy800 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_801`. -/
@[expose]
noncomputable def nb090AlphaDummy801 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_802`. -/
@[expose]
noncomputable def nb090AlphaDummy802 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_803`. -/
@[expose]
noncomputable def nb090AlphaDummy803 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_804`. -/
@[expose]
noncomputable def nb090AlphaDummy804 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_805`. -/
@[expose]
noncomputable def nb090AlphaDummy805 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy800 A))
          (Class.cv (nb090AlphaDummy801 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy800 A)) (Class.cv (nb090AlphaDummy801 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_806`. -/
@[expose]
noncomputable def nb090AlphaDummy806 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy803 v u h))
          (Class.cv (nb090AlphaDummy804 v u h)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy803 v u h))
          (Class.cv (nb090AlphaDummy804 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_807`. -/
@[expose]
noncomputable def nb090AlphaDummy807 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy800 A))).fv ∪
      ((Class.cv (nb090AlphaDummy801 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_808`. -/
@[expose]
noncomputable def nb090AlphaDummy808 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy804 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_809`. -/
@[expose]
noncomputable def nb090AlphaDummy809 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy800 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy801 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_810`. -/
@[expose]
noncomputable def nb090AlphaDummy810 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy803 v u h)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy804 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_811`. -/
@[expose]
noncomputable def nb090AlphaDummy811 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy800 A))).fv ∪
      ((Class.cv (nb090AlphaDummy800 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_812`. -/
@[expose]
noncomputable def nb090AlphaDummy812 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy803 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_813`. -/
@[expose]
noncomputable def nb090AlphaDummy813 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy801 A))).fv ∪
      ((Class.cv (nb090AlphaDummy801 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_814`. -/
@[expose]
noncomputable def nb090AlphaDummy814 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy804 v u h))).fv ∪
      ((Class.cv (nb090AlphaDummy804 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_815`. -/
@[expose]
noncomputable def nb090AlphaDummy815 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy785 A)
          (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy785 A)
          (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_816`. -/
@[expose]
noncomputable def nb090AlphaDummy816 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy787 v u h)
          (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy778 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy787 v u h)
          (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy778 v u h))
            (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
              (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_817`. -/
@[expose]
noncomputable def nb090AlphaDummy817 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy786 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_818`. -/
@[expose]
noncomputable def nb090AlphaDummy818 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy788 v u h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_819`. -/
@[expose]
noncomputable def nb090AlphaDummy819 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_820`. -/
@[expose]
noncomputable def nb090AlphaDummy820 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_821`. -/
@[expose]
noncomputable def nb090AlphaDummy821 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy779 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_822`. -/
@[expose]
noncomputable def nb090AlphaDummy822 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy780 v u h))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_823`. -/
@[expose]
noncomputable def nb090AlphaDummy823 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy700 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_824`. -/
@[expose]
noncomputable def nb090AlphaDummy824 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy702 v u h))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_825`. -/
@[expose]
noncomputable def nb090AlphaDummy825 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_826`. -/
@[expose]
noncomputable def nb090AlphaDummy826 (v : Var) (u : Var) (h : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_827`. -/
@[expose]
noncomputable def nb090AlphaDummy827 (A : Class) : Var :=
  (freshVar (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_828`. -/
@[expose]
noncomputable def nb090AlphaDummy828 (v : Var) : Var :=
  (freshVar (((synC1st)).fv ∪ ((Class.cv v)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_829`. -/
@[expose]
noncomputable def nb090AlphaDummy829 (A : Class) : Var :=
  (freshVar (({(nb090AlphaDummy827 A)} : Finset Var) ∪
      ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
          (Class.cv (nb090AlphaDummy827 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_830`. -/
@[expose]
noncomputable def nb090AlphaDummy830 (v : Var) : Var :=
  (freshVar (({(nb090AlphaDummy828 v)} : Finset Var) ∪
      ((synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_831`. -/
@[expose]
noncomputable def nb090AlphaDummy831 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy827 A)
            (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
              (Class.cv (nb090AlphaDummy827 A))))
          (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_832`. -/
@[expose]
noncomputable def nb090AlphaDummy832 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq
          (Class.cab (nb090AlphaDummy827 A)
            (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
              (Class.cv (nb090AlphaDummy827 A))))
          (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_833`. -/
@[expose]
noncomputable def nb090AlphaDummy833 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq
          (Class.cab (nb090AlphaDummy828 v)
            (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
          (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_834`. -/
@[expose]
noncomputable def nb090AlphaDummy834 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq
          (Class.cab (nb090AlphaDummy828 v)
            (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
          (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_835`. -/
@[expose]
noncomputable def nb090AlphaDummy835 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy002 A))).fv ∪
      ((Class.cv (nb090AlphaDummy827 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_836`. -/
@[expose]
noncomputable def nb090AlphaDummy836 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy002 A))).fv ∪
      ((Class.cv (nb090AlphaDummy827 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_837`. -/
@[expose]
noncomputable def nb090AlphaDummy837 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_838`. -/
@[expose]
noncomputable def nb090AlphaDummy838 (v : Var) : Var :=
  (freshVar (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_839`. -/
@[expose]
noncomputable def nb090AlphaDummy839 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_840`. -/
@[expose]
noncomputable def nb090AlphaDummy840 (v : Var) : Var :=
  (freshVar (((synCcompl (Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v)))))))).fv ∪ ((synCcompl
          (Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c)))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_841`. -/
@[expose]
noncomputable def nb090AlphaDummy841 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy835 A)
          (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
              (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv ∪
      ((Class.cab (nb090AlphaDummy835 A)
          (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
              (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_842`. -/
@[expose]
noncomputable def nb090AlphaDummy842 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy837 v)
          (synWrex (nb090AlphaDummy838 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
              (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv ∪
      ((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
            (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
              (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_843`. -/
@[expose]
noncomputable def nb090AlphaDummy843 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy836 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_844`. -/
@[expose]
noncomputable def nb090AlphaDummy844 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy836 A))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_845`. -/
@[expose]
noncomputable def nb090AlphaDummy845 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy838 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_846`. -/
@[expose]
noncomputable def nb090AlphaDummy846 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy838 v))).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_847`. -/
@[expose]
noncomputable def nb090AlphaDummy847 (A : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy843 A)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy843 A)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy843 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_848`. -/
@[expose]
noncomputable def nb090AlphaDummy848 (v : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb090AlphaDummy845 v)) (synCnnc))).fv ∪
        ((synCplc (Class.cv (nb090AlphaDummy845 v)) (synC1c))).fv ∪
      ((Class.cv (nb090AlphaDummy845 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_849`. -/
@[expose]
noncomputable def nb090AlphaDummy849 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_850`. -/
@[expose]
noncomputable def nb090AlphaDummy850 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_851`. -/
@[expose]
noncomputable def nb090AlphaDummy851 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_852`. -/
@[expose]
noncomputable def nb090AlphaDummy852 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_853`. -/
@[expose]
noncomputable def nb090AlphaDummy853 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 1)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_854`. -/
@[expose]
noncomputable def nb090AlphaDummy854 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) 2)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_855`. -/
@[expose]
noncomputable def nb090AlphaDummy855 (A : Class) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy850 A))
          (Class.cv (nb090AlphaDummy851 A)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy850 A)) (Class.cv (nb090AlphaDummy851 A)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_856`. -/
@[expose]
noncomputable def nb090AlphaDummy856 (v : Var) : Var :=
  (freshVar (((synCnin (Class.cv (nb090AlphaDummy853 v))
          (Class.cv (nb090AlphaDummy854 v)))).fv ∪
      ((synCnin (Class.cv (nb090AlphaDummy853 v)) (Class.cv (nb090AlphaDummy854 v)))).fv)
    0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_857`. -/
@[expose]
noncomputable def nb090AlphaDummy857 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy850 A))).fv ∪
      ((Class.cv (nb090AlphaDummy851 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_858`. -/
@[expose]
noncomputable def nb090AlphaDummy858 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy853 v))).fv ∪
      ((Class.cv (nb090AlphaDummy854 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_859`. -/
@[expose]
noncomputable def nb090AlphaDummy859 (A : Class) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy850 A)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy851 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_860`. -/
@[expose]
noncomputable def nb090AlphaDummy860 (v : Var) : Var :=
  (freshVar (((synCcompl (Class.cv (nb090AlphaDummy853 v)))).fv ∪
      ((synCcompl (Class.cv (nb090AlphaDummy854 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_861`. -/
@[expose]
noncomputable def nb090AlphaDummy861 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy850 A))).fv ∪
      ((Class.cv (nb090AlphaDummy850 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_862`. -/
@[expose]
noncomputable def nb090AlphaDummy862 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy853 v))).fv ∪
      ((Class.cv (nb090AlphaDummy853 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_863`. -/
@[expose]
noncomputable def nb090AlphaDummy863 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy851 A))).fv ∪
      ((Class.cv (nb090AlphaDummy851 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_864`. -/
@[expose]
noncomputable def nb090AlphaDummy864 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy854 v))).fv ∪
      ((Class.cv (nb090AlphaDummy854 v))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_865`. -/
@[expose]
noncomputable def nb090AlphaDummy865 (A : Class) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy835 A)
          (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy835 A)
          (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
            (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
              (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_866`. -/
@[expose]
noncomputable def nb090AlphaDummy866 (v : Var) : Var :=
  (freshVar (((Class.cab (nb090AlphaDummy837 v)
          (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
            (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
              (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy837 v)
          (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
            (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
              (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                (synCsn (synC0c))))))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_867`. -/
@[expose]
noncomputable def nb090AlphaDummy867 (A : Class) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy836 A))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_868`. -/
@[expose]
noncomputable def nb090AlphaDummy868 (v : Var) : Var :=
  (freshVar (((synCcompl (synCphi (Class.cv (nb090AlphaDummy838 v))))).fv ∪
      ((synCcompl (synCsn (synC0c)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_869`. -/
@[expose]
noncomputable def nb090AlphaDummy869 (A : Class) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_870`. -/
@[expose]
noncomputable def nb090AlphaDummy870 (v : Var) : Var :=
  (freshVar (((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv ∪
      ((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_871`. -/
@[expose]
noncomputable def nb090AlphaDummy871 (A : Class) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy829 A))).fv) 0)

/-- Checked nominal proof certificate identified upstream as `nb090_alpha_dummy_872`. -/
@[expose]
noncomputable def nb090AlphaDummy872 (v : Var) : Var :=
  (freshVar (((Class.cv (nb090AlphaDummy830 v))).fv) 0)

theorem nb090_fresh_000 (A : Class) :
    (nb090AlphaDummy011 A) ∉
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy011] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv)
      0

theorem nb090_fresh_001 (A : Class) :
    (nb090AlphaDummy035 A) ∉
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy035] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_002 (v : Var) (u : Var) :
    (nb090AlphaDummy012 v u) ∉
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv) :=
  by
  simpa only [nb090AlphaDummy012] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv)
      0

theorem nb090_fresh_003 (v : Var) (u : Var) :
    (nb090AlphaDummy036 v u) ∉
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy036] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_004 (A : Class) :
    (nb090AlphaDummy063 A) ∉
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy063] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv)
      0

theorem nb090_fresh_005 (A : Class) :
    (nb090AlphaDummy087 A) ∉
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy087] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_006 (h : Var) :
    (nb090AlphaDummy064 h) ∉
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy064] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv)
      0

theorem nb090_fresh_007 (h : Var) :
    (nb090AlphaDummy088 h) ∉
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy088] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_008 (A : Class) :
    (nb090AlphaDummy099 A) ∉
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy099] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv)
      0

theorem nb090_fresh_009 (A : Class) :
    (nb090AlphaDummy123 A) ∉
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy123] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_010 (h : Var) :
    (nb090AlphaDummy100 h) ∉
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy100] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv)
      0

theorem nb090_fresh_011 (h : Var) :
    (nb090AlphaDummy124 h) ∉
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy124] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_012 (A : Class) :
    (nb090AlphaDummy141 A) ∉
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy141] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv)
      0

theorem nb090_fresh_013 (A : Class) :
    (nb090AlphaDummy165 A) ∉
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy165] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_014 (h : Var) :
    (nb090AlphaDummy142 h) ∉
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy142] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv)
      0

theorem nb090_fresh_015 (h : Var) :
    (nb090AlphaDummy166 h) ∉
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy166] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_016 (A : Class) :
    (nb090AlphaDummy201 A) ∉
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy201] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_017 (A : Class) :
    (nb090AlphaDummy177 A) ∉
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy177] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv)
      0

theorem nb090_fresh_018 (h : Var) :
    (nb090AlphaDummy202 h) ∉
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy202] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_019 (h : Var) :
    (nb090AlphaDummy178 h) ∉
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy178] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv)
      0

theorem nb090_fresh_020 (A : Class) :
    (nb090AlphaDummy237 A) ∉
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy237] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_021 (A : Class) :
    (nb090AlphaDummy213 A) ∉
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy213] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv)
      0

theorem nb090_fresh_022 (h : Var) :
    (nb090AlphaDummy238 h) ∉
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy238] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_023 (h : Var) :
    (nb090AlphaDummy214 h) ∉
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy214] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv)
      0

theorem nb090_fresh_024 (A : Class) :
    (nb090AlphaDummy277 A) ∉
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy277] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_025 (A : Class) :
    (nb090AlphaDummy253 A) ∉
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy253] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv)
      0

theorem nb090_fresh_026 (h : Var) :
    (nb090AlphaDummy278 h) ∉
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy278] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part007`. -/


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

theorem nb090_fresh_027 (h : Var) :
    (nb090AlphaDummy254 h) ∉
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy254] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv)
      0

theorem nb090_fresh_028 (A : Class) :
    (nb090AlphaDummy287 A) ∉
      (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy287] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv)
      0

theorem nb090_fresh_029 (A : Class) :
    (nb090AlphaDummy288 A) ∉
      (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy288] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv)
      1

theorem nb090_distinct_030 (A : Class) :
    (nb090AlphaDummy287 A) ≠ (nb090AlphaDummy288 A) := by
  simpa only [nb090AlphaDummy287, nb090AlphaDummy288] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_031 (u : Var) :
    (nb090AlphaDummy289 u) ∉
      (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) :=
  by
  simpa only [nb090AlphaDummy289] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv)
      0

theorem nb090_fresh_032 (u : Var) :
    (nb090AlphaDummy290 u) ∉
      (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) :=
  by
  simpa only [nb090AlphaDummy290] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv)
      1

theorem nb090_distinct_033 (u : Var) :
    (nb090AlphaDummy289 u) ≠ (nb090AlphaDummy290 u) := by
  simpa only [nb090AlphaDummy289, nb090AlphaDummy290] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq
            (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_034 (A : Class) :
    (nb090AlphaDummy297 A) ∉
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy297] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv)
      0

theorem nb090_fresh_035 (A : Class) :
    (nb090AlphaDummy321 A) ∉
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy321] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_036 (u : Var) :
    (nb090AlphaDummy322 u) ∉
      (((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy322] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_037 (u : Var) :
    (nb090AlphaDummy298 u) ∉
      (((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv) :=
  by
  simpa only [nb090AlphaDummy298] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv)
      0

theorem nb090_fresh_038 (A : Class) :
    (nb090AlphaDummy367 A) ∉
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy367] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_039 (A : Class) :
    (nb090AlphaDummy343 A) ∉
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy343] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv)
      0

theorem nb090_fresh_040 (h : Var) :
    (nb090AlphaDummy368 h) ∉
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy368] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_041 (h : Var) :
    (nb090AlphaDummy344 h) ∉
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy344] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv)
      0

theorem nb090_fresh_042 (A : Class) :
    (nb090AlphaDummy377 A) ∉
      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy377] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv)
      0

theorem nb090_fresh_043 (A : Class) :
    (nb090AlphaDummy378 A) ∉
      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy378] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv)
      1

theorem nb090_distinct_044 (A : Class) :
    (nb090AlphaDummy377 A) ≠ (nb090AlphaDummy378 A) := by
  simpa only [nb090AlphaDummy377, nb090AlphaDummy378] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_045 (v : Var) :
    (nb090AlphaDummy379 v) ∉
      (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) :=
  by
  simpa only [nb090AlphaDummy379] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv)
      0

theorem nb090_fresh_046 (v : Var) :
    (nb090AlphaDummy380 v) ∉
      (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) :=
  by
  simpa only [nb090AlphaDummy380] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv)
      1

theorem nb090_distinct_047 (v : Var) :
    (nb090AlphaDummy379 v) ≠ (nb090AlphaDummy380 v) := by
  simpa only [nb090AlphaDummy379, nb090AlphaDummy380] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq
            (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_048 (A : Class) :
    (nb090AlphaDummy387 A) ∉
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy387] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv)
      0

theorem nb090_fresh_049 (A : Class) :
    (nb090AlphaDummy411 A) ∉
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy411] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_050 (v : Var) :
    (nb090AlphaDummy412 v) ∉
      (((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy412] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_051 (v : Var) :
    (nb090AlphaDummy388 v) ∉
      (((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv) :=
  by
  simpa only [nb090AlphaDummy388] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv)
      0

theorem nb090_fresh_052 (A : Class) :
    (nb090AlphaDummy437 A) ∉
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy437] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv)
      0

theorem nb090_fresh_053 (A : Class) :
    (nb090AlphaDummy461 A) ∉
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy461] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_054 (h : Var) :
    (nb090AlphaDummy438 h) ∉
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy438] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv)
      0

theorem nb090_fresh_055 (h : Var) :
    (nb090AlphaDummy462 h) ∉
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy462] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_056 (A : Class) :
    (nb090AlphaDummy473 A) ∉
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy473] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv)
      0

theorem nb090_fresh_057 (A : Class) :
    (nb090AlphaDummy497 A) ∉
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy497] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_058 (h : Var) :
    (nb090AlphaDummy474 h) ∉
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy474] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv)
      0

theorem nb090_fresh_059 (h : Var) :
    (nb090AlphaDummy498 h) ∉
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy498] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_060 (A : Class) :
    (nb090AlphaDummy515 A) ∉
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy515] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv)
      0

theorem nb090_fresh_061 (A : Class) :
    (nb090AlphaDummy539 A) ∉
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy539] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_062 (h : Var) :
    (nb090AlphaDummy516 h) ∉
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy516] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv)
      0

theorem nb090_fresh_063 (h : Var) :
    (nb090AlphaDummy540 h) ∉
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy540] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_064 (A : Class) :
    (nb090AlphaDummy575 A) ∉
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy575] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_065 (A : Class) :
    (nb090AlphaDummy551 A) ∉
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy551] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv)
      0

theorem nb090_fresh_066 (h : Var) :
    (nb090AlphaDummy576 h) ∉
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy576] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_067 (h : Var) :
    (nb090AlphaDummy552 h) ∉
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy552] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv)
      0

theorem nb090_fresh_068 (A : Class) :
    (nb090AlphaDummy611 A) ∉
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy611] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_069 (A : Class) :
    (nb090AlphaDummy587 A) ∉
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy587] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv)
      0

theorem nb090_fresh_070 (h : Var) :
    (nb090AlphaDummy612 h) ∉
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy612] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_071 (h : Var) :
    (nb090AlphaDummy588 h) ∉
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy588] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv)
      0

theorem nb090_fresh_072 (A : Class) :
    (nb090AlphaDummy623 A) ∉
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy623] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv)
      0

theorem nb090_fresh_073 (A : Class) :
    (nb090AlphaDummy647 A) ∉
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy647] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_074 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy624 v u h) ∉
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy624] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv)
      0

theorem nb090_fresh_075 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy648 v u h) ∉
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy619 v u h)
            (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy648] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy619 v u h)
            (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_076 (A : Class) :
    (nb090AlphaDummy657 A) ∉
      (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy657] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv)
      0

theorem nb090_fresh_077 (A : Class) :
    (nb090AlphaDummy658 A) ∉
      (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy658] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv)
      1

theorem nb090_distinct_078 (A : Class) :
    (nb090AlphaDummy657 A) ≠ (nb090AlphaDummy658 A) := by
  simpa only [nb090AlphaDummy657, nb090AlphaDummy658] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_079 (u : Var) :
    (nb090AlphaDummy659 u) ∉
      (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) :=
  by
  simpa only [nb090AlphaDummy659] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv)
      0

theorem nb090_fresh_080 (u : Var) :
    (nb090AlphaDummy660 u) ∉
      (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) :=
  by
  simpa only [nb090AlphaDummy660] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv)
      1

theorem nb090_distinct_081 (u : Var) :
    (nb090AlphaDummy659 u) ≠ (nb090AlphaDummy660 u) := by
  simpa only [nb090AlphaDummy659, nb090AlphaDummy660] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq
            (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_082 (A : Class) :
    (nb090AlphaDummy667 A) ∉
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy667] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv)
      0

theorem nb090_fresh_083 (A : Class) :
    (nb090AlphaDummy691 A) ∉
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy691] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_084 (u : Var) :
    (nb090AlphaDummy692 u) ∉
      (((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy692] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_085 (u : Var) :
    (nb090AlphaDummy668 u) ∉
      (((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv) :=
  by
  simpa only [nb090AlphaDummy668] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv)
      0

theorem nb090_fresh_086 (A : Class) :
    (nb090AlphaDummy705 A) ∉
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy705] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv)
      0

theorem nb090_fresh_087 (A : Class) :
    (nb090AlphaDummy775 A) ∉
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy699 A)
            (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy775] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy699 A)
            (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_088 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy706 v u h) ∉
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy706] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv)
      0

theorem nb090_fresh_089 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy776 v u h) ∉
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy701 v u h)
            (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy776] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy701 v u h)
            (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_090 (A : Class) :
    (nb090AlphaDummy711 A) ∉
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy711] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv)
      0

theorem nb090_fresh_091 (A : Class) :
    (nb090AlphaDummy712 A) ∉
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy712] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv)
      1

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part008`. -/


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

theorem nb090_distinct_092 (A : Class) :
    (nb090AlphaDummy711 A) ≠ (nb090AlphaDummy712 A) := by
  simpa only [nb090AlphaDummy711, nb090AlphaDummy712] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy707 A) (synWbr (Class.cv (nb090AlphaDummy041 A))
                (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_093 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy713 v u h) ∉
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy713] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv)
      0

theorem nb090_fresh_094 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy714 v u h) ∉
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy714] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv)
      1

theorem nb090_distinct_095 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy713 v u h) ≠ (nb090AlphaDummy714 v u h) := by
  simpa only [nb090AlphaDummy713, nb090AlphaDummy714] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_096 (A : Class) :
    (nb090AlphaDummy721 A) ∉
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy721] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv)
      0

theorem nb090_fresh_097 (A : Class) :
    (nb090AlphaDummy745 A) ∉
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy745] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_098 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy722 v u h) ∉
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy722] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv)
      0

theorem nb090_fresh_099 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy746 v u h) ∉
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy717 v u h)
            (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy746] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy717 v u h)
            (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_100 (A : Class) :
    (nb090AlphaDummy781 A) ∉
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy781] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv)
      0

theorem nb090_fresh_101 (A : Class) :
    (nb090AlphaDummy782 A) ∉
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy782] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv)
      1

theorem nb090_distinct_102 (A : Class) :
    (nb090AlphaDummy781 A) ≠ (nb090AlphaDummy782 A) := by
  simpa only [nb090AlphaDummy781, nb090AlphaDummy782] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy777 A) (synWbr (Class.cv (nb090AlphaDummy042 A))
                (Class.cv (nb090AlphaDummy000 A)) (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_103 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy783 v u h) ∉
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy783] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv)
      0

theorem nb090_fresh_104 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy784 v u h) ∉
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy784] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv)
      1

theorem nb090_distinct_105 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy783 v u h) ≠ (nb090AlphaDummy784 v u h) := by
  simpa only [nb090AlphaDummy783, nb090AlphaDummy784] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_106 (A : Class) :
    (nb090AlphaDummy791 A) ∉
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy791] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv)
      0

theorem nb090_fresh_107 (A : Class) :
    (nb090AlphaDummy815 A) ∉
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy815] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_108 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy792 v u h) ∉
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv) :=
  by
  simpa only [nb090AlphaDummy792] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv)
      0

theorem nb090_fresh_109 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy816 v u h) ∉
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy787 v u h)
            (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy816] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy787 v u h)
            (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_110 (A : Class) :
    (nb090AlphaDummy831 A) ∉
      (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy831] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv)
      0

theorem nb090_fresh_111 (A : Class) :
    (nb090AlphaDummy832 A) ∉
      (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy832] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv)
      1

theorem nb090_distinct_112 (A : Class) :
    (nb090AlphaDummy831 A) ≠ (nb090AlphaDummy832 A) := by
  simpa only [nb090AlphaDummy831, nb090AlphaDummy832] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq
            (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_113 (v : Var) :
    (nb090AlphaDummy833 v) ∉
      (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) :=
  by
  simpa only [nb090AlphaDummy833] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv)
      0

theorem nb090_fresh_114 (v : Var) :
    (nb090AlphaDummy834 v) ∉
      (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) :=
  by
  simpa only [nb090AlphaDummy834] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv)
      1

theorem nb090_distinct_115 (v : Var) :
    (nb090AlphaDummy833 v) ≠ (nb090AlphaDummy834 v) := by
  simpa only [nb090AlphaDummy833, nb090AlphaDummy834] using
    (freshVar_injective (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq
            (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_116 (A : Class) :
    (nb090AlphaDummy841 A) ∉
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy841] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv)
      0

theorem nb090_fresh_117 (A : Class) :
    (nb090AlphaDummy865 A) ∉
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy865] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_118 (v : Var) :
    (nb090AlphaDummy866 v) ∉
      (((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb090AlphaDummy866] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb090_fresh_119 (v : Var) :
    (nb090AlphaDummy842 v) ∉
      (((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv) :=
  by
  simpa only [nb090AlphaDummy842] using
    freshVar_not_mem
      (((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv)
      0

theorem nb090_fresh_120 (A : Class) :
    (nb090AlphaDummy129 A) ∉ (((Class.cv (nb090AlphaDummy000 A))).fv) := by
  simpa only [nb090AlphaDummy129] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy000 A))).fv) 0

theorem nb090_fresh_121 (A : Class) :
    (nb090AlphaDummy130 A) ∉ (((Class.cv (nb090AlphaDummy000 A))).fv) := by
  simpa only [nb090AlphaDummy130] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy000 A))).fv) 1

theorem nb090_distinct_122 (A : Class) :
    (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy130 A) := by
  simpa only [nb090AlphaDummy129, nb090AlphaDummy130] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_123 (A : Class) :
    (nb090AlphaDummy707 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy041 A))).fv) :=
  by
  simpa only [nb090AlphaDummy707] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy041 A))).fv)
      0

theorem nb090_fresh_124 (A : Class) :
    (nb090AlphaDummy777 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  simpa only [nb090AlphaDummy777] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv)
      0

theorem nb090_fresh_125 (A : Class) :
    (nb090AlphaDummy049 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy049] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
      0

theorem nb090_fresh_126 (A : Class) :
    (nb090AlphaDummy050 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy050] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
      1

theorem nb090_fresh_127 (A : Class) :
    (nb090AlphaDummy051 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy051] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
      2

theorem nb090_distinct_128 (A : Class) :
    (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy050 A) := by
  simpa only [nb090AlphaDummy049, nb090AlphaDummy050] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_129 (A : Class) :
    (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy051 A) := by
  simpa only [nb090AlphaDummy049, nb090AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_130 (A : Class) :
    (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy051 A) := by
  simpa only [nb090AlphaDummy050, nb090AlphaDummy051] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_131 (A : Class) :
    (nb090AlphaDummy041 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
      0

theorem nb090_fresh_132 (A : Class) :
    (nb090AlphaDummy042 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
      1

theorem nb090_distinct_133 (A : Class) :
    (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy042 A) := by
  simpa only [nb090AlphaDummy041, nb090AlphaDummy042] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_134 (A : Class) :
    (nb090AlphaDummy333 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb090AlphaDummy333] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) 0

theorem nb090_fresh_135 (A : Class) :
    (nb090AlphaDummy334 A) ∉
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb090AlphaDummy334] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) 1

theorem nb090_distinct_136 (A : Class) :
    (nb090AlphaDummy333 A) ≠ (nb090AlphaDummy334 A) := by
  simpa only [nb090AlphaDummy333, nb090AlphaDummy334] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_fresh_137 (A : Class) :
    (nb090AlphaDummy005 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  simpa only [nb090AlphaDummy005] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv)
      0

theorem nb090_fresh_138 (A : Class) :
    (nb090AlphaDummy006 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  simpa only [nb090AlphaDummy006] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv)
      1

theorem nb090_distinct_139 (A : Class) :
    (nb090AlphaDummy005 A) ≠ (nb090AlphaDummy006 A) := by
  simpa only [nb090AlphaDummy005, nb090AlphaDummy006] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy002 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_140 (A : Class) :
    (nb090AlphaDummy291 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv) :=
  by
  simpa only [nb090AlphaDummy291] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv)
      0

theorem nb090_fresh_141 (A : Class) :
    (nb090AlphaDummy292 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv) :=
  by
  simpa only [nb090AlphaDummy292] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv)
      1

theorem nb090_distinct_142 (A : Class) :
    (nb090AlphaDummy291 A) ≠ (nb090AlphaDummy292 A) := by
  simpa only [nb090AlphaDummy291, nb090AlphaDummy292] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy283 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_143 (A : Class) :
    (nb090AlphaDummy661 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv) :=
  by
  simpa only [nb090AlphaDummy661] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv)
      0

theorem nb090_fresh_144 (A : Class) :
    (nb090AlphaDummy662 A) ∉
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv) :=
  by
  simpa only [nb090AlphaDummy662] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv)
      1

theorem nb090_distinct_145 (A : Class) :
    (nb090AlphaDummy661 A) ≠ (nb090AlphaDummy662 A) := by
  simpa only [nb090AlphaDummy661, nb090AlphaDummy662] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy001 A))).fv ∪
        ((Class.cv (nb090AlphaDummy653 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_146 (A : Class) :
    (nb090AlphaDummy381 A) ∉
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv) :=
  by
  simpa only [nb090AlphaDummy381] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv)
      0

theorem nb090_fresh_147 (A : Class) :
    (nb090AlphaDummy382 A) ∉
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv) :=
  by
  simpa only [nb090AlphaDummy382] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv)
      1

theorem nb090_distinct_148 (A : Class) :
    (nb090AlphaDummy381 A) ≠ (nb090AlphaDummy382 A) := by
  simpa only [nb090AlphaDummy381, nb090AlphaDummy382] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy373 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_149 (A : Class) :
    (nb090AlphaDummy835 A) ∉
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv) :=
  by
  simpa only [nb090AlphaDummy835] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv)
      0

theorem nb090_fresh_150 (A : Class) :
    (nb090AlphaDummy836 A) ∉
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv) :=
  by
  simpa only [nb090AlphaDummy836] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv)
      1

theorem nb090_distinct_151 (A : Class) :
    (nb090AlphaDummy835 A) ≠ (nb090AlphaDummy836 A) := by
  simpa only [nb090AlphaDummy835, nb090AlphaDummy836] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy002 A))).fv ∪
        ((Class.cv (nb090AlphaDummy827 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_152 (A : Class) :
    (nb090AlphaDummy013 A) ∉ (((Class.cv (nb090AlphaDummy006 A))).fv) := by
  simpa only [nb090AlphaDummy013] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy006 A))).fv) 0

theorem nb090_fresh_153 (A : Class) :
    (nb090AlphaDummy014 A) ∉ (((Class.cv (nb090AlphaDummy006 A))).fv) := by
  simpa only [nb090AlphaDummy014] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy006 A))).fv) 1

theorem nb090_distinct_154 (A : Class) :
    (nb090AlphaDummy013 A) ≠ (nb090AlphaDummy014 A) := by
  simpa only [nb090AlphaDummy013, nb090AlphaDummy014] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy006 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_155 (v : Var) (u : Var) :
    (nb090AlphaDummy015 v u) ∉ (((Class.cv (nb090AlphaDummy008 v u))).fv) := by
  simpa only [nb090AlphaDummy015] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy008 v u))).fv) 0

theorem nb090_fresh_156 (v : Var) (u : Var) :
    (nb090AlphaDummy016 v u) ∉ (((Class.cv (nb090AlphaDummy008 v u))).fv) := by
  simpa only [nb090AlphaDummy016] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy008 v u))).fv) 1

theorem nb090_distinct_157 (v : Var) (u : Var) :
    (nb090AlphaDummy015 v u) ≠ (nb090AlphaDummy016 v u) := by
  simpa only [nb090AlphaDummy015, nb090AlphaDummy016] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy008 v u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_158 (A : Class) :
    (nb090AlphaDummy019 A) ∉
      (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy019] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_159 (A : Class) :
    (nb090AlphaDummy020 A) ∉
      (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy020] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_160 (A : Class) :
    (nb090AlphaDummy021 A) ∉
      (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy021] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_161 (A : Class) :
    (nb090AlphaDummy019 A) ≠ (nb090AlphaDummy020 A) := by
  simpa only [nb090AlphaDummy019, nb090AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_162 (A : Class) :
    (nb090AlphaDummy019 A) ≠ (nb090AlphaDummy021 A) := by
  simpa only [nb090AlphaDummy019, nb090AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_163 (A : Class) :
    (nb090AlphaDummy020 A) ≠ (nb090AlphaDummy021 A) := by
  simpa only [nb090AlphaDummy020, nb090AlphaDummy021] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_164 (v : Var) (u : Var) :
    (nb090AlphaDummy022 v u) ∉
      (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy022] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_165 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ∉
      (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy023] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_166 (v : Var) (u : Var) :
    (nb090AlphaDummy024 v u) ∉
      (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy024] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_167 (v : Var) (u : Var) :
    (nb090AlphaDummy022 v u) ≠ (nb090AlphaDummy023 v u) := by
  simpa only [nb090AlphaDummy022, nb090AlphaDummy023] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_distinct_168 (v : Var) (u : Var) :
    (nb090AlphaDummy022 v u) ≠ (nb090AlphaDummy024 v u) := by
  simpa only [nb090AlphaDummy022, nb090AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb090_distinct_169 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ≠ (nb090AlphaDummy024 v u) := by
  simpa only [nb090AlphaDummy023, nb090AlphaDummy024] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb090_fresh_170 (A : Class) :
    (nb090AlphaDummy031 A) ∉
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy020 A))).fv) :=
  by
  simpa only [nb090AlphaDummy031] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy020 A))).fv)
      0

theorem nb090_fresh_171 (A : Class) :
    (nb090AlphaDummy027 A) ∉
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv) :=
  by
  simpa only [nb090AlphaDummy027] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv)
      0

theorem nb090_fresh_172 (A : Class) :
    (nb090AlphaDummy033 A) ∉
      (((Class.cv (nb090AlphaDummy021 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv) :=
  by
  simpa only [nb090AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy021 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv)
      0

theorem nb090_fresh_173 (v : Var) (u : Var) :
    (nb090AlphaDummy032 v u) ∉
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy023 v u))).fv) :=
  by
  simpa only [nb090AlphaDummy032] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy023 v u))).fv)
      0

theorem nb090_fresh_174 (v : Var) (u : Var) :
    (nb090AlphaDummy028 v u) ∉
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv) :=
  by
  simpa only [nb090AlphaDummy028] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv)
      0

theorem nb090_fresh_175 (v : Var) (u : Var) :
    (nb090AlphaDummy034 v u) ∉
      (((Class.cv (nb090AlphaDummy024 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv) :=
  by
  simpa only [nb090AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy024 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv)
      0

theorem nb090_fresh_176 (A : Class) :
    (nb090AlphaDummy617 A) ∉
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  simpa only [nb090AlphaDummy617] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv)
      0

theorem nb090_fresh_177 (A : Class) :
    (nb090AlphaDummy618 A) ∉
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  simpa only [nb090AlphaDummy618] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv)
      1

theorem nb090_distinct_178 (A : Class) :
    (nb090AlphaDummy617 A) ≠ (nb090AlphaDummy618 A) := by
  simpa only [nb090AlphaDummy617, nb090AlphaDummy618] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy042 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_179 (A : Class) :
    (nb090AlphaDummy715 A) ∉
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv) :=
  by
  simpa only [nb090AlphaDummy715] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv)
      0

theorem nb090_fresh_180 (A : Class) :
    (nb090AlphaDummy716 A) ∉
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv) :=
  by
  simpa only [nb090AlphaDummy716] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv)
      1

theorem nb090_distinct_181 (A : Class) :
    (nb090AlphaDummy715 A) ≠ (nb090AlphaDummy716 A) := by
  simpa only [nb090AlphaDummy715, nb090AlphaDummy716] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy707 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_182 (A : Class) :
    (nb090AlphaDummy785 A) ∉
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv) :=
  by
  simpa only [nb090AlphaDummy785] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv)
      0

theorem nb090_fresh_183 (A : Class) :
    (nb090AlphaDummy786 A) ∉
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv) :=
  by
  simpa only [nb090AlphaDummy786] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv)
      1

theorem nb090_distinct_184 (A : Class) :
    (nb090AlphaDummy785 A) ≠ (nb090AlphaDummy786 A) := by
  simpa only [nb090AlphaDummy785, nb090AlphaDummy786] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy042 A))).fv ∪
        ((Class.cv (nb090AlphaDummy777 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_185 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy619 v u h) ∉
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy619] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv)
      0

theorem nb090_fresh_186 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy620 v u h) ∉
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy620] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv)
      1

theorem nb090_distinct_187 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy619 v u h) ≠ (nb090AlphaDummy620 v u h) := by
  simpa only [nb090AlphaDummy619, nb090AlphaDummy620] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_188 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy717 v u h) ∉
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy717] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv)
      0

theorem nb090_fresh_189 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy718 v u h) ∉
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy718] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv)
      1

theorem nb090_distinct_190 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy717 v u h) ≠ (nb090AlphaDummy718 v u h) := by
  simpa only [nb090AlphaDummy717, nb090AlphaDummy718] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_191 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy787 v u h) ∉
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy787] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv)
      0

theorem nb090_fresh_192 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy788 v u h) ∉
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv) :=
  by
  simpa only [nb090AlphaDummy788] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv)
      1

theorem nb090_distinct_193 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy787 v u h) ≠ (nb090AlphaDummy788 v u h) := by
  simpa only [nb090AlphaDummy787, nb090AlphaDummy788] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_194 (A : Class) :
    (nb090AlphaDummy057 A) ∉
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  simpa only [nb090AlphaDummy057] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
      0

theorem nb090_fresh_195 (A : Class) :
    (nb090AlphaDummy058 A) ∉
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  simpa only [nb090AlphaDummy058] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
      1

theorem nb090_distinct_196 (A : Class) :
    (nb090AlphaDummy057 A) ≠ (nb090AlphaDummy058 A) := by
  simpa only [nb090AlphaDummy057, nb090AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy049 A))).fv ∪
        ((Class.cv (nb090AlphaDummy050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_197 (A : Class) :
    (nb090AlphaDummy093 A) ∉
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv) :=
  by
  simpa only [nb090AlphaDummy093] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv)
      0

theorem nb090_fresh_198 (A : Class) :
    (nb090AlphaDummy094 A) ∉
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv) :=
  by
  simpa only [nb090AlphaDummy094] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv)
      1

theorem nb090_distinct_199 (A : Class) :
    (nb090AlphaDummy093 A) ≠ (nb090AlphaDummy094 A) := by
  simpa only [nb090AlphaDummy093, nb090AlphaDummy094] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy049 A))).fv ∪
        ((Class.cv (nb090AlphaDummy051 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_200 (A : Class) :
    (nb090AlphaDummy207 A) ∉
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  simpa only [nb090AlphaDummy207] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
      0

theorem nb090_fresh_201 (A : Class) :
    (nb090AlphaDummy208 A) ∉
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  simpa only [nb090AlphaDummy208] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv)
      1

theorem nb090_distinct_202 (A : Class) :
    (nb090AlphaDummy207 A) ≠ (nb090AlphaDummy208 A) := by
  simpa only [nb090AlphaDummy207, nb090AlphaDummy208] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy051 A))).fv ∪
        ((Class.cv (nb090AlphaDummy050 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_203 (h : Var) :
    (nb090AlphaDummy059 h) ∉
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  simpa only [nb090AlphaDummy059] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv)
      0

theorem nb090_fresh_204 (h : Var) :
    (nb090AlphaDummy060 h) ∉
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  simpa only [nb090AlphaDummy060] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv)
      1

theorem nb090_distinct_205 (h : Var) :
    (nb090AlphaDummy059 h) ≠ (nb090AlphaDummy060 h) := by
  simpa only [nb090AlphaDummy059, nb090AlphaDummy060] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_206 (h : Var) :
    (nb090AlphaDummy095 h) ∉
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) :=
  by
  simpa only [nb090AlphaDummy095] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv)
      0

theorem nb090_fresh_207 (h : Var) :
    (nb090AlphaDummy096 h) ∉
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) :=
  by
  simpa only [nb090AlphaDummy096] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv)
      1

theorem nb090_distinct_208 (h : Var) :
    (nb090AlphaDummy095 h) ≠ (nb090AlphaDummy096 h) := by
  simpa only [nb090AlphaDummy095, nb090AlphaDummy096] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy052 h))).fv ∪
        ((Class.cv (nb090AlphaDummy054 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_209 (h : Var) :
    (nb090AlphaDummy209 h) ∉
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  simpa only [nb090AlphaDummy209] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv)
      0

theorem nb090_fresh_210 (h : Var) :
    (nb090AlphaDummy210 h) ∉
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  simpa only [nb090AlphaDummy210] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv)
      1

theorem nb090_distinct_211 (h : Var) :
    (nb090AlphaDummy209 h) ≠ (nb090AlphaDummy210 h) := by
  simpa only [nb090AlphaDummy209, nb090AlphaDummy210] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy054 h))).fv ∪
        ((Class.cv (nb090AlphaDummy053 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_212 (A : Class) :
    (nb090AlphaDummy065 A) ∉ (((Class.cv (nb090AlphaDummy058 A))).fv) := by
  simpa only [nb090AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy058 A))).fv) 0

theorem nb090_fresh_213 (A : Class) :
    (nb090AlphaDummy066 A) ∉ (((Class.cv (nb090AlphaDummy058 A))).fv) := by
  simpa only [nb090AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy058 A))).fv) 1

theorem nb090_distinct_214 (A : Class) :
    (nb090AlphaDummy065 A) ≠ (nb090AlphaDummy066 A) := by
  simpa only [nb090AlphaDummy065, nb090AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy058 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_215 (h : Var) :
    (nb090AlphaDummy067 h) ∉ (((Class.cv (nb090AlphaDummy060 h))).fv) := by
  simpa only [nb090AlphaDummy067] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy060 h))).fv) 0

theorem nb090_fresh_216 (h : Var) :
    (nb090AlphaDummy068 h) ∉ (((Class.cv (nb090AlphaDummy060 h))).fv) := by
  simpa only [nb090AlphaDummy068] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy060 h))).fv) 1

theorem nb090_distinct_217 (h : Var) :
    (nb090AlphaDummy067 h) ≠ (nb090AlphaDummy068 h) := by
  simpa only [nb090AlphaDummy067, nb090AlphaDummy068] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy060 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_218 (A : Class) :
    (nb090AlphaDummy071 A) ∉
      (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy071] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_219 (A : Class) :
    (nb090AlphaDummy072 A) ∉
      (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_220 (A : Class) :
    (nb090AlphaDummy073 A) ∉
      (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_221 (A : Class) :
    (nb090AlphaDummy071 A) ≠ (nb090AlphaDummy072 A) := by
  simpa only [nb090AlphaDummy071, nb090AlphaDummy072] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_222 (A : Class) :
    (nb090AlphaDummy071 A) ≠ (nb090AlphaDummy073 A) := by
  simpa only [nb090AlphaDummy071, nb090AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_223 (A : Class) :
    (nb090AlphaDummy072 A) ≠ (nb090AlphaDummy073 A) := by
  simpa only [nb090AlphaDummy072, nb090AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_224 (h : Var) :
    (nb090AlphaDummy074 h) ∉
      (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_225 (h : Var) :
    (nb090AlphaDummy075 h) ∉
      (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy075] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_226 (h : Var) :
    (nb090AlphaDummy076 h) ∉
      (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy076] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_227 (h : Var) :
    (nb090AlphaDummy074 h) ≠ (nb090AlphaDummy075 h) := by
  simpa only [nb090AlphaDummy074, nb090AlphaDummy075] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_228 (h : Var) :
    (nb090AlphaDummy074 h) ≠ (nb090AlphaDummy076 h) := by
  simpa only [nb090AlphaDummy074, nb090AlphaDummy076] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_229 (h : Var) :
    (nb090AlphaDummy075 h) ≠ (nb090AlphaDummy076 h) := by
  simpa only [nb090AlphaDummy075, nb090AlphaDummy076] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_230 (A : Class) :
    (nb090AlphaDummy083 A) ∉
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy072 A))).fv) :=
  by
  simpa only [nb090AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy072 A))).fv)
      0

theorem nb090_fresh_231 (A : Class) :
    (nb090AlphaDummy079 A) ∉
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv) :=
  by
  simpa only [nb090AlphaDummy079] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv)
      0

theorem nb090_fresh_232 (A : Class) :
    (nb090AlphaDummy085 A) ∉
      (((Class.cv (nb090AlphaDummy073 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv) :=
  by
  simpa only [nb090AlphaDummy085] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy073 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv)
      0

theorem nb090_fresh_233 (h : Var) :
    (nb090AlphaDummy084 h) ∉
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy075 h))).fv) :=
  by
  simpa only [nb090AlphaDummy084] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy075 h))).fv)
      0

theorem nb090_fresh_234 (h : Var) :
    (nb090AlphaDummy080 h) ∉
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv) :=
  by
  simpa only [nb090AlphaDummy080] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv)
      0

theorem nb090_fresh_235 (h : Var) :
    (nb090AlphaDummy086 h) ∉
      (((Class.cv (nb090AlphaDummy076 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv) :=
  by
  simpa only [nb090AlphaDummy086] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy076 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv)
      0

theorem nb090_fresh_236 (A : Class) :
    (nb090AlphaDummy101 A) ∉ (((Class.cv (nb090AlphaDummy094 A))).fv) := by
  simpa only [nb090AlphaDummy101] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy094 A))).fv) 0

theorem nb090_fresh_237 (A : Class) :
    (nb090AlphaDummy102 A) ∉ (((Class.cv (nb090AlphaDummy094 A))).fv) := by
  simpa only [nb090AlphaDummy102] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy094 A))).fv) 1

theorem nb090_distinct_238 (A : Class) :
    (nb090AlphaDummy101 A) ≠ (nb090AlphaDummy102 A) := by
  simpa only [nb090AlphaDummy101, nb090AlphaDummy102] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy094 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_239 (h : Var) :
    (nb090AlphaDummy103 h) ∉ (((Class.cv (nb090AlphaDummy096 h))).fv) := by
  simpa only [nb090AlphaDummy103] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy096 h))).fv) 0

theorem nb090_fresh_240 (h : Var) :
    (nb090AlphaDummy104 h) ∉ (((Class.cv (nb090AlphaDummy096 h))).fv) := by
  simpa only [nb090AlphaDummy104] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy096 h))).fv) 1

theorem nb090_distinct_241 (h : Var) :
    (nb090AlphaDummy103 h) ≠ (nb090AlphaDummy104 h) := by
  simpa only [nb090AlphaDummy103, nb090AlphaDummy104] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy096 h))).fv) (i := 0) (j := 1)
      (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part009`. -/


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

theorem nb090_fresh_242 (A : Class) :
    (nb090AlphaDummy107 A) ∉
      (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_243 (A : Class) :
    (nb090AlphaDummy108 A) ∉
      (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_244 (A : Class) :
    (nb090AlphaDummy109 A) ∉
      (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy109] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_245 (A : Class) :
    (nb090AlphaDummy107 A) ≠ (nb090AlphaDummy108 A) := by
  simpa only [nb090AlphaDummy107, nb090AlphaDummy108] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_246 (A : Class) :
    (nb090AlphaDummy107 A) ≠ (nb090AlphaDummy109 A) := by
  simpa only [nb090AlphaDummy107, nb090AlphaDummy109] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_247 (A : Class) :
    (nb090AlphaDummy108 A) ≠ (nb090AlphaDummy109 A) := by
  simpa only [nb090AlphaDummy108, nb090AlphaDummy109] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_248 (h : Var) :
    (nb090AlphaDummy110 h) ∉
      (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy110] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_249 (h : Var) :
    (nb090AlphaDummy111 h) ∉
      (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy111] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_250 (h : Var) :
    (nb090AlphaDummy112 h) ∉
      (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy112] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_251 (h : Var) :
    (nb090AlphaDummy110 h) ≠ (nb090AlphaDummy111 h) := by
  simpa only [nb090AlphaDummy110, nb090AlphaDummy111] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_252 (h : Var) :
    (nb090AlphaDummy110 h) ≠ (nb090AlphaDummy112 h) := by
  simpa only [nb090AlphaDummy110, nb090AlphaDummy112] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_253 (h : Var) :
    (nb090AlphaDummy111 h) ≠ (nb090AlphaDummy112 h) := by
  simpa only [nb090AlphaDummy111, nb090AlphaDummy112] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_254 (A : Class) :
    (nb090AlphaDummy119 A) ∉
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy108 A))).fv) :=
  by
  simpa only [nb090AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy108 A))).fv)
      0

theorem nb090_fresh_255 (A : Class) :
    (nb090AlphaDummy115 A) ∉
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv) :=
  by
  simpa only [nb090AlphaDummy115] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv)
      0

theorem nb090_fresh_256 (A : Class) :
    (nb090AlphaDummy121 A) ∉
      (((Class.cv (nb090AlphaDummy109 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv) :=
  by
  simpa only [nb090AlphaDummy121] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy109 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv)
      0

theorem nb090_fresh_257 (h : Var) :
    (nb090AlphaDummy120 h) ∉
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy111 h))).fv) :=
  by
  simpa only [nb090AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy111 h))).fv)
      0

theorem nb090_fresh_258 (h : Var) :
    (nb090AlphaDummy116 h) ∉
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv) :=
  by
  simpa only [nb090AlphaDummy116] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv)
      0

theorem nb090_fresh_259 (h : Var) :
    (nb090AlphaDummy122 h) ∉
      (((Class.cv (nb090AlphaDummy112 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv) :=
  by
  simpa only [nb090AlphaDummy122] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy112 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv)
      0

theorem nb090_fresh_260 (A : Class) :
    (nb090AlphaDummy135 A) ∉
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv) :=
  by
  simpa only [nb090AlphaDummy135] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv)
      0

theorem nb090_fresh_261 (A : Class) :
    (nb090AlphaDummy136 A) ∉
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv) :=
  by
  simpa only [nb090AlphaDummy136] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv)
      1

theorem nb090_distinct_262 (A : Class) :
    (nb090AlphaDummy135 A) ≠ (nb090AlphaDummy136 A) := by
  simpa only [nb090AlphaDummy135, nb090AlphaDummy136] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy129 A))).fv ∪
        ((Class.cv (nb090AlphaDummy130 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_263 (A : Class) :
    (nb090AlphaDummy171 A) ∉
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv) :=
  by
  simpa only [nb090AlphaDummy171] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv)
      0

theorem nb090_fresh_264 (A : Class) :
    (nb090AlphaDummy172 A) ∉
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv) :=
  by
  simpa only [nb090AlphaDummy172] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv)
      1

theorem nb090_distinct_265 (A : Class) :
    (nb090AlphaDummy171 A) ≠ (nb090AlphaDummy172 A) := by
  simpa only [nb090AlphaDummy171, nb090AlphaDummy172] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy130 A))).fv ∪
        ((Class.cv (nb090AlphaDummy129 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_266 (h : Var) :
    (nb090AlphaDummy137 h) ∉
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) :=
  by
  simpa only [nb090AlphaDummy137] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv)
      0

theorem nb090_fresh_267 (h : Var) :
    (nb090AlphaDummy138 h) ∉
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) :=
  by
  simpa only [nb090AlphaDummy138] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv)
      1

theorem nb090_distinct_268 (h : Var) :
    (nb090AlphaDummy137 h) ≠ (nb090AlphaDummy138 h) := by
  simpa only [nb090AlphaDummy137, nb090AlphaDummy138] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
        ((Class.cv (nb090AlphaDummy132 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_269 (h : Var) :
    (nb090AlphaDummy173 h) ∉
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) :=
  by
  simpa only [nb090AlphaDummy173] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv)
      0

theorem nb090_fresh_270 (h : Var) :
    (nb090AlphaDummy174 h) ∉
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) :=
  by
  simpa only [nb090AlphaDummy174] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv)
      1

theorem nb090_distinct_271 (h : Var) :
    (nb090AlphaDummy173 h) ≠ (nb090AlphaDummy174 h) := by
  simpa only [nb090AlphaDummy173, nb090AlphaDummy174] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy132 h))).fv ∪
        ((Class.cv (nb090AlphaDummy131 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_272 (A : Class) :
    (nb090AlphaDummy143 A) ∉ (((Class.cv (nb090AlphaDummy136 A))).fv) := by
  simpa only [nb090AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy136 A))).fv) 0

theorem nb090_fresh_273 (A : Class) :
    (nb090AlphaDummy144 A) ∉ (((Class.cv (nb090AlphaDummy136 A))).fv) := by
  simpa only [nb090AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy136 A))).fv) 1

theorem nb090_distinct_274 (A : Class) :
    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy144 A) := by
  simpa only [nb090AlphaDummy143, nb090AlphaDummy144] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_275 (h : Var) :
    (nb090AlphaDummy145 h) ∉ (((Class.cv (nb090AlphaDummy138 h))).fv) := by
  simpa only [nb090AlphaDummy145] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy138 h))).fv) 0

theorem nb090_fresh_276 (h : Var) :
    (nb090AlphaDummy146 h) ∉ (((Class.cv (nb090AlphaDummy138 h))).fv) := by
  simpa only [nb090AlphaDummy146] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy138 h))).fv) 1

theorem nb090_distinct_277 (h : Var) :
    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy146 h) := by
  simpa only [nb090AlphaDummy145, nb090AlphaDummy146] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_278 (A : Class) :
    (nb090AlphaDummy149 A) ∉
      (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy149] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_279 (A : Class) :
    (nb090AlphaDummy150 A) ∉
      (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy150] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_280 (A : Class) :
    (nb090AlphaDummy151 A) ∉
      (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy151] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_281 (A : Class) :
    (nb090AlphaDummy149 A) ≠ (nb090AlphaDummy150 A) := by
  simpa only [nb090AlphaDummy149, nb090AlphaDummy150] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_282 (A : Class) :
    (nb090AlphaDummy149 A) ≠ (nb090AlphaDummy151 A) := by
  simpa only [nb090AlphaDummy149, nb090AlphaDummy151] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_283 (A : Class) :
    (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy151 A) := by
  simpa only [nb090AlphaDummy150, nb090AlphaDummy151] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_284 (h : Var) :
    (nb090AlphaDummy152 h) ∉
      (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy152] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_285 (h : Var) :
    (nb090AlphaDummy153 h) ∉
      (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy153] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_286 (h : Var) :
    (nb090AlphaDummy154 h) ∉
      (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy154] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_287 (h : Var) :
    (nb090AlphaDummy152 h) ≠ (nb090AlphaDummy153 h) := by
  simpa only [nb090AlphaDummy152, nb090AlphaDummy153] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_288 (h : Var) :
    (nb090AlphaDummy152 h) ≠ (nb090AlphaDummy154 h) := by
  simpa only [nb090AlphaDummy152, nb090AlphaDummy154] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_289 (h : Var) :
    (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy154 h) := by
  simpa only [nb090AlphaDummy153, nb090AlphaDummy154] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_290 (A : Class) :
    (nb090AlphaDummy161 A) ∉
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy150 A))).fv) :=
  by
  simpa only [nb090AlphaDummy161] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy150 A))).fv)
      0

theorem nb090_fresh_291 (A : Class) :
    (nb090AlphaDummy157 A) ∉
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv) :=
  by
  simpa only [nb090AlphaDummy157] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv)
      0

theorem nb090_fresh_292 (A : Class) :
    (nb090AlphaDummy163 A) ∉
      (((Class.cv (nb090AlphaDummy151 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv) :=
  by
  simpa only [nb090AlphaDummy163] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy151 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv)
      0

theorem nb090_fresh_293 (h : Var) :
    (nb090AlphaDummy162 h) ∉
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy153 h))).fv) :=
  by
  simpa only [nb090AlphaDummy162] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy153 h))).fv)
      0

theorem nb090_fresh_294 (h : Var) :
    (nb090AlphaDummy158 h) ∉
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv) :=
  by
  simpa only [nb090AlphaDummy158] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv)
      0

theorem nb090_fresh_295 (h : Var) :
    (nb090AlphaDummy164 h) ∉
      (((Class.cv (nb090AlphaDummy154 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv) :=
  by
  simpa only [nb090AlphaDummy164] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy154 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv)
      0

theorem nb090_fresh_296 (A : Class) :
    (nb090AlphaDummy179 A) ∉ (((Class.cv (nb090AlphaDummy172 A))).fv) := by
  simpa only [nb090AlphaDummy179] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy172 A))).fv) 0

theorem nb090_fresh_297 (A : Class) :
    (nb090AlphaDummy180 A) ∉ (((Class.cv (nb090AlphaDummy172 A))).fv) := by
  simpa only [nb090AlphaDummy180] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy172 A))).fv) 1

theorem nb090_distinct_298 (A : Class) :
    (nb090AlphaDummy179 A) ≠ (nb090AlphaDummy180 A) := by
  simpa only [nb090AlphaDummy179, nb090AlphaDummy180] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy172 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_299 (h : Var) :
    (nb090AlphaDummy181 h) ∉ (((Class.cv (nb090AlphaDummy174 h))).fv) := by
  simpa only [nb090AlphaDummy181] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy174 h))).fv) 0

theorem nb090_fresh_300 (h : Var) :
    (nb090AlphaDummy182 h) ∉ (((Class.cv (nb090AlphaDummy174 h))).fv) := by
  simpa only [nb090AlphaDummy182] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy174 h))).fv) 1

theorem nb090_distinct_301 (h : Var) :
    (nb090AlphaDummy181 h) ≠ (nb090AlphaDummy182 h) := by
  simpa only [nb090AlphaDummy181, nb090AlphaDummy182] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy174 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_302 (A : Class) :
    (nb090AlphaDummy185 A) ∉
      (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy185] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_303 (A : Class) :
    (nb090AlphaDummy186 A) ∉
      (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy186] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_304 (A : Class) :
    (nb090AlphaDummy187 A) ∉
      (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy187] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_305 (A : Class) :
    (nb090AlphaDummy185 A) ≠ (nb090AlphaDummy186 A) := by
  simpa only [nb090AlphaDummy185, nb090AlphaDummy186] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_306 (A : Class) :
    (nb090AlphaDummy185 A) ≠ (nb090AlphaDummy187 A) := by
  simpa only [nb090AlphaDummy185, nb090AlphaDummy187] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_307 (A : Class) :
    (nb090AlphaDummy186 A) ≠ (nb090AlphaDummy187 A) := by
  simpa only [nb090AlphaDummy186, nb090AlphaDummy187] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_308 (h : Var) :
    (nb090AlphaDummy188 h) ∉
      (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy188] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_309 (h : Var) :
    (nb090AlphaDummy189 h) ∉
      (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy189] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_310 (h : Var) :
    (nb090AlphaDummy190 h) ∉
      (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy190] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_311 (h : Var) :
    (nb090AlphaDummy188 h) ≠ (nb090AlphaDummy189 h) := by
  simpa only [nb090AlphaDummy188, nb090AlphaDummy189] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_312 (h : Var) :
    (nb090AlphaDummy188 h) ≠ (nb090AlphaDummy190 h) := by
  simpa only [nb090AlphaDummy188, nb090AlphaDummy190] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_313 (h : Var) :
    (nb090AlphaDummy189 h) ≠ (nb090AlphaDummy190 h) := by
  simpa only [nb090AlphaDummy189, nb090AlphaDummy190] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_314 (A : Class) :
    (nb090AlphaDummy197 A) ∉
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy186 A))).fv) :=
  by
  simpa only [nb090AlphaDummy197] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy186 A))).fv)
      0

theorem nb090_fresh_315 (A : Class) :
    (nb090AlphaDummy193 A) ∉
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv) :=
  by
  simpa only [nb090AlphaDummy193] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv)
      0

theorem nb090_fresh_316 (A : Class) :
    (nb090AlphaDummy199 A) ∉
      (((Class.cv (nb090AlphaDummy187 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv) :=
  by
  simpa only [nb090AlphaDummy199] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy187 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv)
      0

theorem nb090_fresh_317 (h : Var) :
    (nb090AlphaDummy198 h) ∉
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy189 h))).fv) :=
  by
  simpa only [nb090AlphaDummy198] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy189 h))).fv)
      0

theorem nb090_fresh_318 (h : Var) :
    (nb090AlphaDummy194 h) ∉
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv) :=
  by
  simpa only [nb090AlphaDummy194] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv)
      0

theorem nb090_fresh_319 (h : Var) :
    (nb090AlphaDummy200 h) ∉
      (((Class.cv (nb090AlphaDummy190 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv) :=
  by
  simpa only [nb090AlphaDummy200] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy190 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv)
      0

theorem nb090_fresh_320 (A : Class) :
    (nb090AlphaDummy215 A) ∉ (((Class.cv (nb090AlphaDummy208 A))).fv) := by
  simpa only [nb090AlphaDummy215] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy208 A))).fv) 0

theorem nb090_fresh_321 (A : Class) :
    (nb090AlphaDummy216 A) ∉ (((Class.cv (nb090AlphaDummy208 A))).fv) := by
  simpa only [nb090AlphaDummy216] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy208 A))).fv) 1

theorem nb090_distinct_322 (A : Class) :
    (nb090AlphaDummy215 A) ≠ (nb090AlphaDummy216 A) := by
  simpa only [nb090AlphaDummy215, nb090AlphaDummy216] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy208 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_323 (h : Var) :
    (nb090AlphaDummy217 h) ∉ (((Class.cv (nb090AlphaDummy210 h))).fv) := by
  simpa only [nb090AlphaDummy217] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy210 h))).fv) 0

theorem nb090_fresh_324 (h : Var) :
    (nb090AlphaDummy218 h) ∉ (((Class.cv (nb090AlphaDummy210 h))).fv) := by
  simpa only [nb090AlphaDummy218] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy210 h))).fv) 1

theorem nb090_distinct_325 (h : Var) :
    (nb090AlphaDummy217 h) ≠ (nb090AlphaDummy218 h) := by
  simpa only [nb090AlphaDummy217, nb090AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy210 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_326 (A : Class) :
    (nb090AlphaDummy221 A) ∉
      (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy221] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_327 (A : Class) :
    (nb090AlphaDummy222 A) ∉
      (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy222] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_328 (A : Class) :
    (nb090AlphaDummy223 A) ∉
      (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy223] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_329 (A : Class) :
    (nb090AlphaDummy221 A) ≠ (nb090AlphaDummy222 A) := by
  simpa only [nb090AlphaDummy221, nb090AlphaDummy222] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_330 (A : Class) :
    (nb090AlphaDummy221 A) ≠ (nb090AlphaDummy223 A) := by
  simpa only [nb090AlphaDummy221, nb090AlphaDummy223] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_331 (A : Class) :
    (nb090AlphaDummy222 A) ≠ (nb090AlphaDummy223 A) := by
  simpa only [nb090AlphaDummy222, nb090AlphaDummy223] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_332 (h : Var) :
    (nb090AlphaDummy224 h) ∉
      (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy224] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_333 (h : Var) :
    (nb090AlphaDummy225 h) ∉
      (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy225] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_334 (h : Var) :
    (nb090AlphaDummy226 h) ∉
      (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy226] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_335 (h : Var) :
    (nb090AlphaDummy224 h) ≠ (nb090AlphaDummy225 h) := by
  simpa only [nb090AlphaDummy224, nb090AlphaDummy225] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_336 (h : Var) :
    (nb090AlphaDummy224 h) ≠ (nb090AlphaDummy226 h) := by
  simpa only [nb090AlphaDummy224, nb090AlphaDummy226] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_337 (h : Var) :
    (nb090AlphaDummy225 h) ≠ (nb090AlphaDummy226 h) := by
  simpa only [nb090AlphaDummy225, nb090AlphaDummy226] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_338 (A : Class) :
    (nb090AlphaDummy233 A) ∉
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy222 A))).fv) :=
  by
  simpa only [nb090AlphaDummy233] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy222 A))).fv)
      0

theorem nb090_fresh_339 (A : Class) :
    (nb090AlphaDummy229 A) ∉
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv) :=
  by
  simpa only [nb090AlphaDummy229] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv)
      0

theorem nb090_fresh_340 (A : Class) :
    (nb090AlphaDummy235 A) ∉
      (((Class.cv (nb090AlphaDummy223 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv) :=
  by
  simpa only [nb090AlphaDummy235] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy223 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv)
      0

theorem nb090_fresh_341 (h : Var) :
    (nb090AlphaDummy234 h) ∉
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy225 h))).fv) :=
  by
  simpa only [nb090AlphaDummy234] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy225 h))).fv)
      0

theorem nb090_fresh_342 (h : Var) :
    (nb090AlphaDummy230 h) ∉
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv) :=
  by
  simpa only [nb090AlphaDummy230] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv)
      0

theorem nb090_fresh_343 (h : Var) :
    (nb090AlphaDummy236 h) ∉
      (((Class.cv (nb090AlphaDummy226 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv) :=
  by
  simpa only [nb090AlphaDummy236] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy226 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv)
      0

theorem nb090_fresh_344 (A : Class) :
    (nb090AlphaDummy247 A) ∉
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv) :=
  by
  simpa only [nb090AlphaDummy247] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv)
      0

theorem nb090_fresh_345 (A : Class) :
    (nb090AlphaDummy248 A) ∉
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv) :=
  by
  simpa only [nb090AlphaDummy248] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv)
      1

theorem nb090_distinct_346 (A : Class) :
    (nb090AlphaDummy247 A) ≠ (nb090AlphaDummy248 A) := by
  simpa only [nb090AlphaDummy247, nb090AlphaDummy248] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy244 A))).fv ∪
        ((Class.cv (nb090AlphaDummy243 A))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_347 (h : Var) :
    (nb090AlphaDummy249 h) ∉
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv) :=
  by
  simpa only [nb090AlphaDummy249] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv)
      0

theorem nb090_fresh_348 (h : Var) :
    (nb090AlphaDummy250 h) ∉
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv) :=
  by
  simpa only [nb090AlphaDummy250] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv)
      1

theorem nb090_distinct_349 (h : Var) :
    (nb090AlphaDummy249 h) ≠ (nb090AlphaDummy250 h) := by
  simpa only [nb090AlphaDummy249, nb090AlphaDummy250] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy246 h))).fv ∪
        ((Class.cv (nb090AlphaDummy245 h))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_350 (A : Class) :
    (nb090AlphaDummy255 A) ∉ (((Class.cv (nb090AlphaDummy248 A))).fv) := by
  simpa only [nb090AlphaDummy255] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy248 A))).fv) 0

theorem nb090_fresh_351 (A : Class) :
    (nb090AlphaDummy256 A) ∉ (((Class.cv (nb090AlphaDummy248 A))).fv) := by
  simpa only [nb090AlphaDummy256] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy248 A))).fv) 1

theorem nb090_distinct_352 (A : Class) :
    (nb090AlphaDummy255 A) ≠ (nb090AlphaDummy256 A) := by
  simpa only [nb090AlphaDummy255, nb090AlphaDummy256] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy248 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_353 (h : Var) :
    (nb090AlphaDummy257 h) ∉ (((Class.cv (nb090AlphaDummy250 h))).fv) := by
  simpa only [nb090AlphaDummy257] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy250 h))).fv) 0

theorem nb090_fresh_354 (h : Var) :
    (nb090AlphaDummy258 h) ∉ (((Class.cv (nb090AlphaDummy250 h))).fv) := by
  simpa only [nb090AlphaDummy258] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy250 h))).fv) 1

theorem nb090_distinct_355 (h : Var) :
    (nb090AlphaDummy257 h) ≠ (nb090AlphaDummy258 h) := by
  simpa only [nb090AlphaDummy257, nb090AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy250 h))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_356 (A : Class) :
    (nb090AlphaDummy261 A) ∉
      (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy261] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_357 (A : Class) :
    (nb090AlphaDummy262 A) ∉
      (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy262] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_358 (A : Class) :
    (nb090AlphaDummy263 A) ∉
      (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy263] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_359 (A : Class) :
    (nb090AlphaDummy261 A) ≠ (nb090AlphaDummy262 A) := by
  simpa only [nb090AlphaDummy261, nb090AlphaDummy262] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_360 (A : Class) :
    (nb090AlphaDummy261 A) ≠ (nb090AlphaDummy263 A) := by
  simpa only [nb090AlphaDummy261, nb090AlphaDummy263] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_361 (A : Class) :
    (nb090AlphaDummy262 A) ≠ (nb090AlphaDummy263 A) := by
  simpa only [nb090AlphaDummy262, nb090AlphaDummy263] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_362 (h : Var) :
    (nb090AlphaDummy264 h) ∉
      (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy264] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_363 (h : Var) :
    (nb090AlphaDummy265 h) ∉
      (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy265] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_364 (h : Var) :
    (nb090AlphaDummy266 h) ∉
      (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy266] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_365 (h : Var) :
    (nb090AlphaDummy264 h) ≠ (nb090AlphaDummy265 h) := by
  simpa only [nb090AlphaDummy264, nb090AlphaDummy265] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_366 (h : Var) :
    (nb090AlphaDummy264 h) ≠ (nb090AlphaDummy266 h) := by
  simpa only [nb090AlphaDummy264, nb090AlphaDummy266] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_367 (h : Var) :
    (nb090AlphaDummy265 h) ≠ (nb090AlphaDummy266 h) := by
  simpa only [nb090AlphaDummy265, nb090AlphaDummy266] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_368 (A : Class) :
    (nb090AlphaDummy273 A) ∉
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy262 A))).fv) :=
  by
  simpa only [nb090AlphaDummy273] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy262 A))).fv)
      0

theorem nb090_fresh_369 (A : Class) :
    (nb090AlphaDummy269 A) ∉
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv) :=
  by
  simpa only [nb090AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv)
      0

theorem nb090_fresh_370 (A : Class) :
    (nb090AlphaDummy275 A) ∉
      (((Class.cv (nb090AlphaDummy263 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv) :=
  by
  simpa only [nb090AlphaDummy275] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy263 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv)
      0

theorem nb090_fresh_371 (h : Var) :
    (nb090AlphaDummy274 h) ∉
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy265 h))).fv) :=
  by
  simpa only [nb090AlphaDummy274] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy265 h))).fv)
      0

theorem nb090_fresh_372 (h : Var) :
    (nb090AlphaDummy270 h) ∉
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv) :=
  by
  simpa only [nb090AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv)
      0

theorem nb090_fresh_373 (h : Var) :
    (nb090AlphaDummy276 h) ∉
      (((Class.cv (nb090AlphaDummy266 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv) :=
  by
  simpa only [nb090AlphaDummy276] using
    freshVar_not_mem
      (((Class.cv (nb090AlphaDummy266 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv)
      0

theorem nb090_fresh_374 (A : Class) :
    (nb090AlphaDummy327 A) ∉ (((Class.cv (nb090AlphaDummy285 A))).fv) := by
  simpa only [nb090AlphaDummy327] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy285 A))).fv) 0

theorem nb090_fresh_375 (u : Var) :
    (nb090AlphaDummy328 u) ∉ (((Class.cv (nb090AlphaDummy286 u))).fv) := by
  simpa only [nb090AlphaDummy328] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy286 u))).fv) 0

theorem nb090_fresh_376 (A : Class) :
    (nb090AlphaDummy299 A) ∉ (((Class.cv (nb090AlphaDummy292 A))).fv) := by
  simpa only [nb090AlphaDummy299] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy292 A))).fv) 0

theorem nb090_fresh_377 (A : Class) :
    (nb090AlphaDummy300 A) ∉ (((Class.cv (nb090AlphaDummy292 A))).fv) := by
  simpa only [nb090AlphaDummy300] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy292 A))).fv) 1

theorem nb090_distinct_378 (A : Class) :
    (nb090AlphaDummy299 A) ≠ (nb090AlphaDummy300 A) := by
  simpa only [nb090AlphaDummy299, nb090AlphaDummy300] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy292 A))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_379 (u : Var) :
    (nb090AlphaDummy301 u) ∉ (((Class.cv (nb090AlphaDummy294 u))).fv) := by
  simpa only [nb090AlphaDummy301] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy294 u))).fv) 0

theorem nb090_fresh_380 (u : Var) :
    (nb090AlphaDummy302 u) ∉ (((Class.cv (nb090AlphaDummy294 u))).fv) := by
  simpa only [nb090AlphaDummy302] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy294 u))).fv) 1

theorem nb090_distinct_381 (u : Var) :
    (nb090AlphaDummy301 u) ≠ (nb090AlphaDummy302 u) := by
  simpa only [nb090AlphaDummy301, nb090AlphaDummy302] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy294 u))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb090_fresh_382 (A : Class) :
    (nb090AlphaDummy305 A) ∉
      (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy305] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_383 (A : Class) :
    (nb090AlphaDummy306 A) ∉
      (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy306] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_384 (A : Class) :
    (nb090AlphaDummy307 A) ∉
      (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy307] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_385 (A : Class) :
    (nb090AlphaDummy305 A) ≠ (nb090AlphaDummy306 A) := by
  simpa only [nb090AlphaDummy305, nb090AlphaDummy306] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb090_distinct_386 (A : Class) :
    (nb090AlphaDummy305 A) ≠ (nb090AlphaDummy307 A) := by
  simpa only [nb090AlphaDummy305, nb090AlphaDummy307] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb090_distinct_387 (A : Class) :
    (nb090AlphaDummy306 A) ≠ (nb090AlphaDummy307 A) := by
  simpa only [nb090AlphaDummy306, nb090AlphaDummy307] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb090_fresh_388 (u : Var) :
    (nb090AlphaDummy308 u) ∉
      (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy308] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 0

theorem nb090_fresh_389 (u : Var) :
    (nb090AlphaDummy309 u) ∉
      (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy309] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 1

theorem nb090_fresh_390 (u : Var) :
    (nb090AlphaDummy310 u) ∉
      (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb090AlphaDummy310] using
    freshVar_not_mem (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) 2

theorem nb090_distinct_391 (u : Var) :
    (nb090AlphaDummy308 u) ≠ (nb090AlphaDummy309 u) := by
  simpa only [nb090AlphaDummy308, nb090AlphaDummy309] using
    (freshVar_injective (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
